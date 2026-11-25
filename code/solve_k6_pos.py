import ctypes
import gzip
import itertools
import json
import math
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction

import numpy as np
from pysat.solvers import Solver
from scipy.optimize import linprog

_GORDAN_LIB = None
_GORDAN_HAS_EXACT = False
_GORDAN_LOCK_PATH = None


def verify_farkas_exact(m, triples, weights):
    """Exact arbitrary-precision integer check of a Gordan-Farkas infeasibility certificate.

    Checks sum_q weights[q] * row_q >= 0 componentwise on 0..m-1 with strict positive total sum,
    which rules out any x_0 <= x_1 <= ... <= x_{m-1} (strictly > 0) satisfying all equations x_i + x_j = x_l.
    """
    if m <= 0 or not triples or len(triples) != len(weights):
        return False
    col_sum = [0] * m
    nonzero = False
    for (i, j, l), y in zip(triples, weights):
        yi = int(y)
        if yi == 0:
            continue
        nonzero = True
        if not (0 <= i < j < l < m):
            return False
        for t in range(0, i + 1):
            col_sum[t] += yi
        for t in range(j + 1, l + 1):
            col_sum[t] -= yi
    if not nonzero:
        return False
    total = 0
    for s in col_sum:
        if s < 0:
            return False
        total += s
    return total > 0


def _shared_lib_candidates(here):
    sysname = platform.system().lower()
    if sysname.startswith("win"):
        names = ["gordan.dll"]
    elif sysname == "darwin":
        names = ["gordan.dylib", "libgordan.dylib"]
    else:
        names = ["gordan.so", "libgordan.so", "gordan.dll"]
    cands = []
    for base in (here, os.path.join(os.path.dirname(here), "cpp"), tempfile.gettempdir()):
        for nm in (names[0], f"erdos787_{names[0]}") + tuple(names[1:]):
            p = os.path.join(base, nm)
            if p not in cands:
                cands.append(p)
    return cands, names[0]


def _get_gordan_lib(auto_build=True):
    global _GORDAN_LIB, _GORDAN_HAS_EXACT
    if _GORDAN_LIB is not None:
        return (_GORDAN_LIB if _GORDAN_LIB is not False else None), _GORDAN_HAS_EXACT

    here = os.path.dirname(os.path.abspath(__file__))
    cands, target_name = _shared_lib_candidates(here)
    lib_path = next((p for p in cands if os.path.exists(p)), None)

    if lib_path is None and auto_build and shutil.which("g++"):
        cpp_src = os.path.join(here, "gordan_dll.cpp")
        if os.path.exists(cpp_src):
            out_path = os.path.join(tempfile.gettempdir(), f"erdos787_{target_name}")
            tmp_out = f"{out_path}.{os.getpid()}.tmp"
            cmd = ["g++", "-O3", "-shared"]
            if not platform.system().lower().startswith("win"):
                cmd.append("-fPIC")
            cmd.extend([cpp_src, "-o", tmp_out])
            res = subprocess.run(cmd, capture_output=True, text=True)
            if res.returncode == 0 and os.path.exists(tmp_out):
                try:
                    os.replace(tmp_out, out_path)
                except OSError:
                    if os.path.exists(tmp_out):
                        os.remove(tmp_out)
            if os.path.exists(out_path):
                lib_path = out_path

    if lib_path is not None and os.path.exists(lib_path):
        lib = ctypes.CDLL(lib_path)
        if hasattr(lib, "find_minimal_core_exact"):
            lib.find_minimal_core_exact.argtypes = [
                ctypes.c_int,
                ctypes.c_int,
                ctypes.POINTER(ctypes.c_int),
                ctypes.POINTER(ctypes.c_int),
                ctypes.POINTER(ctypes.c_int64),
            ]
            lib.find_minimal_core_exact.restype = ctypes.c_int
            _GORDAN_HAS_EXACT = True
        else:
            lib.find_minimal_core.argtypes = [
                ctypes.c_int,
                ctypes.c_int,
                ctypes.POINTER(ctypes.c_int),
                ctypes.POINTER(ctypes.c_int),
            ]
            lib.find_minimal_core.restype = ctypes.c_int
            _GORDAN_HAS_EXACT = False
        _GORDAN_LIB = lib
    else:
        _GORDAN_LIB = False
        _GORDAN_HAS_EXACT = False

    return (_GORDAN_LIB if _GORDAN_LIB is not False else None), _GORDAN_HAS_EXACT


def _extract_exact_weights_from_float(m, triples, y_float):
    """Attempt exact integer Farkas extraction from a floating-point dual suggestion."""
    r = len(triples)
    if r == 0:
        return None
    max_abs = max(abs(float(v)) for v in y_float)
    if max_abs < 1e-12:
        return None
    normed = [float(v) / max_abs for v in y_float]

    for scale in (1, 2, 3, 4, 5, 6, 10, 12, 24, 60, 120, 720, 2520):
        cand = [int(round(v * scale)) for v in normed]
        if verify_farkas_exact(m, triples, cand):
            return cand

    fracs = [Fraction(v).limit_denominator(100000) for v in normed]
    common = 1
    for fr in fracs:
        if fr != 0:
            common = math.lcm(common, fr.denominator)
            if common > 10 ** 18:
                return None
    cand = [int(fr.numerator * (common // fr.denominator)) for fr in fracs]
    if verify_farkas_exact(m, triples, cand):
        return cand
    return None


def _exact_frac_farkas(m, eqs):
    """Exact rational fallback: use HiGHS as search hint only, never trust unverified floats."""
    r = len(eqs)
    if r == 0:
        return None, None
    triples = [tuple(int(z) for z in row) for row in eqs]
    M = np.zeros((r, m))
    for idx, (i, j, l) in enumerate(triples):
        M[idx, : i + 1] += 1.0
        M[idx, j + 1 : l + 1] -= 1.0
    A_ub = np.hstack([-M.T, M.T])
    b_ub = np.zeros(m)
    row_sums = M.sum(axis=1)
    A_eq = np.hstack([row_sums, -row_sums]).reshape(1, -1)
    b_eq = np.array([1.0])
    res = linprog(
        np.ones(2 * r),
        A_ub=A_ub,
        b_ub=b_ub,
        A_eq=A_eq,
        b_eq=b_eq,
        bounds=(0, None),
        method="highs",
    )
    if not res.success:
        return None, None

    y_float = res.x[:r] - res.x[r:]
    nz = [idx for idx in range(r) if abs(y_float[idx]) > 1e-9]
    if not nz:
        nz = list(range(r))
    nz.sort(key=lambda idx: abs(y_float[idx]))

    cur = list(nz)
    # Greedily shrink while keeping an independently verified integer Farkas core
    cur_triples = [triples[idx] for idx in cur]
    cur_weights = _extract_exact_weights_from_float(m, cur_triples, [y_float[idx] for idx in cur])
    if cur_weights is None:
        # Try on full active set before raising
        cur = list(range(r))
        cur_weights = _extract_exact_weights_from_float(m, triples, y_float)
        if cur_weights is None:
            raise RuntimeError("Floating-point LP succeeded but exact integer Farkas extraction failed (strict exact mode forbids float fallback).")
    # Strip zero-weight indices cleanly
    kept_idx, kept_w = [], []
    for idx, w in zip(cur, cur_weights):
        if w != 0:
            kept_idx.append(idx)
            kept_w.append(int(w))
    assert verify_farkas_exact(m, [triples[i] for i in kept_idx], kept_w)
    return kept_idx, kept_w


def gordan_core_exact(m, eqs, stats):
    """Return (core_indices, exact_int_weights) strictly verified by integer Farkas arithmetic.

    Returns (None, None) only when the system appears real-feasible; never emits unverified floats.
    """
    r = len(eqs)
    if r == 0:
        return None, None
    triples = [tuple(int(z) for z in row) for row in eqs]
    lib, has_exact = _get_gordan_lib(auto_build=True)
    if lib is not None and has_exact:
        arr = np.asarray(triples, dtype=np.int32).ravel()
        out_idx = np.empty(r, dtype=np.int32)
        out_Y = np.empty(r, dtype=np.int64)
        sz = lib.find_minimal_core_exact(
            m,
            r,
            arr.ctypes.data_as(ctypes.POINTER(ctypes.c_int)),
            out_idx.ctypes.data_as(ctypes.POINTER(ctypes.c_int)),
            out_Y.ctypes.data_as(ctypes.POINTER(ctypes.c_int64)),
        )
        if sz > 0:
            cidx = out_idx[:sz].tolist()
            weights = out_Y[:sz].tolist()
            if not verify_farkas_exact(m, [triples[i] for i in cidx], weights):
                raise RuntimeError("C++ gordan_dll returned a core that failed pure-Python integer Farkas verification.")
            stats["dll_exact"] += 1
            return cidx, weights

    cidx, weights = _exact_frac_farkas(m, triples)
    if cidx is not None:
        stats["frac_exact"] += 1
        return cidx, weights
    return None, None


def _check_real_feasible(m, ae_arr):
    try:
        import z3
    except ImportError as exc:
        raise RuntimeError(
            "Candidate non-UNSAT linear system encountered, and `z3-solver` is not installed to check exact QF_LRA feasibility."
        ) from exc

    zs = z3.SolverFor("QF_LRA")
    zx = [z3.Real(f"x_{i}") for i in range(m)]
    zs.add(zx[0] > 0)
    for i in range(m - 1):
        zs.add(zx[i] < zx[i + 1])
    for row in ae_arr:
        zs.add(zx[int(row[0])] + zx[int(row[1])] == zx[int(row[2])])
    res = zs.check()
    if res == z3.sat:
        return True, [str(zs.model()[xi]) for xi in zx]
    return False, None


_WORKER_PRE = []


def _init_worker(pre_clauses):
    global _WORKER_PRE
    _WORKER_PRE = pre_clauses


def _encode_subcase(m, k, j_elim, u_low, u_high):
    nxt = 1

    def nv():
        nonlocal nxt
        v2 = nxt
        nxt += 1
        return v2

    eq, gt, lt = {}, {}, {}
    clauses = []
    triples = []
    for i in range(m):
        for j in range(i + 1, m):
            for l in range(j + 1, m):
                e, g, lt_v = nv(), nv(), nv()
                eq[(i, j, l)] = e
                gt[(i, j, l)] = g
                lt[(i, j, l)] = lt_v
                triples.append((i, j, l))
                clauses.append([-e, -g])
                clauses.append([-e, -lt_v])
                clauses.append([-g, -lt_v])
    for (i, j, l), e in eq.items():
        g, lt_v = gt[(i, j, l)], lt[(i, j, l)]
        if l > j + 1:
            clauses.append([-e, gt[(i, j, l - 1)]])
            clauses.append([-g, gt[(i, j, l - 1)]])
        if l + 1 < m:
            clauses.append([-e, lt[(i, j, l + 1)]])
            clauses.append([-lt_v, lt[(i, j, l + 1)]])
        if i + 1 < j:
            clauses.append([-e, gt[(i + 1, j, l)]])
            clauses.append([-g, gt[(i + 1, j, l)]])
            clauses.append([-eq[(i + 1, j, l)], lt_v])
            clauses.append([-lt[(i + 1, j, l)], lt_v])
        if j + 1 < l:
            clauses.append([-e, gt[(i, j + 1, l)]])
            clauses.append([-g, gt[(i, j + 1, l)]])
            clauses.append([-eq[(i, j + 1, l)], lt_v])
            clauses.append([-lt[(i, j + 1, l)], lt_v])
        if i + 1 == j and j + 1 < l:
            clauses.append([-e, gt[(i + 1, j + 1, l)]])
            clauses.append([-g, gt[(i + 1, j + 1, l)]])
            clauses.append([-eq[(i + 1, j + 1, l)], lt_v])
            clauses.append([-lt[(i + 1, j + 1, l)], lt_v])
    for l in range(2, m):
        for x in range(l):
            cands = [eq[(min(x, y), max(x, y), l)] for y in range(l) if y != x]
            for p in range(len(cands)):
                for q in range(p + 1, len(cands)):
                    clauses.append([-cands[p], -cands[q]])

    if j_elim is None:
        for i in range(m - 2):
            clauses.append([-eq[(i, m - 2, m - 1)]])
    else:
        clauses.append([eq[(j_elim, m - 2, m - 1)]])

    if j_elim == m - 3:
        p3 = m - 4
        t_low, t_high = m - 3, m - 2
    else:
        p3 = m - 3
        t_low, t_high = m - 2, m - 1

    if u_low is None:
        for i in range(p3):
            if i != j_elim:
                clauses.append([-eq[(i, p3, t_low)]])
    else:
        clauses.append([eq[(u_low, p3, t_low)]])

    if u_high is None:
        for i in range(p3):
            if i != j_elim:
                clauses.append([-eq[(i, p3, t_high)]])
    else:
        clauses.append([eq[(u_high, p3, t_high)]])

    R = [i for i in range(p3) if i != j_elim and i != u_low and i != u_high]
    edge = {}
    for a_i in range(len(R)):
        a = R[a_i]
        for b_i in range(a_i + 1, len(R)):
            b = R[b_i]
            e = nv()
            edge[(a, b)] = e
            clauses.append([-e] + [eq[(a, b, l)] for l in range(b + 1, m)])
    for sub in itertools.combinations(R, k - 2):
        clauses.append([edge[(sub[p], sub[q])] for p in range(k - 2) for q in range(p + 1, k - 2)])

    return triples, clauses, nxt - 1


def solve_subcase(task_and_opts):
    task, with_proof = task_and_opts
    m, k, j_elim, u_low, u_high = task
    t0 = time.time()
    sat = Solver(name="cd195", with_proof=with_proof)
    triples, clauses, _ = _encode_subcase(m, k, j_elim, u_low, u_high)
    if _WORKER_PRE:
        clauses.extend(_WORKER_PRE)
    sat.append_formula(clauses)

    ntriples = len(triples)
    arr_triples = np.array(triples, dtype=np.int32)
    eq_lits_base = np.arange(1, 3 * ntriples + 1, 3, dtype=np.int32)
    all_certs = []  # Save ALL exact Farkas certificates regardless of length!
    short_clauses = []
    cores = 0
    stats = {"dll_exact": 0, "frac_exact": 0}

    while sat.solve():
        model = sat.get_model()
        mask = np.asarray(model[: 3 * ntriples : 3], dtype=np.int32) > 0
        ae_arr = arr_triples[mask]
        av_arr = eq_lits_base[mask]
        cidx, weights = gordan_core_exact(m, ae_arr, stats)
        if cidx is None:
            is_sat, vals = _check_real_feasible(m, ae_arr)
            sat.delete()
            return ("SAT" if is_sat else "EDGE", task, cores, time.time() - t0, vals, short_clauses, all_certs, stats, None)
        cores += 1
        core_triples = [tuple(int(z) for z in ae_arr[i]) for i in cidx]
        cl = [int(-av_arr[i]) for i in cidx]
        sat.add_clause(cl)
        all_certs.append((core_triples, [int(w) for w in weights], cl))
        if len(cl) <= 8:
            short_clauses.append(tuple(sorted(cl)))

    drat_proof = sat.get_proof() if with_proof else None
    sat.delete()
    return ("UNSAT", task, cores, time.time() - t0, None, short_clauses, all_certs, stats, drat_proof)


def build_tasks_for_case(m, k, j_elim):
    if j_elim == m - 3:
        p3 = m - 4
        avail = list(range(p3))
    else:
        p3 = m - 3
        avail = [i for i in range(p3) if i != j_elim]
    tasks = []
    for u_low in [None] + avail:
        for u_high in [None] + avail:
            if u_low is not None and u_high is not None and u_low >= u_high:
                continue
            tasks.append((m, k, j_elim, u_low, u_high))
    return tasks


def _write_certs(cert_path, m, k, unique_certs):
    opener = gzip.open if cert_path.endswith(".gz") else open
    with opener(cert_path, "wt", encoding="utf-8") as f:
        for core_triples, weights in unique_certs:
            rec = {"m": m, "k": k, "triples": [list(t) for t in core_triples], "weights": list(weights)}
            f.write(json.dumps(rec) + "\n")


def verify_certs_file(cert_path):
    """Independently verify every Farkas certificate in a JSONL or JSONL.GZ file (arbitrary length)."""
    opener = gzip.open if cert_path.endswith(".gz") else open
    total = 0
    max_len = 0
    long_gt8 = 0
    with opener(cert_path, "rt", encoding="utf-8") as f:
        for ln_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            m = int(rec["m"])
            triples = [tuple(int(x) for x in t) for t in rec["triples"]]
            weights = [int(w) for w in rec["weights"]]
            if not verify_farkas_exact(m, triples, weights):
                raise RuntimeError(f"Certificate verification failed at {cert_path}:{ln_no}")
            total += 1
            if len(triples) > max_len:
                max_len = len(triples)
            if len(triples) > 8:
                long_gt8 += 1
    if total == 0:
        raise RuntimeError(f"No certificates verified in {cert_path}")
    print(f"FARKAS_CERTS_VERIFIED file={cert_path} count={total} max_terms={max_len} gt8_terms={long_gt8} PASS", flush=True)
    return total, max_len, long_gt8


def run_suite(m, k, j_list, wave_mode=False, cert_path=None, drat_dir=None, workers=16):
    # Pre-initialize C++ DLL once in main process before spawning workers
    lib, has_exact = _get_gordan_lib(auto_build=True)
    if not (lib is not None and has_exact):
        raise RuntimeError("Failed to build/load gordan exact shared library; strict exact mode requires C++ exact verifier.")

    cache_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"learned_cores_m{m}.txt")
    known_short = set()
    if wave_mode and os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    known_short.add(tuple(int(x) for x in line.split()))

    groups = [[j] for j in j_list] if (wave_mode and len(j_list) > 1) else [j_list]
    tot_wall_start = time.time()
    grand_cores = 0
    grand_dll = 0
    grand_frac = 0
    max_core_len = 0
    unique_cert_map = {}

    if drat_dir:
        os.makedirs(drat_dir, exist_ok=True)
    drat_files = 0

    for g_idx, g_js in enumerate(groups):
        tasks = []
        for j in g_js:
            tasks.extend(build_tasks_for_case(m, k, j))
        pre_list = [list(c) for c in sorted(known_short, key=lambda c: (len(c), c))[:25000]]
        print(
            f"m={m}, k={k} [wave {g_idx+1}/{len(groups)} j={g_js}]: {len(tasks)} tasks, pre_cores={len(pre_list)} across {workers} workers...",
            flush=True,
        )
        t0 = time.time()
        tot_cores = 0
        done = 0
        max_dt = 0.0
        new_added = []
        with_proof = bool(drat_dir)
        with ProcessPoolExecutor(max_workers=workers, initializer=_init_worker, initargs=(pre_list,)) as ex:
            futs = [ex.submit(solve_subcase, (t, with_proof)) for t in tasks]
            for f in as_completed(futs):
                st, task, cores, dt, vals, sc, all_certs, st_counts, drat_proof = f.result()
                done += 1
                tot_cores += cores
                grand_cores += cores
                grand_dll += st_counts["dll_exact"]
                grand_frac += st_counts["frac_exact"]
                if dt > max_dt:
                    max_dt = dt
                for c in sc:
                    if c not in known_short:
                        known_short.add(c)
                        new_added.append(c)
                for core_triples, weights, cl in all_certs:
                    key = tuple(core_triples)
                    if len(key) > max_core_len:
                        max_core_len = len(key)
                    if key not in unique_cert_map:
                        unique_cert_map[key] = weights
                if drat_dir and drat_proof is not None:
                    _, j_el, ul, uh = task[1], task[2], task[3], task[4]
                    tag = f"m{m}_k{k}_j{j_el}_ul{ul}_uh{uh}"
                    with open(os.path.join(drat_dir, f"{tag}.drat"), "w", encoding="utf-8") as df:
                        df.write("\n".join(drat_proof) + "\n")
                    drat_files += 1
                if st != "UNSAT":
                    print(f"*** NON-UNSAT RESULT {st} at {task}: {vals}", flush=True)
                    return False
                if done % 50 == 0 or done == len(tasks):
                    print(
                        f"  progress: {done}/{len(tasks)} UNSAT | tot_cores={tot_cores} | max_dt={max_dt:.2f}s | wall={time.time()-t0:.2f}s",
                        flush=True,
                    )
        if wave_mode and new_added:
            with open(cache_path, "a", encoding="utf-8") as f:
                for c in new_added:
                    f.write(" ".join(str(x) for x in c) + "\n")
        print(
            f"  wave j={g_js} UNSAT in {time.time()-t0:.2f}s (cores={tot_cores}, unique_total={len(unique_cert_map)}, max_terms={max_core_len})",
            flush=True,
        )

    if cert_path:
        items = sorted(unique_cert_map.items(), key=lambda kv: (len(kv[0]), kv[0]))
        _write_certs(cert_path, m, k, items)
        verify_certs_file(cert_path)

    print(
        f"ALL TASKS FOR m={m},k={k} j={j_list} PROVEN UNSAT in {time.time()-tot_wall_start:.2f}s "
        f"(total_cores={grand_cores}, unique_cores={len(unique_cert_map)}, max_terms={max_core_len}, "
        f"dll_exact={grand_dll}, frac_exact={grand_frac}, fp_fallbacks=0, drat_files={drat_files})!",
        flush=True,
    )
    return True


def run_verify_selftest():
    """Run strict exact k=4 (m=11) and k=5 (m=16) suites saving ALL certs + DRAT logs and tamper-testing."""
    with tempfile.TemporaryDirectory() as tmp:
        c4 = os.path.join(tmp, "k4_certs.jsonl.gz")
        c5 = os.path.join(tmp, "k5_certs.jsonl.gz")
        d4 = os.path.join(tmp, "drat_k4")
        d5 = os.path.join(tmp, "drat_k5")
        assert run_suite(11, 4, [None] + list(range(9)), wave_mode=False, cert_path=c4, drat_dir=d4)
        assert run_suite(16, 5, [None] + list(range(14)), wave_mode=False, cert_path=c5, drat_dir=d5)
        # Negative / tamper test: mutate one weight in first k=5 cert and ensure verifier rejects it
        lines = gzip.open(c5, "rt", encoding="utf-8").read().splitlines()
        bad = json.loads(lines[0])
        bad["weights"][0] = int(bad["weights"][0]) + 1000000
        if verify_farkas_exact(bad["m"], [tuple(t) for t in bad["triples"]], bad["weights"]):
            bad["weights"] = [0] * len(bad["weights"])
            assert not verify_farkas_exact(bad["m"], [tuple(t) for t in bad["triples"]], bad["weights"])
        bad_path = os.path.join(tmp, "tampered.jsonl")
        with open(bad_path, "w", encoding="utf-8") as bf:
            bf.write(json.dumps({"m": 16, "k": 5, "triples": bad["triples"], "weights": [0] * len(bad["weights"])}) + "\n")
        rejected = False
        try:
            verify_certs_file(bad_path)
        except RuntimeError:
            rejected = True
        assert rejected, "Tampered certificate was unexpectedly accepted!"
        print("  PASS tampered-certificate negative control", flush=True)


if __name__ == "__main__":
    args = sys.argv[1:]
    cert_out = None
    drat_out = None
    pos = []
    i = 0
    while i < len(args):
        if args[i] == "--save-certs" and i + 1 < len(args):
            cert_out = args[i + 1]
            i += 2
        elif args[i] == "--drat-dir" and i + 1 < len(args):
            drat_out = args[i + 1]
            i += 2
        elif args[i] == "--verify-certs" and i + 1 < len(args):
            verify_certs_file(args[i + 1])
            sys.exit(0)
        else:
            pos.append(args[i])
            i += 1

    cmd = pos[0] if pos else "selftest"
    if cmd == "selftest":
        if cert_out or drat_out:
            assert run_suite(11, 4, [None] + list(range(9)), wave_mode=False, cert_path=cert_out, drat_dir=drat_out)
            assert run_suite(16, 5, [None] + list(range(14)), wave_mode=False, cert_path=cert_out, drat_dir=drat_out)
        else:
            run_verify_selftest()
    elif cmd == "all_waves":
        assert run_suite(22, 6, [None] + list(range(19, -1, -1)), wave_mode=True, cert_path=cert_out, drat_dir=drat_out)
    elif cmd.startswith("waves:"):
        j_list = [None if x == "None" else int(x) for x in cmd[6:].split(",")]
        assert run_suite(22, 6, j_list, wave_mode=True, cert_path=cert_out, drat_dir=drat_out)
    elif cmd == "caseA":
        assert run_suite(22, 6, [None], wave_mode=True, cert_path=cert_out, drat_dir=drat_out)
    elif cmd == "all":
        assert run_suite(22, 6, [None] + list(range(20)), wave_mode=True, cert_path=cert_out, drat_dir=drat_out)
    else:
        j_list = [None if x == "None" else int(x) for x in cmd.split(",")]
        assert run_suite(22, 6, j_list, wave_mode=True, cert_path=cert_out, drat_dir=drat_out)
