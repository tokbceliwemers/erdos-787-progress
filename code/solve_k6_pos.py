import time, itertools, sys, os, ctypes
import numpy as np
from scipy.optimize import linprog
from pysat.solvers import Solver
from concurrent.futures import ProcessPoolExecutor, as_completed

_GORDAN_LIB = None
def _get_gordan_lib():
    global _GORDAN_LIB
    if _GORDAN_LIB is None:
        here = os.path.dirname(os.path.abspath(__file__))
        dll_path = next((p for p in [os.path.join(here, 'gordan.dll'), os.path.join(os.path.dirname(here), 'cpp', 'gordan.dll')] if os.path.exists(p)), '')
        if os.path.exists(dll_path):
            lib = ctypes.CDLL(dll_path)
            lib.find_minimal_core.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int)]
            lib.find_minimal_core.restype = ctypes.c_int
            _GORDAN_LIB = lib
        else:
            _GORDAN_LIB = False
    return _GORDAN_LIB if _GORDAN_LIB is not False else None

def gordan_core(m, eqs):
    r = len(eqs)
    if r == 0:
        return None
    lib = _get_gordan_lib()
    if lib is not None:
        arr = np.asarray(eqs, dtype=np.int32).ravel()
        out = np.empty(r, dtype=np.int32)
        sz = lib.find_minimal_core(m, r, arr.ctypes.data_as(ctypes.POINTER(ctypes.c_int)), out.ctypes.data_as(ctypes.POINTER(ctypes.c_int)))
        if sz > 0:
            return out[:sz].tolist()
    M = np.zeros((r, m))
    for idx, (i, j, l) in enumerate(eqs):
        M[idx, :i+1] += 1.0
        M[idx, j+1:l+1] -= 1.0
    A_ub = np.hstack([-M.T, M.T])
    b_ub = np.zeros(m)
    row_sums = M.sum(axis=1)
    A_eq = np.hstack([row_sums, -row_sums]).reshape(1, -1)
    b_eq = np.array([1.0])
    res = linprog(np.ones(2*r), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs')
    if not res.success:
        return None
    y = res.x[:r] - res.x[r:]
    return [idx for idx in range(r) if abs(y[idx]) > 1e-7]

_WORKER_PRE = []
def _init_worker(pre_clauses):
    global _WORKER_PRE
    _WORKER_PRE = pre_clauses

def solve_subcase(task):
    m, k, j_elim, u_low, u_high = task
    t0 = time.time()
    sat = Solver(name='cd195')
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
        for j in range(i+1, m):
            for l in range(j+1, m):
                e, g, lt_v = nv(), nv(), nv()
                eq[(i,j,l)] = e; gt[(i,j,l)] = g; lt[(i,j,l)] = lt_v
                triples.append((i, j, l))
                clauses.append([-e, -g]); clauses.append([-e, -lt_v]); clauses.append([-g, -lt_v])
    for (i,j,l), e in eq.items():
        g, lt_v = gt[(i,j,l)], lt[(i,j,l)]
        if l > j+1:
            clauses.append([-e, gt[(i,j,l-1)]]); clauses.append([-g, gt[(i,j,l-1)]])
        if l+1 < m:
            clauses.append([-e, lt[(i,j,l+1)]]); clauses.append([-lt_v, lt[(i,j,l+1)]])
        if i+1 < j:
            clauses.append([-e, gt[(i+1,j,l)]]); clauses.append([-g, gt[(i+1,j,l)]])
            clauses.append([-eq[(i+1,j,l)], lt_v]); clauses.append([-lt[(i+1,j,l)], lt_v])
        if j+1 < l:
            clauses.append([-e, gt[(i,j+1,l)]]); clauses.append([-g, gt[(i,j+1,l)]])
            clauses.append([-eq[(i,j+1,l)], lt_v]); clauses.append([-lt[(i,j+1,l)], lt_v])
        if i+1 == j and j+1 < l:
            clauses.append([-e, gt[(i+1,j+1,l)]]); clauses.append([-g, gt[(i+1,j+1,l)]])
            clauses.append([-eq[(i+1,j+1,l)], lt_v]); clauses.append([-lt[(i+1,j+1,l)], lt_v])
    for l in range(2, m):
        for x in range(l):
            cands = [eq[(min(x,y), max(x,y), l)] for y in range(l) if y != x]
            for p in range(len(cands)):
                for q in range(p+1, len(cands)):
                    clauses.append([-cands[p], -cands[q]])

    if j_elim is None:
        for i in range(m - 2):
            clauses.append([-eq[(i, m-2, m-1)]])
    else:
        clauses.append([eq[(j_elim, m-2, m-1)]])

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
        for b_i in range(a_i+1, len(R)):
            b = R[b_i]
            e = nv()
            edge[(a,b)] = e
            clauses.append([-e] + [eq[(a,b,l)] for l in range(b+1, m)])
    for sub in itertools.combinations(R, k - 2):
        clauses.append([edge[(sub[p], sub[q])] for p in range(k-2) for q in range(p+1, k-2)])

    if _WORKER_PRE:
        clauses.extend(_WORKER_PRE)
    sat.append_formula(clauses)

    ntriples = len(triples)
    arr_triples = np.array(triples, dtype=np.int32)
    eq_lits_base = np.arange(1, 3 * ntriples + 1, 3, dtype=np.int32)
    short_cores = []
    cores = 0
    while sat.solve():
        model = sat.get_model()
        mask = np.asarray(model[:3 * ntriples:3], dtype=np.int32) > 0
        ae_arr = arr_triples[mask]
        av_arr = eq_lits_base[mask]
        cidx = gordan_core(m, ae_arr)
        if cidx is None:
            import z3
            zs = z3.SolverFor('QF_LRA')
            zx = [z3.Real(f'x_{i}') for i in range(m)]
            zs.add(zx[0] > 0)
            for i in range(m-1): zs.add(zx[i] < zx[i+1])
            for row in ae_arr: zs.add(zx[int(row[0])] + zx[int(row[1])] == zx[int(row[2])])
            if zs.check() == z3.sat:
                vals = [str(zs.model()[xi]) for xi in zx]
                sat.delete()
                return ('SAT', task, cores, time.time()-t0, vals, short_cores)
            else:
                sat.delete()
                return ('EDGE', task, cores, time.time()-t0, None, short_cores)
        cores += 1
        cl = [int(-av_arr[i]) for i in cidx]
        sat.add_clause(cl)
        if len(cl) <= 8:
            short_cores.append(tuple(sorted(cl)))
    sat.delete()
    return ('UNSAT', task, cores, time.time()-t0, None, short_cores)

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

def run_suite(m, k, j_list, wave_mode=False):
    cache_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), f'learned_cores_m{m}.txt')
    known_cores = set()
    if wave_mode and os.path.exists(cache_path):
        with open(cache_path) as f:
            for line in f:
                line = line.strip()
                if line:
                    known_cores.add(tuple(int(x) for x in line.split()))

    groups = [[j] for j in j_list] if (wave_mode and len(j_list) > 1) else [j_list]
    tot_wall_start = time.time()
    grand_cores = 0
    for g_idx, g_js in enumerate(groups):
        tasks = []
        for j in g_js:
            tasks.extend(build_tasks_for_case(m, k, j))
        pre_list = [list(c) for c in sorted(known_cores, key=lambda c: (len(c), c))[:25000]]
        print(f'm={m}, k={k} [wave {g_idx+1}/{len(groups)} j={g_js}]: {len(tasks)} tasks, pre_cores={len(pre_list)} across 16 workers...', flush=True)
        t0 = time.time()
        tot_cores = 0
        done = 0
        max_dt = 0.0
        new_added = []
        with ProcessPoolExecutor(max_workers=16, initializer=_init_worker, initargs=(pre_list,)) as ex:
            futs = [ex.submit(solve_subcase, t) for t in tasks]
            for f in as_completed(futs):
                st, task, cores, dt, vals, sc = f.result()
                done += 1
                tot_cores += cores
                grand_cores += cores
                if dt > max_dt: max_dt = dt
                for c in sc:
                    if c not in known_cores:
                        known_cores.add(c)
                        new_added.append(c)
                if st != 'UNSAT':
                    print(f'*** NON-UNSAT RESULT {st} at {task}: {vals}', flush=True)
                    return False
                if done % 50 == 0 or done == len(tasks):
                    print(f'  progress: {done}/{len(tasks)} UNSAT | tot_cores={tot_cores} | max_dt={max_dt:.2f}s | wall={time.time()-t0:.2f}s', flush=True)
        if wave_mode and new_added:
            with open(cache_path, 'a') as f:
                for c in new_added:
                    f.write(' '.join(str(x) for x in c) + '\n')
        print(f'  wave j={g_js} UNSAT in {time.time()-t0:.2f}s (cores={tot_cores}, +{len(new_added)} unique short cores -> total cached {len(known_cores)})', flush=True)
    print(f'ALL TASKS FOR m={m},k={k} j={j_list} PROVEN UNSAT in {time.time()-tot_wall_start:.2f}s (grand_cores={grand_cores})!', flush=True)
    return True

def solve_j_single(task_j):
    m, k, j_elim = task_j
    t0 = time.time()
    sat = Solver(name='cd195')
    nxt = 1
    def nv():
        nonlocal nxt
        v2 = nxt
        nxt += 1
        return v2
    eq, gt, lt = {}, {}, {}
    for i in range(m):
        for j in range(i+1, m):
            for l in range(j+1, m):
                eq[(i,j,l)] = nv()
                gt[(i,j,l)] = nv()
                lt[(i,j,l)] = nv()
                sat.add_clause([-eq[(i,j,l)], -gt[(i,j,l)]])
                sat.add_clause([-eq[(i,j,l)], -lt[(i,j,l)]])
                sat.add_clause([-gt[(i,j,l)], -lt[(i,j,l)]])
    for i in range(m):
        for j in range(i+1, m):
            for l in range(j+1, m):
                if l > j+1:
                    sat.add_clause([-eq[(i,j,l)], gt[(i,j,l-1)]])
                    sat.add_clause([-gt[(i,j,l)], gt[(i,j,l-1)]])
                if l+1 < m:
                    sat.add_clause([-eq[(i,j,l)], lt[(i,j,l+1)]])
                    sat.add_clause([-lt[(i,j,l)], lt[(i,j,l+1)]])
                if i+1 < j:
                    sat.add_clause([-eq[(i,j,l)], gt[(i+1,j,l)]])
                    sat.add_clause([-gt[(i,j,l)], gt[(i+1,j,l)]])
                    sat.add_clause([-eq[(i+1,j,l)], lt[(i,j,l)]])
                    sat.add_clause([-lt[(i+1,j,l)], lt[(i,j,l)]])
                if j+1 < l:
                    sat.add_clause([-eq[(i,j,l)], gt[(i,j+1,l)]])
                    sat.add_clause([-gt[(i,j,l)], gt[(i,j+1,l)]])
                    sat.add_clause([-eq[(i,j+1,l)], lt[(i,j,l)]])
                    sat.add_clause([-lt[(i,j+1,l)], lt[(i,j,l)]])
                if i+1 == j and j+1 < l:
                    sat.add_clause([-eq[(i,j,l)], gt[(i+1,j+1,l)]])
                    sat.add_clause([-gt[(i,j,l)], gt[(i+1,j+1,l)]])
                    sat.add_clause([-eq[(i+1,j+1,l)], lt[(i,j,l)]])
                    sat.add_clause([-lt[(i+1,j+1,l)], lt[(i,j,l)]])
    for l in range(2, m):
        for x in range(l):
            cands = [eq[(min(x,y), max(x,y), l)] for y in range(l) if y != x]
            for p in range(len(cands)):
                for q in range(p+1, len(cands)):
                    sat.add_clause([-cands[p], -cands[q]])

    # Step 2: x_{m-2} with x_{m-1}
    if j_elim is None:
        for i in range(m - 2):
            sat.add_clause([-eq[(i, m-2, m-1)]])
    else:
        sat.add_clause([eq[(j_elim, m-2, m-1)]])

    # Step 3 encoded directly via inR[i] indicators for p3
    if j_elim == m - 3:
        p3 = m - 4
        t_low, t_high = m - 3, m - 2
    else:
        p3 = m - 3
        t_low, t_high = m - 2, m - 1

    avail = [i for i in range(p3) if i != j_elim]
    inR = {}
    for i in avail:
        v = nv()
        inR[i] = v
        sat.add_clause([-eq[(i, p3, t_low)], -v])
        sat.add_clause([-eq[(i, p3, t_high)], -v])
        sat.add_clause([eq[(i, p3, t_low)], eq[(i, p3, t_high)], v])

    edge = {}
    for a_i in range(len(avail)):
        a = avail[a_i]
        for b_i in range(a_i+1, len(avail)):
            b = avail[b_i]
            e = nv()
            edge[(a,b)] = e
            sat.add_clause([-e] + [eq[(a,b,l)] for l in range(b+1, m)])
    for sub in itertools.combinations(avail, k - 2):
        lits_in = [-inR[x] for x in sub]
        sat.add_clause(lits_in + [edge[(sub[p], sub[q])] for p in range(k-2) for q in range(p+1, k-2)])

    all_eq = list(eq.items())
    cores = 0
    while sat.solve():
        model = sat.get_model()
        ae, av = [], []
        for (tup, vid) in all_eq:
            if model[vid - 1] > 0:
                ae.append(tup)
                av.append(vid)
        cidx = gordan_core(m, ae)
        if cidx is None:
            import z3
            zs = z3.SolverFor('QF_LRA')
            zx = [z3.Real(f'x_{i}') for i in range(m)]
            zs.add(zx[0] > 0)
            for i in range(m-1): zs.add(zx[i] < zx[i+1])
            for (i,j,l) in ae: zs.add(zx[i] + zx[j] == zx[l])
            if zs.check() == z3.sat:
                vals = [str(zs.model()[xi]) for xi in zx]
                sat.delete()
                return ('SAT', task_j, cores, time.time()-t0, vals)
            else:
                sat.delete()
                return ('EDGE', task_j, cores, time.time()-t0, None)
        cores += 1
        sat.add_clause([-av[i] for i in cidx])
    sat.delete()
    return ('UNSAT', task_j, cores, time.time()-t0, None)

def run_suite_single(m, k, j_list):
    tasks = [(m, k, j) for j in j_list]
    print(f'm={m}, k={k} [SINGLE]: Running {len(tasks)} j-cases for j={j_list} across 16 workers...', flush=True)
    t0 = time.time()
    tot_cores = 0
    done = 0
    with ProcessPoolExecutor(max_workers=16) as ex:
        futs = [ex.submit(solve_j_single, t) for t in tasks]
        for f in as_completed(futs):
            st, task, cores, dt, vals = f.result()
            done += 1
            tot_cores += cores
            if st != 'UNSAT':
                print(f'*** NON-UNSAT RESULT {st} at {task}: {vals}', flush=True)
                return False
            print(f'  [{done}/{len(tasks)}] j={task[2]} UNSAT | cores={cores} | dt={dt:.2f}s | wall={time.time()-t0:.2f}s', flush=True)
    print(f'ALL {len(tasks)} J-CASES FOR m={m},k={k} PROVEN UNSAT in {time.time()-t0:.2f}s (tot_cores={tot_cores})!', flush=True)
    return True

def solve_ju_shared(task_ju):
    m, k, j_elim, u_low = task_ju
    t0 = time.time()
    sat = Solver(name='cd195')
    nxt = 1
    def nv():
        nonlocal nxt
        v2 = nxt
        nxt += 1
        return v2
    eq, gt, lt = {}, {}, {}
    clauses = []
    for i in range(m):
        for j in range(i+1, m):
            for l in range(j+1, m):
                e, g, lt_v = nv(), nv(), nv()
                eq[(i,j,l)] = e; gt[(i,j,l)] = g; lt[(i,j,l)] = lt_v
                clauses.append([-e, -g]); clauses.append([-e, -lt_v]); clauses.append([-g, -lt_v])
    for i in range(m):
        for j in range(i+1, m):
            for l in range(j+1, m):
                e, g, lt_v = eq[(i,j,l)], gt[(i,j,l)], lt[(i,j,l)]
                if l > j+1:
                    clauses.append([-e, gt[(i,j,l-1)]]); clauses.append([-g, gt[(i,j,l-1)]])
                if l+1 < m:
                    clauses.append([-e, lt[(i,j,l+1)]]); clauses.append([-lt_v, lt[(i,j,l+1)]])
                if i+1 < j:
                    clauses.append([-e, gt[(i+1,j,l)]]); clauses.append([-g, gt[(i+1,j,l)]])
                    clauses.append([-eq[(i+1,j,l)], lt_v]); clauses.append([-lt[(i+1,j,l)], lt_v])
                if j+1 < l:
                    clauses.append([-e, gt[(i,j+1,l)]]); clauses.append([-g, gt[(i,j+1,l)]])
                    clauses.append([-eq[(i,j+1,l)], lt_v]); clauses.append([-lt[(i,j+1,l)], lt_v])
                if i+1 == j and j+1 < l:
                    clauses.append([-e, gt[(i+1,j+1,l)]]); clauses.append([-g, gt[(i+1,j+1,l)]])
                    clauses.append([-eq[(i+1,j+1,l)], lt_v]); clauses.append([-lt[(i+1,j+1,l)], lt_v])
    for l in range(2, m):
        for x in range(l):
            cands = [eq[(min(x,y), max(x,y), l)] for y in range(l) if y != x]
            for p in range(len(cands)):
                for q in range(p+1, len(cands)):
                    clauses.append([-cands[p], -cands[q]])

    if j_elim is None:
        for i in range(m - 2):
            clauses.append([-eq[(i, m-2, m-1)]])
    else:
        clauses.append([eq[(j_elim, m-2, m-1)]])

    if j_elim == m - 3:
        p3 = m - 4
        t_low, t_high = m - 3, m - 2
    else:
        p3 = m - 3
        t_low, t_high = m - 2, m - 1

    avail = [i for i in range(p3) if i != j_elim]
    if u_low is None:
        for i in avail:
            clauses.append([-eq[(i, p3, t_low)]])
    else:
        clauses.append([eq[(u_low, p3, t_low)]])

    rem = [i for i in avail if i != u_low]
    inR = {v: nv() for v in rem}
    edge = {}
    for a_i in range(len(rem)):
        a = rem[a_i]
        for b_i in range(a_i+1, len(rem)):
            b = rem[b_i]
            e = nv()
            edge[(a,b)] = e
            clauses.append([-e] + [eq[(a,b,l)] for l in range(b+1, m)])
    for sub in itertools.combinations(rem, k - 2):
        lits_in = [-inR[x] for x in sub]
        clauses.append(lits_in + [edge[(sub[p], sub[q])] for p in range(k-2) for q in range(p+1, k-2)])

    sel_none = nv()
    for i in avail:
        clauses.append([-sel_none, -eq[(i, p3, t_high)]])

    sat.append_formula(clauses)
    all_eq = list(eq.items())
    sat.set_phases([-v for _, v in all_eq])

    u_highs = [None] + [u for u in rem if u_low is None or u > u_low]
    cores = 0
    for u_high in u_highs:
        if u_high is None:
            assumps = [sel_none] + [inR[v] for v in rem]
        else:
            assumps = [eq[(u_high, p3, t_high)]] + [inR[v] for v in rem if v != u_high]
        while sat.solve(assumptions=assumps):
            model = sat.get_model()
            ae, av = [], []
            for (tup, vid) in all_eq:
                if model[vid - 1] > 0:
                    ae.append(tup)
                    av.append(vid)
            cidx = gordan_core(m, ae)
            if cidx is None:
                import z3
                zs = z3.SolverFor('QF_LRA')
                zx = [z3.Real(f'x_{i}') for i in range(m)]
                zs.add(zx[0] > 0)
                for i in range(m-1): zs.add(zx[i] < zx[i+1])
                for (i,j,l) in ae: zs.add(zx[i] + zx[j] == zx[l])
                if zs.check() == z3.sat:
                    vals = [str(zs.model()[xi]) for xi in zx]
                    sat.delete()
                    return ('SAT', (task_ju, u_high), cores, time.time()-t0, vals)
                else:
                    sat.delete()
                    return ('EDGE', (task_ju, u_high), cores, time.time()-t0, None)
            cores += 1
            sat.add_clause([-av[i] for i in cidx])
    sat.delete()
    return ('UNSAT', task_ju, cores, time.time()-t0, None)

def run_ju_suite(m, k, j_list):
    tasks = []
    for j_elim in j_list:
        p3 = m - 4 if j_elim == m - 3 else m - 3
        avail = [i for i in range(p3) if i != j_elim]
        for u_low in [None] + avail:
            tasks.append((m, k, j_elim, u_low))
    print(f'm={m}, k={k} [JU-SHARED]: Running {len(tasks)} (j,u_low) tasks for j={j_list} across 16 workers...', flush=True)
    t0 = time.time()
    tot_cores = 0
    done = 0
    max_dt = 0.0
    with ProcessPoolExecutor(max_workers=16) as ex:
        futs = [ex.submit(solve_ju_shared, t) for t in tasks]
        for f in as_completed(futs):
            st, task, cores, dt, vals = f.result()
            done += 1
            tot_cores += cores
            if dt > max_dt: max_dt = dt
            if st != 'UNSAT':
                print(f'*** NON-UNSAT RESULT {st} at {task}: {vals}', flush=True)
                return False
            if done % 20 == 0 or done == len(tasks):
                print(f'  progress: {done}/{len(tasks)} UNSAT | tot_cores={tot_cores} | max_dt={max_dt:.2f}s | wall={time.time()-t0:.2f}s', flush=True)
    print(f'ALL {len(tasks)} (j,u_low) TASKS FOR m={m},k={k} PROVEN UNSAT in {time.time()-t0:.2f}s (tot_cores={tot_cores})!', flush=True)
    return True

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'selftest'
    if cmd == 'selftest':
        assert run_suite(11, 4, [None] + list(range(9)), wave_mode=False)
        assert run_suite(16, 5, [None] + list(range(14)), wave_mode=False)
    elif cmd == 'all_waves':
        assert run_suite(22, 6, [None] + list(range(19, -1, -1)), wave_mode=True)
    elif cmd.startswith('waves:'):
        j_list = [None if x == 'None' else int(x) for x in cmd[6:].split(',')]
        assert run_suite(22, 6, j_list, wave_mode=True)
    elif cmd == 'selftest_ju':
        assert run_ju_suite(11, 4, [None] + list(range(9)))
        assert run_ju_suite(16, 5, [None] + list(range(14)))
    elif cmd == 'caseA_ju':
        run_ju_suite(22, 6, [None])
    elif cmd == 'caseB_ju':
        run_ju_suite(22, 6, list(range(20)))
    elif cmd == 'all_ju':
        run_ju_suite(22, 6, [None] + list(range(20)))
    elif cmd == 'selftest_single':
        assert run_suite_single(11, 4, [None] + list(range(9)))
        assert run_suite_single(16, 5, [None] + list(range(14)))
    elif cmd == 'caseA':
        assert run_suite(22, 6, [None], wave_mode=True)
    elif cmd == 'caseB_single':
        run_suite_single(22, 6, list(range(20)))
    elif cmd == 'all':
        assert run_suite(22, 6, [None] + list(range(20)), wave_mode=True)
    elif cmd.startswith('single:'):
        j_list = [None if x == 'None' else int(x) for x in cmd[7:].split(',')]
        run_suite_single(22, 6, j_list)
    else:
        j_list = [None if x == 'None' else int(x) for x in cmd.split(',')]
        assert run_suite(22, 6, j_list, wave_mode=True)
