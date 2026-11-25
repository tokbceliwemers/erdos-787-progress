import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.abspath(__file__))

LEAN_MODULES = [
    "Erdos787Standalone.lean",
    "ThresholdsStandalone.lean",
    "Threshold45Standalone.lean",
    "WitnessesStandalone.lean",
    "NewWitnessesStandalone.lean",
    "InfiniteFamilyStandalone.lean",
    "GeometryAndCarriesStandalone.lean",
    "AsymptoticClosureStandalone.lean",
]

AXIOM_PROBES = [
    "Erdos787AsymptoticClosure.dd_same_coset_drop",
    "Erdos787AsymptoticClosure.ddVecs_sum_avoiding_bound",
    "Erdos787AsymptoticClosure.ddIntSet_props",
    "Erdos787AsymptoticClosure.dd5_count_l37_eq",
    "Erdos787AsymptoticClosure.box8_sum_eq_ddCountAux",
    "Erdos787AsymptoticClosure.ddCountAux_le_ddVecs",
    "Erdos787AsymptoticClosure.dd_beats_quadratic_explicit",
    "Erdos787AsymptoticClosure.ruzsa_beats_quadratic_explicit",
    "Erdos787AsymptoticClosure.ruzsa_quasipolynomial_nat",
]


def run(cmd, cwd=ROOT):
    res = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if res.returncode != 0:
        print(res.stdout)
        print(res.stderr, file=sys.stderr)
        raise RuntimeError(f"Command failed ({res.returncode}): {' '.join(cmd)}")
    return res.stdout.strip()


def check_lean():
    if not shutil.which("lean"):
        raise RuntimeError("`lean` not found in PATH")
    print("[1/4] Compiling all 8 Pure Lean 4 standalone modules and auditing axioms...")
    for mod in LEAN_MODULES:
        p = os.path.join(ROOT, "proofs", mod)
        txt = open(p, "r", encoding="utf-8").read()
        for ln_no, ln in enumerate(txt.splitlines(), 1):
            if re.match(r"^\s*axiom\s+", ln):
                raise RuntimeError(f"Unexpected axiom in {mod}:{ln_no}")
            if re.match(r"^\s*(by\s+)?sorry\b", ln):
                raise RuntimeError(f"Unexpected sorry in {mod}:{ln_no}")
            if "native_decide" in ln and "zero `native_decide`" not in ln:
                raise RuntimeError(f"Unexpected native_decide in {mod}:{ln_no}")
        run(["lean", p])
        print(f"  PASS proofs/{mod}")

    with tempfile.TemporaryDirectory() as tmp:
        src = open(os.path.join(ROOT, "proofs", "AsymptoticClosureStandalone.lean"), "r", encoding="utf-8").read()
        probe = src + "\n" + "\n".join(f"#print axioms {thm}" for thm in AXIOM_PROBES) + "\n"
        probe_path = os.path.join(tmp, "audit_axioms.lean")
        open(probe_path, "w", encoding="utf-8").write(probe)
        out = run(["lean", probe_path])
        for line in out.splitlines():
            if "depends on axioms:" in line and "[propext, Classical.choice, Quot.sound]" not in line:
                raise RuntimeError(f"Non-standard axiom dependency: {line}")
        print("  PASS axiom audit (only [propext, Classical.choice, Quot.sound])")


def check_witnesses():
    if not shutil.which("g++"):
        raise RuntimeError("`g++` not found in PATH")
    print("[2/4] Compiling C++ dual-exact witness verifier and auditing n = 1..143...")
    with tempfile.TemporaryDirectory() as tmp:
        exe = os.path.join(tmp, "verify_witnesses_143.exe" if os.name == "nt" else "verify_witnesses_143")
        src = os.path.join(ROOT, "code", "verify_witnesses_143.cpp")
        run(["g++", "-O3", "-std=c++17", src, "-o", exe])
        print(" ", run([exe, os.path.join(ROOT, "data", "verified_1_100.txt"), "0"]))
        print(" ", run([exe, os.path.join(ROOT, "data", "verified_100_143.txt"), "1"]))


def check_lattices():
    if not shutil.which("g++"):
        raise RuntimeError("`g++` not found in PATH")
    print("[3/4] Compiling and running C++ lattice & finite template executables...")
    cpp_tests = [
        ("ruzsa_lattice_test.cpp", False),
        ("ruzsa_variants_test.cpp", False),
        ("test_templates_and_e7.cpp", False),
        ("test_zero_centered_dd.cpp", False),
        ("attack_k7_and_lattices.cpp", True),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        for fname, use_omp in cpp_tests:
            exe = os.path.join(tmp, fname.replace(".cpp", ".exe" if os.name == "nt" else ""))
            cmd = ["g++", "-O3", "-std=c++17"]
            if use_omp:
                cmd.append("-fopenmp")
            cmd.extend([os.path.join(ROOT, "code", fname), "-o", exe])
            run(cmd)
            run([exe])
            print(f"  PASS code/{fname}")


def check_algebra():
    print("[4/4] Verifying infinite doubling sequence and closed-form identities...")
    F = [
        -42, -26, -24, -22, -20, -18, -16, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0,
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 20, 22, 24, 26, 42,
    ]
    for d in range(6):
        k = d + 6
        assert len(F) == len(set(F)) == k * k + 3 * k - 11
        if k >= 7:
            assert len(F) > k * k + k + 1
        odds = [-(2 * j + 1) for j in range(k + 2)] + [2 * j + 1 for j in range(k + 2)]
        F = odds + [2 * x for x in F]
    for k in range(1, 7):
        n_jump = k * k + k + 2
        assert 4 * n_jump - 7 == (2 * k + 1) ** 2
    print("  PASS algebraic jump identities and F_0..F_5 doubling sizes")


if __name__ == "__main__":
    check_lean()
    check_witnesses()
    check_lattices()
    check_algebra()
    print("ALL PUBLISH PACKAGE VERIFICATIONS PASSED (EXIT 0).")
