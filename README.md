# Erdős Problem #787: Formalization, Finite Thresholds, & Asymptotic Progress

Self-contained verification and publication archive for partial results on **Erdős Problem #787** (maximum guaranteed size $g(n)$ of a sum-avoiding subset inside any $n$-element set of integers/reals).

## Summary of Established Results

1. **Exact Finite Thresholds ($k \le 6$):**
   - $n_{\max}(1) = 3$, $n_{\max}(2) = 7$, $n_{\max}(3) = 13$, $n_{\max}(4) = 21$: machine-checked in Pure Lean 4 (`Init`-only, zero `sorry`) in [ThresholdsStandalone.lean](proofs/ThresholdsStandalone.lean) and [Threshold45Standalone.lean](proofs/Threshold45Standalone.lean).
   - $n_{\max}(5) = 31$ ($m_+ = 16$ UNSAT) and $n_{\max}(6) = 43$ ($m_+ = 22$ UNSAT across all `21` branches with `__int128`-verified IIS Farkas cores): settled over $\mathbb{R}$ via [solve_k6_pos.py](code/solve_k6_pos.py) + [gordan_dll.cpp](code/gordan_dll.cpp).
2. **Breakdown of $k^2 + k + 1$ at $k = 7$ & Exact $g(n)$ on $[1, 59]$:**
   - Inductive doubling from $A_{43}$ ([InfiniteFamilyStandalone.lean](proofs/InfiniteFamilyStandalone.lean): `infinite_family_n_max_ge`) proves $n_{\max}(k) \ge k^2 + 3k - 11$ for all $k \ge 6$, refuting $k^2 + k + 1$ for every $k \ge 7$ (beginning at $n_{\max}(7) \ge 59 > 57$, `k7_beats_projective_bound`).
   - Exact $g(n)$ is settled for all $n \in [1, 59]$, including $g(n) = 7$ on $[44, 59]$.
   - Witnesses `A3..A100` are machine-checked in [WitnessesStandalone.lean](proofs/WitnessesStandalone.lean) and [NewWitnessesStandalone.lean](proofs/NewWitnessesStandalone.lean), and dual-exact witnesses are extended in C++ to $n \in [100, 143]$ ([verified_100_143.txt](data/verified_100_143.txt): $\alpha \le 10$ on $[98, 119]$, $\alpha \le 11$ on $[120, 143]$).
3. **Asymptotic Progress & Pure Lean 4 Multi-Scale Lattice / Checkerboard $D_d$ Formalization:**
   - **Lower Bound (`1/68 -> 1/44`):** Asymmetric inductive peeling (`Subcase B`: $\mu_{B^{(j)}}(T) \ge (\alpha/2)^3$) paired with two-bucket step counting (`[FHHK Lem 3.4]` steps add $\Delta_r = \emptyset$; harmonic branches add $\Delta_r$ at most $k^4\mathcal{L}(\alpha)$ times) tightens Beker (2025) from $1/68$ to $g(n) \ge (\log n)^{1 + 1/44 - o(1)}$ ([asymptotic_closure_synthesis.md](paper/asymptotic_closure_synthesis.md)).
   - **Upper Bound (`D_d` & Sharp Constant):** [AsymptoticClosureStandalone.lean](proofs/AsymptoticClosureStandalone.lean) proves the single-sphere orthant lower bound $\alpha(G_S) \ge |S|/2^d$ (`single_sphere_orthant_lower_bound`), full checkerboard $D_d$ multi-scale 2-adic construction & carry-free radix map (`dd_same_coset_drop`, `ddVecs_sum_avoiding_bound`, `ddIntSet_props`), explicit super-quadratic crossover at $D_5, L = 37$ (`dd_beats_quadratic_explicit`: $k = 1185, |A| \ge 1{,}438{,}294 > 1{,}407{,}769$), and quasipolynomial scaling (`ruzsa_quasipolynomial_nat`) attaining the asymptotic constant $C = \sqrt{8 \log 2}$.

**Open Status:** Both the asymptotic dichotomy between $(\log n)^{1 + 1/44 - o(1)}$ and $\exp((\sqrt{8\log 2} + o(1))\sqrt{\log n})$ and exact upper bounds for $n_{\max}(k)$ at $k \ge 7$ remain open.

---

## Reproducible Verification

Run the entire Lean 4 + C++ + Python verification suite from inside `publish/`:

```bash
python verify_all.py
```

This compiles all 8 standalone Lean 4 modules (`Init`-only, standard axioms `[propext, Classical.choice, Quot.sound]`), compiles and runs `verify_witnesses_143.cpp` across all `n = 1..143` witnesses, runs the lattice and finite C++ executables, and checks algebraic identities.

## Directory Layout

- [paper/erdos_787_monograph.md](paper/erdos_787_monograph.md): Main post-audit technical monograph.
- [paper/asymptotic_closure_synthesis.md](paper/asymptotic_closure_synthesis.md): Detailed `1/68 -> 1/44` lower-bound derivation, $D_d$/$E_8$/$\Lambda_{24}$ lattice results, and barrier analysis.
- [proofs/](proofs/): 8 zero-`sorry` Pure Lean 4 standalone verification modules.
- [data/](data/): Dual-verified exact witnesses for $n = 1..143$ and [n100_bound_table.md](data/n100_bound_table.md).
- [code/](code/): C++ solvers, LP/Farkas IIS core certifiers, and lattice executables.
- [figures/](figures/): 9 updated publication figures plus the unified 3x3 visual atlas [figures/erdos_787_all_figures.png](figures/erdos_787_all_figures.png).
