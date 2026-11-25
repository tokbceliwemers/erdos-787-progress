# Exact Values, Witness Certificates, and Bounded Corridor for g(n) up to n = 100

## 1. Mathematical Classification and Delineation Principles

In evaluating $g(n) = \min_{|A|=n, A \subset \mathbb{R}} M(A) = \min_{|A|=n, A \subset \mathbb{Z}} \alpha(G_A)$, all finite intervals up to $n = 100$ are classified into two rigorous tiers:

1. **Unconditionally Proven Exact Values ($n \in [1, 59]$):**
   - $n_{\max}(1) = 3$, $n_{\max}(2) = 7$, $n_{\max}(3) = 13$ (`proofs/ThresholdsStandalone.lean`), and $n_{\max}(4) = 21$ (`proofs/Threshold45Standalone.lean`) are unconditionally proven over sorted lists / $\mathbb{R}$ in **Pure Lean 4** (zero `sorry`, zero external axioms).
   - $n_{\max}(5) = 31$ (`m = 16` UNSAT over $\mathbb{R}$, paired with Pure Lean 4 `A31`) and $n_{\max}(6) = 43$ (`m = 22` UNSAT across all 21 subcases `Case A` and `Case B, j=0..19` via strict-exact `__int128` Farkas + SAT in `../code/solve_k6_pos.py`, `../code/gordan_dll.cpp`, and `../code/k6_pos_solver.cpp`, paired with Pure Lean 4 `A43`) settle $k = 5, 6$ over $\mathbb{R}$.
   - Therefore, $g(44) \ge 7$ holds unconditionally; combined with explicit Pure Lean 4 witnesses `A52..A59` (`proofs/NewWitnessesStandalone.lean`, including `A59` from `InfiniteFamilyStandalone.lean`) showing $M(A_{59}) = 7$, monotonicity proves **$g(n) = 7$ exact for every $n \in [44, 59]$**. In particular, at $n = 58$ and $n = 59$, $g(n) = 7$ refutes the projective closed-form jump to $8$.

2. **Lean-Certified Bounded Corridor ($n \in [60, 100]$):**
   - Because $n_{\max}(6) = 43$, monotonicity guarantees $g(n) \ge 7$ unconditionally for all $n \ge 44$.
   - Explicit witnesses for **every single $n \in [52, 100]$** are dual-exact verified in C++ (`./verified_1_100.txt`) and formally machine-checked in Pure Lean 4 (`proofs/NewWitnessesStandalone.lean`):
     - $n \in [60, 77] \implies 7 \le g(n) \le 8$ (witness `A77`, $M(A_{77}) = 8$)
     - $n \in [78, 97] \implies 7 \le g(n) \le 9$ (witness `A97`, $M(A_{97}) = 9$)
     - $n \in [98, 100] \implies 7 \le g(n) \le 10$ (witness `A100`, $M(A_{100}) = 10$)

---

## 2. Milestone Summary Table for Key Sizes up to n = 100

| $n$ Range | Proven Lower Bound | Certified Upper Bound | Exact / Corridor Status | Primary Basis |
| :---: | :---: | :---: | :---: | :--- |
| **$1 \dots 3$** | $1$ | $1$ | **1 (Proven Exact)** | Pure Lean 4 `A3` & `n_max_1_exact` ($n_{\max}(1)=3$) |
| **$4 \dots 7$** | $2$ | $2$ | **2 (Proven Exact)** | Pure Lean 4 `A7` & `n_max_2_exact` ($n_{\max}(2)=7$) |
| **$8 \dots 13$** | $3$ | $3$ | **3 (Proven Exact)** | Pure Lean 4 `A13*` & `n_max_3_exact` ($n_{\max}(3)=13$) |
| **$14 \dots 21$** | $4$ | $4$ | **4 (Proven Exact)** | Pure Lean 4 `A21` & `Threshold45Standalone` ($n_{\max}(4)=21$) |
| **$22 \dots 31$** | $5$ | $5$ | **5 (Proven Exact)** | Pure Lean 4 `A31` & $m=16$ Gordan/Farkas+SAT ($n_{\max}(5)=31$) |
| **$32 \dots 43$** | $6$ | $6$ | **6 (Proven Exact)** | Pure Lean 4 `A43` & $m=22$ Gordan/Farkas+SAT ($n_{\max}(6)=43$) |
| **$44 \dots 59$** | $7$ | $7$ | **7 (Proven Exact)** | $n_{\max}(6)=43$ ($g(44)\ge 7$) & Pure Lean 4 `A59` ($M(A_{59})=7$) |
| **$60 \dots 77$** | $7$ | $8$ | **Corridor $[7, 8]$** | $g(44)\ge 7$ & Pure Lean 4 `A60..A77` |
| **$78 \dots 97$** | $7$ | $9$ | **Corridor $[7, 9]$** | $g(44)\ge 7$ & Pure Lean 4 `A78..A97` |
| **$98 \dots 100$** | $7$ | $10$ | **Corridor $[7, 10]$** | $g(44)\ge 7$ & Pure Lean 4 `A98..A100` |

---

## 3. Complete Dual-Exact Verified Value Table for all n = 1 to 100

| $n$ | Proven Lower | Certified Upper | $|E(G_{A_n})|$ | Method | Strict Status |
| :---: | :---: | :---: | :---: | :---: | :--- |
| 1 | 1 | 1 | 0 | `del_from_2` | **1 (Proven Exact)** |
| 2 | 1 | 1 | 1 | `del_from_3` | **1 (Proven Exact)** |
| 3 | 1 | 1 | 3 | `glued_3+3_M1` | **1 (Proven Exact)** |
| 4 | 2 | 2 | 5 | `glued_sh_3+3_M1` | **2 (Proven Exact)** |
| 5 | 2 | 2 | 8 | `glued_3+3_M2` | **2 (Proven Exact)** |
| 6 | 2 | 2 | 12 | `del_from_7` | **2 (Proven Exact)** |
| 7 | 2 | 2 | 17 | `glued_3+7_M1` | **2 (Proven Exact)** |
| 8 | 3 | 3 | 22 | `glued_sh_7+7_M1` | **3 (Proven Exact)** |
| 9 | 3 | 3 | 22 | `glued_3+7_M2` | **3 (Proven Exact)** |
| 10 | 3 | 3 | 33 | `del_from_11` | **3 (Proven Exact)** |
| 11 | 3 | 3 | 39 | `glued_7+7_M2` | **3 (Proven Exact)** |
| 12 | 3 | 3 | 38 | `del_from_13` | **3 (Proven Exact)** |
| 13 | 3 | 3 | 48 | `glued_3+13_M1` | **3 (Proven Exact)** |
| 14 | 4 | 4 | 61 | `glued_7+13_M1` | **4 (Proven Exact)** |
| 15 | 4 | 4 | 53 | `glued_3+13_M2` | **4 (Proven Exact)** |
| 16 | 4 | 4 | 78 | `sphere_linproj_d4` | **4 (Proven Exact)** |
| 17 | 4 | 4 | 62 | `glued_7+13_M3` | **4 (Proven Exact)** |
| 18 | 4 | 4 | 90 | `del_from_19` | **4 (Proven Exact)** |
| 19 | 4 | 4 | 105 | `del_from_20` | **4 (Proven Exact)** |
| 20 | 4 | 4 | 123 | `del_from_21` | **4 (Proven Exact)** |
| 21 | 4 | 4 | 146 | `glued_3+21_M1` | **4 (Proven Exact)** |
| 22 | 5 | 5 | 162 | `glued_sh_13+21_M1` | **5 (Proven Exact)** |
| 23 | 5 | 5 | 151 | `glued_3+21_M2` | **5 (Proven Exact)** |
| 24 | 5 | 5 | 185 | `glued_sh_21+7_M5` | **5 (Proven Exact)** |
| 25 | 5 | 5 | 168 | `glued_7+21_M2` | **5 (Proven Exact)** |
| 26 | 5 | 5 | 175 | `del_from_27` | **5 (Proven Exact)** |
| 27 | 5 | 5 | 197 | `del_from_28` | **5 (Proven Exact)** |
| 28 | 5 | 5 | 216 | `del_from_29` | **5 (Proven Exact)** |
| 29 | 5 | 5 | 238 | `glued_13+21_M2` | **5 (Proven Exact)** |
| 30 | 5 | 5 | 263 | `del_from_31` | **5 (Proven Exact)** |
| 31 | 5 | 5 | 291 | `glued_3+31_M1` | **5 (Proven Exact)** |
| 32 | 6 | 6 | 319 | `glued_sh_31+7_M5` | **6 (Proven Exact)** |
| 33 | 6 | 6 | 296 | `glued_3+31_M2` | **6 (Proven Exact)** |
| 34 | 6 | 6 | 285 | `del_from_35` | **6 (Proven Exact)** |
| 35 | 6 | 6 | 313 | `glued_7+31_M2` | **6 (Proven Exact)** |
| 36 | 6 | 6 | 373 | `del_from_37` | **6 (Proven Exact)** |
| 37 | 6 | 6 | 394 | `sym_core1_C10` | **6 (Proven Exact)** |
| 38 | 6 | 6 | 355 | `del_from_39` | **6 (Proven Exact)** |
| 39 | 6 | 6 | 383 | `glued_13+31_M2` | **6 (Proven Exact)** |
| 40 | 6 | 6 | 464 | `del_from_41` | **6 (Proven Exact)** |
| 41 | 6 | 6 | 498 | `sym_core2_C12` | **6 (Proven Exact)** |
| 42 | 6 | 6 | 535 | `del_from_43` | **6 (Proven Exact)** |
| 43 | 6 | 6 | 575 | `glued_3+43_M1` | **6 (Proven Exact)** |
| 44 | 7 | 7 | 615 | `glued_sh_43+7_M7` | **7 (Proven Exact)** |
| 45 | 7 | 7 | 580 | `glued_3+43_M2` | **7 (Proven Exact)** |
| 46 | 7 | 7 | 557 | `del_from_47` | **7 (Proven Exact)** |
| 47 | 7 | 7 | 597 | `glued_7+43_M2` | **7 (Proven Exact)** |
| 48 | 7 | 7 | 687 | `del_from_49` | **7 (Proven Exact)** |
| 49 | 7 | 7 | 714 | `sym_core1_C14` | **7 (Proven Exact)** |
| 50 | 7 | 7 | 739 | `del_from_51` | **7 (Proven Exact)** |
| 51 | 7 | 7 | 747 | `glued_3+51_M1` | **7 (Proven Exact)** |
| 52 | 7 | 7 | 672 | `k7_mode=2_U=120` | **7 (Proven Exact)** |
| 53 | 7 | 7 | 854 | `sym_core2_C16` | **7 (Proven Exact)** |
| 54 | 7 | 7 | 749 | `k7_mode=2_U=120` | **7 (Proven Exact)** |
| 55 | 7 | 7 | 783 | `glued_21+43_M2` | **7 (Proven Exact)** |
| 56 | 7 | 7 | 820 | `a55_add_neg17` | **7 (Proven Exact)** |
| 57 | 7 | 7 | 858 | `k7_mode=1_U=120` | **7 (Proven Exact)** |
| 58 | 7 | 7 | 903 | `a57_add_13` | **7 (Proven Exact)** |
| 59 | 7 | 7 | 949 | `rec_A59` | **7 (Proven Exact)** |
| 60 | 7 | 8 | 884 | `del_from_61` | Corridor [7, 8] |
| 61 | 7 | 8 | 892 | `glued_31+51_M2` | Corridor [7, 8] |
| 62 | 7 | 8 | 949 | `del_from_63` | Corridor [7, 8] |
| 63 | 7 | 8 | 957 | `glued_21+51_M2` | Corridor [7, 8] |
| 64 | 7 | 8 | 888 | `del_from_65` | Corridor [7, 8] |
| 65 | 7 | 8 | 928 | `glued_31+43_M4` | Corridor [7, 8] |
| 66 | 7 | 8 | 956 | `del_from_67` | Corridor [7, 8] |
| 67 | 7 | 8 | 997 | `del_from_68` | Corridor [7, 8] |
| 68 | 7 | 8 | 1036 | `del_from_69` | Corridor [7, 8] |
| 69 | 7 | 8 | 1079 | `del_from_70` | Corridor [7, 8] |
| 70 | 7 | 8 | 1113 | `del_from_71` | Corridor [7, 8] |
| 71 | 7 | 8 | 1159 | `rec_A71` | Corridor [7, 8] |
| 72 | 7 | 8 | 1196 | `del_from_73` | Corridor [7, 8] |
| 73 | 7 | 8 | 1236 | `rec_A73` | Corridor [7, 8] |
| 74 | 7 | 8 | 1279 | `del_from_75` | Corridor [7, 8] |
| 75 | 7 | 8 | 1325 | `rec_A75` | Corridor [7, 8] |
| 76 | 7 | 8 | 1372 | `del_from_77` | Corridor [7, 8] |
| 77 | 7 | 8 | 1424 | `rec_A77` | Corridor [7, 8] |
| 78 | 7 | 9 | 1927 | `del_from_79` | Corridor [7, 9] |
| 79 | 7 | 9 | 2003 | `sym_core2_C26` | Corridor [7, 9] |
| 80 | 7 | 9 | 1306 | `del_from_81` | Corridor [7, 9] |
| 81 | 7 | 9 | 1349 | `del_from_82` | Corridor [7, 9] |
| 82 | 7 | 9 | 1393 | `del_from_83` | Corridor [7, 9] |
| 83 | 7 | 9 | 1415 | `del_from_84` | Corridor [7, 9] |
| 84 | 7 | 9 | 1440 | `del_from_85` | Corridor [7, 9] |
| 85 | 7 | 9 | 1468 | `del_from_86` | Corridor [7, 9] |
| 86 | 7 | 9 | 1517 | `del_from_87` | Corridor [7, 9] |
| 87 | 7 | 9 | 1548 | `del_from_88` | Corridor [7, 9] |
| 88 | 7 | 9 | 1582 | `del_from_89` | Corridor [7, 9] |
| 89 | 7 | 9 | 1634 | `rec_A89` | Corridor [7, 9] |
| 90 | 7 | 9 | 1671 | `del_from_91` | Corridor [7, 9] |
| 91 | 7 | 9 | 1711 | `rec_A91` | Corridor [7, 9] |
| 92 | 7 | 9 | 1754 | `del_from_93` | Corridor [7, 9] |
| 93 | 7 | 9 | 1800 | `rec_A93` | Corridor [7, 9] |
| 94 | 7 | 9 | 1849 | `del_from_95` | Corridor [7, 9] |
| 95 | 7 | 9 | 1901 | `rec_A95` | Corridor [7, 9] |
| 96 | 7 | 9 | 1954 | `del_from_97` | Corridor [7, 9] |
| 97 | 7 | 9 | 2012 | `rec_A97` | Corridor [7, 9] |
| 98 | 7 | 10 | 2065 | `del_from_99` | Corridor [7, 10] |
| 99 | 7 | 10 | 2129 | `rec_A99` | Corridor [7, 10] |
| 100 | 7 | 10 | 2190 | `rec_A100` | Corridor [7, 10] |

---

## 4. Visualizations and Scripts

- Complete bound table plotted up to $n = 100$ in [g_n_to_100.png](../figures/g_n_to_100.png) via (generated from bound data).
- Transition thresholds and breakdown at $k = 7$ plotted in [threshold_hierarchy_step_function.png](../figures/threshold_hierarchy_step_function.png) via (generated from bound data).
- Broad envelopes plotted in [g_n_plot.png](../figures/g_n_plot.png) via (generated from bound data).
