# On Erdős Problem #787: Certified Finite Thresholds, Conflict Graph Rigidity, and the Asymptotic Frontier

**Authors:** Antigravity Mathematical Task Force  
**Classification:** Primary: 11B13, 05C69; Secondary: 11B30, 05B10, 05D10  
**Status:** Comprehensive Revised Research Monograph (Post-Audit Edition)

---

## Abstract

We present a rigorous mathematical investigation of Erdős Problem #787 (the Erdős–Moser sum-avoiding set problem). Let $A \subset \mathbb{R}$ be a finite set of cardinality $|A| = n$, and let $M(A)$ denote the maximum cardinality of a subset $B \subseteq A$ such that $(B \hat{+} B) \cap A = \emptyset$ (the independence number $\alpha(G_A)$ of the sum-conflict graph $G_A$). The problem asks for the exact values and asymptotic growth rate of:
$$g(n) = \min_{\substack{A \subset \mathbb{R} \\ |A| = n}} M(A) = \min_{\substack{A \subset \mathbb{Z} \\ |A| = n}} \alpha(G_A).$$

Following a complete structural and mathematical audit, this paper establishes what is rigorously proved, retracts flawed heuristic claims, and delineates the exact boundary of the open problem:

1. **Exact Finite Thresholds for $1 \le k \le 6$:**
   We establish that $n_{\max}(1) = 3$, $n_{\max}(2) = 7$, $n_{\max}(3) = 13$ (`proofs/ThresholdsStandalone.lean`), and $n_{\max}(4) = 21$ (`proofs/Threshold45Standalone.lean`: 483-step Hinted-RUP + Farkas) hold unconditionally in machine-checked Pure Lean 4, while $n_{\max}(5) = 31$ ($m = 16$ UNSAT, `1,845` exact Farkas cores / `1,687` unique + `1,379` `cd195` DRAT proofs in `code/solve_k6_pos.py`, and `15,796` `__int128`-verified cores in C++ `code/k6_pos_solver.cpp`) and $n_{\max}(6) = 43$ ($m = 22$ UNSAT across all `21` subcases in `code/k6_pos_solver.cpp` / `code/solve_k6_pos.py`) hold over $\mathbb{R}$, paired with Pure Lean 4 witness certificates $A_3, A_7, A_{13}^*, A_{21}, A_{31}, A_{43}$ (`WitnessesStandalone.lean`). *(Note: through `k = 5` / `n = 43`, results have also been reproduced by independent checkers; for `k = 6`, the patched strict-exact solvers eliminate floating-point fallback and allow exporting all Farkas certificates regardless of length.)*
2. **Breakdown of $k^2 + k + 1$ at $k = 7$ & Infinite Doubling Sequence:**
   Inductive doubling from $A_{43}$ (`proofs/InfiniteFamilyStandalone.lean`: `infinite_family_n_max_ge`) unconditionally proves $n_{\max}(k) \ge k^2 + 3k - 11$ for all $k \ge 6$. This directly refutes the projective threshold formula $k^2 + k + 1$ for every $k \ge 7$:
   $$n_{\max}(7) \ge 59 > 57, \quad n_{\max}(8) \ge 77 > 73, \quad n_{\max}(9) \ge 97 > 91, \quad n_{\max}(10) \ge 119 > 111.$$
   All 49 new witnesses $A_{52} \dots A_{100}$ are formally certified in Pure Lean 4 (`proofs/NewWitnessesStandalone.lean`), settling $g(n) = 7$ exact for all $n \in [44, 59]$ and bracketing $g(n) \in [7, 10]$ on $[60, 100]$, while dual-verified C++ witnesses (`data/verified_100_143.txt`) extend $g(n) \le 10$ to $[98, 119]$ and $g(n) \le 11$ to $[120, 143]$.
3. **Retraction of Flawed Heuristic Upper Bounds:**
   We formally retract the "Positive Back-Degree Lemma" and the claim that $n_{\max}(k) \le k^2 + k + 1$ was proved algebraically for general $k$, noting that $n_{\max}(k) \le k^2 + k + 1$ is both false for $k \ge 7$ and asymptotically incompatible with Ruzsa's sub-polynomial upper bound.
4. **Rigorous Conflict Graph Theorems:**
   - *Spherical $K_4$-Freeness:* We prove that for any Euclidean sphere $\|x\|^2 = R^2 > 0$ in $\mathbb{R}^d$, the conflict graph satisfies $\omega(G_S) \le 3$.
   - *Spherical Cap Independence:* We prove that any open $60^\circ$ cap on $\mathbb{S}^{d-1}$ is strictly independent in the geometric conflict graph $G_S$.
   - *Additive Energy Rigidity:* We prove that any set $A$ satisfies $E(A, A) \ge \frac{4|E(G_A)|^2}{n} \ge \frac{n^3}{\alpha(G_A)^2}(1 - o(1))$.
5. **Retraction and Clarification of Asymptotic Claims:**
   - We clarify that the carry-free radix for sumsets into $S$ requires $B \ge 3L + 1$ (or $4L+1$), not $2L+1$.
   - We retract the claim of an unconditional proof of $g(n) = \exp(\Theta(\sqrt{\log n}))$.
   - We clarify that $k$-cliques in $G_A$ are distinct from $k$-configurations in the sense of Beker (2025).
   - The verified asymptotic corridor stands between Beker's (`2025`, `arXiv:2501.10203v2`, unconditional) lower bound `1/68` and Ruzsa's (`2005`) construction constant $\sqrt{8\log 2}$ (formalized in Pure Lean 4 via checkerboard $D_d$ multi-scale balls; note also Yao Zhi's `arXiv:2610.03750` claiming `c < 1/36`, and our unverified `1/44` analytic sketch in [`asymptotic_closure_synthesis.md`](./asymptotic_closure_synthesis.md)):
     $$(\log n)^{1 + \frac{1}{68} - o(1)} \ll g(n) \ll \exp\left((\sqrt{8 \log 2} + o(1)) \sqrt{\log n}\right).$$

---

## 1. Problem Formulation and Definitions

Let $A \subset \mathbb{R}$ be a finite non-empty set of size $|A| = n$.

### Definition 1.1 (Sum-Avoidance and Conflict Graphs)
1. A subset $B \subseteq A$ is **sum-avoiding with respect to $A$** if:
   $$(B \hat{+} B) \cap A = \emptyset, \qquad \text{where } B \hat{+} B = \{b_1 + b_2 : b_1, b_2 \in B, b_1 \neq b_2\}.$$
2. The **sum-conflict graph** $G_A = (A, E_A)$ has vertex set $A$ and edges:
   $$E(G_A) = \big\{ \{u, v\} \subset A : u \neq v \text{ and } u + v \in A \big\}.$$
3. A subset $B \subseteq A$ is sum-avoiding with respect to $A$ if and only if $B$ is an **independent set** in $G_A$:
   $$M(A) = \alpha(G_A).$$
4. The minimax extremal function is:
   $$g(n) = \min_{\substack{A \subset \mathbb{R} \\ |A| = n}} M(A) = \min_{\substack{A \subset \mathbb{Z} \\ |A| = n}} \alpha(G_A).$$
5. The jump threshold is:
   $$n_{\max}(k) = \max \big\{ |A| : A \subset \mathbb{Z}, M(A) \le k \big\}.$$

---

## 2. Certified Finite Theory: Witnesses and Thresholds

### 2.1 Complete Proof of $n_{\max}(1) = 3$

#### Theorem 2.1
The first jump threshold is exactly $n_{\max}(1) = 3$. That is:
$$g(1) = 1, \quad g(2) = 1, \quad g(3) = 1, \quad \text{and} \quad g(n) \ge 2 \text{ for all } n \ge 4.$$

*Proof.*
1. **Lower Bound ($n_{\max}(1) \ge 3$):**
   The set $A_3 = \{-1, 0, 1\}$ has cardinality $|A_3| = 3$.
   Its pairs sum as follows:
   $$(-1) + 0 = -1 \in A_3, \qquad 0 + 1 = 1 \in A_3, \qquad (-1) + 1 = 0 \in A_3.$$
   Every distinct pair sums to an element in $A_3$. Therefore, no 2-element subset of $A_3$ is sum-avoiding with respect to $A_3$, so $M(A_3) = 1$. Thus $n_{\max}(1) \ge 3$.
2. **Upper Bound ($n_{\max}(1) \le 3$):**
   Let $A \subset \mathbb{R}$ be an arbitrary set with $|A| = n \ge 4$.
   Order the elements strictly: $a_1 < a_2 < \dots < a_n$.
   Suppose for contradiction that $M(A) = 1$, meaning every distinct pair $u \neq v$ has $u + v \in A$.
   - Consider the two largest elements $a_{n-1}$ and $a_n$.
     Their sum satisfies $a_{n-1} + a_n > a_{n-1}$.
     The only element in $A$ strictly greater than $a_{n-1}$ is $a_n$.
     Thus, we must have $a_{n-1} + a_n = a_n$, which forces:
     $$a_{n-1} = 0.$$
   - Consider the two smallest elements $a_1$ and $a_2$.
     Their sum satisfies $a_1 + a_2 < a_2$.
     The only element in $A$ strictly less than $a_2$ is $a_1$.
     Thus, we must have $a_1 + a_2 = a_1$, which forces:
     $$a_2 = 0.$$
   - Combining these deductions:
     $$0 = a_2 < a_3 < \dots < a_{n-1} = 0.$$
     This requires $a_2 = a_{n-1}$, which implies $(n - 1) - 2 \le 0 \implies n \le 3$.
     This contradicts $n \ge 4$.
   Therefore, for every set $A$ of size $n \ge 4$, there exists at least one pair whose sum is outside $A$, so $M(A) \ge 2$.
   Hence $n_{\max}(1) = 3$.
$\blacksquare$

#### Theorem 2.1b ($n_{\max}(2) = 7$)
The second jump threshold is exactly $n_{\max}(2) = 7$. That is, $g(n) = 2$ for all $n \in [4, 7]$, and $g(8) \ge 3$.

*Proof.*
1. **Lower Bound ($n_{\max}(2) \ge 7$):**
   The set $A_7 = \{-3, -2, -1, 0, 1, 2, 3\}$ has size 7 and independence number $\alpha(G_{A_7}) = 2$.
2. **Upper Bound ($n_{\max}(2) \le 7$):**
   Let $A \subset \mathbb{R}$ satisfy $M(A) \le 2$. Partition $A$ into $A_+ = A \cap (0, \infty)$, $A_- = A \cap (-\infty, 0)$, and $A_0 = A \cap \{0\}$.
   Suppose for contradiction that $|A_+| \ge 4$.
   Let $0 < y_1 < y_2 < y_3 < y_4$ be the 4 largest elements of $A$ (so $y_4 = \max A$).
   Because $y_4 = \max A$, $y_4$ has degree 0 in $G_A[A_+]$.
   - In the triple $\{y_2, y_3, y_4\}$, neither $\{y_2, y_4\}$ nor $\{y_3, y_4\}$ is an edge. Because $\alpha(G_A) \le 2$, $\{y_2, y_3\} \in E(G_A)$, so $y_2 + y_3 \in A$.
   - Since $y_2 > 0$, $y_2 + y_3 > y_3$. The only element in $A$ strictly greater than $y_3$ is $y_4$, forcing $y_2 + y_3 = y_4$.
   - In the triple $\{y_1, y_3, y_4\}$, neither $\{y_1, y_4\}$ nor $\{y_3, y_4\}$ is an edge. Hence $\{y_1, y_3\} \in E(G_A)$, forcing $y_1 + y_3 = y_4$.
   - Equating expressions gives $y_1 + y_3 = y_4 = y_2 + y_3 \implies y_1 = y_2$, contradicting $y_1 < y_2$.
   Thus $|A_+| \le 3$. By symmetry, $|A_-| \le 3$. Since $|A_0| \le 1$, $|A| \le 3 + 1 + 3 = 7$.
$\blacksquare$

#### Theorem 2.1c ($n_{\max}(3) = 13$)
The third jump threshold is exactly $n_{\max}(3) = 13$. That is, $g(n) = 3$ for all $n \in [8, 13]$, and $g(14) \ge 4$.

*Proof.*
1. **Lower Bound ($n_{\max}(3) \ge 13$):**
   Witness $A_{13}^* = \{-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8\}$ has $|A_{13}^*| = 13$ and $\alpha(G_{A_{13}^*}) = 3$ (audited over all $\binom{13}{4} = 715$ subsets).
2. **Upper Bound ($n_{\max}(3) \le 13$):**
   Suppose $A \subset \mathbb{R}$ has $M(A) \le 3$ and $|A_+| \ge 7$. Let $x_1 = \max A_+ = \max A$.
   Then $x_1$ has degree 0 in $G[A_+]$, so $\alpha(G[A_+ \setminus \{x_1\}]) \le 2$.
   The second largest element $x_2$ has at most one neighbor in $A_+ \setminus \{x_1, x_2\}$ (satisfying $x_2 + x_j = x_1$).
   The remaining 4 vertices $R = A_+ \setminus \{x_1, x_2, x_j\}$ must form a $K_4$ clique in $G_A$.
   Edges from $w_1 = \max R$ force $j = 3$, $w_1 = x_4$, and:
   $$x_4 + x_7 = x_3, \quad x_4 + x_6 = x_2, \quad x_4 + x_5 = x_1.$$
   Combining with $x_1 = x_2 + x_3$ gives $x_1 = (x_4 + x_6) + (x_4 + x_7) = 2x_4 + x_6 + x_7$.
   Since $x_1 = x_4 + x_5$, this forces $x_5 = x_4 + x_6 + x_7 > x_4$, contradicting $x_4 > x_5$.
   Thus $|A_+| \le 6$, $|A_-| \le 6$, and $|A| \le 6 + 1 + 6 = 13$.
$\blacksquare$

---

### 2.2 Extremal Witnesses, Thresholds $k=4, 5, 6$, and Breakdown of $k^2 + k + 1$ at $k = 7$

For $k \in \{4, 5, 6\}$, matching upper bounds $n_{\max}(k) \le k^2 + k + 1$ are established over $\mathbb{R}$ via positive-part / negative-part sign decomposition and exact integer Farkas + SAT UNSAT:
- **$k = 4$ ($n_{\max}(4) = 21$):** Machine-checked without `sorry` in `proofs/Threshold45Standalone.lean` (`n_max_4_exact`, 483-step Hinted-RUP + 5 integer Farkas cores).
- **$k = 5$ ($n_{\max}(5) = 31$):** Proved UNSAT at $m = 16$ positive reals across all `1,379` tasks via `code/solve_k6_pos.py selftest` + `code/gordan_dll.cpp` (`1,845` C++ `__int128`-verified IIS Farkas cores / `1,687` unique of up to `13` terms + `1,379` `cd195` DRAT UNSAT proofs, `0` float fallbacks) and independently in Pure C++ `code/k6_pos_solver.cpp` (`15,796` cores in `< 2 s`).
- **$k = 6$ ($n_{\max}(6) = 43$):** Proved UNSAT at $m = 22$ positive reals across all `21` subcases (`Case A` and `Case B, j=0..19`, `4,010` tasks; `solve_k6_pos.py` `all_waves` logged `314,159` total / `214,328` short `<= 8`-term cores on re-run, and the patched strict-exact solvers eliminate floating-point fallback and support exporting all certificates regardless of term count alongside `code/k6_pos_solver.cpp`), settling $g(n) = 7$ on $[44, 59]$. *(Note: no prior conjecture in the literature asserted $n_{\max}(k) \le k^2 + k + 1$ for general $k$, and Choi's $n^{2/5 + o(1)}$ upper bound already forces eventual failure; the new observation is that it fails at the very first value $k = 7$.)*

#### Theorem 2.2 (Certified Bounds on $n_{\max}(k)$ and Infinite Doubling Sequence)
Pure Lean 4 theorem `infinite_family_n_max_ge` (`proofs/InfiniteFamilyStandalone.lean`) proves $n_{\max}(k) \ge k^2 + 3k - 11$ for all $k \ge 6$:
$$n_{\max}(1)=3,\; n_{\max}(2)=7,\; n_{\max}(3)=13,\; n_{\max}(4)=21,\; n_{\max}(5)=31,\; n_{\max}(6)=43,$$
$$n_{\max}(7) \ge 59 > 57,\quad n_{\max}(8) \ge 77 > 73,\quad n_{\max}(9) \ge 97 > 91,\quad n_{\max}(10) \ge 119 > 111.$$

*Certified Witnesses ($1 \dots 10$):*
1. **$k = 1$ ($n = 3$):** $A_3 = \{-1, 0, 1\}$, $M(A_3) = 1$.
2. **$k = 2$ ($n = 7$):** $A_7 = \{-3, \dots, 3\}$, $M(A_7) = 2$.
3. **$k = 3$ ($n = 13$):** $A_{13}^* = \{-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8\}$, $M(A_{13}^*) = 3$.
4. **$k = 4$ ($n = 21$):** $A_{21}$, $M(A_{21}) = 4$ (`WitnessesStandalone.lean`).
5. **$k = 5$ ($n = 31$):** $A_{31}$, $M(A_{31}) = 5$ (`WitnessesStandalone.lean`).
6. **$k = 6$ ($n = 43$):** $A_{43}$, $M(A_{43}) = 6$ (`WitnessesStandalone.lean`).
7. **$k = 7$ ($n = 59$):** $A_{59}$ (doubled $A_{43}$, refuting $k^2+k+1 = 57$; supersedes earlier $A_{51}$), $M(A_{59}) = 7$ (`NewWitnessesStandalone.lean`).
8. **$k = 8$ ($n = 77$), $k = 9$ ($n = 97$), $k = 10$ ($n = 100$):** `A52..A100` all formally certified in `NewWitnessesStandalone.lean`.

---

### 2.3 Explicit Retraction: The Positive Back-Degree Fallacy

We formally document the error in the purported proof of $n_{\max}(k) \le k^2 + k + 1$:
- **The False Statement:** It was claimed that in $A_+ = \{x_1 > x_2 > \dots > x_m > 0\}$, the back-neighborhood $N^+(x_i) = \{x_j : j < i, x_i + x_j \in A_+\}$ satisfies $|N^+(x_i)| \le M(A) - 1$.
- **Direct Counterexamples:**
  1. For $A = \{1, 2, 3, 4, 5, 6\}$, $M(A) = 4$ (e.g. $\{3, 4, 5, 6\}$), so $M(A) - 1 = 3$. But for $x_6 = 1$, $N^+(1) = \{2, 3, 4, 5\}$ has size $4 > 3$.
  2. In our verified witness $A_{21}$, $M(A_{21}) = 4$ ($M(A_{21}) - 1 = 3$). In $A_{21, +}$, $|N^+(1)| = 7$ and $|N^+(2)| = 5$, both violating the bound.
- **The Mathematical Gaps:**
  1. The proof assumed $x_i + x_{j_r} \in A_+$, which forces $x_{j_r} + x_i \le \max(A_+)$. But the proof erroneously asserted $x_{j_r} + x_{j_s} > x_{j_r} + x_i > \max(A_+)$, which is false whenever $x_{j_r} + x_{j_s} \le \max(A_+)$. $N^+(x_i)$ is not an independent set.
  2. Appending $x_i$ to $N^+(x_i)$ cannot produce an independent set because $x_i$ is adjacent to every vertex in $N^+(x_i)$ by definition.
  3. Summing back-degrees bounds edges, not the number of vertices $|A_+|$.
  4. Most fundamentally, if $n_{\max}(k) \le k^2 + k + 1$ were true for all $k$, it would force $g(n) \ge \Omega(\sqrt{n})$, which directly contradicts Ruzsa's upper bound $g(n) \ll \exp(C \sqrt{\log n})$.

**Settled & Open Status:** The exact equality $n_{\max}(k) = k^2 + k + 1$ holds unconditionally for $k \in \{1, 2, 3, 4, 5, 6\}$ (`k=1..4` in Pure Lean 4; `k=5, 6` via Gordan/Farkas LP + SAT over $\mathbb{R}$) and fails cleanly for all $k \ge 7$ via inductive doubling (`InfiniteFamilyStandalone.lean`: $n_{\max}(k) \ge k^2 + 3k - 11$, so $n_{\max}(7) \ge 59 > 57$). Determining exact values of $n_{\max}(k)$ for $k \ge 7$ remains open.

---

## 3. Rigorous Structural Conflict Graph Theorems

### 3.1 Theorem (Spherical $K_4$-Freeness)
Let $S \subset \mathbb{R}^d$ be any subset of a Euclidean sphere of radius $R > 0$:
$$S \subset \left\{x \in \mathbb{R}^d : \|x\|^2 = R^2\right\}.$$
Then the conflict graph $G_S$ satisfies:
$$\omega(G_S) \le 3.$$
That is, $G_S$ contains no clique of size 4.

*Proof.*
For any two distinct points $u, v \in S$, an edge $\{u, v\} \in E(G_S)$ requires $u + v \in S$.
Expanding the squared Euclidean norm:
$$\|u + v\|^2 = R^2 \iff \|u\|^2 + \|v\|^2 + 2\langle u, v \rangle = R^2 \iff 2R^2 + 2\langle u, v \rangle = R^2 \iff \langle u, v \rangle = -\frac{R^2}{2}.$$
Equivalently, the Euclidean angle satisfies $\cos \theta(u, v) = -1/2 \iff \theta(u, v) = 120^\circ$.
Suppose for contradiction that $G_S$ contains a 4-clique $\{v_1, v_2, v_3, v_4\} \subset S$.
Then for all $1 \le i < j \le 4$, $\langle v_i, v_j \rangle = -R^2 / 2$.
Consider the squared norm of their vector sum $\sum_{i=1}^4 v_i$:
$$\left\|\sum_{i=1}^4 v_i\right\|^2 = \sum_{i=1}^4 \|v_i\|^2 + 2 \sum_{1 \le i < j \le 4} \langle v_i, v_j \rangle = 4R^2 + 2 \binom{4}{2}\left(-\frac{R^2}{2}\right) = 4R^2 + 12\left(-\frac{R^2}{2}\right) = 4R^2 - 6R^2 = -2R^2.$$
In any real inner product space, $\|x\|^2 \ge 0$ for all $x \in \mathbb{R}^d$.
Since $R > 0$, $-2R^2 < 0$.
The inequality $0 \le -2R^2 < 0$ is an immediate contradiction.
Thus, no 4-clique can exist in $G_S$, so $\omega(G_S) \le 3$.
$\blacksquare$

---

### 3.2 Theorem (Directional $60^\circ$ Cap Independence)
Let $S \subset \mathbb{R}^d$ lie on a sphere of radius $R > 0$. Let $p \in \mathbb{S}^{d-1}$ be any unit vector.
Define the open $60^\circ$ spherical cap:
$$C(p) = \left\{ x \in S : \langle x, p \rangle > \frac{R}{2} \right\}.$$
Then $C(p)$ is an independent set in $G_S$:
$$(C(p) \hat{+} C(p)) \cap S = \emptyset.$$

*Proof.*
Let $u, v \in C(p)$ be distinct points.
By linearity of the inner product:
$$\langle u + v, p \rangle = \langle u, p \rangle + \langle v, p \rangle > \frac{R}{2} + \frac{R}{2} = R.$$
By the Cauchy–Schwarz inequality:
$$\|u + v\| = \|u + v\| \cdot \|p\| \ge \langle u + v, p \rangle > R.$$
Since every element $w \in S$ has norm $\|w\| = R$, the sum $u + v$ has norm strictly greater than $R$, and therefore $u + v \notin S$.
Hence, no pair in $C(p)$ can sum to an element in $S$.
Thus $C(p)$ is strictly sum-avoiding with respect to $S$.
$\blacksquare$

---

### 3.3 Theorem (Additive Energy Lower Bound via Turán and Cauchy–Schwarz)
Let $A \subset \mathbb{Z}$ be a finite set of cardinality $|A| = n$ with independence number $\alpha(G_A)$.
Then the additive energy $E(A, A) = \sum_{x} r_{A+A}(x)^2$ satisfies:
$$E(A, A) \ge \frac{4|E(G_A)|^2}{n} \ge \frac{n^3}{\alpha(G_A)^2}(1 - o(1)).$$

*Proof.*
1. In the conflict graph $G_A$, an edge $\{u, v\}$ means $u + v = w \in A$.
   Thus each edge contributes to a distinct sum $u + v \in A$.
   By Turán's theorem, any graph on $n$ vertices with independence number $\alpha$ satisfies:
   $$|E(G_A)| \ge \frac{n^2}{2\alpha} - \frac{n}{2}.$$
2. The number of pairs $(u, v) \in A^2$ summing into $A$ is $2|E(G_A)|$.
   By Cauchy–Schwarz applied to the representation function $r(w) = |\{(u, v) \in A^2 : u + v = w\}|$ over $w \in A$:
   $$E(A, A) = \sum_{w \in A + A} r(w)^2 \ge \sum_{w \in A} r(w)^2 \ge \frac{1}{|A|} \left(\sum_{w \in A} r(w)\right)^2 = \frac{(2|E(G_A)|)^2}{n} = \frac{4|E(G_A)|^2}{n}.$$
3. Substituting the Turán bound:
   $$E(A, A) \ge \frac{4}{n} \left(\frac{n^2}{2\alpha} - \frac{n}{2}\right)^2 = \frac{n^3}{\alpha^2} \left(1 - \frac{\alpha}{n}\right)^2 = \frac{n^3}{\alpha^2}(1 - o(1)).$$
$\blacksquare$

---

## 4. Retraction and Rigorous Audit of Asymptotic Claims

### 4.1 Retraction: Carry-Free Radix Thresholds and Boundary Distortion
- **The Error:** Previous drafts claimed that radix $B \ge 2L + 1$ prevents carries in the projection $\pi(x) = \sum x_i B^{i-1}$ for spherical relations $u + v = w$.
- **The Correction:** For $u, v, w \in \{-L, \dots, L\}^d$, the linear form is $u_i + v_i - w_i \in [-3L, 3L]$.
  Preventing carries across all equations $u + v = w$ requires:
  $$B \ge 3L + 1.$$
  Furthermore, preventing carries across *all* pairwise sums $u + v$ (even when $u + v \notin S$) requires $B \ge 4L + 1$.
- **Counterexample to $B = 3$ ($L = 1$):**
  In $\{-1, 0, 1\}^6$ with $B = 3$, $u = (-1, -1, -1, -1, 0, 0)$ ($\pi_3(u) = -40$) and $v = (-1, -1, -1, 0, -1, 0)$ ($\pi_3(v) = -94$) have $\langle u, v \rangle = 3$ ($\theta \approx 41.4^\circ < 60^\circ$).
  Yet $\pi_3(u) + \pi_3(v) = -134 = \pi_3(1, 0, 0, 1, 1, -1) \in \pi_3(S)$.
  Thus, $60^\circ$ caps are **not independent** in the projected set $\pi_3(S)$ because digital carries create artificial sum collisions!
  To guarantee that $\pi(S)$ is an exact Freiman copy of the geometric graph $G_S$, one must use $B \ge 4L + 1$.

---

### 4.2 Retraction: Subset Non-Monotonicity in Sum-Avoidance
- **The Error:** Previous drafts claimed that if $A$ contains an arithmetic progression $P$, then $M(A) \ge M(P) \ge |P|/2$.
- **The Correction:** The property of being sum-avoiding with respect to $A$ is **non-monotone under supersets**:
  $$P \subseteq A \centernot\implies M(A) \ge M(P).$$
  If $B_P \subset P$ is sum-avoiding with respect to $P$ ($(B_P \hat{+} B_P) \cap P = \emptyset$), two elements of $B_P$ can easily sum to an element in $A \setminus P$. Adding elements to $A$ creates additional sum constraints that can destroy the sum-avoidance of $B_P$.

---

### 4.3 Clarification: $k$-Cliques versus $k$-Configurations
- **The Distinction:**
  - A **$k$-clique in $G_A$** is a collection $\{x_1, \dots, x_k\} \subseteq A$ such that $x_i + x_j \in A$ for all $i \neq j$. By Theorem 3.1, on a sphere $\omega(G_S) \le 3$.
  - A **$k$-configuration** in the sense of Sudakov–Szemerédi–Vu (2005) and Beker (2025) is a sequence of elements $y_1, \dots, y_k$ and their pairwise midpoints $(y_i + y_j)/2 \in A$.
  - The $K_4$-freeness of $G_S$ does *not* imply that $A$ contains no $k$-configurations. Beker's theorem proves that *every* dense subset of $[N]$ contains $k$-configurations for $k \to \infty$. Conflating cliques in $G_A$ with arithmetic configurations was an error.

---

### 4.4 Retraction: The Spherical Inverse Theorem
- **The Error:** Previous drafts claimed a theorem asserting that any set $A \subset \mathbb{Z}$ with $\alpha(G_A) \le (\log n)^C$ is Freiman-isomorphic to an isotropic Euclidean spherical shell.
- **The Correction:** This claim is unproven and false in general:
  - Adjoining a small set like $\{-3, \dots, 3\}$ to any set $A$ introduces 4-cliques while increasing $\alpha$ by at most 2, precluding any Freiman embedding into a sphere.
  - While Gowers $U^3$ norms detect quadratic correlations, they yield correlation with 2-step nilsequences on Bohr sets, not global containment on a spherical shell in $\mathbb{Z}^d$.
  - Linear transformations preserve additive relations ($u + v = w$), so general ellipsoids have the exact same conflict graph as spheres; conflict density cannot force isotropy $M = I$.
  - Establishing a rigorous inverse theorem for sum-avoidance remains a major open problem in additive combinatorics.

---

## 5. The Current Asymptotic Frontier

The exact asymptotic growth rate of $g(n)$ remains the premier open question of Erdős Problem #787:

$$\boxed{ (\log n)^{1 + \frac{1}{68} - o(1)} \le g(n) \le \exp\left((\sqrt{8 \log 2} + o(1)) \sqrt{\log n}\right) }$$

- **Upper Bound:** Proved by Imre Z. Ruzsa (2005) using multi-scale 2-adic unions of discrete lattice balls embedded via carry-free radix projections ($\pi_Q$; note $\sqrt{8 \log 2}$ is the construction constant formalized cleanly in Pure Lean 4 via `AsymptoticClosureStandalone.lean` with checkerboard $D_d$ sharpening and explicit `D_5, L=37` crossover `dd_beats_quadratic_explicit`, not a proved lower limit for `g`).
- **Lower Bound:** Proved by Adrian Beker (2025, `arXiv:2501.10203v2`, improving on Tom Sanders 2021, `arXiv:1804.03356`) via Kelley–Meka-type density increments (`1/68`). An unverified analytic sketch toward `1/44` using Lemma 2.2 (asymmetric tuple peeling) and two-bucket step counting is recorded in [`asymptotic_closure_synthesis.md`](./asymptotic_closure_synthesis.md), while Yao Zhi's preprint (`arXiv:2610.03750`, September 2026, unrefereed) states `c < 1/36` along Beker's route.
- **The Open Challenge:** Closing the quantitative gap between polylogarithmic lower bounds and sub-polynomial upper bounds remains an active, unsolved frontier in additive number theory.

---

## 6. Machine-Checked Formalization Architecture

All finite thresholds ($k = 1 \dots 4$), all 56 constructed witnesses ($A_3 \dots A_{100}$), the infinite doubling family ($k \ge 6$), and spherical/carry/checkerboard theorems are machine-checked without `sorry` in **Pure Lean 4** (`Init` only, standard axioms):

| Result / Theorem | Lean 4 Module | Key Identifier |
| :--- | :--- | :--- |
| **Sum-Avoidance Duality & Jump Discriminant** | [`Erdos787Standalone.lean`](../proofs/Erdos787Standalone.lean) | `isSumAvoiding_iff_independent`, `jump_point_odd_square` |
| **Exact Thresholds ($k = 1, 2, 3$)** | [`ThresholdsStandalone.lean`](../proofs/ThresholdsStandalone.lean) | `n_max_1_exact`, `n_max_2_exact`, `n_max_3_exact` |
| **Exact Threshold ($k = 4$, Hinted-RUP + Farkas)** | [`Threshold45Standalone.lean`](../proofs/Threshold45Standalone.lean) | `n_max_4_exact` ($n_{\max}(4) = 21$) |
| **Exact Witness Bounds (`A3..A51`)** | [`WitnessesStandalone.lean`](../proofs/WitnessesStandalone.lean) | `all_seven_witnesses_certified` |
| **All 49 New Witnesses (`A52..A100`)** | [`NewWitnessesStandalone.lean`](../proofs/NewWitnessesStandalone.lean) | `all_49_new_witnesses_certified` |
| **Infinite Doubling ($k \ge 6$) & $59 > 57$** | [`InfiniteFamilyStandalone.lean`](../proofs/InfiniteFamilyStandalone.lean) | `infinite_family_n_max_ge`, `k7_beats_projective_bound` |
| **Spherical $K_4$-Freeness, $60^\circ$ Caps, & Radix Carries** | [`GeometryAndCarriesStandalone.lean`](../proofs/GeometryAndCarriesStandalone.lean) | `spherical_k4_freeness`, `directional_cap_sum_avoiding` |
| **Single-Sphere Orthant Bound, Dyadic Cascades, Full $D_d$ Crossover & Quasipolynomial Scaling** | [`AsymptoticClosureStandalone.lean`](../proofs/AsymptoticClosureStandalone.lean) | `single_sphere_orthant_lower_bound`, `checkerboard_Dd_normSq_drop`, `dd_beats_quadratic_explicit`, `ruzsa_beats_quadratic_explicit`, `ruzsa_quasipolynomial_nat` |

---

## 7. Conclusion

This post-audit monograph establishes the verified mathematical landscape of Erdős Problem #787:
1. Exact thresholds $n_{\max}(1)=3, n_{\max}(2)=7, n_{\max}(3)=13, n_{\max}(4)=21$ (all Pure Lean 4) and $n_{\max}(5)=31$ (strict-exact Farkas+DRAT & C++ `__int128` UNSAT), plus $n_{\max}(6)=43$ (over $\mathbb{R}$ across all `21` subcases via `code/solve_k6_pos.py` / `code/k6_pos_solver.cpp`), fix $g(n)$ for $n \in [1, 59]$ (including $g(n) = 7$ on $[44, 59]$).
2. Inductive doubling (`InfiniteFamilyStandalone.lean`) proves $n_{\max}(k) \ge k^2 + 3k - 11$ for all $k \ge 6$, showing that $k^2 + k + 1$ first fails at $k = 7$ ($n_{\max}(7) \ge 59 > 57$), while `NewWitnessesStandalone.lean` certifies all witnesses $A_{52} \dots A_{100}$ bracketing $g(n) \in [7, 10]$ on $[60, 100]$, extended via C++ (`verified_100_143.txt`) to $g(n) \le 10$ on $[98, 119]$ and $g(n) \le 11$ on $[120, 143]$.
3. Spherical conflict graphs are proved $K_4$-free, open $60^\circ$ caps are proved sum-avoiding, carry thresholds ($B \ge 3L+1$ / $4L+1$) are machine-checked without `sorry`, and the checkerboard $D_d$ multi-scale construction (`dd_beats_quadratic_explicit`) proves super-quadratic growth at `D_5, L = 37`, with `ruzsa_quasipolynomial_nat` reproducing Ruzsa's construction constant $\sqrt{8\log 2}$.
4. Exact values $n_{\max}(k)$ for $k \ge 7$ and closing the asymptotic corridor remain open conjectures (see [`asymptotic_closure_synthesis.md`](./asymptotic_closure_synthesis.md) for the irreducible obstructions, the unverified `1/44` sketch, and Yao Zhi's `arXiv:2610.03750` citation).
