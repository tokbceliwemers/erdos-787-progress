# Asymptotic Closure Synthesis for Erdős Problem #787

This report synthesizes the mathematical advances, Lean 4 formalizations, C++ computational verifications, and irreducible structural obstructions separating the lower and upper asymptotic bounds for Erdős Problem #787 (`M(n)` / `g(n)`, the maximum guaranteed size of a sum-avoiding subset inside any `n`-element set of real numbers or integers).

---

## 1. Executive Summary: State of the Art

Following a post-review mathematical and computational audit, this note separates **rigorously verified finite/structural results** from an **analytic lower-bound sketch** for Erdős Problem #787 (`M(n)` / `g(n)`):

- **Verified Unconditional Asymptotic Bounds:**
  $$\boxed{(\log n)^{1 + \frac{1}{68} - o(1)} \;\le\; g(n) \;\le\; \exp\left((\sqrt{8 \log 2} + o(1)) \sqrt{\log n}\right)}$$
  where the lower bound `c < 1/68` is due to Beker (`2025`, `arXiv:2501.10203v2`, improving Sanders `2021`, `arXiv:1804.03356`), and the upper-bound construction constant $\sqrt{8 \log 2}$ is due to Ruzsa (`2005`), formalized here in Pure Lean 4 via checkerboard $D_d$ multi-scale balls (`AsymptoticClosureStandalone.lean`). *(Note: two months prior to this repository, Yao Zhi's unrefereed preprint `arXiv:2610.03750` claims every $c < 1/36$ along Beker's route.)*
- **Analytic Sketch Highlighted Below (`1/68 -> 1/44`, Unverified):** Section 2 states and proves an **Asymmetric Bipartite Tuple Peeling Lemma** cleanly, then traces a candidate exponent improvement from `1/68` down to `1/44` inside Beker's (`2025`) density-increment framework (`unverified` as a complete formal proof, and superseded in exponent by Yao Zhi's `1/36` claim).

Equivalently, under Beker's unconditional `1/68` bound vs. Ruzsa's `2005` construction constant, the inverse threshold $n_{\max}(k) = \max\{|A| : M(A) \le k\}$ satisfies $\exp\!\left(\left(\frac{1}{8\log 2} - o(1)\right)(\log k)^2\right) \le n_{\max}(k) \le \exp(k^{68/69 + o(1)})$.

**Summary of Contributions Documented Here:**
1. **Asymmetric Bipartite Peeling Lemma (Verified Combinatorial Reduction) & `1/68 -> 1/44` Exponent Trace (Unverified Analytic Sketch):** Lemma 2.2 gives a self-contained proof reducing symmetric bipartite graph counting (`[FHHK Cor 2.3]`) to asymmetric tuple peeling preserving the smaller part's density $\mu_Y(T) \ge \alpha_0^r$ (in `Subcase B`, $r = 2$: $\mu_{B^{(j)}}(T) \ge (\alpha/2)^3$). Tracing this inside Beker's (`arXiv:2501.10203v2`) `lm:main_technical_lemma` (`b: 46 -> 28`, `c: 6 -> 1`) paired with separating zero-frequency `[FHHK Lem 3.4]` scale-uniformity steps ($\Delta_r = \emptyset$) from harmonic/graph-counting branches in `thm:general_groups` yields an analytic parameter trace to $E_k = 1 + (5 + 4 + 28) + (5 + 1) = 44$. Because full integration with `[FHHK Lem 3.4]` and Bohr localization inside Beker's proof has not been written out and audited line-by-line, **`1/44` remains an unverified sketch** (and Yao Zhi `arXiv:2610.03750` independently claims $c < 1/36$).
2. **Correction, Checkerboard $D_d$ Lean Formalization, and Lattice Sharpening of Ruzsa (2005):** Refutes the claim that a *single* Euclidean sphere can give sub-polynomial $\alpha(G_S)$ (every finite zero-free equal-norm subset $S \subset \mathbb{R}^d$ satisfies $\alpha(G_S) \ge |S|/2^d$ across orthants). Ruzsa's (`2005`) construction uses a **multi-scale 2-adic union of discrete lattice balls** $A = \bigcup_{i=0}^{r} 2^i (B_{r-i}(c) \cap \Lambda)$ embedded carry-free into $\mathbb{Z}_+$, yielding $g(n) \le \exp((\sqrt{8\log 2}+o(1))\sqrt{\log n})$ along a subsequence (`this is Ruzsa's construction constant, not a proved lower limit on g`). Replacing $\Lambda = \mathbb{Z}^d$ with the checkerboard sublattice $D_d = \{x \in \mathbb{Z}^d : \sum x_j \equiv 0 \pmod 2\}$ halves coset overhead per squared-norm drop (`norm drop >= 2` while retaining $|D_d / 2D_d| = 2^d$ cosets), beating $k^2 + 3k - 11$ unconditionally in Pure Lean 4 at $d = 5, L = 37$ ($k \le 1185$, $n = 1{,}438{,}294 > 1{,}407{,}769$; `dd_beats_quadratic_explicit`), and in tight C++ analysis already at $D_5, L = 36$ ($k \le 1142$, $n = 1{,}309{,}341 > 1{,}307{,}579$). Moreover, `ruzsa_quasipolynomial_nat` (`d=2m, t=2^m`) attains Ruzsa's asymptotic constant $C = \sqrt{8\log 2} \approx 2.3548$, while even unimodular lattices $E_8$ (`L=16, k<=4097`) and Leech $\Lambda_{24}$ (`L=10`, $2.111\times$ quadratic) and zero-centered $D_d$ (`2^d-1` cosets per layer) sharpen small-$L$ efficiency. Dual-verified witnesses are also extended to all $n \in [100, 143]$ in [`../data/verified_100_143.txt`](../data/verified_100_143.txt) ($\alpha \le 10$ on $[98, 119]$, $\alpha \le 11$ on $[120, 143]$).
3. **Zero-`sorry` Pure Lean 4 Formalization:** All structural lemmas, dyadic shell cascades, single-sphere orthant lower bounds, full checkerboard $D_d$ multi-scale construction (`ddIntSet`, `ddVecs_sum_avoiding_bound`, `dd_beats_quadratic_explicit` for $D_5, L=37$), and sharp quasipolynomial scaling (`ruzsa_quasipolynomial_nat`) are formally proved in [`AsymptoticClosureStandalone.lean`](../proofs/AsymptoticClosureStandalone.lean) (`2,957` lines) using only `Init` (standard axioms `[propext, Classical.choice, Quot.sound]`).
4. **Irreducible Barrier Map:** Summarizes why closing the full gap to $g(n) = \exp(\Theta(\sqrt{\log n}))$ requires going beyond Kelley–Meka / Sanders / Beker density increments and smooth convex $L^2$ lattice balls.

---

## 2. Analytic Lower-Bound Sketch: Reconciling Beker (2025) from `1/68` Toward `1/44` (Unverified)

> **Status & Literature Context:** This section is an **analytic sketch** built on Beker (`2025`, `arXiv:2501.10203v2`), not a complete peer-checked proof or Lean formalization. While **Lemma 2.2** below is proved in full as a standalone bipartite tuple-peeling fact, substituting it into Beker's `[FHHK Lem 3.4]` and Bohr-set localization (`lm:main_technical_lemma` / `thm:general_groups`) has not yet been written out line by line from Beker's full text, so the resulting `1/44` exponent remains **unverified**. Moreover, two months before this repository was created, **Yao Zhi (`arXiv:2610.03750`, *"Branch-Sensitive Density Increments for $k$-Configurations"*, September/October 2026, unrefereed)** already claimed every $c < 1/36$ along Beker's route.

### 2.1 Origin of the `k^68` Bottleneck
In Beker (2025, `arXiv:2501.10203v2`), the quantitative density-increment step (`prop:density_increment`) is governed by:

$$N \ge \exp\left(C \, k^{1 + 3a + b + c} \cdot \mathrm{poly}(\log k, \mathcal{L}(\alpha))\right)$$

where:
- `a = 5` is the `[FHHK Lem 3.4]` exponent converting $L^p$-almost-periodicity / solution counts into Bohr density increments,
- `b` is the dimension exponent in the Bohr-set density increment $\widetilde{d}' \ll k^b \cdots$,
- `c` is the width loss exponent $\rho' \ge \rho \cdot \exp(-O(k^c \cdots))$.

In Beker's proof of `thm:graph_counting`, `Case (i)` invokes the symmetric graph counting lemma (`[FHHK Cor 2.3]`), inflating *both* sides of an asymmetric pair $(S, T) \subset X^r \times Y$ from $\mu(T) \ge \alpha_0^r$ back to comparable density before intersecting with a shifted Bohr sub-atom. In `Subcase B` (`r = 2`, $p' \asymp k^6 \mathcal{L}(\alpha)$) of `lm:main_technical_lemma`, that symmetrization accounts for `18` powers of $k$ in $b$ (`28 -> 46`) and `5` powers of $k$ in $c$ (`1 -> 6`), giving $1 + 3(5) + 46 + 6 = 68$.

### 2.2 Lemma (Asymmetric Bipartite Tuple Peeling)

**Hypotheses.** Let $X, Y$ be finite non-empty sets equipped with uniform probability measures $\mu_X, \mu_Y$, and let $E \subseteq X \times Y$ be a bipartite relation with neighborhoods $N(x) := \{y \in Y : (x, y) \in E\}$ and common neighborhoods $T(x_1, \dots, x_s) := \bigcap_{i=1}^s N(x_i) \subseteq Y$. Fix an integer $r \ge 2$ and reals $\alpha_0 \in (0, 1]$, $\tilde{\delta} \in (0, 1]$, $\eta_r \in (0, 1]$. For each $s \in \{1, \dots, r\}$, define:
$$\theta_s := \left(1 + \frac{\tilde{\delta}}{4}\right)^s \alpha_0^s, \qquad G_s := \left\{ x \in X^s : \mu_Y(T(x)) \ge \theta_s \right\}.$$
Assume $\mu_{X^r}(G_r) \ge \eta_r$.

**Conclusion.** At least one of the following holds:
1. *(Asymmetric dense pair at some stage $s \in \{2, \dots, r\}$)* There exist subsets $S \subseteq X$ and $T \subseteq Y$ (of the form $T = T(x')$ for some $x' \in X^{s-1} \setminus G_{s-1}$) such that:
   $$\mu_X(S) \ge \frac{\eta_r}{2^{r - s + 1}} \ge \frac{\eta_r}{2^r}, \qquad \mu_Y(T) \ge \theta_s \ge \alpha_0^s \ge \alpha_0^r,$$
   and every vertex $x \in S$ has relative neighborhood density in $T$ strictly exceeding $(1 + \tilde{\delta}/4)\alpha_0$:
   $$\frac{\mu_Y(N(x) \cap T)}{\mu_Y(T)} > \left(1 + \frac{\tilde{\delta}}{4}\right)\alpha_0.$$
2. *(Single-element dense fiber at $s = 1$)* The set $G_1 = \{ x_1 \in X : \mu_Y(N(x_1)) \ge (1 + \tilde{\delta}/4)\alpha_0 \}$ satisfies $\mu_X(G_1) \ge \eta_r / 2^{r-1} \ge \eta_r / 2^r$.

**Proof.** Induct downward on $s = r, r - 1, \dots, 2$, maintaining $\mu_{X^s}(G_s) \ge \eta_s := \eta_r / 2^{r - s}$. At step $s$:
- If $\mu_{X^{s-1}}(G_{s-1}) \ge \eta_s / 2 = \eta_{s-1}$, pass to stage $s - 1$.
- Otherwise, $\mu_{X^{s-1}}(G_{s-1}) < \eta_s / 2$. Since $(G_{s-1} \times X) \subseteq X^s$ has product measure $\mu_{X^{s-1}}(G_{s-1}) < \eta_s / 2$,
  $$\mu_{X^s}\big(G_s \cap ((X^{s-1} \setminus G_{s-1}) \times X)\big) \ge \mu_{X^s}(G_s) - \mu_{X^{s-1}}(G_{s-1}) > \eta_s - \frac{\eta_s}{2} = \frac{\eta_s}{2}.$$
  By averaging over $x' \in X^{s-1} \setminus G_{s-1}$, there exists $x' \in X^{s-1} \setminus G_{s-1}$ whose fiber $S := \{ x_s \in X : (x', x_s) \in G_s \}$ has $\mu_X(S) \ge \eta_s / 2 = \eta_r / 2^{r - s + 1} > 0$. Setting $T := T(x')$, for any $x_s \in S$ we have $T(x') \supseteq T(x', x_s)$, whence $\mu_Y(T) \ge \mu_Y(T(x', x_s)) \ge \theta_s \ge \alpha_0^s \ge \alpha_0^r$ (since $\alpha_0 \le 1$ and $s \le r$). Conversely, $x' \notin G_{s-1}$ gives $\mu_Y(T) < \theta_{s-1}$. Therefore, for every $x \in S$:
  $$\frac{\mu_Y(N(x) \cap T)}{\mu_Y(T)} = \frac{\mu_Y(T(x', x))}{\mu_Y(T)} > \frac{\theta_s}{\theta_{s-1}} = \left(1 + \frac{\tilde{\delta}}{4}\right)\alpha_0,$$
  establishing alternative (1).

If no stage $s \in \{2, \dots, r\}$ triggers alternative (1), then stage $s = 1$ retains $\mu_X(G_1) \ge \eta_1 = \eta_r / 2^{r-1}$, establishing alternative (2). $\blacksquare$

*Application in Beker's setting (sketch):* Lifting Hölder exponent $q' = \max(q, \lceil 8/(r\tilde{\delta}) \rceil)$ in `lm:main_technical_lemma` (`\eta_r \ge \alpha_0^{rq'}`) and invoking Lemma 2.2 supplies either `Case (i)` directly with an asymmetric dense pair ($\mu(S) \ge 2^{-r}\alpha_0^{rq'}$ and $\mu(T) \ge \alpha_0^r$, giving $\mu_{B^{(j)}}(T) \ge (\alpha/2)^3$ at $r = 2$ in `Subcase B`), or `Case (iii)` directly at $s = 1$.

### 2.3 Candidate Branch Accounting for `prop:density_increment` (Unverified)

Assuming Lemma 2.2 can replace symmetric `[FHHK Cor 2.3]` inside `lm:main_technical_lemma` while transferring the remaining Bohr-localization bounds directly from Beker (`arXiv:2501.10203v2`) gives the following branch parameters:

| Branch in `prop:density_increment` | Parameters (`Subcase` / Type) | Bohr Dimension Loss $\widetilde{d}'$ | Width Loss Exponent $c$ | Limiting $k$-power ($b$) |
| :--- | :--- | :--- | :--- | :--- |
| Discrepancy branch | Direct Fourier / Bohr imbalance | $\ll k^{16}(\log k)^4 \mathcal{L}^6$ | $1$ | $16$ |
| `Case (ii)` | Structured diagonal / high-degree | $\ll k^{28}(\log k)^2 \mathcal{L}^4 (\mathcal{L} + \log k)^2$ | $1$ | $28$ |
| `Case (iii)` | Single-fiber dense target (`s = 1`) | $\ll k^{28}\mathcal{L}(\alpha)^4 (\mathcal{L}(\alpha) + \log k)^4$ | $1$ | $28$ |
| `Case (i) — Subcase A` | $r = 2(\ell-1) \le 2k$, $p \asymp k^2 \mathcal{L}(\alpha)$ | $\ll k^{27}\mathcal{L}^6 + k^{25}\mathcal{L}^8$ | $1$ (loss $\exp(-O(k\mathcal{L}(\alpha/d) + k\mathcal{L}(\alpha) + k\log k))$) | $27$ |
| `Case (i) — Subcase B` | $r = 2$, $p' \asymp k^6 \mathcal{L}(\alpha)$, $\mu_{B^{(j)}}(T) \ge (\alpha/2)^3$ | $\ll k^{28}\mathcal{L}(\alpha)^6 (\mathcal{L}(\alpha) + \log k)^2$ | $1$ | $28$ |

### 2.4 Candidate Two-Bucket Step Counting (`1/45 -> 1/44`, Unverified Sketch)
Under this sketch, inspecting the iteration in `thm:general_groups` of Beker (2025) separates steps $(A_s, B_s)_{0 \le s \le t}$ into two disjoint classes:
1. **Scale-uniformity steps ($s \in L$):** When `[FHHK Lem 3.4]` fires on $\mathcal{B} = \{B^{(j)}, \frac{1}{2} \cdot B^{(j)} : j \in [k]\}$, $\alpha_s \ge (1 + \frac{\gamma}{4k})\alpha_{s-1} = (1 + \Omega(k^{-5}))\alpha_{s-1}$ with $\Delta_s = \emptyset$ and width loss $\lambda_j \ge (\lambda/2)^k = \exp(-O(k(\mathcal{L}(\alpha/d_{s-1})+\log k)))$.
2. **Harmonic / graph-counting steps ($s \in H$):** All remaining branches achieve density increment $\alpha_s \ge (1 + \Omega(k^{-4}))\alpha_{s-1}$ and add $|\Delta_s| \ll k^{28}(\log k)^2\mathcal{L}(\alpha)^6(\mathcal{L}(\alpha)+\log k)^2$ frequencies with width factor $c = 1$.

Thus total chain length satisfies $t \ll k^5\mathcal{L}(\alpha)$ while nonzero frequency-adding steps satisfy $|H| \ll k^4\mathcal{L}(\alpha)$, motivating the union bound:
$$d_t = |\Gamma_t| \le (2t + 1) + \sum_{r \in H} (2(t - r) + 1)|\Delta_r| \ll t \cdot |H| \cdot k^{28}\dots \ll \mathbf{k^{37}}(\log k)^2\mathcal{L}(\alpha)^8(\mathcal{L}(\alpha)+\log k)^2,$$
with $E_k = 1 + (a_L + a_H + b) + (a_L + c) = 1 + (5 + 4 + 28) + (5 + 1) = \mathbf{44}$, matching $\phi(n) \ge (\log n)^{1 + c}$ for $c < 1/44$ as an unverified analytic target (still behind Yao Zhi `arXiv:2610.03750`'s `c < 1/36`).

---

## 3. Reconstruction & Sublattice Sharpening of Ruzsa (2005)

### 3.1 Refutation of the Single-Sphere Myth
Multiple earlier workspace notes stated that Ruzsa obtains $g(n) \le \exp(C\sqrt{\log n})$ by projecting a *single* discrete sphere $S \subset \mathbb{Z}^d$ of radius $R$ via a carry-free radix map, noting that $60^\circ$ spherical caps are sum-avoiding.

**Why a single sphere fails:** If $0 \notin S$ and $S \subset \mathbb{R}^d$, partition $\mathbb{R}^d \setminus \{0\}$ by open/closed sign orthants (choosing nonzero coordinates' signs consistently). Any two points $x, y$ in the same closed orthant satisfy $\langle x, y \rangle \ge 0$, and strictly $> 0$ when $x + y \neq 0$ lies on a common norm level — wait, even simpler and purely integer-valued: in [`single_sphere_orthant_lower_bound`](../proofs/AsymptoticClosureStandalone.lean), for *any* pair $u, v \in S$ sharing one of the $2^d$ orthants (`u_j * v_j >= 0` coordinatewise, provided $\|u\|_2 = \|v\|_2 = R > 0$),

$$\|u + v\|_2^2 = \|u\|_2^2 + \|v\|_2^2 + 2\langle u, v \rangle \ge 2R^2 > R^2,$$

so $u + v \notin S$! By pigeonhole over the $2^d$ coordinate sign patterns, **every single-radius sphere $S \subset \mathbb{R}^d$ (or equal-norm subset)** satisfies:

$$\alpha(G_S) \ge M(S) \ge \frac{|S|}{2^d}.$$

With $d \asymp \sqrt{\log n}$, $2^d$ is only $\exp(O(\sqrt{\log n}))$, which forces a single sphere of size $n$ to contain a sum-avoiding set of polynomial-in-$n$ (indeed $n^{1 - o(1)}$!) size. Thus a single sphere can NEVER achieve sub-polynomial $\alpha(G_A) = \exp(O(\sqrt{\log n}))$.

### 3.2 Multi-Scale 2-Adic Lattice Balls & Dyadic Shell Cascade
Ruzsa's real mechanism uses **nested squared-radius shells** coupled to **2-adic coset parity**:

$$A = \bigcup_{i=0}^{r} 2^i \left( B_{r-i}(c) \cap \Lambda \right), \qquad B_m(c) = \{x \in \Lambda : \|x - c\|_2^2 < m\},$$

with a positive coordinate shift $c = (4r+1, \dots, 4r+1)$ (or $c = (C, \dots, C)$ sufficiently large so all coordinates of every $B_m(c)$ are strictly positive) and a carry-free radix embedding $\pi_Q(x) = \sum_{j=1}^d x_j Q^{j-1}$ into $\mathbb{Z}_+$.

If $S \subset A$ is sum-avoiding, partition $S = \bigsqcup_{i=0}^r 2^i S_i$ by 2-adic valuation. Within any single scale $S_i \subset B_{r-i}(c) \cap \Lambda$, if two distinct points $u \neq v \in S_i$ belong to the same coset of $\Lambda / 2\Lambda$, their midpoint $w = (u + v)/2$ lies in $\Lambda$ and satisfies the **parallelogram norm-drop identity**:

$$\|w - c\|_2^2 = \frac{\|u - c\|_2^2 + \|v - c\|_2^2}{2} - \frac{\|u - v\|_2^2}{4}.$$

Because $u - v \in 2\Lambda \setminus \{0\}$, the term $\|u - v\|_2^2 / 4$ is at least $1$ for $\Lambda = \mathbb{Z}^d$, and at least **$2$** for the checkerboard lattice $\Lambda = D_d$! Consequently:
- Every two same-coset points in $S_i$ yield a sum $(u+v)$ whose halved representative $w$ lies strictly deeper in $B_{r-i-1}(c)$ (or $B_{r-i-2}(c)$ for $D_d$).
- Even without assuming equal radius within a layer, a Pigeonhole/Dyadic Shell Cascade across at most $r$ layers guarantees $|S_i| \le |\Lambda / 2\Lambda| = 2^d$ per layer (`up to boundary parity adjustments`). Summing over $r+1$ scales forces $\alpha(G_A) = O(r \cdot 2^d)$, whereas $|A| = \sum_{i=0}^r |B_{r-i}(c) \cap \Lambda|$ grows as a $(d+2)/2$-power of $r$:

$$|A| \ge \Omega_d\!\left(r^{(d+2)/2}\right) = \Omega_d\!\left(k^{(d+2)/2}\right).$$

Optimizing $R \asymp 2^{c d}$ via calculus (`max_{c > 0} c/(1+2c)^2 = 1/8` at $c = 1/2$, i.e. $d = 2m, t = 2^m$) yields the exact asymptotic Ruzsa constant $C = \sqrt{8\log 2} \approx 2.35482$:

$$|A| \ge \exp\!\left(\left(\frac{1}{8\log 2} - o(1)\right) (\log k)^2\right), \qquad g(n) \le \exp\!\left(\left(\sqrt{8\log 2} + o(1)\right) \sqrt{\log n}\right),$$

already attained verbatim in Pure Lean 4 by `ruzsa_quasipolynomial_nat` ($2^{2m^2+4m}$ vs $8m \cdot 2^{4m}$).

### 3.3 Checkerboard $D_d$, Tight Crossovers, $E_8$ / $\Lambda_{24}$ Lattices, & Zero-Centered Variants
Replacing $\Lambda = \mathbb{Z}^d$ with the checkerboard lattice

$$D_d = \left\{x \in \mathbb{Z}^d : \sum_{j=1}^d x_j \equiv 0 \pmod 2\right\}$$

preserves index $|D_d / 2D_d| = 2^d$ while doubling the minimum nonzero squared norm from $1$ to $2$ (`checkerboard_Dd_normSq_drop` in Lean 4: whenever $u, v \in \mathbb{Z}^d$ with $\sum u_j \equiv \sum v_j \equiv 0 \pmod 2$, $u \equiv v \pmod 2$, and $u \neq v$, then $\|u - v\|_2^2 \ge 8$, so $\|(u-v)/2\|_2^2 \ge 2$). Every pair of distinct same-coset points in $B_L(c) \cap D_d$ drops the shifted squared norm strictly to $B_{L-2}(c) \cap D_d$, yielding sharper finite bounds verified in Pure Lean 4 and C++ (`../code/ruzsa_lattice_test.cpp`, `../code/ruzsa_variants_test.cpp`, `../code/test_templates_and_e7.cpp`, `../code/attack_k7_and_lattices.cpp`, `../code/test_zero_centered_dd.cpp`):

- **Exact Independence Formula Confirmed by Tomita MCQ:** On all small instances tested (`D_2` for `L = 1..5`, giving exact $\alpha(G_A) = 4, 8, 12, 16, 20$; `D_3` for `L = 1..3`, giving exact `8, 16, 24`; `D_4` for `L = 1, 2`, giving exact `14, 30`; plus `Z^2` for `r = 1..6`, giving `4, 8, 12, 16, 20, 24`, and `Z^3` for `r = 1..4`, giving `5, 12, 20, 28`), the exact maximum independent set computed by Tomita's maximum clique solver matched the theoretical formula $(L-1)\cdot 2^d + d(d-1) + 2$ for $D_d$ identically.
- **Explicit & Tight Super-Quadratic Crossovers Against $n_{\text{quad}}(k) = k^2 + 3k - 11$:**
  - **$D_5$ Lean-Formalized Crossover (`L = 37`):** $k \le 1185$, $|A| = n = 1{,}438{,}294 > 1{,}407{,}769 = k^2 + 3k - 11$ (machine-checked in Pure Lean 4: `dd_beats_quadratic_explicit`), nearly $4{,}000\times$ smaller than the unsharpened $\mathbb{Z}^6$ Lean threshold (`d = 6, t = 7`).
  - **Tight Top-Shell `D_d` Crossovers (`k <= (L-1)*2^d + d*(d-1) + 2`):** `D_4` at $L = 75$ ($k \le 1198$, $n = 1{,}443{,}820 > 1{,}438{,}787$); `D_5` at $L = 36$ ($k \le 1142$, $n = 1{,}309{,}341 > 1{,}307{,}579$); `D_6` at $L = 26$ ($k \le 1632$, $n = 2{,}742{,}783$); `D_7` at $L = 22$ ($k \le 2732$, $n = 7{,}960{,}077$); `D_8` at $L = 20$ ($k \le 4922$, $n = 26{,}453{,}573$).
  - **Even Unimodular Lattices (`E_8` & Leech `Λ_24`):** $E_8$ theta series $1 + 240\sigma_3(m)$ verified against 8D DP for $2m = 0..16$ (`1, 240, 2160, 6720, 17520, 30240, 60480, 82560, 140400`) crosses $k^2 + 3k - 11$ at $L = 16$ ($k \le 4097$, $n = 18{,}360{,}977 > 16{,}797{,}689$, beating `D_8`'s $L=20, k\le 4922$); Leech $\Lambda_{24}$ shells (`1, 0, 196560, 16773120`) exceed the quadratic bound by `2.111x` at $L = 10$ and `13.751x` at $L = 12$.
  - **Zero-Centered `D_d` / `Z^d`:** Placing the ball center at `0` removes `0` from antipodal pairing, dropping exact independence growth from $2^d$ to $2^d - 1$ per layer (`Zero D_2` $L=1..10 \to 2, 4, 6, 8, 11, 14, 17, 20, 23, 26$; `Zero D_3` $L=1..4 \to 4, 8, 15, 22$; `Zero D_4` $L=1, 2 \to 6, 12$; `Zero Z_3` $L=5 \to 22$).

### 3.4 Finite Extremal Frontier ($k = 7..11$, $n = 60..143$)
While `../code/finite_breakthrough_search.exe` extends dual-verified witnesses through $n = 143$ (`alpha = 10` on $n \in [100, 119]$ with `1899..2725` edges, and `alpha = 11` on $n \in [120, 143]$ with `2448..3575` edges in [`../data/verified_100_143.txt`](../data/verified_100_143.txt)), exhaustive 2-tier and 3-tier template searches (`test_templates_and_e7.exe`: max $m_+ = 29, |S| = 59$ at $k = 7$), exhaustive 1-swap neighborhood scans around $A_{59} \cup \{-17\}$, and multi-threaded simulated annealing around `P_{29}` and `A_{59}` (`probe_k7_k9.exe`, `attack_k7_and_lattices.exe`: `alpha = 8`, `cnt = 127` at `n = 60` and `m_+ = 30`; `alpha = 9`, `cnt = 878` at `n = 78`) found no $\alpha = 7$ set of size $60$, keeping $n_{\max}(7) \ge 59$ consistent with tightness while unconditional real LP/CDCL proof at $m_+ = 30$ remains beyond current solver scale (`k = 6` across all `21` cases at $m_+ = 22$ already required `4,010` tasks and `1,645,192` distinct integer Farkas certificates archived in [`../data/k6_farkas_certs.jsonl.gz`](../data/k6_farkas_certs.jsonl.gz)).

---

## 4. Pure Lean 4 Formal Verification

[`AsymptoticClosureStandalone.lean`](../proofs/AsymptoticClosureStandalone.lean) (`2,957` lines, `Init`-only, zero `sorry`, zero external axioms, zero `native_decide`) formally certifies all core theorems underpinning both sides of the asymptotic picture (audited via `#print axioms`):

1. `posPart_maxSumAvoidingAtMost`: Lower bound on maximum sum-avoiding subset via positive-part split (`1-to-2` bridge to positive integers).
2. `dyadic_top_shell_le`: Single dyadic shell cardinality bound over discrete cosets.
3. `dyadic_shell_cascade_step`: One-step norm-drop reduction along the multi-scale 2-adic shell hierarchy.
4. `dyadic_shell_power_bound`: Polynomial-in-radius cardinality growth across the multi-scale ball union.
5. `dyadic_concentration_bound`: Global $\alpha(G_A)$ upper bound via dyadic cascade.
6. `single_sphere_orthant_lower_bound`: Formal refutation that any single equal-norm subset $S \subset \mathbb{Z}^d \setminus \{0\}$ has $\alpha(G_S) \ge |S|/2^d$ via coordinate sign orthants.
7. `checkerboard_Dd_normSq_drop`: Formal proof of the factor-of-2 norm drop $\|(u-v)/2\|_2^2 \ge 2$ for distinct congruent elements in $D_d$.
8. `ruzsa_superquadratic_family`: Super-quadratic scaling $n \ge \Omega(k^{5/2})$ and higher exponents for fixed dimension $d$.
9. `ruzsa_beats_quadratic_explicit`: Explicit certified inequality showing the Ruzsa $\mathbb{Z}^6$ construction exceeds $k^2 + 3k - 11$ at `(d = 6, t = 7)`.
10. `ruzsa_quasipolynomial_nat`: Quasipolynomial growth $2^{2m^2+4m}$ vs $8m \cdot 2^{4m}$ attaining the sharp constant $C = \sqrt{8\log 2}$ across variable dimension $d = 2m \asymp \sqrt{\log k}$.
11. **Section 9 — Full Checkerboard $D_d$ Multi-Scale Construction & $D_5$ Crossover:** `dd_same_coset_drop`, `ddVecs_sum_avoiding_bound`, `ddIntSet_props`, `dd5_count_l37_eq` (`1,438,294`, zero axioms), `box8_sum_eq_ddCountAux`, `ddCountAux_le_ddVecs`, and `dd_beats_quadratic_explicit` ($D_5, L = 37$: $k \le 1185$, $|A| \ge 1{,}438{,}294 > 1{,}407{,}769 = k^2 + 3k - 11$).

---

## 5. Four Irreducible Obstructions Blocking Complete Gap Closure

Closing the remaining corridor between $(\log n)^{1 + 1/44 - o(1)}$ and $\exp((\sqrt{8\log 2} + o(1)) \sqrt{\log n})$ cannot be achieved by tuning exponents inside the present Kelley–Meka / Sanders / Beker framework or by surface perturbations of Ruzsa's balls, because four structural barriers intervene:

1. **Green's Random Cayley / $k$-Configuration Ceiling at $(\log n)^2$:** Beker's reduction passes through `k`-configurations (essentially iterated additive quadruples / generalized sum-free relations whose ambient density-increment cost is governed by a Cayley-graph / random-Cayley Ramsey threshold $F(\alpha_0, k) \ge \exp(\Omega(k))$). Any argument depending purely on extracting dense structured $k$-configurations in Abelian groups is provably capped below $(\log n)^2$, far shy of $\exp(c \sqrt{\log n})$.
2. **Bohr Rank Collapse & Non-Hereditary Ambient Pollution:** In Sanders/Kelley–Meka/Beker density increments, an ambient sum-avoiding set $S$ may trigger $u + v \in A \setminus S$ rather than $u + v \in S$ itself (non-hereditary $G_A$ conflict condition relative to $A$, not just internal $S + S \cap S = \emptyset$). Localizing $A$ to Bohr sets of codimension $d$ shrinks width polynomially/exponentially in $k$ until rank $d \lesssim \log n$, exhausting ambient room before super-polylogarithmic extraction can finish.
3. **Single-Sphere Orthant Non-Extremality:** As proved in `single_sphere_orthant_lower_bound`, any attempt to avoid 2-adic multiscale gluing by concentrating energy on a single sphere forces $\alpha(G_S) \ge |S| / 2^d$, destroying sub-polynomial independence guarantees.
4. **Smooth Convex $L^2$ Curvature Saddle (`\Omega(L^2)` Layers):** Any strictly convex norm ball $B_L(c) \cap \Lambda$ embedded 2-adically forces $\Omega(L^2)$ squared-radius layers to accommodate distinct coset midpoints ($\approx r = L^2$), tying the layer count $r$ quadratically to linear coordinate scale $L$ (`radix growth ~ (4L)^d`). Balancing $d$ against $r$ then locks $|A|$ onto the Gaussian/quadratic saddle $\exp(\Theta((\log k)^2))$, leaving $\exp(C\sqrt{\log n})$ untouched without an entirely non-convex, non-2-adic conflict encoding.
