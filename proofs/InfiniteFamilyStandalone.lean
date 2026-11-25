/-!
# InfiniteFamilyStandalone.lean
### Pure Lean 4 Formal Proof of `n_max(k) ≥ k^2 + 3k - 11` for all `k ≥ 6`

Self-contained formalization using **Pure Lean 4** (`Init` / `Std` only, zero Mathlib, zero `sorry`).

Main Theorem (`infinite_family_n_max_ge`):
Define `famSeq 0 := A43` (`k = 6`) and recursively for `d ≥ 0` (`k = d + 6`):
  `famSeq (d + 1) := oddBlock (d + 7) ++ (famSeq d).map (2 * ·)`
where `oddBlock k` enumerates `{±(2j + 1) : 0 ≤ j ≤ k}` (all `2k + 2` odd integers in `[-(2k+1), 2k+1]`).
Then for every `k ≥ 6` (with `d = k - 6`):
1. `(famSeq d).Nodup`
2. `(famSeq d).length = k * k + 3 * k - 11`
3. Every integer `x` with `-(2 * k + 2 : Int) ≤ x ≤ (2 * k + 2 : Int)` belongs to `famSeq d`.
4. `HasExactMaxSumAvoiding (famSeq d) k`.
-/

set_option maxRecDepth 2000000

namespace Erdos787InfiniteFamily

def IsSumAvoiding (A B : List Int) : Prop :=
  ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → (b1 + b2) ∉ A

def isSumAvoidingBool (A B : List Int) : Bool :=
  B.all fun b1 => B.all fun b2 => if b1 != b2 then !(A.contains (b1 + b2)) else true

theorem isSumAvoidingBool_sound (A B : List Int) (h : isSumAvoidingBool A B = true) :
    IsSumAvoiding A B := by
  unfold isSumAvoidingBool at h
  intro b1 hb1 b2 hb2 hne hsum
  have h1 := (List.all_eq_true.1 h) b1 hb1
  have h2 := (List.all_eq_true.1 h1) b2 hb2
  have hne_b : (b1 != b2) = true := bne_iff_ne.mpr hne
  simp [hne_b] at h2
  exact h2 hsum

def isCliqueBool (A C : List Int) : Bool :=
  C.all fun u => C.all fun v => if u != v then A.contains (u + v) else true

theorem isCliqueBool_sound (A C : List Int) (h : isCliqueBool A C = true) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (u + v) ∈ A := by
  intro u hu v hv hne
  unfold isCliqueBool at h
  have h1 := (List.all_eq_true.1 h) u hu
  have h2 := (List.all_eq_true.1 h1) v hv
  have hne_b : (u != v) = true := bne_iff_ne.mpr hne
  simp [hne_b] at h2
  exact h2

def isCliqueCoverBool (A cand : List Int) (Cs : List (List Int)) : Bool :=
  Cs.all (isCliqueBool A) && cand.all (fun x => Cs.any (fun C => C.contains x))

theorem isCliqueCoverBool_sound (A cand : List Int) (Cs : List (List Int))
    (h : isCliqueCoverBool A cand Cs = true) :
    (∀ C ∈ Cs, isCliqueBool A C = true) ∧ (∀ x ∈ cand, ∃ C ∈ Cs, x ∈ C) := by
  unfold isCliqueCoverBool at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun x hx => ?_⟩
  rcases List.any_eq_true.1 (h.2 x hx) with ⟨C, hCm, hCh⟩
  exact ⟨C, hCm, List.contains_iff_mem.mp hCh⟩

theorem clique_cover_indep_le
    (A : List Int) (Cs : List (List Int)) (B : List Int)
    (hCliques : ∀ C ∈ Cs, isCliqueBool A C = true)
    (hCover : ∀ x ∈ B, ∃ C ∈ Cs, x ∈ C)
    (hNodup : B.Nodup) (hIndep : IsSumAvoiding A B) :
    B.length ≤ Cs.length := by
  induction Cs generalizing B with
  | nil =>
    cases B with
    | nil => exact Nat.le_refl 0
    | cons b _ => obtain ⟨C, hC, _⟩ := hCover b (by simp); cases hC
  | cons C Cs' ih =>
    have hC_cl := hCliques C (by simp)
    have hCs'_cl : ∀ C' ∈ Cs', isCliqueBool A C' = true := fun C' hC' => hCliques C' (by simp [hC'])
    by_cases hex : ∃ b ∈ B, b ∈ C
    · rcases hex with ⟨b, hbB, hbC⟩
      let B' := B.erase b
      have hB'_nd : B'.Nodup := hNodup.erase b
      have hB'_in : IsSumAvoiding A B' := fun x hx y hy hne =>
        hIndep x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy) hne
      have hB'_cov : ∀ x ∈ B', ∃ C' ∈ Cs', x ∈ C' := by
        intro x hx
        have hmem := (hNodup.mem_erase_iff).mp hx
        have hxNotC : x ∉ C := fun hxC =>
          hIndep x hmem.2 b hbB hmem.1 (isCliqueBool_sound A C hC_cl x hxC b hbC hmem.1)
        obtain ⟨C0, hC0m, hxC0⟩ := hCover x hmem.2
        rcases List.mem_cons.1 hC0m with rfl | hC0'
        · exact False.elim (hxNotC hxC0)
        · exact ⟨C0, hC0', hxC0⟩
      have hih := ih B' hCs'_cl hB'_cov hB'_nd hB'_in
      have hlen : B'.length = B.length - 1 := List.length_erase_of_mem hbB
      have hpos : 0 < B.length := List.length_pos_of_mem hbB
      rw [List.length_cons]; omega
    · have hB_cov : ∀ x ∈ B, ∃ C' ∈ Cs', x ∈ C' := by
        intro x hxB
        have hxNotC : x ∉ C := fun hxC => hex ⟨x, hxB, hxC⟩
        obtain ⟨C0, hC0m, hxC0⟩ := hCover x hxB
        rcases List.mem_cons.1 hC0m with rfl | hC0'
        · exact False.elim (hxNotC hxC0)
        · exact ⟨C0, hC0', hxC0⟩
      exact Nat.le_succ_of_le (ih B hCs'_cl hB_cov hNodup hIndep)

def HasExactMaxSumAvoiding (A : List Int) (k : Nat) : Prop :=
  (∃ B : List Int, B.Nodup ∧ (∀ x ∈ B, x ∈ A) ∧ IsSumAvoiding A B ∧ B.length = k) ∧
  (∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k)

/-! ### Base Witness `A43` (`k = 6`) -/

def A43 : List Int :=
  [-42, -26, -24, -22, -20, -18, -16, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0,
   1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 20, 22, 24, 26, 42]

def B6 : List Int := [13, 14, 22, 24, 26, 42]

def Cs43 : List (List Int) :=
  [ [-42, 0, 42],
    [-22, -20, -4, -2, 16, 26],
    [-24, -18, 2, 18, 24],
    [-26, -16, 4, 20, 22],
    [-13, -11, -9, -7, -5, -3, -1, 6, 8, 10, 12, 14],
    [-14, -12, -10, -8, -6, 1, 3, 5, 7, 9, 11, 13] ]

theorem A43_card : A43.length = 43 := rfl
theorem A43_nodup : A43.Nodup := by decide
theorem B6_len : B6.length = 6 := rfl
theorem B6_nodup : B6.Nodup := by decide
theorem B6_sub : ∀ x ∈ B6, x ∈ A43 := by decide
theorem B6_sumAvoiding : IsSumAvoiding A43 B6 := isSumAvoidingBool_sound A43 B6 (by decide)
theorem B6_ge13 : B6.all (fun z => decide (13 ≤ z)) = true := by decide
theorem Cs43_valid : isCliqueCoverBool A43 A43 Cs43 = true := by decide

theorem A43_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A43) → IsSumAvoiding A43 B → B.length ≤ 6 := by
  intro B hNd hSub hAvoid
  have h := isCliqueCoverBool_sound A43 A43 Cs43 Cs43_valid
  have hLe := clique_cover_indep_le A43 Cs43 B h.1 (fun x hx => h.2 x (hSub x hx)) hNd hAvoid
  have hLen : Cs43.length = 6 := rfl
  omega

theorem A43_band_dec :
    (List.range 29).all (fun i => A43.contains ((i : Int) - 14)) = true := by decide

theorem A43_band : ∀ x : Int, -14 ≤ x → x ≤ 14 → x ∈ A43 := by
  intro x hlo hhi
  have h := (List.all_eq_true.1 A43_band_dec) (x + 14).toNat (List.mem_range.2 (by omega))
  have hMem : (((x + 14).toNat : Int) - 14) ∈ A43 := List.contains_iff_mem.1 h
  have hCast : ((x + 14).toNat : Int) = x + 14 := Int.ofNat_toNat (x + 14) ▸ by omega
  have hEq : ((x + 14).toNat : Int) - 14 = x := by omega
  rwa [hEq] at hMem

/-! ### Recursive Doubling Family (`k ≥ 6`) -/

def oddPairs : Nat → List Int
  | 0 => [-1, 1]
  | r + 1 => [-((2 * (r + 1) + 1 : Nat) : Int), ((2 * (r + 1) + 1 : Nat) : Int)] ++ oddPairs r

def oddBlock (k : Nat) : List Int := oddPairs k

/-- `famSeq d` constructs the extremal witness at independence number `k = d + 6`. -/
def famSeq : Nat → List Int
  | 0 => A43
  | d + 1 => oddBlock (d + 7) ++ (famSeq d).map (2 * ·)

def famWitness : Nat → List Int
  | 0 => B6
  | d + 1 => (famWitness d).map (2 * ·) ++ [((2 * (d + 7) + 1 : Nat) : Int)]

private theorem oddPairs_length : ∀ r : Nat, (oddPairs r).length = 2 * r + 2
  | 0 => rfl
  | r + 1 => by simp [oddPairs, oddPairs_length r]; omega

private theorem oddPairs_mem_iff (x : Int) :
    ∀ r : Nat, x ∈ oddPairs r ↔
      (x % 2 = 1 ∨ x % 2 = -1) ∧ -((2 * r + 1 : Nat) : Int) ≤ x ∧ x ≤ ((2 * r + 1 : Nat) : Int)
  | 0 => by
    simp only [oddPairs, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl) <;> refine ⟨by omega, by omega, by omega⟩
    · intro ⟨hmod, hlo, hhi⟩
      omega
  | r + 1 => by
    simp only [oddPairs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, oddPairs_mem_iff x r]
    constructor
    · rintro ((rfl | rfl) | ⟨hmod, hlo, hhi⟩) <;> refine ⟨by omega, by omega, by omega⟩
    · intro ⟨hmod, hlo, hhi⟩
      by_cases hb1 : x = -((2 * (r + 1) + 1 : Nat) : Int)
      · exact Or.inl (Or.inl hb1)
      · by_cases hb2 : x = ((2 * (r + 1) + 1 : Nat) : Int)
        · exact Or.inl (Or.inr hb2)
        · refine Or.inr ⟨hmod, by omega, by omega⟩

private theorem oddPairs_nodup : ∀ r : Nat, (oddPairs r).Nodup
  | 0 => by decide
  | r + 1 => by
    unfold oddPairs
    rw [List.nodup_append]
    refine ⟨?_, oddPairs_nodup r, ?_⟩
    · refine List.nodup_cons.2 ⟨by simp; omega, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩⟩
    · intro a ha b hb heq
      subst heq
      rw [oddPairs_mem_iff a r] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega

theorem famSeq_nodup : ∀ d : Nat, (famSeq d).Nodup
  | 0 => A43_nodup
  | d + 1 => by
    unfold famSeq
    rw [List.nodup_append]
    refine ⟨oddPairs_nodup (d + 7), (famSeq_nodup d).map (2 * ·) (fun _ _ hne heq => hne (by omega)), ?_⟩
    intro a ha b hb heq
    subst heq
    rw [oddBlock, oddPairs_mem_iff a (d + 7)] at ha
    rw [List.mem_map] at hb
    rcases hb with ⟨z, _, hz⟩
    omega

theorem famSeq_length : ∀ d : Nat,
    (famSeq d).length = (d + 6) * (d + 6) + 3 * (d + 6) - 11
  | 0 => by simp [famSeq, A43_card]
  | d + 1 => by
    have ih := famSeq_length d
    unfold famSeq
    rw [List.length_append, List.length_map, oddBlock, oddPairs_length, ih]
    have hGe1 : 36 ≤ (d + 6) * (d + 6) :=
      Nat.mul_le_mul (by omega : 6 ≤ d + 6) (by omega : 6 ≤ d + 6)
    have hStep : (d + 1 + 6) * (d + 1 + 6) + 3 * (d + 1 + 6) =
        (d + 6) * (d + 6) + 3 * (d + 6) + (2 * (d + 7) + 2) := by
      have hMul : (d + 1 + 6) * (d + 1 + 6) = (d + 6) * (d + 6) + 2 * (d + 6) + 1 := by
        have : d + 1 + 6 = (d + 6) + 1 := by omega
        rw [this, Nat.add_mul, Nat.mul_add]
        omega
      omega
    omega

theorem famSeq_band : ∀ d : Nat,
    ∀ x : Int, -((2 * (d + 6) + 2 : Nat) : Int) ≤ x → x ≤ ((2 * (d + 6) + 2 : Nat) : Int) → x ∈ famSeq d
  | 0 => fun x hlo hhi => A43_band x (by omega) (by omega)
  | d + 1 => fun x hlo hhi => by
    unfold famSeq
    rw [List.mem_append]
    by_cases heven : x % 2 = 0
    · refine Or.inr (List.mem_map.2 ⟨x / 2, ?_, by omega⟩)
      exact famSeq_band d (x / 2) (by omega) (by omega)
    · refine Or.inl ?_
      rw [oddBlock, oddPairs_mem_iff x (d + 7)]
      refine ⟨by omega, ?_, ?_⟩
      · have : x ≠ -((2 * (d + 1 + 6) + 2 : Nat) : Int) := by intro h; subst h; omega
        omega
      · have : x ≠ ((2 * (d + 1 + 6) + 2 : Nat) : Int) := by intro h; subst h; omega
        omega

private theorem nodup_map_div2 :
    ∀ {L : List Int}, L.Nodup → (∀ z ∈ L, z % 2 = 0) → (L.map (· / 2)).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hNd, hEv => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hNd
    refine ⟨?_, nodup_map_div2 hNd.2 (fun z hz => hEv z (List.mem_cons_of_mem x hz))⟩
    intro hx
    rw [List.mem_map] at hx
    rcases hx with ⟨y, hy, hdiv⟩
    have h1 := hEv x (by simp)
    have h2 := hEv y (List.mem_cons_of_mem x hy)
    have hxy : y = x := by omega
    exact hNd.1 (hxy ▸ hy)

theorem famSeq_indep_le : ∀ d : Nat,
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ famSeq d) → IsSumAvoiding (famSeq d) B →
      B.length ≤ d + 6
  | 0 => fun B hNd hSub hAvoid => A43_upper_bound B hNd hSub hAvoid
  | d + 1 => fun B hNd hSub hAvoid => by
    let Beven := B.filter (fun z => decide (z % 2 = 0))
    let Bodd := B.filter (fun z => !(decide (z % 2 = 0)))
    have hPart : Beven.length + Bodd.length = B.length := by
      clear hNd hSub hAvoid
      induction B with
      | nil => simp [Beven, Bodd]
      | cons a as ih =>
        by_cases ha : a % 2 = 0
        · simp [Beven, Bodd, ha] at ih ⊢
          omega
        · simp [Beven, Bodd, ha] at ih ⊢
          omega
    have hOdd_clique : ∀ u ∈ Bodd, ∀ v ∈ Bodd, u ≠ v → (u + v) ∈ famSeq (d + 1) := by
      intro u hu v hv hne
      have huM := List.mem_filter.1 hu
      have hvM := List.mem_filter.1 hv
      have huIn := hSub u huM.1
      have hvIn := hSub v hvM.1
      unfold famSeq at huIn hvIn
      rw [List.mem_append, List.mem_map] at huIn hvIn
      have huNotEv : u % 2 ≠ 0 := by
        intro h
        have h' : (!(decide (u % 2 = 0))) = false := by simp [h]
        rw [h'] at huM
        cases huM.2
      have hvNotEv : v % 2 ≠ 0 := by
        intro h
        have h' : (!(decide (v % 2 = 0))) = false := by simp [h]
        rw [h'] at hvM
        cases hvM.2
      have huOdd : u ∈ oddBlock (d + 7) := by
        rcases huIn with h1 | ⟨z, _, rfl⟩
        · exact h1
        · omega
      have hvOdd : v ∈ oddBlock (d + 7) := by
        rcases hvIn with h1 | ⟨z, _, rfl⟩
        · exact h1
        · omega
      rw [oddBlock, oddPairs_mem_iff u (d + 7)] at huOdd
      rw [oddBlock, oddPairs_mem_iff v (d + 7)] at hvOdd
      have hHalfIn : (u + v) / 2 ∈ famSeq d := famSeq_band d ((u + v) / 2) (by omega) (by omega)
      have hTwo : 2 * ((u + v) / 2) = u + v := by omega
      unfold famSeq
      exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨(u + v) / 2, hHalfIn, hTwo⟩))
    have hOdd_le_1 : Bodd.length ≤ 1 := by
      have hNdOdd : Bodd.Nodup := (List.filter_sublist).nodup hNd
      match hB : Bodd with
      | [] => simp
      | [_] => simp
      | u :: v :: tail =>
        exfalso
        have huB : u ∈ Bodd := hB ▸ List.mem_cons_self
        have hvB : v ∈ Bodd := hB ▸ List.mem_cons_of_mem u List.mem_cons_self
        have hNdList : (u :: v :: tail).Nodup := hB ▸ hNdOdd
        rw [List.nodup_cons] at hNdList
        have hne : u ≠ v := fun h => hNdList.1 (h ▸ List.mem_cons_self)
        have hsum := hOdd_clique u (by simp) v (by simp) hne
        exact hAvoid u (List.mem_filter.1 huB).1 v (List.mem_filter.1 hvB).1 hne hsum
    let B' := Beven.map (· / 2)
    have hEvMod : ∀ w ∈ Beven, w % 2 = 0 := fun w hw => of_decide_eq_true (List.mem_filter.1 hw).2
    have hB'nd : B'.Nodup := nodup_map_div2 ((List.filter_sublist).nodup hNd) hEvMod
    have hB'sub : ∀ z ∈ B', z ∈ famSeq d := by
      intro z hz
      rw [List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      have hmod := hEvMod w hw
      have hwIn := hSub w (List.mem_filter.1 hw).1
      unfold famSeq at hwIn
      rw [List.mem_append, List.mem_map] at hwIn
      rcases hwIn with hwOdd | ⟨y, hy, hyEq⟩
      · rw [oddBlock, oddPairs_mem_iff w (d + 7)] at hwOdd
        omega
      · have hyz : y = w / 2 := by omega
        simpa [hyz] using hy
    have hB'avoid : IsSumAvoiding (famSeq d) B' := by
      intro z1 hz1 z2 hz2 hne hsum
      rw [List.mem_map] at hz1 hz2
      rcases hz1 with ⟨w1, hw1, rfl⟩
      rcases hz2 with ⟨w2, hw2, rfl⟩
      have h1 := hEvMod w1 hw1
      have h2 := hEvMod w2 hw2
      have hwne : w1 ≠ w2 := fun h => hne (by rw [h])
      have hTwo : w1 + w2 = 2 * (w1 / 2 + w2 / 2) := by omega
      have hSumIn : (w1 + w2) ∈ famSeq (d + 1) := by
        unfold famSeq
        exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨w1 / 2 + w2 / 2, hsum, hTwo.symm⟩))
      exact hAvoid w1 (List.mem_filter.1 hw1).1 w2 (List.mem_filter.1 hw2).1 hwne hSumIn
    have hB'le := famSeq_indep_le d B' hB'nd hB'sub hB'avoid
    have hEvLen : Beven.length ≤ d + 6 := by simpa [B', List.length_map] using hB'le
    omega

theorem famWitness_props : ∀ d : Nat,
    (famWitness d).Nodup ∧
    (famWitness d).length = d + 6 ∧
    (∀ b ∈ famWitness d, b ∈ famSeq d) ∧
    (∀ b ∈ famWitness d, ((2 * (d + 6) + 1 : Nat) : Int) ≤ b) ∧
    IsSumAvoiding (famSeq d) (famWitness d)
  | 0 => by
    refine ⟨B6_nodup, B6_len, B6_sub, ?_, B6_sumAvoiding⟩
    intro b hb
    exact of_decide_eq_true ((List.all_eq_true.1 B6_ge13) b hb)
  | d + 1 => by
    obtain ⟨hNd, hLen, hSub, hGe, hAvoid⟩ := famWitness_props d
    let wNew : Int := ((2 * (d + 7) + 1 : Nat) : Int)
    have hwNew_mem : wNew ∈ oddBlock (d + 7) := by
      rw [oddBlock, oddPairs_mem_iff wNew (d + 7)]
      refine ⟨Or.inl (by omega), by omega, by omega⟩
    have hMapGe : ∀ y ∈ (famWitness d).map (2 * ·), ((2 * (d + 7) + 1 : Nat) : Int) < y := by
      intro y hy
      rw [List.mem_map] at hy
      rcases hy with ⟨b, hb, rfl⟩
      have := hGe b hb
      omega
    have hNdNext : (famWitness (d + 1)).Nodup := by
      unfold famWitness
      rw [List.nodup_append]
      refine ⟨hNd.map (2 * ·) (fun _ _ hne heq => hne (by omega)),
              List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro x hx y hy heq
      rcases List.mem_cons.1 hy with rfl | hnil
      · have := hMapGe x hx; subst heq; omega
      · simp at hnil
    have hLenNext : (famWitness (d + 1)).length = d + 1 + 6 := by
      simp [famWitness, hLen]
    have hSubNext : ∀ b ∈ famWitness (d + 1), b ∈ famSeq (d + 1) := by
      intro b hb
      unfold famWitness at hb
      rw [List.mem_append, List.mem_singleton] at hb
      unfold famSeq
      rw [List.mem_append]
      rcases hb with hM | rfl
      · rw [List.mem_map] at hM
        rcases hM with ⟨a, ha, rfl⟩
        exact Or.inr (List.mem_map.2 ⟨a, hSub a ha, rfl⟩)
      · exact Or.inl hwNew_mem
    have hGeNext : ∀ b ∈ famWitness (d + 1), ((2 * (d + 1 + 6) + 1 : Nat) : Int) ≤ b := by
      intro b hb
      unfold famWitness at hb
      rw [List.mem_append, List.mem_singleton] at hb
      rcases hb with hM | rfl
      · have := hMapGe b hM; omega
      · omega
    have hOddNotInNext : ∀ z : Int, z % 2 = 1 → z > wNew → z ∉ famSeq (d + 1) := by
      intro z hmod hgt hmem
      unfold famSeq at hmem
      rw [List.mem_append, List.mem_map] at hmem
      rcases hmem with hOdd | ⟨y, _, hyEq⟩
      · rw [oddBlock, oddPairs_mem_iff z (d + 7)] at hOdd; omega
      · omega
    have hAvoidNext : IsSumAvoiding (famSeq (d + 1)) (famWitness (d + 1)) := by
      intro x hx y hy hne hsum
      unfold famWitness at hx hy
      rw [List.mem_append, List.mem_singleton] at hx hy
      rcases hx with hxM | rfl <;> rcases hy with hyM | rfl
      · rw [List.mem_map] at hxM hyM
        rcases hxM with ⟨a, ha, rfl⟩
        rcases hyM with ⟨b, hb, rfl⟩
        have habNe : a ≠ b := fun h => hne (by rw [h])
        unfold famSeq at hsum
        rw [List.mem_append, List.mem_map] at hsum
        rcases hsum with hOdd | ⟨z, hz, hzEq⟩
        · rw [oddBlock, oddPairs_mem_iff (2 * a + 2 * b) (d + 7)] at hOdd; omega
        · have hzSum : a + b = z := by omega
          exact hAvoid a ha b hb habNe (hzSum ▸ hz)
      · have hxGt := hMapGe x hxM
        rw [List.mem_map] at hxM
        rcases hxM with ⟨a, ha, rfl⟩
        have hGeA := hGe a ha
        exact hOddNotInNext (2 * a + wNew) (by omega) (by omega) hsum
      · have hyGt := hMapGe y hyM
        rw [List.mem_map] at hyM
        rcases hyM with ⟨b, hb, rfl⟩
        have hGeB := hGe b hb
        exact hOddNotInNext (wNew + 2 * b) (by omega) (by omega) hsum
      · exact absurd rfl hne
    exact ⟨hNdNext, hLenNext, hSubNext, hGeNext, hAvoidNext⟩

/-- Main Infinite Family Theorem:
    For EVERY `k ≥ 6`, there exists a duplicate-free integer list `A` of length `k^2 + 3k - 11`
    whose exact maximum sum-avoiding subset size is `k` (surpassing `k^2 + k + 1` by `2(k - 6)` for `k ≥ 7`). -/
theorem infinite_family_n_max_ge (k : Nat) (hk : k ≥ 6) :
    ∃ A : List Int, A.Nodup ∧ A.length = k * k + 3 * k - 11 ∧ HasExactMaxSumAvoiding A k := by
  let d := k - 6
  have hdk : d + 6 = k := by omega
  obtain ⟨hNdW, hLenW, hSubW, _, hAvoidW⟩ := famWitness_props d
  refine ⟨famSeq d, famSeq_nodup d, ?_, ?_, ?_⟩
  · rw [famSeq_length d, hdk]
  · exact ⟨famWitness d, hNdW, hSubW, hAvoidW, hdk ▸ hLenW⟩
  · intro B hNd hSub hAvoid
    have := famSeq_indep_le d B hNd hSub hAvoid
    omega

/-- Explicit Corollary at `k = 7`: `famSeq 1` (`A59`) has cardinality `59 > 57 = 7^2 + 7 + 1`
    and exact maximum sum-avoiding size `7`. -/
theorem k7_beats_projective_bound :
    (famSeq 1).Nodup ∧ (famSeq 1).length = 59 ∧ HasExactMaxSumAvoiding (famSeq 1) 7 := by
  obtain ⟨hNdW, hLenW, hSubW, _, hAvoidW⟩ := famWitness_props 1
  exact ⟨famSeq_nodup 1, famSeq_length 1,
    ⟨famWitness 1, hNdW, hSubW, hAvoidW, hLenW⟩,
    famSeq_indep_le 1⟩

end Erdos787InfiniteFamily
