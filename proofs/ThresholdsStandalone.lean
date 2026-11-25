/-!
# ThresholdsStandalone.lean
### Complete Pure Lean 4 Proofs of Finite Thresholds n_max(1) = 3, n_max(2) = 7, and n_max(3) = 13

Self-contained formalization using **Pure Lean 4** (`Init` / `Std` only, zero Mathlib, zero `sorry`).

Contents:
1. Foundational Definitions & Computational Reflection Soundness:
   - `isSumAvoidingBool_iff`
   - `hasSumAvoidingSubset_false` and `hasSumAvoidingSubset_true`
   - `exists_sublist_of_subset`
2. Sorting & Strict Order Infrastructure for `List Int`
3. Complete Proof of `n_max_1_upper` (any `Nodup` list of length ≥ 4 has a sum-avoiding pair)
4. Complete Proof of `n_max_2_upper` via `posPart`, `negPart`, `pos_sum_avoiding_lift`,
   `neg_sum_avoiding_lift`, and `pos_le_3_of_no_3` (length ≥ 8 forces a sum-avoiding triple)
5. Complete Proof of `n_max_3_upper` via `pos_le_6_of_no_4` (additive elimination:
   length ≥ 14 forces a sum-avoiding quadruple)
6. Exact Saturated Witnesses `A3`, `A7`, `A13_star` certified via `hasSumAvoidingSubset_false`,
   establishing complete upper and lower bounds for n_max(1) = 3, n_max(2) = 7, n_max(3) = 13.
-/

set_option maxRecDepth 2000000

namespace Erdos787Thresholds

/-! ==================================================================== -/
/-! ### Section 1: Definitions & Computational Reflection Soundness      -/
/-! ==================================================================== -/

/-- A list of integers `B` is sum-avoiding with respect to `A` if no two distinct
    elements of `B` sum to an element of `A`. -/
def IsSumAvoiding (A B : List Int) : Prop :=
  ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → (b1 + b2) ∉ A

/-- Computable boolean decision procedure for sum-avoidance. -/
def isSumAvoidingBool (A B : List Int) : Bool :=
  B.all fun b1 =>
    B.all fun b2 =>
      if b1 != b2 then !(A.contains (b1 + b2)) else true

/-- Helper generating all length-`k` order-preserving sublists of `l`. -/
def sublistsOfLen (k : Nat) (l : List Int) : List (List Int) :=
  match k, l with
  | 0, _ => [[]]
  | _, [] => []
  | k + 1, x :: xs =>
    (sublistsOfLen k xs).map (x :: ·) ++ sublistsOfLen (k + 1) xs

/-- Boolean decision procedure checking whether `A` has a sum-avoiding sublist of length `k`. -/
def hasSumAvoidingSubset (k : Nat) (A : List Int) : Bool :=
  (sublistsOfLen k A).any (isSumAvoidingBool A)

/-- Soundness and completeness of `isSumAvoidingBool` with respect to `IsSumAvoiding`. -/
theorem isSumAvoidingBool_iff (A B : List Int) :
    isSumAvoidingBool A B = true ↔ IsSumAvoiding A B := by
  unfold isSumAvoidingBool IsSumAvoiding
  rw [List.all_eq_true]
  constructor
  · intro h b1 hb1 b2 hb2 hne hsum
    have h1 := (List.all_eq_true.1 (h b1 hb1)) b2 hb2
    have hneB : (b1 != b2) = true := bne_iff_ne.2 hne
    rw [hneB] at h1
    simp only at h1
    have hc : A.contains (b1 + b2) = true := List.contains_iff_mem.2 hsum
    rw [hc] at h1
    cases h1
  · intro h b1 hb1
    rw [List.all_eq_true]
    intro b2 hb2
    by_cases hne : b1 = b2
    · subst hne
      simp
    · have hneB : (b1 != b2) = true := bne_iff_ne.2 hne
      rw [hneB]
      simp only [ite_true, Bool.not_eq_true']
      by_cases hc : A.contains (b1 + b2) = true
      · exact absurd (List.contains_iff_mem.1 hc) (h b1 hb1 b2 hb2 hne)
      · cases hb : A.contains (b1 + b2)
        · rfl
        · exact absurd hb hc

/-- `IsSumAvoiding` depends only on list membership. -/
theorem isSumAvoiding_congr_mem {A B1 B2 : List Int} (h : ∀ z, z ∈ B1 ↔ z ∈ B2) :
    IsSumAvoiding A B1 ↔ IsSumAvoiding A B2 := by
  constructor
  · intro h1 b1 hb1 b2 hb2 hne
    exact h1 b1 ((h b1).2 hb1) b2 ((h b2).2 hb2) hne
  · intro h2 b1 hb1 b2 hb2 hne
    exact h2 b1 ((h b1).1 hb1) b2 ((h b2).1 hb2) hne

/-- Every element produced by `sublistsOfLen k A` is a sublist of `A`. -/
theorem mem_sublistsOfLen_sublist :
    ∀ {k : Nat} {A B : List Int}, B ∈ sublistsOfLen k A → B.Sublist A
  | 0, A, B, h => by
    simp only [sublistsOfLen, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact List.nil_sublist A
  | _ + 1, [], B, h => by
    simp [sublistsOfLen] at h
  | k + 1, a :: as, B, h => by
    simp only [sublistsOfLen, List.mem_append, List.mem_map] at h
    rcases h with ⟨B', hB', rfl⟩ | hB
    · exact List.Sublist.cons_cons a (mem_sublistsOfLen_sublist hB')
    · exact List.Sublist.cons a (mem_sublistsOfLen_sublist hB)

/-- Every element produced by `sublistsOfLen k A` has length `k`. -/
theorem mem_sublistsOfLen_length :
    ∀ {k : Nat} {A B : List Int}, B ∈ sublistsOfLen k A → B.length = k
  | 0, _, B, h => by
    simp only [sublistsOfLen, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    rfl
  | _ + 1, [], B, h => by
    simp [sublistsOfLen] at h
  | k + 1, a :: as, B, h => by
    simp only [sublistsOfLen, List.mem_append, List.mem_map] at h
    rcases h with ⟨B', hB', rfl⟩ | hB
    · simp [mem_sublistsOfLen_length hB']
    · exact mem_sublistsOfLen_length hB

/-- If `A` has no duplicates, every element of `sublistsOfLen k A` has no duplicates. -/
theorem mem_sublistsOfLen_nodup {k : Nat} {A B : List Int}
    (hA : A.Nodup) (h : B ∈ sublistsOfLen k A) : B.Nodup :=
  (mem_sublistsOfLen_sublist h).nodup hA

/-- Any duplicate-free list `B` whose elements belong to `A` has an order-preserving
    representative `B' ∈ sublistsOfLen B.length A` with the exact same elements. -/
theorem exists_sublistOfLen_equiv :
    ∀ (A B : List Int), B.Nodup → (∀ x ∈ B, x ∈ A) →
      ∃ B' ∈ sublistsOfLen B.length A, B'.Nodup ∧ (∀ z, z ∈ B' ↔ z ∈ B)
  | [], B, _, hSub => by
    cases B with
    | nil =>
      refine ⟨[], ?_, List.nodup_nil, fun _ => Iff.rfl⟩
      simp [sublistsOfLen]
    | cons x xs =>
      have hx : x ∈ ([] : List Int) := hSub x (by simp)
      simp at hx
  | a :: as, [], _, _ => by
    refine ⟨[], ?_, List.nodup_nil, fun _ => Iff.rfl⟩
    simp [sublistsOfLen]
  | a :: as, b :: bs, hNodup, hSub => by
    by_cases ha : a ∈ b :: bs
    · let B1 := (b :: bs).erase a
      have hB1_nodup : B1.Nodup := List.Nodup.erase a hNodup
      have hB1_not_mem : a ∉ B1 := List.Nodup.not_mem_erase hNodup
      have hB1_len : B1.length = bs.length := by
        dsimp [B1]
        rw [List.length_erase_of_mem ha]
        simp
      have hB1_sub : ∀ x ∈ B1, x ∈ as := by
        intro x hx
        have hxB : x ∈ b :: bs := List.mem_of_mem_erase hx
        have hxne : x ≠ a := fun h => hB1_not_mem (h ▸ hx)
        rcases List.mem_cons.1 (hSub x hxB) with rfl | hmem
        · exact absurd rfl hxne
        · exact hmem
      obtain ⟨B'', hB''_mem, hB''_nodup, hB''_iff⟩ :=
        exists_sublistOfLen_equiv as B1 hB1_nodup hB1_sub
      rw [hB1_len] at hB''_mem
      refine ⟨a :: B'', ?_, ?_, ?_⟩
      · simp only [List.length_cons, sublistsOfLen, List.mem_append, List.mem_map]
        exact Or.inl ⟨B'', hB''_mem, rfl⟩
      · rw [List.nodup_cons]
        exact ⟨fun h => hB1_not_mem ((hB''_iff a).1 h), hB''_nodup⟩
      · intro z
        by_cases hz : z = a
        · subst hz
          simp [ha]
        · rw [List.mem_cons, or_iff_right hz, hB''_iff]
          exact List.mem_erase_of_ne hz
    · have hSub_as : ∀ x ∈ b :: bs, x ∈ as := by
        intro x hx
        rcases List.mem_cons.1 (hSub x hx) with rfl | hmem
        · exact absurd hx ha
        · exact hmem
      obtain ⟨B', hB'_mem, hB'_nodup, hB'_iff⟩ :=
        exists_sublistOfLen_equiv as (b :: bs) hNodup hSub_as
      refine ⟨B', ?_, hB'_nodup, hB'_iff⟩
      simp only [List.length_cons, sublistsOfLen, List.mem_append]
      exact Or.inr hB'_mem

/-- Any `Nodup` list `B` of elements in `A` can be reordered into a true `List.Sublist` of `A`. -/
theorem exists_sublist_of_subset (A B : List Int)
    (hNodup : B.Nodup) (hSub : ∀ x ∈ B, x ∈ A) :
    ∃ B' : List Int, B'.Sublist A ∧ B'.Nodup ∧ B'.length = B.length ∧ (∀ z, z ∈ B' ↔ z ∈ B) := by
  obtain ⟨B', hMem, hB'Nodup, hIff⟩ := exists_sublistOfLen_equiv A B hNodup hSub
  exact ⟨B', mem_sublistsOfLen_sublist hMem, hB'Nodup, mem_sublistsOfLen_length hMem, hIff⟩

/-- Soundness of negative certification:
    If `hasSumAvoidingSubset k A = false`, then NO duplicate-free list `B` of length `k`
    whose elements belong to `A` can be sum-avoiding in `A`. -/
theorem hasSumAvoidingSubset_false (k : Nat) (A : List Int)
    (h : hasSumAvoidingSubset k A = false) :
    ∀ B : List Int, (∀ x ∈ B, x ∈ A) → B.Nodup → B.length = k → ¬ IsSumAvoiding A B := by
  intro B hSub hNodup hLen hAvoid
  unfold hasSumAvoidingSubset at h
  rw [List.any_eq_false] at h
  obtain ⟨B', hB'_mem, _, hIff⟩ := exists_sublistOfLen_equiv A B hNodup hSub
  rw [hLen] at hB'_mem
  have hAvoid' : IsSumAvoiding A B' := (isSumAvoiding_congr_mem hIff).2 hAvoid
  have hBool : isSumAvoidingBool A B' = true := (isSumAvoidingBool_iff A B').2 hAvoid'
  exact h B' hB'_mem hBool

/-- Soundness of positive certification:
    If `A.Nodup` and `hasSumAvoidingSubset k A = true`, then `A` contains a `Nodup`
    sum-avoiding sublist `B` of length `k`. -/
theorem hasSumAvoidingSubset_true (k : Nat) (A : List Int)
    (hNodup : A.Nodup) (h : hasSumAvoidingSubset k A = true) :
    ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = k ∧ IsSumAvoiding A B := by
  unfold hasSumAvoidingSubset at h
  rw [List.any_eq_true] at h
  obtain ⟨B, hMem, hBool⟩ := h
  exact ⟨B, mem_sublistsOfLen_sublist hMem, mem_sublistsOfLen_nodup hNodup hMem,
    mem_sublistsOfLen_length hMem, (isSumAvoidingBool_iff A B).1 hBool⟩


/-! ==================================================================== -/
/-! ### Section 2: Sorting & Strict Order Infrastructure                 -/
/-! ==================================================================== -/

/-- A list of integers is strictly sorted ascending if every earlier element is `<` every later element. -/
def IsStrictlySorted (L : List Int) : Prop :=
  List.Pairwise (· < ·) L

/-- A list of integers is strictly sorted descending if every earlier element is `>` every later element. -/
def IsStrictlyDesc (L : List Int) : Prop :=
  List.Pairwise (· > ·) L

/-- Ascending merge sort on `List Int`. -/
def sortAsc (A : List Int) : List Int :=
  A.mergeSort (fun a b => decide (a ≤ b))

theorem sortAsc_mem (A : List Int) (x : Int) : x ∈ sortAsc A ↔ x ∈ A :=
  List.mem_mergeSort

theorem sortAsc_length (A : List Int) : (sortAsc A).length = A.length :=
  List.length_mergeSort A

theorem sortAsc_nodup (A : List Int) (hNodup : A.Nodup) : (sortAsc A).Nodup :=
  (List.mergeSort_perm A _).nodup_iff.2 hNodup

private theorem sortAsc_pairwise_le (A : List Int) :
    List.Pairwise (· ≤ ·) (sortAsc A) := by
  have h := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (fun a b => by
      by_cases h : a ≤ b
      · simp [h]
      · have hba : b ≤ a := by omega
        simp [h, hba])
    A
  exact h.imp (fun {a b} hab => by simpa using hab)

private theorem pairwise_lt_of_pairwise_le_nodup :
    ∀ {L : List Int}, List.Pairwise (· ≤ ·) L → L.Nodup → IsStrictlySorted L
  | [], _, _ => List.Pairwise.nil
  | x :: xs, hLe, hNd => by
    rw [List.pairwise_cons] at hLe
    rw [List.nodup_cons] at hNd
    rw [IsStrictlySorted, List.pairwise_cons]
    refine ⟨?_, pairwise_lt_of_pairwise_le_nodup hLe.2 hNd.2⟩
    intro y hy
    have hxy : x ≤ y := hLe.1 y hy
    have hne : x ≠ y := fun heq => hNd.1 (heq ▸ hy)
    omega

theorem sortAsc_strictlySorted (A : List Int) (hNodup : A.Nodup) :
    IsStrictlySorted (sortAsc A) :=
  pairwise_lt_of_pairwise_le_nodup (sortAsc_pairwise_le A) (sortAsc_nodup A hNodup)

theorem isStrictlySorted_nodup {L : List Int} (h : IsStrictlySorted L) : L.Nodup :=
  h.imp (fun {a b} hab => by omega)

theorem isStrictlyDesc_reverse {L : List Int} (h : IsStrictlySorted L) :
    IsStrictlyDesc L.reverse := by
  rw [IsStrictlyDesc, List.pairwise_reverse]
  exact h

/-- Top-bound helpers for strictly descending lists. -/
private theorem desc_le_head {x1 : Int} {t : List Int}
    (h : IsStrictlyDesc (x1 :: t)) :
    ∀ z ∈ (x1 :: t), z ≤ x1 := by
  rw [IsStrictlyDesc, List.pairwise_cons] at h
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hzt
  · omega
  · have := h.1 z hzt; omega

private theorem desc_gt_second {x1 x2 : Int} {t : List Int}
    (h : IsStrictlyDesc (x1 :: x2 :: t)) :
    ∀ z ∈ (x1 :: x2 :: t), z > x2 → z = x1 := by
  rw [IsStrictlyDesc, List.pairwise_cons] at h
  have h2 := h.2
  rw [List.pairwise_cons] at h2
  intro z hz hgt
  rcases List.mem_cons.1 hz with rfl | hz2
  · rfl
  · rcases List.mem_cons.1 hz2 with rfl | hzt
    · omega
    · have := h2.1 z hzt; omega

private theorem desc_gt_third {x1 x2 x3 : Int} {t : List Int}
    (h : IsStrictlyDesc (x1 :: x2 :: x3 :: t)) :
    ∀ z ∈ (x1 :: x2 :: x3 :: t), z > x3 → z = x1 ∨ z = x2 := by
  rw [IsStrictlyDesc, List.pairwise_cons] at h
  have h2 := h.2
  rw [List.pairwise_cons] at h2
  have h3 := h2.2
  rw [List.pairwise_cons] at h3
  intro z hz hgt
  rcases List.mem_cons.1 hz with rfl | hz2
  · exact Or.inl rfl
  · rcases List.mem_cons.1 hz2 with rfl | hz3
    · exact Or.inr rfl
    · rcases List.mem_cons.1 hz3 with rfl | hzt
      · omega
      · have := h3.1 z hzt; omega

private theorem desc_gt_fourth {x1 x2 x3 x4 : Int} {t : List Int}
    (h : IsStrictlyDesc (x1 :: x2 :: x3 :: x4 :: t)) :
    ∀ z ∈ (x1 :: x2 :: x3 :: x4 :: t), z > x4 → z = x1 ∨ z = x2 ∨ z = x3 := by
  rw [IsStrictlyDesc, List.pairwise_cons] at h
  have h2 := h.2
  rw [List.pairwise_cons] at h2
  have h3 := h2.2
  rw [List.pairwise_cons] at h3
  have h4 := h3.2
  rw [List.pairwise_cons] at h4
  intro z hz hgt
  rcases List.mem_cons.1 hz with rfl | hz2
  · exact Or.inl rfl
  · rcases List.mem_cons.1 hz2 with rfl | hz3
    · exact Or.inr (Or.inl rfl)
    · rcases List.mem_cons.1 hz3 with rfl | hz4
      · exact Or.inr (Or.inr rfl)
      · rcases List.mem_cons.1 hz4 with rfl | hzt
        · omega
        · have := h4.1 z hzt; omega


/-! ==================================================================== -/
/-! ### Section 3: Complete Proof of n_max_1_upper (n_max(1) ≤ 3)        -/
/-! ==================================================================== -/

/-- No 4 strictly ordered integers `a < b < c < d` can have both `a + b` and `c + d`
    inside `{a, b, c, d}`. -/
theorem no_four_has_both_pairs_sum_in (a b c d : Int)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h_ab : a + b ∈ [a, b, c, d])
    (h_cd : c + d ∈ [a, b, c, d]) :
    False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_ab h_cd
  by_cases hd : d ≤ 0
  · rcases h_ab with h1 | h2 | h3 | h4 <;> omega
  · by_cases ha : a ≥ 0
    · rcases h_cd with k1 | k2 | k3 | k4 <;> omega
    · have hc : c = 0 := by
        rcases h_cd with k1 | k2 | k3 | k4 <;> omega
      have hb : b = 0 := by
        rcases h_ab with h1 | h2 | h3 | h4 <;> omega
      omega

/-- Extract the two largest elements `(c, d)` from any strictly ascending list of length ≥ 2. -/
private theorem strictlySorted_two_largest :
    ∀ {R : List Int}, IsStrictlySorted R → R.length ≥ 2 →
      ∃ c d, c ∈ R ∧ d ∈ R ∧ c < d ∧ (∀ z ∈ R, z ≤ d) ∧ (∀ z ∈ R, c < z → d ≤ z)
  | [], _, hLen => by simp at hLen
  | [_], _, hLen => by simp at hLen
  | [c, d], hSort, _ => by
    rw [IsStrictlySorted, List.pairwise_cons] at hSort
    have hcd : c < d := hSort.1 d (by simp)
    refine ⟨c, d, by simp, by simp, hcd, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> omega
    · intro z hz hcz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> omega
  | x :: y :: z :: zs, hSort, _ => by
    rw [IsStrictlySorted, List.pairwise_cons] at hSort
    have hSort' : IsStrictlySorted (y :: z :: zs) := hSort.2
    obtain ⟨c, d, hc, hd, hcd, hmax, hpen⟩ :=
      strictlySorted_two_largest hSort' (by simp)
    have hxc : x < c := hSort.1 c hc
    refine ⟨c, d, List.mem_cons_of_mem x hc, List.mem_cons_of_mem x hd, hcd, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw'
      · omega
      · exact hmax w hw'
    · intro w hw hcw
      rcases List.mem_cons.1 hw with rfl | hw'
      · omega
      · exact hpen w hw' hcw

/-- Sorted helper for `n_max_1_upper`. -/
private theorem n_max_1_upper_sorted :
    ∀ (L : List Int), IsStrictlySorted L → L.length ≥ 4 →
      ∃ u ∈ L, ∃ v ∈ L, u ≠ v ∧ (u + v) ∉ L
  | [], _, hLen => by simp at hLen
  | [_], _, hLen => by simp at hLen
  | [_, _], _, hLen => by simp at hLen
  | [_, _, _], _, hLen => by simp at hLen
  | a :: b :: x :: y :: rest, hSort, _ => by
    have hSort' := hSort
    rw [IsStrictlySorted, List.pairwise_cons] at hSort'
    have hab : a < b := hSort'.1 b (by simp)
    have hSort_b : IsStrictlySorted (b :: x :: y :: rest) := hSort'.2
    rw [IsStrictlySorted, List.pairwise_cons] at hSort_b
    obtain ⟨c, d, hc, hd, hcd, hmaxR, hpenR⟩ :=
      strictlySorted_two_largest hSort_b.2 (by simp)
    have hbc : b < c := hSort_b.1 c hc
    have haL : a ∈ a :: b :: x :: y :: rest := by simp
    have hbL : b ∈ a :: b :: x :: y :: rest := by simp
    have hcL : c ∈ a :: b :: x :: y :: rest :=
      List.mem_cons_of_mem a (List.mem_cons_of_mem b hc)
    have hdL : d ∈ a :: b :: x :: y :: rest :=
      List.mem_cons_of_mem a (List.mem_cons_of_mem b hd)
    have hMin : ∀ z ∈ a :: b :: x :: y :: rest, a ≤ z := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz'
      · omega
      · exact Int.le_of_lt (hSort'.1 z hz')
    have hSecMin : ∀ z ∈ a :: b :: x :: y :: rest, z < b → z ≤ a := by
      intro z hz hzb
      rcases List.mem_cons.1 hz with rfl | hz'
      · omega
      · rcases List.mem_cons.1 hz' with rfl | hz''
        · omega
        · exact absurd (hSort_b.1 z hz'') (by omega)
    have hMax : ∀ z ∈ a :: b :: x :: y :: rest, z ≤ d := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz'
      · omega
      · rcases List.mem_cons.1 hz' with rfl | hz''
        · omega
        · exact hmaxR z hz''
    have hSecMax : ∀ z ∈ a :: b :: x :: y :: rest, c < z → d ≤ z := by
      intro z hz hcz
      rcases List.mem_cons.1 hz with rfl | hz'
      · omega
      · rcases List.mem_cons.1 hz' with rfl | hz''
        · omega
        · exact hpenR z hz'' hcz
    by_cases h_ab : (a + b) ∈ a :: b :: x :: y :: rest
    · by_cases h_cd : (c + d) ∈ a :: b :: x :: y :: rest
      · exfalso
        by_cases hd0 : d ≤ 0
        · have := hMin (a + b) h_ab; omega
        · by_cases ha0 : a ≥ 0
          · have := hMax (c + d) h_cd; omega
          · have h1 : a + b = a := by
              have := hMin (a + b) h_ab
              have := hSecMin (a + b) h_ab (by omega)
              omega
            have h2 : c + d = d := by
              have := hMax (c + d) h_cd
              have := hSecMax (c + d) h_cd (by omega)
              omega
            exact no_four_has_both_pairs_sum_in a b c d hab hbc hcd
              (by rw [h1]; simp) (by rw [h2]; simp)
      · exact ⟨c, hcL, d, hdL, by omega, h_cd⟩
    · exact ⟨a, haL, b, hbL, by omega, h_ab⟩

/-- **Theorem `n_max_1_upper`**:
    Any duplicate-free integer list `A` of length ≥ 4 contains a pair of distinct
    elements whose sum is outside `A`. -/
theorem n_max_1_upper (A : List Int) (hNodup : A.Nodup) (hLen : A.length ≥ 4) :
    ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ (u + v) ∉ A := by
  let L := sortAsc A
  have hL_sort : IsStrictlySorted L := sortAsc_strictlySorted A hNodup
  have hL_len : L.length ≥ 4 := by simpa [L, sortAsc_length] using hLen
  have hL_mem : ∀ x, x ∈ L ↔ x ∈ A := sortAsc_mem A
  obtain ⟨u, hu, v, hv, hne, hsum⟩ := n_max_1_upper_sorted L hL_sort hL_len
  exact ⟨u, (hL_mem u).1 hu, v, (hL_mem v).1 hv, hne, fun h => hsum ((hL_mem (u + v)).2 h)⟩

/-- Sublist corollary of `n_max_1_upper`: any `Nodup` list `A` of length ≥ 4 contains
    a `Nodup` sum-avoiding sublist of length 2. -/
theorem n_max_1_upper_sublist (A : List Int) (hNodup : A.Nodup) (hLen : A.length ≥ 4) :
    ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 2 ∧ IsSumAvoiding A B := by
  obtain ⟨u, hu, v, hv, hne, hsum⟩ := n_max_1_upper A hNodup hLen
  have hB_nodup : ([u, v] : List Int).Nodup := by
    rw [List.nodup_cons]
    exact ⟨by simp [hne], List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩⟩
  have hB_sub : ∀ x ∈ ([u, v] : List Int), x ∈ A := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  have hB_avoid : IsSumAvoiding A [u, v] := by
    intro b1 hb1 b2 hb2 hbne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb1 hb2
    rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
    · exact absurd rfl hbne
    · exact hsum
    · rw [Int.add_comm]; exact hsum
    · exact absurd rfl hbne
  obtain ⟨B', hSub', hNodup', hLen', hIff⟩ := exists_sublist_of_subset A [u, v] hB_nodup hB_sub
  exact ⟨B', hSub', hNodup', by simpa using hLen', (isSumAvoiding_congr_mem hIff).2 hB_avoid⟩


/-! ==================================================================== -/
/-! ### Section 4: Positive / Negative Splitting & n_max_2_upper         -/
/-! ==================================================================== -/

/-- Strictly positive elements of `A`. -/
def posPart (A : List Int) : List Int :=
  A.filter (· > 0)

/-- Negated strictly negative elements of `A` (all strictly positive). -/
def negPart (A : List Int) : List Int :=
  (A.filter (· < 0)).map (- ·)

theorem posPart_mem_iff (A : List Int) (x : Int) :
    x ∈ posPart A ↔ x ∈ A ∧ x > 0 := by
  simp [posPart]

theorem negPart_mem_iff (A : List Int) (x : Int) :
    x ∈ negPart A ↔ (-x) ∈ A ∧ x > 0 := by
  simp only [negPart, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
    refine ⟨?_, by omega⟩
    simpa using ha
  · rintro ⟨hx, hpos⟩
    exact ⟨-x, ⟨hx, by omega⟩, by omega⟩

theorem posPart_nodup (A : List Int) (hNodup : A.Nodup) : (posPart A).Nodup :=
  (List.filter_sublist).nodup hNodup

theorem negPart_nodup (A : List Int) (hNodup : A.Nodup) : (negPart A).Nodup := by
  have hFilt : (A.filter (· < 0)).Nodup := (List.filter_sublist).nodup hNodup
  exact hFilt.map (- ·) (fun _ _ hne hneg => hne (by omega))

theorem length_pos_neg_zero (A : List Int) :
    (posPart A).length + (negPart A).length + (A.filter (· == 0)).length = A.length := by
  unfold posPart negPart
  rw [List.length_map]
  induction A with
  | nil => simp
  | cons a as ih =>
    by_cases hp : a > 0
    · have hn : ¬ (a < 0) := by omega
      have hz : a ≠ 0 := by omega
      simp [hp, hn, hz] at ⊢ ih
      omega
    · by_cases hn : a < 0
      · have hz : a ≠ 0 := by omega
        simp [hp, hn, hz] at ⊢ ih
        omega
      · have ha0 : a = 0 := by omega
        subst ha0
        simp at ⊢ ih
        omega

theorem zero_filter_length_le_one (A : List Int) (hNodup : A.Nodup) :
    (A.filter (· == 0)).length ≤ 1 := by
  have hZ_nodup : (A.filter (· == 0)).Nodup := (List.filter_sublist).nodup hNodup
  match hZ : A.filter (· == 0) with
  | [] => simp
  | [_] => simp
  | z1 :: z2 :: zs =>
    exfalso
    have h1 : z1 ∈ A.filter (· == 0) := hZ ▸ by simp
    have h2 : z2 ∈ A.filter (· == 0) := hZ ▸ by simp
    simp only [List.mem_filter, beq_iff_eq] at h1 h2
    rw [hZ, List.nodup_cons] at hZ_nodup
    have hne : z1 ≠ z2 := fun h => hZ_nodup.1 (h ▸ by simp)
    omega

/-- Lifting sum-avoidance from `posPart A` to `A`. -/
theorem pos_sum_avoiding_lift (A B : List Int)
    (hSub : ∀ x ∈ B, x ∈ posPart A)
    (hAvoid : IsSumAvoiding (posPart A) B) :
    IsSumAvoiding A B := by
  intro b1 hb1 b2 hb2 hne hsum
  have h1pos : b1 > 0 := ((posPart_mem_iff A b1).1 (hSub b1 hb1)).2
  have h2pos : b2 > 0 := ((posPart_mem_iff A b2).1 (hSub b2 hb2)).2
  have hsum_pos : b1 + b2 ∈ posPart A := (posPart_mem_iff A (b1 + b2)).2 ⟨hsum, by omega⟩
  exact hAvoid b1 hb1 b2 hb2 hne hsum_pos

/-- Lifting sum-avoidance from `negPart A` to `A` via reflection `x ↦ -x`. -/
theorem neg_sum_avoiding_lift (A B : List Int)
    (hSub : ∀ x ∈ B, x ∈ negPart A)
    (hAvoid : IsSumAvoiding (negPart A) B) :
    IsSumAvoiding A (B.map (- ·)) := by
  intro y1 hy1 y2 hy2 hne hsum
  rw [List.mem_map] at hy1 hy2
  rcases hy1 with ⟨b1, hb1, rfl⟩
  rcases hy2 with ⟨b2, hb2, rfl⟩
  have hbne : b1 ≠ b2 := fun h => hne (by rw [h])
  have h1pos : b1 > 0 := ((negPart_mem_iff A b1).1 (hSub b1 hb1)).2
  have h2pos : b2 > 0 := ((negPart_mem_iff A b2).1 (hSub b2 hb2)).2
  have hsum_neg : -(b1 + b2) ∈ A := by
    have heq : -(b1 + b2) = -b1 + -b2 := by omega
    rw [heq]
    exact hsum
  have hsum_in_neg : b1 + b2 ∈ negPart A := (negPart_mem_iff A (b1 + b2)).2 ⟨hsum_neg, by omega⟩
  exact hAvoid b1 hb1 b2 hb2 hbne hsum_in_neg

/-- Helper: if `[a, b, c]` fails `IsSumAvoiding P`, at least one pair sums into `P`. -/
private theorem not_isSumAvoiding_triple {P : List Int} {a b c : Int}
    (h : ¬ IsSumAvoiding P [a, b, c]) :
    (a + b) ∈ P ∨ (a + c) ∈ P ∨ (b + c) ∈ P := by
  by_cases hab : (a + b) ∈ P
  · exact Or.inl hab
  · by_cases hac : (a + c) ∈ P
    · exact Or.inr (Or.inl hac)
    · by_cases hbc : (b + c) ∈ P
      · exact Or.inr (Or.inr hbc)
      · exfalso
        apply h
        intro u hu v hv hne
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact hab
        · exact hac
        · rw [Int.add_comm]; exact hab
        · exact absurd rfl hne
        · exact hbc
        · rw [Int.add_comm]; exact hac
        · rw [Int.add_comm]; exact hbc
        · exact absurd rfl hne

/-- Descending helper for `pos_le_3_of_no_3`. -/
private theorem pos_desc_no_all_3_avoid :
    ∀ (D : List Int), IsStrictlyDesc D → (∀ x ∈ D, x > 0) → D.length ≥ 4 →
      (∀ B : List Int, (∀ x ∈ B, x ∈ D) → B.Nodup → B.length = 3 → ¬ IsSumAvoiding D B) →
      False
  | [], _, _, hLen, _ => by simp at hLen
  | [_], _, _, hLen, _ => by simp at hLen
  | [_, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _], _, _, hLen, _ => by simp at hLen
  | y4 :: y3 :: y2 :: y1 :: tail, hDesc, hPos, _, hNo3 => by
    have hy4_mem : y4 ∈ y4 :: y3 :: y2 :: y1 :: tail := by simp
    have hy3_mem : y3 ∈ y4 :: y3 :: y2 :: y1 :: tail := by simp
    have hy2_mem : y2 ∈ y4 :: y3 :: y2 :: y1 :: tail := by simp
    have hy1_mem : y1 ∈ y4 :: y3 :: y2 :: y1 :: tail := by simp
    have hy1_pos : y1 > 0 := hPos y1 hy1_mem
    have hy2_pos : y2 > 0 := hPos y2 hy2_mem
    have hy3_pos : y3 > 0 := hPos y3 hy3_mem
    have hy4_pos : y4 > 0 := hPos y4 hy4_mem
    have hOrd : y4 > y3 ∧ y3 > y2 ∧ y2 > y1 := by
      have h1 := hDesc; rw [IsStrictlyDesc, List.pairwise_cons] at h1
      have h2 := h1.2; rw [List.pairwise_cons] at h2
      have h3 := h2.2; rw [List.pairwise_cons] at h3
      exact ⟨h1.1 y3 (by simp), h2.1 y2 (by simp), h3.1 y1 (by simp)⟩
    have hMax : ∀ z ∈ y4 :: y3 :: y2 :: y1 :: tail, z ≤ y4 := desc_le_head hDesc
    have hTop : ∀ z ∈ y4 :: y3 :: y2 :: y1 :: tail, z > y3 → z = y4 := desc_gt_second hDesc
    have h234_nodup : ([y2, y3, y4] : List Int).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_nil⟩⟩⟩ <;>
        simp <;> omega
    have h134_nodup : ([y1, y3, y4] : List Int).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_nil⟩⟩⟩ <;>
        simp <;> omega
    have h234_sub : ∀ x ∈ ([y2, y3, y4] : List Int), x ∈ y4 :: y3 :: y2 :: y1 :: tail := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h134_sub : ∀ x ∈ ([y1, y3, y4] : List Int), x ∈ y4 :: y3 :: y2 :: y1 :: tail := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hNot234 := hNo3 [y2, y3, y4] h234_sub h234_nodup rfl
    have hNot134 := hNo3 [y1, y3, y4] h134_sub h134_nodup rfl
    have hy23 : y2 + y3 ∈ y4 :: y3 :: y2 :: y1 :: tail := by
      rcases not_isSumAvoiding_triple hNot234 with h23 | h24 | h34
      · exact h23
      · exfalso; have := hMax (y2 + y4) h24; omega
      · exfalso; have := hMax (y3 + y4) h34; omega
    have hy13 : y1 + y3 ∈ y4 :: y3 :: y2 :: y1 :: tail := by
      rcases not_isSumAvoiding_triple hNot134 with h13 | h14 | h34
      · exact h13
      · exfalso; have := hMax (y1 + y4) h14; omega
      · exfalso; have := hMax (y3 + y4) h34; omega
    have eq1 : y2 + y3 = y4 := hTop (y2 + y3) hy23 (by omega)
    have eq2 : y1 + y3 = y4 := hTop (y1 + y3) hy13 (by omega)
    omega

/-- **Lemma `pos_le_3_of_no_3`**:
    Any strictly sorted positive list `P` of length ≥ 4 contains a `Nodup`
    sum-avoiding sublist `B` of length 3. -/
theorem pos_le_3_of_no_3 (P : List Int)
    (hSort : IsStrictlySorted P) (hPos : ∀ x ∈ P, x > 0) (hLen : P.length ≥ 4) :
    ∃ B : List Int, B.Sublist P ∧ B.Nodup ∧ B.length = 3 ∧ IsSumAvoiding P B := by
  have hNodup : P.Nodup := isStrictlySorted_nodup hSort
  cases hHas : hasSumAvoidingSubset 3 P
  · exfalso
    have hNo3 := hasSumAvoidingSubset_false 3 P hHas
    have hNo3D : ∀ B : List Int, (∀ x ∈ B, x ∈ P.reverse) → B.Nodup → B.length = 3 → ¬ IsSumAvoiding P.reverse B := by
      intro B hSub hNd hL hAv
      apply hNo3 B (fun x hx => List.mem_reverse.1 (hSub x hx)) hNd hL
      intro b1 hb1 b2 hb2 hne hsum
      exact hAv b1 hb1 b2 hb2 hne (List.mem_reverse.2 hsum)
    exact pos_desc_no_all_3_avoid P.reverse (isStrictlyDesc_reverse hSort)
      (fun x hx => hPos x (List.mem_reverse.1 hx)) (by simpa using hLen) hNo3D
  · exact hasSumAvoidingSubset_true 3 P hNodup hHas

/-- **Theorem `n_max_2_upper`** (`n_max(2) ≤ 7`):
    Any duplicate-free integer list `A` of length ≥ 8 contains a `Nodup` sum-avoiding
    sublist `B` of length 3. -/
theorem n_max_2_upper (A : List Int) (hNodup : A.Nodup) (hLen : A.length ≥ 8) :
    ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 3 ∧ IsSumAvoiding A B := by
  have hPart := length_pos_neg_zero A
  have hZero := zero_filter_length_le_one A hNodup
  have hSplit : (posPart A).length ≥ 4 ∨ (negPart A).length ≥ 4 := by omega
  rcases hSplit with hPosLen | hNegLen
  · let P := sortAsc (posPart A)
    have hP_sort : IsStrictlySorted P := sortAsc_strictlySorted (posPart A) (posPart_nodup A hNodup)
    have hP_mem : ∀ x, x ∈ P ↔ x ∈ posPart A := sortAsc_mem (posPart A)
    have hP_pos : ∀ x ∈ P, x > 0 := fun x hx => ((posPart_mem_iff A x).1 ((hP_mem x).1 hx)).2
    have hP_len : P.length ≥ 4 := by simpa [P, sortAsc_length] using hPosLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_3_of_no_3 P hP_sort hP_pos hP_len
    have hB_subPos : ∀ x ∈ B, x ∈ posPart A := fun x hx => (hP_mem x).1 (hB_subP.mem hx)
    have hB_avoidPos : IsSumAvoiding (posPart A) B := by
      intro b1 hb1 b2 hb2 hne hsum
      exact hB_avoidP b1 hb1 b2 hb2 hne ((hP_mem (b1 + b2)).2 hsum)
    have hB_avoidA : IsSumAvoiding A B := pos_sum_avoiding_lift A B hB_subPos hB_avoidPos
    have hB_subA : ∀ x ∈ B, x ∈ A := fun x hx => ((posPart_mem_iff A x).1 (hB_subPos x hx)).1
    obtain ⟨B', hB'_sub, hB'_nodup, hB'_len, hIff⟩ := exists_sublist_of_subset A B hB_nodup hB_subA
    exact ⟨B', hB'_sub, hB'_nodup, hB'_len.trans hB_len, (isSumAvoiding_congr_mem hIff).2 hB_avoidA⟩
  · let P := sortAsc (negPart A)
    have hP_sort : IsStrictlySorted P := sortAsc_strictlySorted (negPart A) (negPart_nodup A hNodup)
    have hP_mem : ∀ x, x ∈ P ↔ x ∈ negPart A := sortAsc_mem (negPart A)
    have hP_pos : ∀ x ∈ P, x > 0 := fun x hx => ((negPart_mem_iff A x).1 ((hP_mem x).1 hx)).2
    have hP_len : P.length ≥ 4 := by simpa [P, sortAsc_length] using hNegLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_3_of_no_3 P hP_sort hP_pos hP_len
    have hB_subNeg : ∀ x ∈ B, x ∈ negPart A := fun x hx => (hP_mem x).1 (hB_subP.mem hx)
    have hB_avoidNeg : IsSumAvoiding (negPart A) B := by
      intro b1 hb1 b2 hb2 hne hsum
      exact hB_avoidP b1 hb1 b2 hb2 hne ((hP_mem (b1 + b2)).2 hsum)
    let Bneg := B.map (- ·)
    have hBneg_avoidA : IsSumAvoiding A Bneg := neg_sum_avoiding_lift A B hB_subNeg hB_avoidNeg
    have hBneg_nodup : Bneg.Nodup := hB_nodup.map (- ·) (fun _ _ hne hneg => hne (by omega))
    have hBneg_len : Bneg.length = 3 := by simp [Bneg, hB_len]
    have hBneg_subA : ∀ x ∈ Bneg, x ∈ A := by
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨b, hb, rfl⟩
      exact ((negPart_mem_iff A b).1 (hB_subNeg b hb)).1
    obtain ⟨B', hB'_sub, hB'_nodup, hB'_len, hIff⟩ := exists_sublist_of_subset A Bneg hBneg_nodup hBneg_subA
    exact ⟨B', hB'_sub, hB'_nodup, hB'_len.trans hBneg_len, (isSumAvoiding_congr_mem hIff).2 hBneg_avoidA⟩


/-! ==================================================================== -/
/-! ### Section 5: Additive Elimination & n_max_3_upper (n_max(3) ≤ 13)  -/
/-! ==================================================================== -/

/-- Helper: if `[x1, x2, c, d]` fails `IsSumAvoiding P` and the 5 pairs
    `{x1, x2}`, `{x1, c}`, `{x1, d}`, `{x2, c}`, `{x2, d}` all sum outside `P`,
    then `c + d ∈ P`. -/
private theorem not_isSumAvoiding_quad_last {P : List Int} {x1 x2 c d : Int}
    (hnot : ¬ IsSumAvoiding P [x1, x2, c, d])
    (h12 : (x1 + x2) ∉ P) (h1c : (x1 + c) ∉ P) (h1d : (x1 + d) ∉ P)
    (h2c : (x2 + c) ∉ P) (h2d : (x2 + d) ∉ P) :
    (c + d) ∈ P := by
  by_cases hcd : (c + d) ∈ P
  · exact hcd
  · exfalso
    apply hnot
    intro u hu v hv hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact h12
    · exact h1c
    · exact h1d
    · rw [Int.add_comm]; exact h12
    · exact absurd rfl hne
    · exact h2c
    · exact h2d
    · rw [Int.add_comm]; exact h1c
    · rw [Int.add_comm]; exact h2c
    · exact absurd rfl hne
    · exact hcd
    · rw [Int.add_comm]; exact h1d
    · rw [Int.add_comm]; exact h2d
    · rw [Int.add_comm]; exact hcd
    · exact absurd rfl hne

/-- Case A pigeonhole elimination: if `(x2 + x3) ∉ P` and 3 distinct elements `u, v, w < x3`
    all avoid forming a sum in `P` with `x2`, then `x3 + u`, `x3 + v`, `x3 + w` must all lie
    in `{x1, x2}`, contradiction. -/
private theorem caseA_pigeonhole (P : List Int)
    (hNo4 : ∀ B : List Int, (∀ x ∈ B, x ∈ P) → B.Nodup → B.length = 4 → ¬ IsSumAvoiding P B)
    (x1 x2 x3 u v w : Int)
    (hx1 : x1 ∈ P) (hx2 : x2 ∈ P) (hx3 : x3 ∈ P)
    (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (h12 : x1 > x2) (h23 : x2 > x3) (h3u : x3 > u) (h3v : x3 > v) (h3w : x3 > w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hupos : u > 0) (hvpos : v > 0) (hwpos : w > 0)
    (hx2pos : x2 > 0) (hx3pos : x3 > 0)
    (hMax : ∀ z ∈ P, z ≤ x1)
    (hTop2 : ∀ z ∈ P, z > x3 → z = x1 ∨ z = x2)
    (hn23 : (x2 + x3) ∉ P)
    (hn2u : (x2 + u) ∉ P) (hn2v : (x2 + v) ∉ P) (hn2w : (x2 + w) ∉ P) :
    False := by
  have hx1_iso : ∀ y > 0, (x1 + y) ∉ P := fun y hy hmem => by
    have := hMax (x1 + y) hmem; omega
  have force_target : ∀ t ∈ P, x3 > t → t > 0 → (x2 + t) ∉ P → (x3 + t = x1 ∨ x3 + t = x2) := by
    intro t ht h3t htpos hn2t
    have hNod : ([x1, x2, x3, t] : List Int).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_nil⟩⟩⟩⟩ <;>
        simp <;> omega
    have hSub : ∀ q ∈ ([x1, x2, x3, t] : List Int), q ∈ P := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> assumption
    have hNot := hNo4 [x1, x2, x3, t] hSub hNod rfl
    have h3t_mem : (x3 + t) ∈ P :=
      not_isSumAvoiding_quad_last hNot
        (hx1_iso x2 hx2pos) (hx1_iso x3 hx3pos) (hx1_iso t htpos) hn23 hn2t
    exact hTop2 (x3 + t) h3t_mem (by omega)
  have fu := force_target u hu h3u hupos hn2u
  have fv := force_target v hv h3v hvpos hn2v
  have fw := force_target w hw h3w hwpos hn2w
  omega

/-- Strict order-preserving bijection from a 3-element strictly increasing sequence into `{x3, x2, x1}`. -/
private theorem order_match_3 {a b c x3 x2 x1 : Int}
    (hab : a < b) (hbc : b < c) (h32 : x3 < x2) (h21 : x2 < x1)
    (ha : a = x1 ∨ a = x2 ∨ a = x3)
    (hb : b = x1 ∨ b = x2 ∨ b = x3)
    (hc : c = x1 ∨ c = x2 ∨ c = x3) :
    a = x3 ∧ b = x2 ∧ c = x1 := by
  omega

/-- Descending helper for `pos_le_6_of_no_4`. -/
private theorem pos_desc_no_all_4_avoid :
    ∀ (D : List Int), IsStrictlyDesc D → (∀ x ∈ D, x > 0) → D.length ≥ 7 →
      (∀ B : List Int, (∀ x ∈ B, x ∈ D) → B.Nodup → B.length = 4 → ¬ IsSumAvoiding D B) →
      False
  | [], _, _, hLen, _ => by simp at hLen
  | [_], _, _, hLen, _ => by simp at hLen
  | [_, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: tail, hDesc, hPos, _, hNo4 => by
    let D := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: tail
    have hx1_mem : x1 ∈ D := by simp [D]
    have hx2_mem : x2 ∈ D := by simp [D]
    have hx3_mem : x3 ∈ D := by simp [D]
    have hx4_mem : x4 ∈ D := by simp [D]
    have hx5_mem : x5 ∈ D := by simp [D]
    have hx6_mem : x6 ∈ D := by simp [D]
    have hx7_mem : x7 ∈ D := by simp [D]
    have hx1_pos : x1 > 0 := hPos x1 hx1_mem
    have hx2_pos : x2 > 0 := hPos x2 hx2_mem
    have hx3_pos : x3 > 0 := hPos x3 hx3_mem
    have hx4_pos : x4 > 0 := hPos x4 hx4_mem
    have hx5_pos : x5 > 0 := hPos x5 hx5_mem
    have hx6_pos : x6 > 0 := hPos x6 hx6_mem
    have hx7_pos : x7 > 0 := hPos x7 hx7_mem
    have hOrd : x1 > x2 ∧ x2 > x3 ∧ x3 > x4 ∧ x4 > x5 ∧ x5 > x6 ∧ x6 > x7 := by
      have p1 := hDesc; rw [IsStrictlyDesc, List.pairwise_cons] at p1
      have p2 := p1.2; rw [List.pairwise_cons] at p2
      have p3 := p2.2; rw [List.pairwise_cons] at p3
      have p4 := p3.2; rw [List.pairwise_cons] at p4
      have p5 := p4.2; rw [List.pairwise_cons] at p5
      have p6 := p5.2; rw [List.pairwise_cons] at p6
      exact ⟨p1.1 x2 (by simp), p2.1 x3 (by simp), p3.1 x4 (by simp),
             p4.1 x5 (by simp), p5.1 x6 (by simp), p6.1 x7 (by simp)⟩
    rcases hOrd with ⟨h12, h23, h34, h45, h56, h67⟩
    have hMax : ∀ z ∈ D, z ≤ x1 := desc_le_head hDesc
    have hTop1 : ∀ z ∈ D, z > x2 → z = x1 := desc_gt_second hDesc
    have hTop2 : ∀ z ∈ D, z > x3 → z = x1 ∨ z = x2 := desc_gt_third hDesc
    have hTop3 : ∀ z ∈ D, z > x4 → z = x1 ∨ z = x2 ∨ z = x3 := desc_gt_fourth hDesc
    have hx1_iso : ∀ y > 0, (x1 + y) ∉ D := fun y hy hmem => by
      have := hMax (x1 + y) hmem; omega
    by_cases hx23 : (x2 + x3) ∈ D
    · -- Case B: x2 + x3 ∈ D forces x2 + x3 = x1.
      have heq1 : x2 + x3 = x1 := hTop1 (x2 + x3) hx23 (by omega)
      have hx2_avoid_small : ∀ y, 0 < y → y < x3 → (x2 + y) ∉ D := by
        intro y hy0 hy3 hmem
        have heq := hTop1 (x2 + y) hmem (by omega)
        omega
      have force_x4_target : ∀ t ∈ D, 0 < t → t < x4 →
          (x4 + t = x1 ∨ x4 + t = x2 ∨ x4 + t = x3) := by
        intro t ht ht0 ht4
        have hNod : ([x1, x2, x4, t] : List Int).Nodup := by
          refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_nil⟩⟩⟩⟩ <;>
            simp <;> omega
        have hSub : ∀ q ∈ ([x1, x2, x4, t] : List Int), q ∈ D := by
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> assumption
        have hNot := hNo4 [x1, x2, x4, t] hSub hNod rfl
        have hmem : (x4 + t) ∈ D :=
          not_isSumAvoiding_quad_last hNot
            (hx1_iso x2 hx2_pos) (hx1_iso x4 hx4_pos) (hx1_iso t ht0)
            (hx2_avoid_small x4 hx4_pos h34) (hx2_avoid_small t ht0 (by omega))
        exact hTop3 (x4 + t) hmem (by omega)
      have h47 := force_x4_target x7 hx7_mem hx7_pos (by omega)
      have h46 := force_x4_target x6 hx6_mem hx6_pos (by omega)
      have h45_t := force_x4_target x5 hx5_mem hx5_pos h45
      obtain ⟨eq47, eq46, eq45⟩ :=
        order_match_3 (a := x4 + x7) (b := x4 + x6) (c := x4 + x5) (x3 := x3) (x2 := x2) (x1 := x1)
          (by omega) (by omega) h23 h12 h47 h46 h45_t
      omega
    · -- Case A: x2 + x3 ∉ D, pigeonhole on {x4, x5, x6, x7} into {x1, x2}.
      have hx2_lt_avoid : ∀ y z : Int, (x2 + y) ∈ D → y > 0 → z > 0 → z < y → (x2 + z) ∉ D := by
        intro y z hmy hy0 hz0 hzy hmz
        have e1 := hTop1 (x2 + y) hmy (by omega)
        have e2 := hTop1 (x2 + z) hmz (by omega)
        omega
      by_cases hx24 : (x2 + x4) ∈ D
      · exact caseA_pigeonhole D hNo4 x1 x2 x3 x5 x6 x7
          hx1_mem hx2_mem hx3_mem hx5_mem hx6_mem hx7_mem
          h12 h23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hx5_pos hx6_pos hx7_pos hx2_pos hx3_pos hMax hTop2 hx23
          (hx2_lt_avoid x4 x5 hx24 hx4_pos hx5_pos h45)
          (hx2_lt_avoid x4 x6 hx24 hx4_pos hx6_pos (by omega))
          (hx2_lt_avoid x4 x7 hx24 hx4_pos hx7_pos (by omega))
      · by_cases hx25 : (x2 + x5) ∈ D
        · exact caseA_pigeonhole D hNo4 x1 x2 x3 x4 x6 x7
            hx1_mem hx2_mem hx3_mem hx4_mem hx6_mem hx7_mem
            h12 h23 h34 (by omega) (by omega) (by omega) (by omega) (by omega)
            hx4_pos hx6_pos hx7_pos hx2_pos hx3_pos hMax hTop2 hx23
            hx24
            (hx2_lt_avoid x5 x6 hx25 hx5_pos hx6_pos h56)
            (hx2_lt_avoid x5 x7 hx25 hx5_pos hx7_pos (by omega))
        · by_cases hx26 : (x2 + x6) ∈ D
          · exact caseA_pigeonhole D hNo4 x1 x2 x3 x4 x5 x7
              hx1_mem hx2_mem hx3_mem hx4_mem hx5_mem hx7_mem
              h12 h23 h34 (by omega) (by omega) (by omega) (by omega) (by omega)
              hx4_pos hx5_pos hx7_pos hx2_pos hx3_pos hMax hTop2 hx23
              hx24 hx25
              (hx2_lt_avoid x6 x7 hx26 hx6_pos hx7_pos h67)
          · exact caseA_pigeonhole D hNo4 x1 x2 x3 x4 x5 x6
              hx1_mem hx2_mem hx3_mem hx4_mem hx5_mem hx6_mem
              h12 h23 h34 (by omega) (by omega) (by omega) (by omega) (by omega)
              hx4_pos hx5_pos hx6_pos hx2_pos hx3_pos hMax hTop2 hx23
              hx24 hx25 hx26

/-- **Lemma `pos_le_6_of_no_4`** (Additive Elimination for `k = 3`):
    Any strictly sorted positive list `P` of length ≥ 7 contains a `Nodup`
    sum-avoiding sublist `B` of length 4. -/
theorem pos_le_6_of_no_4 (P : List Int)
    (hSort : IsStrictlySorted P) (hPos : ∀ x ∈ P, x > 0) (hLen : P.length ≥ 7) :
    ∃ B : List Int, B.Sublist P ∧ B.Nodup ∧ B.length = 4 ∧ IsSumAvoiding P B := by
  have hNodup : P.Nodup := isStrictlySorted_nodup hSort
  cases hHas : hasSumAvoidingSubset 4 P
  · exfalso
    have hNo4 := hasSumAvoidingSubset_false 4 P hHas
    have hNo4D : ∀ B : List Int, (∀ x ∈ B, x ∈ P.reverse) → B.Nodup → B.length = 4 → ¬ IsSumAvoiding P.reverse B := by
      intro B hSub hNd hL hAv
      apply hNo4 B (fun x hx => List.mem_reverse.1 (hSub x hx)) hNd hL
      intro b1 hb1 b2 hb2 hne hsum
      exact hAv b1 hb1 b2 hb2 hne (List.mem_reverse.2 hsum)
    exact pos_desc_no_all_4_avoid P.reverse (isStrictlyDesc_reverse hSort)
      (fun x hx => hPos x (List.mem_reverse.1 hx)) (by simpa using hLen) hNo4D
  · exact hasSumAvoidingSubset_true 4 P hNodup hHas

/-- **Theorem `n_max_3_upper`** (`n_max(3) ≤ 13`):
    Any duplicate-free integer list `A` of length ≥ 14 contains a `Nodup` sum-avoiding
    sublist `B` of length 4. -/
theorem n_max_3_upper (A : List Int) (hNodup : A.Nodup) (hLen : A.length ≥ 14) :
    ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 4 ∧ IsSumAvoiding A B := by
  have hPart := length_pos_neg_zero A
  have hZero := zero_filter_length_le_one A hNodup
  have hSplit : (posPart A).length ≥ 7 ∨ (negPart A).length ≥ 7 := by omega
  rcases hSplit with hPosLen | hNegLen
  · let P := sortAsc (posPart A)
    have hP_sort : IsStrictlySorted P := sortAsc_strictlySorted (posPart A) (posPart_nodup A hNodup)
    have hP_mem : ∀ x, x ∈ P ↔ x ∈ posPart A := sortAsc_mem (posPart A)
    have hP_pos : ∀ x ∈ P, x > 0 := fun x hx => ((posPart_mem_iff A x).1 ((hP_mem x).1 hx)).2
    have hP_len : P.length ≥ 7 := by simpa [P, sortAsc_length] using hPosLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_6_of_no_4 P hP_sort hP_pos hP_len
    have hB_subPos : ∀ x ∈ B, x ∈ posPart A := fun x hx => (hP_mem x).1 (hB_subP.mem hx)
    have hB_avoidPos : IsSumAvoiding (posPart A) B := by
      intro b1 hb1 b2 hb2 hne hsum
      exact hB_avoidP b1 hb1 b2 hb2 hne ((hP_mem (b1 + b2)).2 hsum)
    have hB_avoidA : IsSumAvoiding A B := pos_sum_avoiding_lift A B hB_subPos hB_avoidPos
    have hB_subA : ∀ x ∈ B, x ∈ A := fun x hx => ((posPart_mem_iff A x).1 (hB_subPos x hx)).1
    obtain ⟨B', hB'_sub, hB'_nodup, hB'_len, hIff⟩ := exists_sublist_of_subset A B hB_nodup hB_subA
    exact ⟨B', hB'_sub, hB'_nodup, hB'_len.trans hB_len, (isSumAvoiding_congr_mem hIff).2 hB_avoidA⟩
  · let P := sortAsc (negPart A)
    have hP_sort : IsStrictlySorted P := sortAsc_strictlySorted (negPart A) (negPart_nodup A hNodup)
    have hP_mem : ∀ x, x ∈ P ↔ x ∈ negPart A := sortAsc_mem (negPart A)
    have hP_pos : ∀ x ∈ P, x > 0 := fun x hx => ((negPart_mem_iff A x).1 ((hP_mem x).1 hx)).2
    have hP_len : P.length ≥ 7 := by simpa [P, sortAsc_length] using hNegLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_6_of_no_4 P hP_sort hP_pos hP_len
    have hB_subNeg : ∀ x ∈ B, x ∈ negPart A := fun x hx => (hP_mem x).1 (hB_subP.mem hx)
    have hB_avoidNeg : IsSumAvoiding (negPart A) B := by
      intro b1 hb1 b2 hb2 hne hsum
      exact hB_avoidP b1 hb1 b2 hb2 hne ((hP_mem (b1 + b2)).2 hsum)
    let Bneg := B.map (- ·)
    have hBneg_avoidA : IsSumAvoiding A Bneg := neg_sum_avoiding_lift A B hB_subNeg hB_avoidNeg
    have hBneg_nodup : Bneg.Nodup := hB_nodup.map (- ·) (fun _ _ hne hneg => hne (by omega))
    have hBneg_len : Bneg.length = 4 := by simp [Bneg, hB_len]
    have hBneg_subA : ∀ x ∈ Bneg, x ∈ A := by
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨b, hb, rfl⟩
      exact ((negPart_mem_iff A b).1 (hB_subNeg b hb)).1
    obtain ⟨B', hB'_sub, hB'_nodup, hB'_len, hIff⟩ := exists_sublist_of_subset A Bneg hBneg_nodup hBneg_subA
    exact ⟨B', hB'_sub, hB'_nodup, hB'_len.trans hBneg_len, (isSumAvoiding_congr_mem hIff).2 hBneg_avoidA⟩


/-! ==================================================================== -/
/-! ### Section 6: Exact Saturated Lower Bounds & Threshold Certificates  -/
/-! ==================================================================== -/

/-- Witness `A3 = {-1, 0, 1}` establishing `n_max(1) ≥ 3`. -/
def A3 : List Int := [-1, 0, 1]

theorem A3_card : A3.length = 3 := rfl
theorem A3_nodup : A3.Nodup := by decide
theorem A3_no_sum_avoiding_2_bool : hasSumAvoidingSubset 2 A3 = false := by decide

theorem A3_no_sum_avoiding_2 :
    ∀ B : List Int, (∀ x ∈ B, x ∈ A3) → B.Nodup → B.length = 2 → ¬ IsSumAvoiding A3 B :=
  hasSumAvoidingSubset_false 2 A3 A3_no_sum_avoiding_2_bool

/-- Witness `A7 = {-3, -2, -1, 0, 1, 2, 3}` establishing `n_max(2) ≥ 7`. -/
def A7 : List Int := [-3, -2, -1, 0, 1, 2, 3]

theorem A7_card : A7.length = 7 := rfl
theorem A7_nodup : A7.Nodup := by decide
theorem A7_has_sum_avoiding_2 : IsSumAvoiding A7 [2, 3] :=
  (isSumAvoidingBool_iff A7 [2, 3]).1 (by decide)
theorem A7_no_sum_avoiding_3_bool : hasSumAvoidingSubset 3 A7 = false := by decide

theorem A7_no_sum_avoiding_3 :
    ∀ B : List Int, (∀ x ∈ B, x ∈ A7) → B.Nodup → B.length = 3 → ¬ IsSumAvoiding A7 B :=
  hasSumAvoidingSubset_false 3 A7 A7_no_sum_avoiding_3_bool

/-- Witness `A13* = {-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8}` establishing `n_max(3) ≥ 13`. -/
def A13_star : List Int := [-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8]

theorem A13_star_card : A13_star.length = 13 := rfl
theorem A13_star_nodup : A13_star.Nodup := by decide
theorem A13_has_sum_avoiding_3 : IsSumAvoiding A13_star [5, 7, 8] :=
  (isSumAvoidingBool_iff A13_star [5, 7, 8]).1 (by decide)
theorem A13_no_sum_avoiding_4_bool : hasSumAvoidingSubset 4 A13_star = false := by decide

theorem A13_star_no_sum_avoiding_4 :
    ∀ B : List Int, (∀ x ∈ B, x ∈ A13_star) → B.Nodup → B.length = 4 → ¬ IsSumAvoiding A13_star B :=
  hasSumAvoidingSubset_false 4 A13_star A13_no_sum_avoiding_4_bool

/-- Complete characterization `n_max(1) = 3`. -/
theorem n_max_1_exact :
    (A3.Nodup ∧ A3.length = 3 ∧
      ∀ B : List Int, (∀ x ∈ B, x ∈ A3) → B.Nodup → B.length = 2 → ¬ IsSumAvoiding A3 B) ∧
    (∀ A : List Int, A.Nodup → A.length ≥ 4 →
      ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 2 ∧ IsSumAvoiding A B) :=
  ⟨⟨A3_nodup, A3_card, A3_no_sum_avoiding_2⟩, n_max_1_upper_sublist⟩

/-- Complete characterization `n_max(2) = 7`. -/
theorem n_max_2_exact :
    (A7.Nodup ∧ A7.length = 7 ∧
      ∀ B : List Int, (∀ x ∈ B, x ∈ A7) → B.Nodup → B.length = 3 → ¬ IsSumAvoiding A7 B) ∧
    (∀ A : List Int, A.Nodup → A.length ≥ 8 →
      ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 3 ∧ IsSumAvoiding A B) :=
  ⟨⟨A7_nodup, A7_card, A7_no_sum_avoiding_3⟩, n_max_2_upper⟩

/-- Complete characterization `n_max(3) = 13`. -/
theorem n_max_3_exact :
    (A13_star.Nodup ∧ A13_star.length = 13 ∧
      ∀ B : List Int, (∀ x ∈ B, x ∈ A13_star) → B.Nodup → B.length = 4 → ¬ IsSumAvoiding A13_star B) ∧
    (∀ A : List Int, A.Nodup → A.length ≥ 14 →
      ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 4 ∧ IsSumAvoiding A B) :=
  ⟨⟨A13_star_nodup, A13_star_card, A13_star_no_sum_avoiding_4⟩, n_max_3_upper⟩

end Erdos787Thresholds
