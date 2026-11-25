/-!
# WitnessesStandalone.lean
### Machine-Checked Pure Lean 4 Certification of All 7 Extremal Witnesses for Erdős Problem #787

This self-contained module (Pure Lean 4 `Init` only, zero Mathlib, zero `sorry`, zero extra axioms)
formally proves BOTH lower and upper bounds on `M(A)` (the maximum sum-avoiding subset size)
for all 7 known extremal witnesses:
- `A3`       (`n = 3`,  `M(A3)       = 1`, via 1-clique partition)
- `A7`       (`n = 7`,  `M(A7)       = 2`, via 2-clique partition)
- `A13_star` (`n = 13`, `M(A13_star) = 3`, via 3-node branch-and-bound certificate tree)
- `A21`      (`n = 21`, `M(A21)      = 4`, via 4-clique partition)
- `A31`      (`n = 31`, `M(A31)      = 5`, via 5-clique partition)
- `A43`      (`n = 43`, `M(A43)      = 6`, via 6-clique partition)
- `A51`      (`n = 51`, `M(A51)      = 7`, via 5-node branch-and-bound certificate tree)
-/

namespace Erdos787Witnesses

/-! ==================================================================== -/
/-! ### Section 1: Foundational Definitions & Boolean Soundness Bridges  -/
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

/-- Soundness of `isSumAvoidingBool`: if it returns `true`, then `IsSumAvoiding A B` holds. -/
theorem isSumAvoidingBool_sound (A B : List Int)
    (h : isSumAvoidingBool A B = true) : IsSumAvoiding A B := by
  intro b1 hb1 b2 hb2 hne hsum
  unfold isSumAvoidingBool at h
  rw [List.all_eq_true] at h
  have h1 := h b1 hb1
  rw [List.all_eq_true] at h1
  have h2 := h1 b2 hb2
  have hne_b : (b1 != b2) = true := bne_iff_ne.mpr hne
  simp [hne_b] at h2
  exact h2 hsum

/-- Computable boolean check that every pair of distinct elements `u, v ∈ C`
    satisfies `(u + v) ∈ A`, i.e., `C` induces a clique in the conflict graph of `A`. -/
def isCliqueBool (A C : List Int) : Bool :=
  C.all fun u =>
    C.all fun v =>
      if u != v then A.contains (u + v) else true

/-- Soundness of `isCliqueBool`. -/
theorem isCliqueBool_sound (A C : List Int) (h : isCliqueBool A C = true) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (u + v) ∈ A := by
  intro u hu v hv hne
  unfold isCliqueBool at h
  rw [List.all_eq_true] at h
  have h1 := h u hu
  rw [List.all_eq_true] at h1
  have h2 := h1 v hv
  have hne_b : (u != v) = true := bne_iff_ne.mpr hne
  simp [hne_b] at h2
  exact h2

/-- Computable boolean check that `Cs` is a list of cliques in `A` covering `cand`. -/
def isCliqueCoverBool (A cand : List Int) (Cs : List (List Int)) : Bool :=
  Cs.all (isCliqueBool A) && cand.all (fun x => Cs.any (fun C => C.contains x))

/-- Soundness of `isCliqueCoverBool`. -/
theorem isCliqueCoverBool_sound (A cand : List Int) (Cs : List (List Int))
    (h : isCliqueCoverBool A cand Cs = true) :
    (∀ C ∈ Cs, isCliqueBool A C = true) ∧ (∀ x ∈ cand, ∃ C ∈ Cs, x ∈ C) := by
  unfold isCliqueCoverBool at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro x hx
  have hany := h.2 x hx
  rw [List.any_eq_true] at hany
  rcases hany with ⟨C, hC_mem, hC_has⟩
  exact ⟨C, hC_mem, List.contains_iff_mem.mp hC_has⟩


/-! ==================================================================== -/
/-! ### Section 2: O(n²) Clique Partition Upper Bound Soundness        -/
/-! ==================================================================== -/

/-- Generalized clique-cover pigeonhole lemma: if `Cs` is a list of cliques in `A`
    covering every element of `B`, and `B` is duplicate-free and sum-avoiding in `A`,
    then `B.length ≤ Cs.length`. -/
theorem clique_cover_indep_le
    (A : List Int) (Cs : List (List Int)) (B : List Int)
    (hCliques : ∀ C ∈ Cs, isCliqueBool A C = true)
    (hCover : ∀ x ∈ B, ∃ C ∈ Cs, x ∈ C)
    (hNodup : B.Nodup)
    (hIndep : IsSumAvoiding A B) :
    B.length ≤ Cs.length := by
  induction Cs generalizing B with
  | nil =>
    cases B with
    | nil => exact Nat.le_refl 0
    | cons b bs =>
      obtain ⟨C, hC, _⟩ := hCover b (by simp)
      cases hC
  | cons C Cs' ih =>
    have hC_clique : isCliqueBool A C = true := hCliques C (by simp)
    have hCs'_clique : ∀ C' ∈ Cs', isCliqueBool A C' = true :=
      fun C' hC' => hCliques C' (by simp [hC'])
    by_cases hex : ∃ b ∈ B, b ∈ C
    · rcases hex with ⟨b, hbB, hbC⟩
      let B' := B.erase b
      have hB'_nodup : B'.Nodup := hNodup.erase b
      have hB'_indep : IsSumAvoiding A B' := by
        intro x hx y hy hne
        exact hIndep x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy) hne
      have hB'_cover : ∀ x ∈ B', ∃ C' ∈ Cs', x ∈ C' := by
        intro x hx
        have hmem := (hNodup.mem_erase_iff).mp hx
        have hne : x ≠ b := hmem.1
        have hxB : x ∈ B := hmem.2
        have hxNotC : x ∉ C := by
          intro hxC
          have hsum_in : (x + b) ∈ A := isCliqueBool_sound A C hC_clique x hxC b hbC hne
          exact hIndep x hxB b hbB hne hsum_in
        obtain ⟨C0, hC0_mem, hxC0⟩ := hCover x hxB
        simp only [List.mem_cons] at hC0_mem
        rcases hC0_mem with rfl | hC0'
        · exact False.elim (hxNotC hxC0)
        · exact ⟨C0, hC0', hxC0⟩
      have h_ih := ih B' hCs'_clique hB'_cover hB'_nodup hB'_indep
      have hlen : B'.length = B.length - 1 := List.length_erase_of_mem hbB
      have hpos : 0 < B.length := List.length_pos_of_mem hbB
      rw [List.length_cons]
      omega
    · have hB_cover : ∀ x ∈ B, ∃ C' ∈ Cs', x ∈ C' := by
        intro x hxB
        have hxNotC : x ∉ C := fun hxC => hex ⟨x, hxB, hxC⟩
        obtain ⟨C0, hC0_mem, hxC0⟩ := hCover x hxB
        simp only [List.mem_cons] at hC0_mem
        rcases hC0_mem with rfl | hC0'
        · exact False.elim (hxNotC hxC0)
        · exact ⟨C0, hC0', hxC0⟩
      have h_ih := ih B hCs'_clique hB_cover hNodup hIndep
      exact Nat.le_succ_of_le h_ih

/-- Clique Partition Upper Bound Soundness Theorem:
    If `Cs` is a list of cliques in `A` covering all elements of `A`, then any
    duplicate-free sum-avoiding subset `B ⊆ A` has length at most `Cs.length`. -/
theorem clique_partition_upper_bound
    (A : List Int) (Cs : List (List Int))
    (hCliques : ∀ C ∈ Cs, isCliqueBool A C = true)
    (hCover : ∀ x ∈ A, ∃ C ∈ Cs, x ∈ C) :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ Cs.length :=
  fun B hNodup hSub hIndep =>
    clique_cover_indep_le A Cs B hCliques (fun x hx => hCover x (hSub x hx)) hNodup hIndep


/-! ==================================================================== -/
/-! ### Section 3: Branch-and-Bound Certificate Tree (`CertTree`)        -/
/-! ==================================================================== -/

/-- Certificate tree bounding the maximum independent set size of a conflict graph:
    - `leafClique Cs`: certifies `Cs` has `≤ k` cliques covering all remaining candidates.
    - `branch v tIn tOut`: branches on whether vertex `v` belongs to `B`:
        * in `tIn` (`v ∈ B`), `v` and all neighbors of `v` in `A` are removed and budget drops by 1;
        * in `tOut` (`v ∉ B`), `v` is removed and budget stays `k`. -/
inductive CertTree where
  | leafClique (Cs : List (List Int)) : CertTree
  | branch (v : Int) (tIn tOut : CertTree) : CertTree

/-- Executable verifier checking that `T` certifies `α(G_A[cand]) ≤ k`. -/
def checkCertTree (A cand : List Int) (k : Nat) : CertTree → Bool
  | .leafClique Cs => decide (Cs.length ≤ k) && isCliqueCoverBool A cand Cs
  | .branch v tIn tOut =>
    match k with
    | 0 => false
    | k' + 1 =>
      let candIn := cand.filter (fun u => u != v && !(A.contains (v + u)))
      let candOut := cand.filter (fun u => u != v)
      checkCertTree A candIn k' tIn && checkCertTree A candOut (k' + 1) tOut

/-- Soundness of `CertTree`: if `checkCertTree A cand k T = true`, then any duplicate-free
    sum-avoiding list `B` drawn from `cand` has length at most `k`. -/
theorem certTree_sound (A : List Int) (T : CertTree) :
    ∀ (cand : List Int) (k : Nat),
      checkCertTree A cand k T = true →
      ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ cand) → IsSumAvoiding A B → B.length ≤ k := by
  induction T with
  | leafClique Cs =>
    intro cand k hCheck B hNodup hSub hIndep
    unfold checkCertTree at hCheck
    rw [Bool.and_eq_true] at hCheck
    have hLen : Cs.length ≤ k := decide_eq_true_eq.mp hCheck.1
    have hCov := isCliqueCoverBool_sound A cand Cs hCheck.2
    have hLe : B.length ≤ Cs.length :=
      clique_cover_indep_le A Cs B hCov.1 (fun x hx => hCov.2 x (hSub x hx)) hNodup hIndep
    exact Nat.le_trans hLe hLen
  | branch v tIn tOut ihIn ihOut =>
    intro cand k hCheck B hNodup hSub hIndep
    cases k with
    | zero =>
      unfold checkCertTree at hCheck
      cases hCheck
    | succ k' =>
      unfold checkCertTree at hCheck
      rw [Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hIn, hOut⟩
      by_cases hv : v ∈ B
      · let B' := B.erase v
        let candIn := cand.filter (fun u => u != v && !(A.contains (v + u)))
        have hB'_nodup : B'.Nodup := hNodup.erase v
        have hB'_indep : IsSumAvoiding A B' := by
          intro x hx y hy hne
          exact hIndep x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy) hne
        have hB'_sub : ∀ x ∈ B', x ∈ candIn := by
          intro x hx
          have hmem := (hNodup.mem_erase_iff).mp hx
          have hne : x ≠ v := hmem.1
          have hxB : x ∈ B := hmem.2
          have hnot_sum : (v + x) ∉ A := hIndep v hv x hxB hne.symm
          have hcontains_false : A.contains (v + x) = false := by
            cases hc : A.contains (v + x)
            · rfl
            · exact False.elim (hnot_sum (List.contains_iff_mem.mp hc))
          refine List.mem_filter.mpr ⟨hSub x hxB, ?_⟩
          rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
          exact ⟨hne, hcontains_false⟩
        have h_ih := ihIn candIn k' hIn B' hB'_nodup hB'_sub hB'_indep
        have hlen : B'.length = B.length - 1 := List.length_erase_of_mem hv
        have hpos : 0 < B.length := List.length_pos_of_mem hv
        omega
      · let candOut := cand.filter (fun u => u != v)
        have hB_sub : ∀ x ∈ B, x ∈ candOut := by
          intro x hxB
          have hne : x ≠ v := fun heq => hv (heq ▸ hxB)
          refine List.mem_filter.mpr ⟨hSub x hxB, ?_⟩
          exact bne_iff_ne.mpr hne
        exact ihOut candOut (k' + 1) hOut B hNodup hB_sub hIndep

/-- Top-level specialization of `certTree_sound` to `cand = A`. -/
theorem certTree_upper_bound (A : List Int) (k : Nat) (T : CertTree)
    (h : checkCertTree A A k T = true) :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k :=
  certTree_sound A T A k h

/-- Exact witness specification: `M(A) = k`, i.e., `A` contains a duplicate-free
    sum-avoiding subset of length `k`, and every duplicate-free sum-avoiding subset
    of `A` has length at most `k`. -/
def HasExactMaxSumAvoiding (A : List Int) (k : Nat) : Prop :=
  (∃ B : List Int, B.Nodup ∧ (∀ x ∈ B, x ∈ A) ∧ IsSumAvoiding A B ∧ B.length = k) ∧
  (∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k)


/-! ==================================================================== -/
/-! ### Section 4: Clique-Partition Certified Witnesses (k = 1,2,4,5,6)  -/
/-! ==================================================================== -/

/-! #### Witness 1: A₃ (n = 3, M(A₃) = 1) -/

def A3 : List Int := [-1, 0, 1]
def B1 : List Int := [1]
def Cs3 : List (List Int) := [[-1, 0, 1]]

theorem A3_card : A3.length = 3 := rfl
theorem A3_nodup : A3.Nodup := by decide

theorem B1_len : B1.length = 1 := rfl
theorem B1_nodup : B1.Nodup := by decide
theorem B1_sub : ∀ x ∈ B1, x ∈ A3 := by decide
theorem B1_sumAvoidingBool : isSumAvoidingBool A3 B1 = true := by decide
theorem B1_sumAvoiding : IsSumAvoiding A3 B1 :=
  isSumAvoidingBool_sound A3 B1 B1_sumAvoidingBool

theorem Cs3_len : Cs3.length = 1 := rfl
theorem Cs3_valid : isCliqueCoverBool A3 A3 Cs3 = true := by decide

theorem A3_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A3) → IsSumAvoiding A3 B → B.length ≤ 1 := by
  have h := isCliqueCoverBool_sound A3 A3 Cs3 Cs3_valid
  simpa [Cs3_len] using clique_partition_upper_bound A3 Cs3 h.1 h.2

theorem A3_exact_M : HasExactMaxSumAvoiding A3 1 :=
  ⟨⟨B1, B1_nodup, B1_sub, B1_sumAvoiding, B1_len⟩, A3_upper_bound⟩


/-! #### Witness 2: A₇ (n = 7, M(A₇) = 2) -/

def A7 : List Int := [-3, -2, -1, 0, 1, 2, 3]
def B2 : List Int := [2, 3]
def Cs7 : List (List Int) := [[-2, -1, 0, 3], [-3, 1, 2]]

theorem A7_card : A7.length = 7 := rfl
theorem A7_nodup : A7.Nodup := by decide

theorem B2_len : B2.length = 2 := rfl
theorem B2_nodup : B2.Nodup := by decide
theorem B2_sub : ∀ x ∈ B2, x ∈ A7 := by decide
theorem B2_sumAvoidingBool : isSumAvoidingBool A7 B2 = true := by decide
theorem B2_sumAvoiding : IsSumAvoiding A7 B2 :=
  isSumAvoidingBool_sound A7 B2 B2_sumAvoidingBool

theorem Cs7_len : Cs7.length = 2 := rfl
theorem Cs7_valid : isCliqueCoverBool A7 A7 Cs7 = true := by decide

theorem A7_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A7) → IsSumAvoiding A7 B → B.length ≤ 2 := by
  have h := isCliqueCoverBool_sound A7 A7 Cs7 Cs7_valid
  simpa [Cs7_len] using clique_partition_upper_bound A7 Cs7 h.1 h.2

theorem A7_exact_M : HasExactMaxSumAvoiding A7 2 :=
  ⟨⟨B2, B2_nodup, B2_sub, B2_sumAvoiding, B2_len⟩, A7_upper_bound⟩


/-! #### Witness 4: A₂₁ (n = 21, M(A₂₁) = 4) -/

def A21 : List Int :=
  [-15, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15]
def B4 : List Int := [3, 7, 9, 15]
def Cs21 : List (List Int) :=
  [ [-15, 0, 15],
    [-5, -4, -3, -2, -1, 6, 9],
    [-9, -6, 1, 7, 8],
    [-8, -7, 2, 3, 4, 5] ]

theorem A21_card : A21.length = 21 := rfl
theorem A21_nodup : A21.Nodup := by decide

theorem B4_len : B4.length = 4 := rfl
theorem B4_nodup : B4.Nodup := by decide
theorem B4_sub : ∀ x ∈ B4, x ∈ A21 := by decide
theorem B4_sumAvoidingBool : isSumAvoidingBool A21 B4 = true := by decide
theorem B4_sumAvoiding : IsSumAvoiding A21 B4 :=
  isSumAvoidingBool_sound A21 B4 B4_sumAvoidingBool

theorem Cs21_len : Cs21.length = 4 := rfl
theorem Cs21_valid : isCliqueCoverBool A21 A21 Cs21 = true := by decide

theorem A21_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A21) → IsSumAvoiding A21 B → B.length ≤ 4 := by
  have h := isCliqueCoverBool_sound A21 A21 Cs21 Cs21_valid
  simpa [Cs21_len] using clique_partition_upper_bound A21 Cs21 h.1 h.2

theorem A21_exact_M : HasExactMaxSumAvoiding A21 4 :=
  ⟨⟨B4, B4_nodup, B4_sub, B4_sumAvoiding, B4_len⟩, A21_upper_bound⟩


/-! #### Witness 5: A₃₁ (n = 31, M(A₃₁) = 5) -/

def A31 : List Int :=
  [-30, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0,
   1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 30]
def B5 : List Int := [9, 10, 16, 18, 30]
def Cs31 : List (List Int) :=
  [ [-30, 0, 30],
    [-16, -14, -2, 12, 18],
    [-18, -12, 2, 14, 16],
    [-9, -7, -5, -3, -1, 4, 6, 8, 10],
    [-10, -8, -6, -4, 1, 3, 5, 7, 9] ]

theorem A31_card : A31.length = 31 := rfl
theorem A31_nodup : A31.Nodup := by decide

theorem B5_len : B5.length = 5 := rfl
theorem B5_nodup : B5.Nodup := by decide
theorem B5_sub : ∀ x ∈ B5, x ∈ A31 := by decide
theorem B5_sumAvoidingBool : isSumAvoidingBool A31 B5 = true := by decide
theorem B5_sumAvoiding : IsSumAvoiding A31 B5 :=
  isSumAvoidingBool_sound A31 B5 B5_sumAvoidingBool

theorem Cs31_len : Cs31.length = 5 := rfl
theorem Cs31_valid : isCliqueCoverBool A31 A31 Cs31 = true := by decide

theorem A31_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A31) → IsSumAvoiding A31 B → B.length ≤ 5 := by
  have h := isCliqueCoverBool_sound A31 A31 Cs31 Cs31_valid
  simpa [Cs31_len] using clique_partition_upper_bound A31 Cs31 h.1 h.2

theorem A31_exact_M : HasExactMaxSumAvoiding A31 5 :=
  ⟨⟨B5, B5_nodup, B5_sub, B5_sumAvoiding, B5_len⟩, A31_upper_bound⟩


/-! #### Witness 6: A₄₃ (n = 43, M(A₄₃) = 6) -/

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
theorem B6_sumAvoidingBool : isSumAvoidingBool A43 B6 = true := by decide
theorem B6_sumAvoiding : IsSumAvoiding A43 B6 :=
  isSumAvoidingBool_sound A43 B6 B6_sumAvoidingBool

theorem Cs43_len : Cs43.length = 6 := rfl
theorem Cs43_valid : isCliqueCoverBool A43 A43 Cs43 = true := by decide

theorem A43_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A43) → IsSumAvoiding A43 B → B.length ≤ 6 := by
  have h := isCliqueCoverBool_sound A43 A43 Cs43 Cs43_valid
  simpa [Cs43_len] using clique_partition_upper_bound A43 Cs43 h.1 h.2

theorem A43_exact_M : HasExactMaxSumAvoiding A43 6 :=
  ⟨⟨B6, B6_nodup, B6_sub, B6_sumAvoiding, B6_len⟩, A43_upper_bound⟩


/-! ==================================================================== -/
/-! ### Section 5: Branch-and-Bound Certified Witnesses (k = 3, 7)       -/
/-! ==================================================================== -/

/-! #### Witness 3: A₁₃* (n = 13, M(A₁₃*) = 3) -/

def A13_star : List Int := [-9, -6, -5, -4, -3, -1, 0, 1, 2, 3, 5, 7, 8]
def B3 : List Int := [5, 7, 8]

/-- 3-node branch-and-bound certificate tree for `A₁₃*` (branch on `-1`). -/
def T13 : CertTree :=
  .branch (-1)
    (.leafClique [[-9, 5], [7, -6]])
    (.leafClique [[-9, 8, 0], [7, -4, 1, -5], [-3, 2, 3, -6, 5]])

theorem A13_star_card : A13_star.length = 13 := rfl
theorem A13_star_nodup : A13_star.Nodup := by decide

theorem B3_len : B3.length = 3 := rfl
theorem B3_nodup : B3.Nodup := by decide
theorem B3_sub : ∀ x ∈ B3, x ∈ A13_star := by decide
theorem B3_sumAvoidingBool : isSumAvoidingBool A13_star B3 = true := by decide
theorem B3_sumAvoiding : IsSumAvoiding A13_star B3 :=
  isSumAvoidingBool_sound A13_star B3 B3_sumAvoidingBool

theorem T13_valid : checkCertTree A13_star A13_star 3 T13 = true := by decide

theorem A13_star_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A13_star) → IsSumAvoiding A13_star B → B.length ≤ 3 :=
  certTree_upper_bound A13_star 3 T13 T13_valid

theorem A13_star_exact_M : HasExactMaxSumAvoiding A13_star 3 :=
  ⟨⟨B3, B3_nodup, B3_sub, B3_sumAvoiding, B3_len⟩, A13_star_upper_bound⟩


/-! #### Witness 7: A₅₁ (n = 51, M(A₅₁) = 7) -/

def A51 : List Int :=
  [-66, -48, -42, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8,
   -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
   18, 20, 22, 24, 26, 28, 42, 48, 66]
def B7 : List Int := [12, 15, 26, 28, 42, 48, 66]

/-- 5-node (depth-2) branch-and-bound certificate tree for `A₅₁` (branch on `28`, then `-28`). -/
def T51 : CertTree :=
  .branch 28
    (.leafClique
      [ [66, -66],
        [48, 18],
        [42, 24],
        [26, 22, 2, -11],
        [15, 13, 11, 9, 7, 5, 1, 3, -1, -5, -3, -7, -9],
        [16, 12, 10, 8, 6, 4] ])
    (.branch (-28)
      (.leafClique
        [ [-66, 66],
          [-48, -18],
          [-42, -24],
          [-26, -22, -2, 11],
          [-16, -12, -10, -8, -6, 1, -4, 3, 5, 7, 9],
          [-15, -13, -11, -9, -7, -5, -3, -1] ])
      (.leafClique
        [ [-66, 0, 18, 48],
          [-48, -18, 24, 42],
          [-42, -24, 66],
          [-26, -16, 4, 6, 8, 10, 12, 14],
          [-22, -20, 20, 22],
          [-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15],
          [-14, -12, -10, -8, -6, -4, -2, 2, 16, 26] ]))

theorem A51_card : A51.length = 51 := rfl
theorem A51_nodup : A51.Nodup := by decide

theorem B7_len : B7.length = 7 := rfl
theorem B7_nodup : B7.Nodup := by decide
theorem B7_sub : ∀ x ∈ B7, x ∈ A51 := by decide
theorem B7_sumAvoidingBool : isSumAvoidingBool A51 B7 = true := by decide
theorem B7_sumAvoiding : IsSumAvoiding A51 B7 :=
  isSumAvoidingBool_sound A51 B7 B7_sumAvoidingBool

theorem T51_valid : checkCertTree A51 A51 7 T51 = true := by decide

theorem A51_upper_bound :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A51) → IsSumAvoiding A51 B → B.length ≤ 7 :=
  certTree_upper_bound A51 7 T51 T51_valid

theorem A51_exact_M : HasExactMaxSumAvoiding A51 7 :=
  ⟨⟨B7, B7_nodup, B7_sub, B7_sumAvoiding, B7_len⟩, A51_upper_bound⟩


/-! ==================================================================== -/
/-! ### Section 6: Master Certification Theorem                          -/
/-! ==================================================================== -/

/-- Master certification theorem establishing exact cardinality, duplicate-freeness,
    and exact maximum sum-avoiding subset size `M(A)` for all 7 witnesses. -/
theorem all_seven_witnesses_certified :
    (A3.length = 3       ∧ A3.Nodup       ∧ HasExactMaxSumAvoiding A3 1) ∧
    (A7.length = 7       ∧ A7.Nodup       ∧ HasExactMaxSumAvoiding A7 2) ∧
    (A13_star.length = 13 ∧ A13_star.Nodup ∧ HasExactMaxSumAvoiding A13_star 3) ∧
    (A21.length = 21     ∧ A21.Nodup     ∧ HasExactMaxSumAvoiding A21 4) ∧
    (A31.length = 31     ∧ A31.Nodup     ∧ HasExactMaxSumAvoiding A31 5) ∧
    (A43.length = 43     ∧ A43.Nodup     ∧ HasExactMaxSumAvoiding A43 6) ∧
    (A51.length = 51     ∧ A51.Nodup     ∧ HasExactMaxSumAvoiding A51 7) :=
  ⟨⟨A3_card, A3_nodup, A3_exact_M⟩,
   ⟨A7_card, A7_nodup, A7_exact_M⟩,
   ⟨A13_star_card, A13_star_nodup, A13_star_exact_M⟩,
   ⟨A21_card, A21_nodup, A21_exact_M⟩,
   ⟨A31_card, A31_nodup, A31_exact_M⟩,
   ⟨A43_card, A43_nodup, A43_exact_M⟩,
   ⟨A51_card, A51_nodup, A51_exact_M⟩⟩

end Erdos787Witnesses
