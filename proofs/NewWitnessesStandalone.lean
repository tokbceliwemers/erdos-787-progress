/-!
# NewWitnessesStandalone.lean
### Machine-Checked Pure Lean 4 Certification of All 49 Constructed Witnesses for `n = 52 .. 100`

Self-contained module (**Pure Lean 4** `Init` only, zero Mathlib, zero `sorry`, zero extra axioms)
formally proving exact cardinality, duplicate-freeness, and exact maximum sum-avoiding subset size
`HasExactMaxSumAvoiding A_n alpha_n` (both lower and upper bounds via independent set + `CertTree`)
for every constructed set `A52` through `A100` (`49` sets total):
- `n = 52 .. 59`: `M(A_n) = 7` (breaking `k^2 + k + 1 = 57` at `n = 58, 59`)
- `n = 60 .. 77`: `M(A_n) = 8` (including `A77`, proving `n_max(8) >= 77`)
- `n = 78 .. 97`: `M(A_n) = 9` (including `A97`, proving `n_max(9) >= 97`)
- `n = 98 .. 100`: `M(A_n) = 10`
-/

namespace Erdos787NewWitnesses

/-! ==================================================================== -/
/-! ### Section 1: Foundational Definitions, BST Lookup & Soundness    -/
/-! ==================================================================== -/

def IsSumAvoiding (A B : List Int) : Prop :=
  ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → (b1 + b2) ∉ A

def isSumAvoidingBool (A B : List Int) : Bool :=
  B.all fun b1 =>
    B.all fun b2 =>
      if b1 != b2 then !(A.contains (b1 + b2)) else true

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

def isStrictlySortedBool : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && isStrictlySortedBool (y :: rest)

private theorem isStrictlySortedBool_head_lt :
    ∀ (x : Int) (xs : List Int), isStrictlySortedBool (x :: xs) = true → ∀ y ∈ xs, x < y
  | _, [], _, _, hy => by cases hy
  | x, y :: rest, h, z, hz => by
    unfold isStrictlySortedBool at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hz with rfl | hrest
    · exact h.1
    · have hyz := isStrictlySortedBool_head_lt y rest h.2 z hrest
      omega

theorem isStrictlySortedBool_nodup :
    ∀ xs : List Int, isStrictlySortedBool xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have hlt : ∀ y ∈ xs, x < y := isStrictlySortedBool_head_lt x xs h
    have hrest : isStrictlySortedBool xs = true := by
      cases xs with
      | nil => rfl
      | cons y ys =>
        unfold isStrictlySortedBool at h
        exact (Bool.and_eq_true _ _ ▸ h).2
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, isStrictlySortedBool_nodup xs hrest⟩
    have := hlt x hx
    omega

inductive ITree where
  | empty
  | node (v : Int) (l r : ITree)

def ITree.has (x : Int) : ITree → Bool
  | .empty => false
  | .node v l r => if x == v then true else if x < v then l.has x else r.has x

def ITree.toList : ITree → List Int
  | .empty => []
  | .node v l r => l.toList ++ v :: r.toList

theorem ITree.has_mem_toList (x : Int) : ∀ t : ITree, t.has x = true → x ∈ t.toList
  | .empty, h => by simp [ITree.has] at h
  | .node v l r, h => by
    unfold ITree.has at h
    unfold ITree.toList
    cases hxv : (x == v)
    · rw [hxv] at h
      by_cases hlt : x < v
      · simp [hlt] at h
        exact List.mem_append_left _ (ITree.has_mem_toList x l h)
      · simp [hlt] at h
        exact List.mem_append_right _ (List.mem_cons_of_mem v (ITree.has_mem_toList x r h))
    · have heq : x = v := beq_iff_eq.1 hxv
      subst heq
      simp

theorem all_itree_mem (A B : List Int) (tA : ITree) (ht : tA.toList = A)
    (h : B.all tA.has = true) : ∀ x ∈ B, x ∈ A := by
  intro x hx
  have hxT := (List.all_eq_true.1 h) x hx
  exact ht ▸ ITree.has_mem_toList x tA hxT

def isUpperCliqueBool (tA : ITree) : List Int → Bool
  | [] => true
  | u :: rest => rest.all (fun v => u != v && tA.has (u + v)) && isUpperCliqueBool tA rest

theorem isUpperCliqueBool_sound (A : List Int) (tA : ITree) (ht : tA.toList = A) :
    ∀ C : List Int, isUpperCliqueBool tA C = true →
      ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (u + v) ∈ A
  | [], _, _, hu, _, _, _ => by cases hu
  | u :: us, h, x, hx, y, hy, hne => by
    unfold isUpperCliqueBool at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    have hMemA : ∀ z, tA.has z = true → z ∈ A := fun z hz => ht ▸ ITree.has_mem_toList z tA hz
    rcases List.mem_cons.1 hx with rfl | hxu <;> rcases List.mem_cons.1 hy with rfl | hyu
    · exact absurd rfl hne
    · have hp := h.1 y hyu
      rw [Bool.and_eq_true] at hp
      exact hMemA (x + y) hp.2
    · have hp := h.1 x hxu
      rw [Bool.and_eq_true] at hp
      rw [Int.add_comm]
      exact hMemA (y + x) hp.2
    · exact isUpperCliqueBool_sound A tA ht us h.2 x hxu y hyu hne

def isCliqueCoverTreeBool (tA : ITree) (cand : List Int) (Cs : List (List Int)) : Bool :=
  Cs.all (isUpperCliqueBool tA) && cand.all (fun x => Cs.any (fun C => C.contains x))

theorem isCliqueCoverTreeBool_sound (A : List Int) (tA : ITree) (ht : tA.toList = A)
    (cand : List Int) (Cs : List (List Int))
    (h : isCliqueCoverTreeBool tA cand Cs = true) :
    (∀ C ∈ Cs, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (u + v) ∈ A) ∧ (∀ x ∈ cand, ∃ C ∈ Cs, x ∈ C) := by
  unfold isCliqueCoverTreeBool at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun C hC => isUpperCliqueBool_sound A tA ht C (h.1 C hC), fun x hx => ?_⟩
  rcases List.any_eq_true.1 (h.2 x hx) with ⟨C, hCm, hCh⟩
  exact ⟨C, hCm, List.contains_iff_mem.mp hCh⟩

theorem clique_cover_indep_le
    (A : List Int) (Cs : List (List Int)) (B : List Int)
    (hCliques : ∀ C ∈ Cs, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (u + v) ∈ A)
    (hCover : ∀ x ∈ B, ∃ C ∈ Cs, x ∈ C)
    (hNodup : B.Nodup) (hIndep : IsSumAvoiding A B) :
    B.length ≤ Cs.length := by
  induction Cs generalizing B with
  | nil =>
    cases B with
    | nil => exact Nat.le_refl 0
    | cons b _ =>
      obtain ⟨C, hC, _⟩ := hCover b (by simp)
      cases hC
  | cons C Cs' ih =>
    have hC_cl := hCliques C (by simp)
    have hCs'_cl : ∀ C' ∈ Cs', ∀ u ∈ C', ∀ v ∈ C', u ≠ v → (u + v) ∈ A :=
      fun C' hC' => hCliques C' (by simp [hC'])
    by_cases hex : ∃ b ∈ B, b ∈ C
    · rcases hex with ⟨b, hbB, hbC⟩
      let B' := B.erase b
      have hB'_nodup : B'.Nodup := hNodup.erase b
      have hB'_indep : IsSumAvoiding A B' := fun x hx y hy hne =>
        hIndep x (List.mem_of_mem_erase hx) y (List.mem_of_mem_erase hy) hne
      have hB'_cover : ∀ x ∈ B', ∃ C' ∈ Cs', x ∈ C' := by
        intro x hx
        have hmem := (hNodup.mem_erase_iff).mp hx
        have hx_ne : x ≠ b := hmem.1
        have hxB : x ∈ B := hmem.2
        have hx_not_C : x ∉ C := fun hxC =>
          hIndep x hxB b hbB hx_ne (hC_cl x hxC b hbC hx_ne)
        obtain ⟨C0, hC0m, hxC0⟩ := hCover x hxB
        rcases List.mem_cons.1 hC0m with rfl | hC0_in_tail
        · exact False.elim (hx_not_C hxC0)
        · exact ⟨C0, hC0_in_tail, hxC0⟩
      have hih := ih B' hCs'_cl hB'_cover hB'_nodup hB'_indep
      have hlen : B'.length = B.length - 1 := List.length_erase_of_mem hbB
      have hpos : 0 < B.length := List.length_pos_of_mem hbB
      rw [List.length_cons]
      omega
    · have hB_cover : ∀ x ∈ B, ∃ C' ∈ Cs', x ∈ C' := by
        intro x hxB
        have hx_not_C : x ∉ C := fun hxC => hex ⟨x, hxB, hxC⟩
        obtain ⟨C0, hC0m, hxC0⟩ := hCover x hxB
        rcases List.mem_cons.1 hC0m with rfl | hC0_in_tail
        · exact False.elim (hx_not_C hxC0)
        · exact ⟨C0, hC0_in_tail, hxC0⟩
      exact Nat.le_succ_of_le (ih B hCs'_cl hB_cover hNodup hIndep)

inductive CertTree where
  | leafClique (Cs : List (List Int)) : CertTree
  | branch (v : Int) (tIn tOut : CertTree) : CertTree

def checkCertTree (A : List Int) (tA : ITree) (cand : List Int) (k : Nat) : CertTree → Bool
  | .leafClique Cs => decide (Cs.length ≤ k) && isCliqueCoverTreeBool tA cand Cs
  | .branch v tIn tOut =>
    match k with
    | 0 => false
    | k' + 1 =>
      let candIn := cand.filter (fun u => u != v && !(A.contains (v + u)))
      let candOut := cand.filter (fun u => u != v)
      checkCertTree A tA candIn k' tIn && checkCertTree A tA candOut (k' + 1) tOut

theorem certTree_sound (A : List Int) (tA : ITree) (ht : tA.toList = A) (T : CertTree) :
    ∀ (cand : List Int) (k : Nat),
      checkCertTree A tA cand k T = true →
      ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ cand) → IsSumAvoiding A B → B.length ≤ k := by
  induction T with
  | leafClique Cs =>
    intro cand k hCheck B hNodup hSub hIndep
    unfold checkCertTree at hCheck
    rw [Bool.and_eq_true] at hCheck
    have hLen : Cs.length ≤ k := decide_eq_true_eq.mp hCheck.1
    have hCov := isCliqueCoverTreeBool_sound A tA ht cand Cs hCheck.2
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

theorem certTree_upper_bound (A : List Int) (tA : ITree) (ht : tA.toList = A)
    (k : Nat) (T : CertTree) (h : checkCertTree A tA A k T = true) :
    ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k :=
  certTree_sound A tA ht T A k h

def HasExactMaxSumAvoiding (A : List Int) (k : Nat) : Prop :=
  (∃ B : List Int, B.Nodup ∧ (∀ x ∈ B, x ∈ A) ∧ IsSumAvoiding A B ∧ B.length = k) ∧
  (∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k)

/-! ==================================================================== -/
/-! ### Section 2: Certified Witnesses A52 .. A100                       -/
/-! ==================================================================== -/

def A52 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 36, 40, 44, 48, 52, 84]
def TA52 : ITree := .node 0 (.node (-15) (.node (-32) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty))) (.node (-20) (.node (-24) (.node (-28) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-12) (.node (-14) (.empty) (.empty)) (.node (-10) (.empty) (.empty))) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 13 (.node 12 (.node 10 (.empty) (.empty)) (.empty)) (.node 15 (.node 14 (.empty) (.empty)) (.empty)))) (.node 36 (.node 24 (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))) (.node 32 (.node 28 (.empty) (.empty)) (.empty))) (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B52 : List Int := [-84, -52, -48, -44, -28, -22, -15]
def T52 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, 36, -36, 4, -4], [-44, 44, 40, -40, 8, -8], [15, -15, -3, -5, -1, -7, 1, -9, 3, 5, 13], [-22, 22, -18, 18, 14, -14, 10, -6, -10, 6, -2, 2], [-28, 28, -24, 24, -20, 20, 16, -16, -12, 12]]

theorem A52_card : A52.length = 52 := rfl
theorem TA52_list : TA52.toList = A52 := rfl
theorem A52_nodup : A52.Nodup := isStrictlySortedBool_nodup A52 (by decide)
theorem B52_len : B52.length = 7 := rfl
theorem B52_nodup : B52.Nodup := isStrictlySortedBool_nodup B52 (by decide)
theorem B52_sub : ∀ x ∈ B52, x ∈ A52 := all_itree_mem A52 B52 TA52 TA52_list (by decide)
theorem B52_sumAvoiding : IsSumAvoiding A52 B52 := isSumAvoidingBool_sound A52 B52 (by decide)
theorem T52_valid : checkCertTree A52 TA52 A52 7 T52 = true := by decide

theorem A52_exact_M : HasExactMaxSumAvoiding A52 7 :=
  ⟨⟨B52, B52_nodup, B52_sub, B52_sumAvoiding, B52_len⟩, certTree_upper_bound A52 TA52 TA52_list 7 T52 T52_valid⟩

def A53 : List Int := [-54, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 54]
def TA53 : ITree := .node 0 (.node (-13) (.node (-24) (.node (-30) (.node (-34) (.node (-54) (.empty) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty))) (.node (-16) (.node (-20) (.node (-22) (.empty) (.empty)) (.node (-18) (.empty) (.empty))) (.node (-14) (.node (-15) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-11) (.node (-12) (.empty) (.empty)) (.node (-10) (.empty) (.empty))) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 14 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 11 (.node 9 (.node 8 (.empty) (.empty)) (.node 10 (.empty) (.empty))) (.node 13 (.node 12 (.empty) (.empty)) (.empty)))) (.node 26 (.node 20 (.node 16 (.node 15 (.empty) (.empty)) (.node 18 (.empty) (.empty))) (.node 24 (.node 22 (.empty) (.empty)) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 54 (.node 34 (.empty) (.empty)) (.empty)))))
def B53 : List Int := [-54, -34, -32, -30, -28, -18, -15]
def T53 : CertTree := .leafClique [[-54, 54, 0], [-34, 34, -20, 20], [-32, 32, -22, 22, -2, 2], [-30, 30, -24, 24, 4, -4], [-28, 28, -26, 26, -6, 6], [-13, -15, 15, 13, 11, 9, 7, 5, 3, 1, -1, -11, -9, -7, -5, -3], [-18, 18, -16, 16, -14, 14, 12, -12, 10, -10, -8, 8]]

theorem A53_card : A53.length = 53 := rfl
theorem TA53_list : TA53.toList = A53 := rfl
theorem A53_nodup : A53.Nodup := isStrictlySortedBool_nodup A53 (by decide)
theorem B53_len : B53.length = 7 := rfl
theorem B53_nodup : B53.Nodup := isStrictlySortedBool_nodup B53 (by decide)
theorem B53_sub : ∀ x ∈ B53, x ∈ A53 := all_itree_mem A53 B53 TA53 TA53_list (by decide)
theorem B53_sumAvoiding : IsSumAvoiding A53 B53 := isSumAvoidingBool_sound A53 B53 (by decide)
theorem T53_valid : checkCertTree A53 TA53 A53 7 T53 = true := by decide

theorem A53_exact_M : HasExactMaxSumAvoiding A53 7 :=
  ⟨⟨B53, B53_nodup, B53_sub, B53_sumAvoiding, B53_len⟩, certTree_upper_bound A53 TA53 TA53_list 7 T53 T53_valid⟩

def A54 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA54 : ITree := .node 0 (.node (-16) (.node (-32) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty))) (.node (-22) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)))) (.node (-7) (.node (-10) (.node (-14) (.node (-15) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-8) (.node (-9) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 18 (.node 8 (.node 5 (.node 2 (.node 1 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.empty))) (.node 14 (.node 10 (.node 9 (.empty) (.empty)) (.node 12 (.empty) (.empty))) (.node 16 (.node 15 (.empty) (.empty)) (.empty)))) (.node 36 (.node 26 (.node 22 (.node 20 (.empty) (.empty)) (.node 24 (.empty) (.empty))) (.node 32 (.node 28 (.empty) (.empty)) (.empty))) (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B54 : List Int := [-84, -52, -48, -44, -28, -26, -15]
def T54 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, -36, 36, -4, 4], [15, -15, 9, -5, -3, -7, -1, -9, 1, 5, 7], [44, -44, 40, -40, 8, -8], [-28, 28, -24, 24, -20, 20, 16, -16, 12, -12], [-26, 26, -22, 22, 18, -18, 14, -14, 10, -10, 6, 2, -2, -6]]

theorem A54_card : A54.length = 54 := rfl
theorem TA54_list : TA54.toList = A54 := rfl
theorem A54_nodup : A54.Nodup := isStrictlySortedBool_nodup A54 (by decide)
theorem B54_len : B54.length = 7 := rfl
theorem B54_nodup : B54.Nodup := isStrictlySortedBool_nodup B54 (by decide)
theorem B54_sub : ∀ x ∈ B54, x ∈ A54 := all_itree_mem A54 B54 TA54 TA54_list (by decide)
theorem B54_sumAvoiding : IsSumAvoiding A54 B54 := isSumAvoidingBool_sound A54 B54 (by decide)
theorem T54_valid : checkCertTree A54 TA54 A54 7 T54 = true := by decide

theorem A54_exact_M : HasExactMaxSumAvoiding A54 7 :=
  ⟨⟨B54, B54_nodup, B54_sub, B54_sumAvoiding, B54_len⟩, certTree_upper_bound A54 TA54 TA54_list 7 T54 T54_valid⟩

def A55 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA55 : ITree := .node 0 (.node (-16) (.node (-32) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty))) (.node (-22) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)))) (.node (-7) (.node (-10) (.node (-14) (.node (-15) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-8) (.node (-9) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 16 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 9 (.node 8 (.empty) (.empty)) (.node 10 (.empty) (.empty))) (.node 15 (.node 14 (.empty) (.empty)) (.empty)))) (.node 32 (.node 24 (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))) (.node 28 (.node 26 (.empty) (.empty)) (.empty))) (.node 48 (.node 40 (.node 36 (.empty) (.empty)) (.node 44 (.empty) (.empty))) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B55 : List Int := [-84, -52, -48, -44, -28, -26, -15]
def T55 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, 36, -36, -4, 4], [-44, 44, 40, -40, 8, -8], [15, -15, -3, -5, -1, -7, 1, -9, 3, 5, 7, 9], [-28, 28, -24, 24, -20, 20, 16, -16, 12, -12], [-26, 26, -22, 22, 18, -18, 14, -14, 10, -10, 6, 2, -6, -2]]

theorem A55_card : A55.length = 55 := rfl
theorem TA55_list : TA55.toList = A55 := rfl
theorem A55_nodup : A55.Nodup := isStrictlySortedBool_nodup A55 (by decide)
theorem B55_len : B55.length = 7 := rfl
theorem B55_nodup : B55.Nodup := isStrictlySortedBool_nodup B55 (by decide)
theorem B55_sub : ∀ x ∈ B55, x ∈ A55 := all_itree_mem A55 B55 TA55 TA55_list (by decide)
theorem B55_sumAvoiding : IsSumAvoiding A55 B55 := isSumAvoidingBool_sound A55 B55 (by decide)
theorem T55_valid : checkCertTree A55 TA55 A55 7 T55 = true := by decide

theorem A55_exact_M : HasExactMaxSumAvoiding A55 7 :=
  ⟨⟨B55, B55_nodup, B55_sub, B55_sumAvoiding, B55_len⟩, certTree_upper_bound A55 TA55 TA55_list 7 T55 T55_valid⟩

def A56 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -17, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA56 : ITree := .node 0 (.node (-16) (.node (-28) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.node (-32) (.empty) (.empty)))) (.node (-20) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-17) (.node (-18) (.empty) (.empty)) (.empty)))) (.node (-7) (.node (-10) (.node (-14) (.node (-15) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-8) (.node (-9) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 16 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 9 (.node 8 (.empty) (.empty)) (.node 10 (.empty) (.empty))) (.node 15 (.node 14 (.empty) (.empty)) (.empty)))) (.node 32 (.node 24 (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))) (.node 28 (.node 26 (.empty) (.empty)) (.empty))) (.node 48 (.node 40 (.node 36 (.empty) (.empty)) (.node 44 (.empty) (.empty))) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B56 : List Int := [-84, -52, -48, -44, -28, -26, -17]
def T56 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, -36, 36, 4, -4], [-44, 44, -40, 40, 8, -8], [15, -15, -5, -3, -1, 1, 3, 5, 7, 9, -7, -9, -17], [-28, 28, -24, 24, -20, 20, 16, -16, 12, -12], [-26, 26, -22, 22, -18, 18, -14, 14, -10, 10, -6, 6, 2, -2]]

theorem A56_card : A56.length = 56 := rfl
theorem TA56_list : TA56.toList = A56 := rfl
theorem A56_nodup : A56.Nodup := isStrictlySortedBool_nodup A56 (by decide)
theorem B56_len : B56.length = 7 := rfl
theorem B56_nodup : B56.Nodup := isStrictlySortedBool_nodup B56 (by decide)
theorem B56_sub : ∀ x ∈ B56, x ∈ A56 := all_itree_mem A56 B56 TA56 TA56_list (by decide)
theorem B56_sumAvoiding : IsSumAvoiding A56 B56 := isSumAvoidingBool_sound A56 B56 (by decide)
theorem T56_valid : checkCertTree A56 TA56 A56 7 T56 = true := by decide

theorem A56_exact_M : HasExactMaxSumAvoiding A56 7 :=
  ⟨⟨B56, B56_nodup, B56_sub, B56_sumAvoiding, B56_len⟩, certTree_upper_bound A56 TA56 TA56_list 7 T56 T56_valid⟩

def A57 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -17, -16, -15, -14, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA57 : ITree := .node 0 (.node (-16) (.node (-28) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.node (-32) (.empty) (.empty)))) (.node (-20) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-17) (.node (-18) (.empty) (.empty)) (.empty)))) (.node (-8) (.node (-11) (.node (-14) (.node (-15) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.empty))))) (.node 17 (.node 9 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 14 (.node 11 (.node 10 (.empty) (.empty)) (.node 12 (.empty) (.empty))) (.node 16 (.node 15 (.empty) (.empty)) (.empty)))) (.node 32 (.node 24 (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))) (.node 28 (.node 26 (.empty) (.empty)) (.empty))) (.node 48 (.node 40 (.node 36 (.empty) (.empty)) (.node 44 (.empty) (.empty))) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B57 : List Int := [-84, -52, -48, -44, -28, -26, -17]
def T57 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, -36, 36, -4, 4], [-44, 44, -40, 40, -8, 8], [-17, 17, -15, 15, 7, 11, 9, 5, 3, -3, -5, -7, -11, -9], [-28, 28, -24, 24, -16, -20, 20, 16, 12, -12], [-26, 26, -18, -22, 22, 18, -10, 10, 14, -14, -6, 6, 2, -2]]

theorem A57_card : A57.length = 57 := rfl
theorem TA57_list : TA57.toList = A57 := rfl
theorem A57_nodup : A57.Nodup := isStrictlySortedBool_nodup A57 (by decide)
theorem B57_len : B57.length = 7 := rfl
theorem B57_nodup : B57.Nodup := isStrictlySortedBool_nodup B57 (by decide)
theorem B57_sub : ∀ x ∈ B57, x ∈ A57 := all_itree_mem A57 B57 TA57 TA57_list (by decide)
theorem B57_sumAvoiding : IsSumAvoiding A57 B57 := isSumAvoidingBool_sound A57 B57 (by decide)
theorem T57_valid : checkCertTree A57 TA57 A57 7 T57 = true := by decide

theorem A57_exact_M : HasExactMaxSumAvoiding A57 7 :=
  ⟨⟨B57, B57_nodup, B57_sub, B57_sumAvoiding, B57_len⟩, certTree_upper_bound A57 TA57 TA57_list 7 T57 T57_valid⟩

def A58 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA58 : ITree := .node 1 (.node (-15) (.node (-28) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.node (-32) (.empty) (.empty)))) (.node (-20) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-10) (.node (-12) (.node (-14) (.empty) (.empty)) (.node (-11) (.empty) (.empty))) (.node (-8) (.node (-9) (.empty) (.empty)) (.node (-7) (.empty) (.empty)))) (.node (-2) (.node (-4) (.node (-5) (.empty) (.empty)) (.node (-3) (.empty) (.empty))) (.node 0 (.node (-1) (.empty) (.empty)) (.empty))))) (.node 16 (.node 9 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 13 (.node 11 (.node 10 (.empty) (.empty)) (.node 12 (.empty) (.empty))) (.node 15 (.node 14 (.empty) (.empty)) (.empty)))) (.node 32 (.node 24 (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))) (.node 28 (.node 26 (.empty) (.empty)) (.empty))) (.node 48 (.node 40 (.node 36 (.empty) (.empty)) (.node 44 (.empty) (.empty))) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B58 : List Int := [-84, -52, -48, -44, -28, -26, -15]
def T58 : CertTree := .branch (0) (.leafClique []) (.branch (-84) (.leafClique [[-52, -32, 28, 24, 20, 16, 12, 8, 4], [-48, -36, 26, 22, -4], [-44, -40, 18, -8], [-28, -24, -20, -16, -12, 14, 10, 6, 2], [-26, -22, -18, -14, -10, -6, -2, 15, 11], [-15, -11, 9, -9, 7, -7, 5, -5, 3, -3, 1, -1, 13]]) (.leafClique [[84, -52, -32], [52, 32, -48, -36, -4], [48, 36, -44, -40, -8, 4], [44, 40, 8, -18, -26, -22], [-15, -11, 15, -9, -7, -5, 13, -3, 11, -1, 9, 1, 7, 3, 5], [-14, 28, 24, 20, 16, 12, -10, -6, -2, -12], [2, 26, 22, 18, 14, 10, 6, -28, -24, -20, -16]]))

theorem A58_card : A58.length = 58 := rfl
theorem TA58_list : TA58.toList = A58 := rfl
theorem A58_nodup : A58.Nodup := isStrictlySortedBool_nodup A58 (by decide)
theorem B58_len : B58.length = 7 := rfl
theorem B58_nodup : B58.Nodup := isStrictlySortedBool_nodup B58 (by decide)
theorem B58_sub : ∀ x ∈ B58, x ∈ A58 := all_itree_mem A58 B58 TA58 TA58_list (by decide)
theorem B58_sumAvoiding : IsSumAvoiding A58 B58 := isSumAvoidingBool_sound A58 B58 (by decide)
theorem T58_valid : checkCertTree A58 TA58 A58 7 T58 = true := by decide

theorem A58_exact_M : HasExactMaxSumAvoiding A58 7 :=
  ⟨⟨B58, B58_nodup, B58_sub, B58_sumAvoiding, B58_len⟩, certTree_upper_bound A58 TA58 TA58_list 7 T58 T58_valid⟩

def A59 : List Int := [-84, -52, -48, -44, -40, -36, -32, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 52, 84]
def TA59 : ITree := .node 0 (.node (-15) (.node (-28) (.node (-44) (.node (-52) (.node (-84) (.empty) (.empty)) (.node (-48) (.empty) (.empty))) (.node (-36) (.node (-40) (.empty) (.empty)) (.node (-32) (.empty) (.empty)))) (.node (-20) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)))) (.node (-7) (.node (-11) (.node (-13) (.node (-14) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.node (-8) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 15 (.node 8 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.node 7 (.empty) (.empty)))) (.node 12 (.node 10 (.node 9 (.empty) (.empty)) (.node 11 (.empty) (.empty))) (.node 14 (.node 13 (.empty) (.empty)) (.empty)))) (.node 32 (.node 22 (.node 18 (.node 16 (.empty) (.empty)) (.node 20 (.empty) (.empty))) (.node 26 (.node 24 (.empty) (.empty)) (.node 28 (.empty) (.empty)))) (.node 48 (.node 40 (.node 36 (.empty) (.empty)) (.node 44 (.empty) (.empty))) (.node 84 (.node 52 (.empty) (.empty)) (.empty)))))
def B59 : List Int := [-84, -52, -48, -44, -28, -26, -15]
def T59 : CertTree := .leafClique [[-84, 84, 0], [-52, 52, -32, 32], [-48, 48, -36, 36, 4, -4], [-44, 44, -40, 40, 8, -8], [-28, 28, -24, 24, -20, 20, 16, -16, 12, -12], [-15, 15, 9, 7, 11, 5, 3, 1, -1, 13, -3, -5, -7, -9, -11, -13], [-26, 26, 22, -22, 18, -18, 14, -14, 10, -10, 6, -6, 2, -2]]

theorem A59_card : A59.length = 59 := rfl
theorem TA59_list : TA59.toList = A59 := rfl
theorem A59_nodup : A59.Nodup := isStrictlySortedBool_nodup A59 (by decide)
theorem B59_len : B59.length = 7 := rfl
theorem B59_nodup : B59.Nodup := isStrictlySortedBool_nodup B59 (by decide)
theorem B59_sub : ∀ x ∈ B59, x ∈ A59 := all_itree_mem A59 B59 TA59 TA59_list (by decide)
theorem B59_sumAvoiding : IsSumAvoiding A59 B59 := isSumAvoidingBool_sound A59 B59 (by decide)
theorem T59_valid : checkCertTree A59 TA59 A59 7 T59 = true := by decide

theorem A59_exact_M : HasExactMaxSumAvoiding A59 7 :=
  ⟨⟨B59, B59_nodup, B59_sub, B59_sumAvoiding, B59_len⟩, certTree_upper_bound A59 TA59 TA59_list 7 T59 T59_valid⟩

def A60 : List Int := [-96, -84, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 84, 96, 132]
def TA60 : ITree := .node 1 (.node (-18) (.node (-36) (.node (-52) (.node (-84) (.node (-96) (.empty) (.empty)) (.node (-56) (.empty) (.empty))) (.node (-44) (.node (-48) (.empty) (.empty)) (.node (-40) (.empty) (.empty)))) (.node (-26) (.node (-30) (.node (-32) (.empty) (.empty)) (.node (-28) (.empty) (.empty))) (.node (-22) (.node (-24) (.empty) (.empty)) (.node (-20) (.empty) (.empty))))) (.node (-6) (.node (-10) (.node (-14) (.node (-16) (.empty) (.empty)) (.node (-12) (.empty) (.empty))) (.node (-8) (.node (-9) (.empty) (.empty)) (.node (-7) (.empty) (.empty)))) (.node (-2) (.node (-4) (.node (-5) (.empty) (.empty)) (.node (-3) (.empty) (.empty))) (.node 0 (.node (-1) (.empty) (.empty)) (.empty))))) (.node 22 (.node 9 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 16 (.node 12 (.node 10 (.empty) (.empty)) (.node 14 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.empty)))) (.node 44 (.node 30 (.node 26 (.node 24 (.empty) (.empty)) (.node 28 (.empty) (.empty))) (.node 36 (.node 32 (.empty) (.empty)) (.node 40 (.empty) (.empty)))) (.node 84 (.node 52 (.node 48 (.empty) (.empty)) (.node 56 (.empty) (.empty))) (.node 132 (.node 96 (.empty) (.empty)) (.empty)))))
def B60 : List Int := [-96, -84, -56, -52, -48, -30, -24, -9]
def T60 : CertTree := .branch (-28) (.leafClique [[-32, -52], [-84, 132], [-40, -44, 96], [-36, -48], [-96], [-22, -30, -26, -18, -14, -10, -6], [-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]]) (.branch (28) (.leafClique [[132, -96], [32, 52], [96, 36], [84, 48], [40, 44], [30, 26, 22, 18, 14, 10, 6], [9, 7, 5, 3, 1, -1, -3, -5, -7, -9]]) (.leafClique [[132, -96, 0], [96, -84, 36, -12], [84, -56, 48, -40], [3, 9, 7, 5, 1, -1, -3, -5, -7, -9], [56, -52, -44, 40, -4], [52, -48, 44, -36, -8, 4], [30, -30, 26, 22, -26, -22, -18, 18, -14, 14, 10, -10, 6, -6, 2, -2], [32, 24, -32, -24, 20, -20, 16, -16, 12, 8]]))

theorem A60_card : A60.length = 60 := rfl
theorem TA60_list : TA60.toList = A60 := rfl
theorem A60_nodup : A60.Nodup := isStrictlySortedBool_nodup A60 (by decide)
theorem B60_len : B60.length = 8 := rfl
theorem B60_nodup : B60.Nodup := isStrictlySortedBool_nodup B60 (by decide)
theorem B60_sub : ∀ x ∈ B60, x ∈ A60 := all_itree_mem A60 B60 TA60 TA60_list (by decide)
theorem B60_sumAvoiding : IsSumAvoiding A60 B60 := isSumAvoidingBool_sound A60 B60 (by decide)
theorem T60_valid : checkCertTree A60 TA60 A60 8 T60 = true := by decide

theorem A60_exact_M : HasExactMaxSumAvoiding A60 8 :=
  ⟨⟨B60, B60_nodup, B60_sub, B60_sumAvoiding, B60_len⟩, certTree_upper_bound A60 TA60 TA60_list 8 T60 T60_valid⟩

def A61 : List Int := [-132, -96, -84, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 84, 96, 132]
def TA61 : ITree := .node 0 (.node (-20) (.node (-40) (.node (-56) (.node (-96) (.node (-132) (.empty) (.empty)) (.node (-84) (.empty) (.empty))) (.node (-48) (.node (-52) (.empty) (.empty)) (.node (-44) (.empty) (.empty)))) (.node (-28) (.node (-32) (.node (-36) (.empty) (.empty)) (.node (-30) (.empty) (.empty))) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))))) (.node (-7) (.node (-12) (.node (-16) (.node (-18) (.empty) (.empty)) (.node (-14) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.node (-8) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty))))) (.node 22 (.node 8 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.node 7 (.empty) (.empty)))) (.node 14 (.node 10 (.node 9 (.empty) (.empty)) (.node 12 (.empty) (.empty))) (.node 18 (.node 16 (.empty) (.empty)) (.node 20 (.empty) (.empty))))) (.node 44 (.node 30 (.node 26 (.node 24 (.empty) (.empty)) (.node 28 (.empty) (.empty))) (.node 36 (.node 32 (.empty) (.empty)) (.node 40 (.empty) (.empty)))) (.node 84 (.node 52 (.node 48 (.empty) (.empty)) (.node 56 (.empty) (.empty))) (.node 132 (.node 96 (.empty) (.empty)) (.empty)))))
def B61 : List Int := [-132, -96, -84, -56, -52, -30, -24, -9]
def T61 : CertTree := .branch (-28) (.leafClique [[-32, -52], [-40, -44, 96], [-132, 132], [-96, -36], [-84, -48], [-22, -30, -26, -18, -14, -10, -6], [-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]]) (.branch (28) (.leafClique [[32, 52], [132, -132], [40, 44, -96], [96, 36], [84, 48], [30, 26, 22, 18, 14, 10, 6], [9, 7, 5, 3, 1, -1, -3, -5, -7, -9]]) (.leafClique [[-132, 132, 0], [-96, -36, 84, 48], [-84, -48, 96, 36], [-56, -40, 56, 40], [-9, -7, -5, -3, -1, 1, 3, 5, 7, 9], [-52, -44, -4, 52, 44, 4], [-30, -26, -22, -18, -14, -10, -6, -2, 18, 14, 10, 6, 2, 30, 26, 22], [-24, -32, -20, -16, -12, -8, 24, 32, 20, 16, 12, 8]]))

theorem A61_card : A61.length = 61 := rfl
theorem TA61_list : TA61.toList = A61 := rfl
theorem A61_nodup : A61.Nodup := isStrictlySortedBool_nodup A61 (by decide)
theorem B61_len : B61.length = 8 := rfl
theorem B61_nodup : B61.Nodup := isStrictlySortedBool_nodup B61 (by decide)
theorem B61_sub : ∀ x ∈ B61, x ∈ A61 := all_itree_mem A61 B61 TA61 TA61_list (by decide)
theorem B61_sumAvoiding : IsSumAvoiding A61 B61 := isSumAvoidingBool_sound A61 B61 (by decide)
theorem T61_valid : checkCertTree A61 TA61 A61 8 T61 = true := by decide

theorem A61_exact_M : HasExactMaxSumAvoiding A61 8 :=
  ⟨⟨B61, B61_nodup, B61_sub, B61_sumAvoiding, B61_len⟩, certTree_upper_bound A61 TA61 TA61_list 8 T61 T61_valid⟩

def A62 : List Int := [-96, -84, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 84, 96, 132]
def TA62 : ITree := .node 1 (.node (-18) (.node (-36) (.node (-52) (.node (-84) (.node (-96) (.empty) (.empty)) (.node (-56) (.empty) (.empty))) (.node (-44) (.node (-48) (.empty) (.empty)) (.node (-40) (.empty) (.empty)))) (.node (-26) (.node (-30) (.node (-32) (.empty) (.empty)) (.node (-28) (.empty) (.empty))) (.node (-22) (.node (-24) (.empty) (.empty)) (.node (-20) (.empty) (.empty))))) (.node (-7) (.node (-12) (.node (-15) (.node (-16) (.empty) (.empty)) (.node (-14) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.node (-8) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 22 (.node 9 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 15 (.node 12 (.node 10 (.empty) (.empty)) (.node 14 (.empty) (.empty))) (.node 18 (.node 16 (.empty) (.empty)) (.node 20 (.empty) (.empty))))) (.node 44 (.node 30 (.node 26 (.node 24 (.empty) (.empty)) (.node 28 (.empty) (.empty))) (.node 36 (.node 32 (.empty) (.empty)) (.node 40 (.empty) (.empty)))) (.node 84 (.node 52 (.node 48 (.empty) (.empty)) (.node 56 (.empty) (.empty))) (.node 132 (.node 96 (.empty) (.empty)) (.empty)))))
def B62 : List Int := [-96, -84, -56, -52, -48, -30, -24, -15]
def T62 : CertTree := .branch (-28) (.leafClique [[-32, -52], [-84, 132], [-40, -44, 96], [-36, -48], [-96], [-26, -30, -22, -18, -14, -10, -6], [-7, -15, -9, -5, -3, -1, 1, 3, 5, 7, 9, 15]]) (.branch (28) (.leafClique [[132, -96], [32, 52], [96, 36], [84, 48], [40, 44], [26, 30, 22, 18, 14, 10, 6], [15, 7, 9, 5, 3, 1, -1, -3, -5, -7, -9, -15]]) (.leafClique [[132, -96, 0], [96, -84, 36, -12], [84, -56, 48, -40], [56, -52, -44, 40, -4], [52, -48, 44, -36, -8, 4], [3, 15, 9, 7, 5, 1, -1, -3, -5, -7, -9, -15], [32, -32, -24, 24, 20, -20, 16, -16, 12, 8], [30, 26, -30, -26, 22, -22, 18, -18, 14, -14, 10, -10, 2, -2, -6, 6]]))

theorem A62_card : A62.length = 62 := rfl
theorem TA62_list : TA62.toList = A62 := rfl
theorem A62_nodup : A62.Nodup := isStrictlySortedBool_nodup A62 (by decide)
theorem B62_len : B62.length = 8 := rfl
theorem B62_nodup : B62.Nodup := isStrictlySortedBool_nodup B62 (by decide)
theorem B62_sub : ∀ x ∈ B62, x ∈ A62 := all_itree_mem A62 B62 TA62 TA62_list (by decide)
theorem B62_sumAvoiding : IsSumAvoiding A62 B62 := isSumAvoidingBool_sound A62 B62 (by decide)
theorem T62_valid : checkCertTree A62 TA62 A62 8 T62 = true := by decide

theorem A62_exact_M : HasExactMaxSumAvoiding A62 8 :=
  ⟨⟨B62, B62_nodup, B62_sub, B62_sumAvoiding, B62_len⟩, certTree_upper_bound A62 TA62 TA62_list 8 T62 T62_valid⟩

def A63 : List Int := [-132, -96, -84, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 84, 96, 132]
def TA63 : ITree := .node 0 (.node (-20) (.node (-40) (.node (-56) (.node (-96) (.node (-132) (.empty) (.empty)) (.node (-84) (.empty) (.empty))) (.node (-48) (.node (-52) (.empty) (.empty)) (.node (-44) (.empty) (.empty)))) (.node (-28) (.node (-32) (.node (-36) (.empty) (.empty)) (.node (-30) (.empty) (.empty))) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-18) (.empty) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 20 (.node 8 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.node 7 (.empty) (.empty)))) (.node 14 (.node 10 (.node 9 (.empty) (.empty)) (.node 12 (.empty) (.empty))) (.node 16 (.node 15 (.empty) (.empty)) (.node 18 (.empty) (.empty))))) (.node 40 (.node 28 (.node 24 (.node 22 (.empty) (.empty)) (.node 26 (.empty) (.empty))) (.node 32 (.node 30 (.empty) (.empty)) (.node 36 (.empty) (.empty)))) (.node 56 (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty))) (.node 96 (.node 84 (.empty) (.empty)) (.node 132 (.empty) (.empty))))))
def B63 : List Int := [-132, -96, -84, -56, -52, -30, -24, -15]
def T63 : CertTree := .branch (-28) (.leafClique [[-32, -52], [-40, -44, 96], [-132, 132], [-96, -36], [-84, -48], [-26, -30, -22, -18, -14, -10, -6], [-7, -15, -9, -5, -3, -1, 1, 3, 5, 7, 9, 15]]) (.branch (28) (.leafClique [[32, 52], [132, -132], [40, 44, -96], [96, 36], [84, 48], [26, 30, 22, 18, 14, 10, 6], [15, 7, 9, 5, 3, -1, 1, -3, -5, -7, -9, -15]]) (.leafClique [[-132, 132, 0], [-96, -36, 84, 48], [-84, -48, 96, 36], [-56, -40, 56, 40], [-52, -44, -4, 52, 44, 4], [-15, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 15], [-30, -26, -22, -18, -14, -10, -2, -6, 18, 14, 10, 2, 6, 26, 30, 22], [-24, -32, -20, -16, -12, -8, 24, 32, 20, 16, 12, 8]]))

theorem A63_card : A63.length = 63 := rfl
theorem TA63_list : TA63.toList = A63 := rfl
theorem A63_nodup : A63.Nodup := isStrictlySortedBool_nodup A63 (by decide)
theorem B63_len : B63.length = 8 := rfl
theorem B63_nodup : B63.Nodup := isStrictlySortedBool_nodup B63 (by decide)
theorem B63_sub : ∀ x ∈ B63, x ∈ A63 := all_itree_mem A63 B63 TA63 TA63_list (by decide)
theorem B63_sumAvoiding : IsSumAvoiding A63 B63 := isSumAvoidingBool_sound A63 B63 (by decide)
theorem T63_valid : checkCertTree A63 TA63 A63 8 T63 = true := by decide

theorem A63_exact_M : HasExactMaxSumAvoiding A63 8 :=
  ⟨⟨B63, B63_nodup, B63_sub, B63_sumAvoiding, B63_len⟩, certTree_upper_bound A63 TA63 TA63_list 8 T63 T63_valid⟩

def A64 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -48, -44, -40, -36, -32, -30, -28, -24, -20, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA64 : ITree := .node 1 (.node (-20) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.empty) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-28) (.node (-30) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-7) (.node (-12) (.node (-16) (.node (-18) (.empty) (.empty)) (.node (-14) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.node (-8) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 28 (.node 9 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 16 (.node 12 (.node 10 (.empty) (.empty)) (.node 14 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 24 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.empty) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B64 : List Int := [-168, -104, -96, -88, -56, -44, -30, -9]
def T64 : CertTree := .branch (4) (.leafClique [[9, 7], [30, 18, -30], [168, -168], [56, -56], [-64, 64, 104, -104], [-72, -96, 72, 96], [-80, -88, 80, 88]]) (.leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-5, -3, -7, -1, -9, 1, 3, 5, 9, 7], [-96, 96, 72, -72, -8, 8], [-88, 88, -80, 80, -16, 16], [30, -30, -18, 18, 14, -14, -10, 10, -6, 6, -2, 2], [52, 44, -44, -36, 36, -28, 28, 20, -20, 12, -12, -4], [56, -56, -48, 48, 40, -40, 32, -32, 24, -24]])

theorem A64_card : A64.length = 64 := rfl
theorem TA64_list : TA64.toList = A64 := rfl
theorem A64_nodup : A64.Nodup := isStrictlySortedBool_nodup A64 (by decide)
theorem B64_len : B64.length = 8 := rfl
theorem B64_nodup : B64.Nodup := isStrictlySortedBool_nodup B64 (by decide)
theorem B64_sub : ∀ x ∈ B64, x ∈ A64 := all_itree_mem A64 B64 TA64 TA64_list (by decide)
theorem B64_sumAvoiding : IsSumAvoiding A64 B64 := isSumAvoidingBool_sound A64 B64 (by decide)
theorem T64_valid : checkCertTree A64 TA64 A64 8 T64 = true := by decide

theorem A64_exact_M : HasExactMaxSumAvoiding A64 8 :=
  ⟨⟨B64, B64_nodup, B64_sub, B64_sumAvoiding, B64_len⟩, certTree_upper_bound A64 TA64 TA64_list 8 T64 T64_valid⟩

def A65 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -24, -20, -18, -16, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA65 : ITree := .node 0 (.node (-24) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-36) (.node (-44) (.node (-48) (.empty) (.empty)) (.node (-40) (.empty) (.empty))) (.node (-30) (.node (-32) (.empty) (.empty)) (.node (-28) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-18) (.node (-20) (.empty) (.empty)) (.node (-16) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 28 (.node 9 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 16 (.node 12 (.node 10 (.empty) (.empty)) (.node 14 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 24 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.empty) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B65 : List Int := [-168, -104, -96, -88, -56, -52, -30, -9]
def T65 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [9, -7, -5, -9, -3, -1, 1, 3, 5, 7], [96, -96, -72, 72, 8, -8], [88, -88, 80, -80, 16, -16], [-30, 30, 18, -18, -14, 14, -10, 10, 6, -6, -2, 2], [56, -56, 48, -48, -40, 40, -32, 32, -24, 24], [52, -52, -44, 44, 36, -36, 28, -28, -20, 20, -12, 12, 4, -4]]

theorem A65_card : A65.length = 65 := rfl
theorem TA65_list : TA65.toList = A65 := rfl
theorem A65_nodup : A65.Nodup := isStrictlySortedBool_nodup A65 (by decide)
theorem B65_len : B65.length = 8 := rfl
theorem B65_nodup : B65.Nodup := isStrictlySortedBool_nodup B65 (by decide)
theorem B65_sub : ∀ x ∈ B65, x ∈ A65 := all_itree_mem A65 B65 TA65 TA65_list (by decide)
theorem B65_sumAvoiding : IsSumAvoiding A65 B65 := isSumAvoidingBool_sound A65 B65 (by decide)
theorem T65_valid : checkCertTree A65 TA65 A65 8 T65 = true := by decide

theorem A65_exact_M : HasExactMaxSumAvoiding A65 8 :=
  ⟨⟨B65, B65_nodup, B65_sub, B65_sumAvoiding, B65_len⟩, certTree_upper_bound A65 TA65 TA65_list 8 T65 T65_valid⟩

def A66 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -48, -44, -40, -36, -32, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA66 : ITree := .node 1 (.node (-20) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.empty) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-24) (.node (-28) (.empty) (.empty)) (.node (-22) (.empty) (.empty))))) (.node (-7) (.node (-12) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty))) (.node (-9) (.node (-10) (.empty) (.empty)) (.node (-8) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.empty) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 28 (.node 12 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 9 (.node 8 (.empty) (.empty)) (.node 10 (.empty) (.empty)))) (.node 18 (.node 15 (.node 14 (.empty) (.empty)) (.node 16 (.empty) (.empty))) (.node 22 (.node 20 (.empty) (.empty)) (.node 24 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.empty) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B66 : List Int := [-168, -104, -96, -88, -56, -44, -22, -15]
def T66 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, 64, -64], [-96, 96, -72, 72, 8, -8], [-88, 88, -80, 80, 16, -16], [15, 3, 9, 5, 1, -1, -3, -5, -7, -9, -15], [30, 22, -22, -18, 18, -14, 14, 10, -10, -2, 2, 6, -6], [56, -56, -48, 48, 40, -40, -32, 32, 24, -24], [52, 44, -44, 36, -36, -28, 28, -20, 20, 12, -12, 4, -4]]

theorem A66_card : A66.length = 66 := rfl
theorem TA66_list : TA66.toList = A66 := rfl
theorem A66_nodup : A66.Nodup := isStrictlySortedBool_nodup A66 (by decide)
theorem B66_len : B66.length = 8 := rfl
theorem B66_nodup : B66.Nodup := isStrictlySortedBool_nodup B66 (by decide)
theorem B66_sub : ∀ x ∈ B66, x ∈ A66 := all_itree_mem A66 B66 TA66 TA66_list (by decide)
theorem B66_sumAvoiding : IsSumAvoiding A66 B66 := isSumAvoidingBool_sound A66 B66 (by decide)
theorem T66_valid : checkCertTree A66 TA66 A66 8 T66 = true := by decide

theorem A66_exact_M : HasExactMaxSumAvoiding A66 8 :=
  ⟨⟨B66, B66_nodup, B66_sub, B66_sumAvoiding, B66_len⟩, certTree_upper_bound A66 TA66 TA66_list 8 T66 T66_valid⟩

def A67 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA67 : ITree := .node 0 (.node (-22) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-36) (.node (-44) (.node (-48) (.empty) (.empty)) (.node (-40) (.empty) (.empty))) (.node (-28) (.node (-32) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 24 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 6 (.empty) (.empty)) (.node 9 (.empty) (.empty)))) (.node 16 (.node 14 (.node 12 (.empty) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B67 : List Int := [-168, -104, -96, -88, -56, -52, -22, -15]
def T67 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, 8, -8], [15, 9, -9, -7, -15, -5, -3, -1, 1, 3, 5], [88, -88, 80, -80, 16, -16], [22, 30, -22, 18, -18, -14, 14, -10, 10, -2, 2, -6, 6], [-56, 56, 48, -48, 40, -40, 32, -32, 24, -24], [52, -52, -44, 44, -36, 36, -28, 28, 20, -20, 12, -12, 4, -4]]

theorem A67_card : A67.length = 67 := rfl
theorem TA67_list : TA67.toList = A67 := rfl
theorem A67_nodup : A67.Nodup := isStrictlySortedBool_nodup A67 (by decide)
theorem B67_len : B67.length = 8 := rfl
theorem B67_nodup : B67.Nodup := isStrictlySortedBool_nodup B67 (by decide)
theorem B67_sub : ∀ x ∈ B67, x ∈ A67 := all_itree_mem A67 B67 TA67 TA67_list (by decide)
theorem B67_sumAvoiding : IsSumAvoiding A67 B67 := isSumAvoidingBool_sound A67 B67 (by decide)
theorem T67_valid : checkCertTree A67 TA67 A67 8 T67 = true := by decide

theorem A67_exact_M : HasExactMaxSumAvoiding A67 8 :=
  ⟨⟨B67, B67_nodup, B67_sub, B67_sumAvoiding, B67_len⟩, certTree_upper_bound A67 TA67 TA67_list 8 T67 T67_valid⟩

def A68 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA68 : ITree := .node 0 (.node (-22) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-28) (.node (-30) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 24 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 6 (.empty) (.empty)) (.node 9 (.empty) (.empty)))) (.node 16 (.node 14 (.node 12 (.empty) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B68 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T68 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, 64, -64], [-96, 96, -72, 72, -8, 8], [9, -9, -15, -7, -5, -3, -1, 1, 3, 5, 15], [88, -88, 80, -80, 16, -16], [56, -56, -48, 48, -40, 40, 32, -32, 24, -24], [-30, 30, -22, 22, -18, 18, 14, -14, -10, 10, -2, 2, -6, 6], [-52, 52, -44, 44, -36, 36, -28, 28, -20, 20, -12, 12, 4, -4]]

theorem A68_card : A68.length = 68 := rfl
theorem TA68_list : TA68.toList = A68 := rfl
theorem A68_nodup : A68.Nodup := isStrictlySortedBool_nodup A68 (by decide)
theorem B68_len : B68.length = 8 := rfl
theorem B68_nodup : B68.Nodup := isStrictlySortedBool_nodup B68 (by decide)
theorem B68_sub : ∀ x ∈ B68, x ∈ A68 := all_itree_mem A68 B68 TA68 TA68_list (by decide)
theorem B68_sumAvoiding : IsSumAvoiding A68 B68 := isSumAvoidingBool_sound A68 B68 (by decide)
theorem T68_valid : checkCertTree A68 TA68 A68 8 T68 = true := by decide

theorem A68_exact_M : HasExactMaxSumAvoiding A68 8 :=
  ⟨⟨B68, B68_nodup, B68_sub, B68_sumAvoiding, B68_len⟩, certTree_upper_bound A68 TA68 TA68_list 8 T68 T68_valid⟩

def A69 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA69 : ITree := .node 0 (.node (-22) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-28) (.node (-30) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.empty) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 26 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 6 (.empty) (.empty)) (.node 9 (.empty) (.empty)))) (.node 18 (.node 15 (.node 14 (.node 12 (.empty) (.empty)) (.empty)) (.node 16 (.empty) (.empty))) (.node 22 (.node 20 (.empty) (.empty)) (.node 24 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B69 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T69 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, -8, 8], [9, -9, -15, -7, -5, -3, -1, 1, 3, 5, 15], [88, -88, 80, -80, 16, -16], [-56, 56, 48, -48, -40, 40, 32, -32, 24, -24], [-52, 52, 44, -44, 36, -36, -28, 28, 20, -20, 12, -12, -4, 4], [-30, 26, 30, -22, 22, -18, 18, 14, -14, -10, 10, 2, -2, 6, -6]]

theorem A69_card : A69.length = 69 := rfl
theorem TA69_list : TA69.toList = A69 := rfl
theorem A69_nodup : A69.Nodup := isStrictlySortedBool_nodup A69 (by decide)
theorem B69_len : B69.length = 8 := rfl
theorem B69_nodup : B69.Nodup := isStrictlySortedBool_nodup B69 (by decide)
theorem B69_sub : ∀ x ∈ B69, x ∈ A69 := all_itree_mem A69 B69 TA69 TA69_list (by decide)
theorem B69_sumAvoiding : IsSumAvoiding A69 B69 := isSumAvoidingBool_sound A69 B69 (by decide)
theorem T69_valid : checkCertTree A69 TA69 A69 8 T69 = true := by decide

theorem A69_exact_M : HasExactMaxSumAvoiding A69 8 :=
  ⟨⟨B69, B69_nodup, B69_sub, B69_sumAvoiding, B69_len⟩, certTree_upper_bound A69 TA69 TA69_list 8 T69 T69_valid⟩

def A70 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA70 : ITree := .node 1 (.node (-22) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-28) (.node (-30) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-10) (.node (-12) (.empty) (.empty)) (.node (-9) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 26 (.node 10 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 8 (.node 7 (.empty) (.empty)) (.node 9 (.empty) (.empty)))) (.node 18 (.node 15 (.node 14 (.node 12 (.empty) (.empty)) (.empty)) (.node 16 (.empty) (.empty))) (.node 22 (.node 20 (.empty) (.empty)) (.node 24 (.empty) (.empty))))) (.node 56 (.node 40 (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))) (.node 48 (.node 44 (.empty) (.empty)) (.node 52 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.empty) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B70 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T70 : CertTree := .branch (-168) (.leafClique [[-104, -64, 56, 48, 40, 32, 24, 16, 8], [-96, -72, 52, 44, -8], [-88, -80, 36, -16], [-56, -48, -40, -32, -24, 28, 20, 12, 4], [-52, -44, -36, -28, -20, -12, -4, 30, 22], [-15, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 15], [-30, -22, -18, 18, 14, -14, 10, -10, 6, -2, 2, -6, 26]]) (.branch (4) (.leafClique [[30, -30], [9, 7, 15, -15], [168, -64, -104], [56, -72, -96], [64, 104, -80, -88], [72, 96], [80, 88]]) (.leafClique [[168, -104, -64, 0], [104, -96, -72, 64, -8], [96, -88, -80, 72, -16, 8], [88, 80, -56, -48, -40, -32, -24, 16], [3, 5, 1, -1, -3, -5, -7, -9, 7, -15, 15, 9], [-52, 56, -44, 48, -36, 40, -28, -20, 32, -12, 24, -4], [26, -30, 30, -22, 22, -18, 18, 14, -14, 10, -10, -6, -2, 6, 2], [52, 44, 36, 28, 20, 12]]))

theorem A70_card : A70.length = 70 := rfl
theorem TA70_list : TA70.toList = A70 := rfl
theorem A70_nodup : A70.Nodup := isStrictlySortedBool_nodup A70 (by decide)
theorem B70_len : B70.length = 8 := rfl
theorem B70_nodup : B70.Nodup := isStrictlySortedBool_nodup B70 (by decide)
theorem B70_sub : ∀ x ∈ B70, x ∈ A70 := all_itree_mem A70 B70 TA70 TA70_list (by decide)
theorem B70_sumAvoiding : IsSumAvoiding A70 B70 := isSumAvoidingBool_sound A70 B70 (by decide)
theorem T70_valid : checkCertTree A70 TA70 A70 8 T70 = true := by decide

theorem A70_exact_M : HasExactMaxSumAvoiding A70 8 :=
  ⟨⟨B70, B70_nodup, B70_sub, B70_sumAvoiding, B70_len⟩, certTree_upper_bound A70 TA70 TA70_list 8 T70 T70_valid⟩

def A71 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA71 : ITree := .node 0 (.node (-24) (.node (-52) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-64) (.node (-72) (.empty) (.empty)) (.node (-56) (.empty) (.empty)))) (.node (-32) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))) (.node (-28) (.node (-30) (.empty) (.empty)) (.node (-26) (.empty) (.empty))))) (.node (-9) (.node (-15) (.node (-18) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty)) (.node (-16) (.empty) (.empty))) (.node (-12) (.node (-14) (.empty) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 24 (.node 9 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.node 8 (.empty) (.empty)))) (.node 16 (.node 14 (.node 12 (.node 10 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 52 (.node 36 (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B71 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T71 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, -8, 8], [-88, 88, 80, -80, -16, 16], [7, -9, -15, -7, -5, -3, -1, 1, 3, 5, 9, 15], [-56, 56, 48, -48, -40, 40, 32, -32, 24, -24], [-52, 52, 44, -44, 36, -36, 28, -28, -20, 20, -12, 12, 4, -4], [26, -30, 30, -26, -22, 22, -18, 18, 14, -14, -10, 10, -2, -6, 2, 6]]

theorem A71_card : A71.length = 71 := rfl
theorem TA71_list : TA71.toList = A71 := rfl
theorem A71_nodup : A71.Nodup := isStrictlySortedBool_nodup A71 (by decide)
theorem B71_len : B71.length = 8 := rfl
theorem B71_nodup : B71.Nodup := isStrictlySortedBool_nodup B71 (by decide)
theorem B71_sub : ∀ x ∈ B71, x ∈ A71 := all_itree_mem A71 B71 TA71 TA71_list (by decide)
theorem B71_sumAvoiding : IsSumAvoiding A71 B71 := isSumAvoidingBool_sound A71 B71 (by decide)
theorem T71_valid : checkCertTree A71 TA71 A71 8 T71 = true := by decide

theorem A71_exact_M : HasExactMaxSumAvoiding A71 8 :=
  ⟨⟨B71, B71_nodup, B71_sub, B71_sumAvoiding, B71_len⟩, certTree_upper_bound A71 TA71 TA71_list 8 T71 T71_valid⟩

def A72 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -11, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA72 : ITree := .node 1 (.node (-22) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.empty) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 24 (.node 10 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 8 (.node 7 (.empty) (.empty)) (.node 9 (.empty) (.empty)))) (.node 16 (.node 14 (.node 12 (.node 11 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 52 (.node 36 (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B72 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T72 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, 64, -64], [-96, 96, 72, -72, 8, -8], [-88, 88, 80, -80, 16, -16], [-11, 3, -9, -5, -3, -1, 1, 5, 7, 9, 11, 15, -15], [-56, 56, 48, -48, 40, -40, -32, 32, 24, -24], [52, -52, 44, -44, -36, 36, 28, -28, 20, -20, 12, -12, 4, -4], [-30, 30, 22, -22, -26, 26, 18, -18, -14, 14, -10, 10, 2, -2, -6, 6]]

theorem A72_card : A72.length = 72 := rfl
theorem TA72_list : TA72.toList = A72 := rfl
theorem A72_nodup : A72.Nodup := isStrictlySortedBool_nodup A72 (by decide)
theorem B72_len : B72.length = 8 := rfl
theorem B72_nodup : B72.Nodup := isStrictlySortedBool_nodup B72 (by decide)
theorem B72_sub : ∀ x ∈ B72, x ∈ A72 := all_itree_mem A72 B72 TA72 TA72_list (by decide)
theorem B72_sumAvoiding : IsSumAvoiding A72 B72 := isSumAvoidingBool_sound A72 B72 (by decide)
theorem T72_valid : checkCertTree A72 TA72 A72 8 T72 = true := by decide

theorem A72_exact_M : HasExactMaxSumAvoiding A72 8 :=
  ⟨⟨B72, B72_nodup, B72_sub, B72_sumAvoiding, B72_len⟩, certTree_upper_bound A72 TA72 TA72_list 8 T72 T72_valid⟩

def A73 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA73 : ITree := .node 0 (.node (-22) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.empty) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 24 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 7 (.node 6 (.empty) (.empty)) (.empty)) (.node 9 (.empty) (.empty)))) (.node 16 (.node 14 (.node 12 (.node 11 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 52 (.node 36 (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B73 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T73 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, 64, -64], [-96, 96, -72, 72, -8, 8], [-88, 88, -80, 80, -16, 16], [-9, 5, 3, 1, -1, -3, -5, -7, 7, -11, 9, -15, 11, 15], [-56, 56, -48, 48, 40, -40, 32, -32, 24, -24], [-52, 52, 44, -44, 36, -36, 28, -28, 20, -20, -12, 12, -4, 4], [-30, 30, -26, 26, 22, -22, -18, 18, -14, 14, 10, -10, 6, -6, 2, -2]]

theorem A73_card : A73.length = 73 := rfl
theorem TA73_list : TA73.toList = A73 := rfl
theorem A73_nodup : A73.Nodup := isStrictlySortedBool_nodup A73 (by decide)
theorem B73_len : B73.length = 8 := rfl
theorem B73_nodup : B73.Nodup := isStrictlySortedBool_nodup B73 (by decide)
theorem B73_sub : ∀ x ∈ B73, x ∈ A73 := all_itree_mem A73 B73 TA73 TA73_list (by decide)
theorem B73_sumAvoiding : IsSumAvoiding A73 B73 := isSumAvoidingBool_sound A73 B73 (by decide)
theorem T73_valid : checkCertTree A73 TA73 A73 8 T73 = true := by decide

theorem A73_exact_M : HasExactMaxSumAvoiding A73 8 :=
  ⟨⟨B73, B73_nodup, B73_sub, B73_sumAvoiding, B73_len⟩, certTree_upper_bound A73 TA73 TA73_list 8 T73 T73_valid⟩

def A74 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA74 : ITree := .node 1 (.node (-22) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-3) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 24 (.node 11 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 10 (.empty) (.empty)))) (.node 16 (.node 14 (.node 13 (.node 12 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 20 (.node 18 (.empty) (.empty)) (.node 22 (.empty) (.empty))))) (.node 52 (.node 36 (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B74 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T74 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, 8, -8], [-88, 88, -80, 80, 16, -16], [7, 15, 13, 11, 9, 5, 3, 1, -1, -3, -7, -9, -11, -13, -15], [-56, 56, 48, -48, -40, 40, 32, -32, -24, 24], [52, -52, 44, -44, 36, -36, 28, -28, 20, -20, 12, -12, 4, -4], [30, -30, -26, 26, -22, 22, -18, 18, 14, -14, 10, -10, 6, -6, 2, -2]]

theorem A74_card : A74.length = 74 := rfl
theorem TA74_list : TA74.toList = A74 := rfl
theorem A74_nodup : A74.Nodup := isStrictlySortedBool_nodup A74 (by decide)
theorem B74_len : B74.length = 8 := rfl
theorem B74_nodup : B74.Nodup := isStrictlySortedBool_nodup B74 (by decide)
theorem B74_sub : ∀ x ∈ B74, x ∈ A74 := all_itree_mem A74 B74 TA74 TA74_list (by decide)
theorem B74_sumAvoiding : IsSumAvoiding A74 B74 := isSumAvoidingBool_sound A74 B74 (by decide)
theorem T74_valid : checkCertTree A74 TA74 A74 8 T74 = true := by decide

theorem A74_exact_M : HasExactMaxSumAvoiding A74 8 :=
  ⟨⟨B74, B74_nodup, B74_sub, B74_sumAvoiding, B74_len⟩, certTree_upper_bound A74 TA74 TA74_list 8 T74 T74_valid⟩

def A75 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA75 : ITree := .node 0 (.node (-22) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-26) (.node (-28) (.empty) (.empty)) (.node (-24) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 22 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 7 (.node 6 (.empty) (.empty)) (.empty)) (.node 9 (.empty) (.empty)))) (.node 15 (.node 13 (.node 12 (.node 11 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty))) (.node 18 (.node 16 (.empty) (.empty)) (.node 20 (.empty) (.empty))))) (.node 52 (.node 32 (.node 28 (.node 26 (.node 24 (.empty) (.empty)) (.empty)) (.node 30 (.empty) (.empty))) (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B75 : List Int := [-168, -104, -96, -88, -56, -52, -30, -15]
def T75 : CertTree := .branch (0) (.leafClique []) (.leafClique [[-168, 168], [-104, 104, -64, 64], [-96, 96, -72, 72, 8, -8], [-88, 88, -80, 80, 16, -16], [-56, 56, -48, 48, 40, -40, 32, -32, 24, -24], [-52, 52, -44, 44, 36, -36, -28, 28, -20, 20, 12, -12, 4, -4], [-5, 7, -3, -1, 1, 3, 5, 9, 11, 13, 15, -7, -15, -13, -11, -9], [30, -30, 26, -26, 22, -22, -18, 18, -14, 14, 10, -10, -6, 6, 2, -2]])

theorem A75_card : A75.length = 75 := rfl
theorem TA75_list : TA75.toList = A75 := rfl
theorem A75_nodup : A75.Nodup := isStrictlySortedBool_nodup A75 (by decide)
theorem B75_len : B75.length = 8 := rfl
theorem B75_nodup : B75.Nodup := isStrictlySortedBool_nodup B75 (by decide)
theorem B75_sub : ∀ x ∈ B75, x ∈ A75 := all_itree_mem A75 B75 TA75 TA75_list (by decide)
theorem B75_sumAvoiding : IsSumAvoiding A75 B75 := isSumAvoidingBool_sound A75 B75 (by decide)
theorem T75_valid : checkCertTree A75 TA75 A75 8 T75 = true := by decide

theorem A75_exact_M : HasExactMaxSumAvoiding A75 8 :=
  ⟨⟨B75, B75_nodup, B75_sub, B75_sumAvoiding, B75_len⟩, certTree_upper_bound A75 TA75 TA75_list 8 T75 T75_valid⟩

def A76 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -17, -16, -15, -14, -13, -12, -11, -10, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA76 : ITree := .node 1 (.node (-20) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-22) (.empty) (.empty))))) (.node (-8) (.node (-14) (.node (-16) (.node (-17) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-3) (.node (-5) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty)) (.node (-4) (.empty) (.empty))) (.node (-1) (.node (-2) (.empty) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 22 (.node 11 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 10 (.empty) (.empty)))) (.node 16 (.node 14 (.node 13 (.node 12 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 18 (.node 17 (.empty) (.empty)) (.node 20 (.empty) (.empty))))) (.node 52 (.node 32 (.node 28 (.node 26 (.node 24 (.empty) (.empty)) (.empty)) (.node 30 (.empty) (.empty))) (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B76 : List Int := [-168, -104, -96, -88, -56, -52, -30, -17]
def T76 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, 8, -8], [-88, 88, -80, 80, -16, 16], [-56, 56, 48, -48, -40, 40, 32, -32, 24, -24], [-52, 52, 44, -44, -36, 36, -28, 28, 20, -20, 12, -12, 4, -4], [17, -17, 7, 15, 13, 11, 9, 5, 3, 1, -1, -3, -13, -11, -15, -7, -5], [30, -30, -26, 26, 22, -22, -18, 18, -14, 14, -10, 10, -6, 6, -2, 2]]

theorem A76_card : A76.length = 76 := rfl
theorem TA76_list : TA76.toList = A76 := rfl
theorem A76_nodup : A76.Nodup := isStrictlySortedBool_nodup A76 (by decide)
theorem B76_len : B76.length = 8 := rfl
theorem B76_nodup : B76.Nodup := isStrictlySortedBool_nodup B76 (by decide)
theorem B76_sub : ∀ x ∈ B76, x ∈ A76 := all_itree_mem A76 B76 TA76 TA76_list (by decide)
theorem B76_sumAvoiding : IsSumAvoiding A76 B76 := isSumAvoidingBool_sound A76 B76 (by decide)
theorem T76_valid : checkCertTree A76 TA76 A76 8 T76 = true := by decide

theorem A76_exact_M : HasExactMaxSumAvoiding A76 8 :=
  ⟨⟨B76, B76_nodup, B76_sub, B76_sumAvoiding, B76_len⟩, certTree_upper_bound A76 TA76 TA76_list 8 T76 T76_valid⟩

def A77 : List Int := [-168, -104, -96, -88, -80, -72, -64, -56, -52, -48, -44, -40, -36, -32, -30, -28, -26, -24, -22, -20, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 64, 72, 80, 88, 96, 104, 168]
def TA77 : ITree := .node 0 (.node (-20) (.node (-48) (.node (-80) (.node (-96) (.node (-104) (.node (-168) (.empty) (.empty)) (.empty)) (.node (-88) (.empty) (.empty))) (.node (-56) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.empty) (.empty)))) (.node (-30) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.empty) (.empty))) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-22) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-17) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-2) (.node (-3) (.empty) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 22 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 7 (.node 6 (.empty) (.empty)) (.empty)) (.node 9 (.empty) (.empty)))) (.node 15 (.node 13 (.node 12 (.node 11 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty))) (.node 18 (.node 17 (.node 16 (.empty) (.empty)) (.empty)) (.node 20 (.empty) (.empty))))) (.node 52 (.node 32 (.node 28 (.node 26 (.node 24 (.empty) (.empty)) (.empty)) (.node 30 (.empty) (.empty))) (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 48 (.empty) (.empty)))) (.node 88 (.node 72 (.node 64 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty))) (.node 104 (.node 96 (.empty) (.empty)) (.node 168 (.empty) (.empty))))))
def B77 : List Int := [-168, -104, -96, -88, -56, -52, -30, -17]
def T77 : CertTree := .leafClique [[-168, 168, 0], [-104, 104, -64, 64], [-96, 96, -72, 72, -8, 8], [-88, 88, -80, 80, -16, 16], [-56, 56, 48, -48, -40, 40, 32, -32, -24, 24], [52, -52, 44, -44, 36, -36, 28, -28, 20, -20, -12, 12, -4, 4], [30, -30, -26, 26, 22, -22, -18, 18, 14, -14, 10, -10, 6, -6, 2, -2], [17, -17, -11, 15, 13, 11, 9, 7, 5, 3, 1, -1, -13, -3, -9, -15, -5, -7]]

theorem A77_card : A77.length = 77 := rfl
theorem TA77_list : TA77.toList = A77 := rfl
theorem A77_nodup : A77.Nodup := isStrictlySortedBool_nodup A77 (by decide)
theorem B77_len : B77.length = 8 := rfl
theorem B77_nodup : B77.Nodup := isStrictlySortedBool_nodup B77 (by decide)
theorem B77_sub : ∀ x ∈ B77, x ∈ A77 := all_itree_mem A77 B77 TA77 TA77_list (by decide)
theorem B77_sumAvoiding : IsSumAvoiding A77 B77 := isSumAvoidingBool_sound A77 B77 (by decide)
theorem T77_valid : checkCertTree A77 TA77 A77 8 T77 = true := by decide

theorem A77_exact_M : HasExactMaxSumAvoiding A77 8 :=
  ⟨⟨B77, B77_nodup, B77_sub, B77_sumAvoiding, B77_len⟩, certTree_upper_bound A77 TA77 TA77_list 8 T77 T77_valid⟩

def A78 : List Int := [-78, -50, -48, -46, -44, -42, -40, -38, -36, -34, -32, -30, -28, -26, -25, -24, -22, -21, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 78]
def TA78 : ITree := .node 1 (.node (-19) (.node (-34) (.node (-44) (.node (-48) (.node (-50) (.node (-78) (.empty) (.empty)) (.empty)) (.node (-46) (.empty) (.empty))) (.node (-38) (.node (-40) (.node (-42) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty)))) (.node (-25) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-26) (.empty) (.empty))) (.node (-21) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty)) (.node (-20) (.empty) (.empty))))) (.node (-9) (.node (-14) (.node (-16) (.node (-17) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty))) (.node (-11) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)) (.node (-10) (.empty) (.empty)))) (.node (-4) (.node (-6) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty)) (.node (-5) (.empty) (.empty))) (.node (-1) (.node (-2) (.node (-3) (.empty) (.empty)) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 21 (.node 11 (.node 6 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 10 (.empty) (.empty)))) (.node 16 (.node 14 (.node 13 (.node 12 (.empty) (.empty)) (.empty)) (.node 15 (.empty) (.empty))) (.node 19 (.node 18 (.node 17 (.empty) (.empty)) (.empty)) (.node 20 (.empty) (.empty))))) (.node 36 (.node 26 (.node 24 (.node 23 (.node 22 (.empty) (.empty)) (.empty)) (.node 25 (.empty) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 34 (.empty) (.empty)))) (.node 46 (.node 42 (.node 40 (.node 38 (.empty) (.empty)) (.empty)) (.node 44 (.empty) (.empty))) (.node 50 (.node 48 (.empty) (.empty)) (.node 78 (.empty) (.empty))))))
def B78 : List Int := [-78, -50, -48, -46, -44, -42, -40, -26, -25]
def T78 : CertTree := .leafClique [[-78, 78, 0], [-50, 50, 28, -28], [-48, 48, 30, -30, 2, -2], [-46, 46, -32, 32, -4, 4], [-44, 44, -34, 34, -6, 6], [-42, 42, -36, 36, -8, 8], [-40, 40, -38, 38, -10, 10], [7, 25, 23, 21, 19, 17, 15, 13, 11, 9, 5, 3, 1, -15, -25, -3, -21, -13, -11, -19, -5, -1, -17, -9, -7], [-26, 26, 24, -24, 22, -22, 20, -20, 18, -18, -16, 16, 14, -14, 12, -12]]

theorem A78_card : A78.length = 78 := rfl
theorem TA78_list : TA78.toList = A78 := rfl
theorem A78_nodup : A78.Nodup := isStrictlySortedBool_nodup A78 (by decide)
theorem B78_len : B78.length = 9 := rfl
theorem B78_nodup : B78.Nodup := isStrictlySortedBool_nodup B78 (by decide)
theorem B78_sub : ∀ x ∈ B78, x ∈ A78 := all_itree_mem A78 B78 TA78 TA78_list (by decide)
theorem B78_sumAvoiding : IsSumAvoiding A78 B78 := isSumAvoidingBool_sound A78 B78 (by decide)
theorem T78_valid : checkCertTree A78 TA78 A78 9 T78 = true := by decide

theorem A78_exact_M : HasExactMaxSumAvoiding A78 9 :=
  ⟨⟨B78, B78_nodup, B78_sub, B78_sumAvoiding, B78_len⟩, certTree_upper_bound A78 TA78 TA78_list 9 T78 T78_valid⟩

def A79 : List Int := [-78, -50, -48, -46, -44, -42, -40, -38, -36, -34, -32, -30, -28, -26, -25, -24, -23, -22, -21, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 78]
def TA79 : ITree := .node 0 (.node (-20) (.node (-34) (.node (-44) (.node (-48) (.node (-50) (.node (-78) (.empty) (.empty)) (.empty)) (.node (-46) (.empty) (.empty))) (.node (-38) (.node (-40) (.node (-42) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty)))) (.node (-25) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-26) (.empty) (.empty))) (.node (-22) (.node (-23) (.node (-24) (.empty) (.empty)) (.empty)) (.node (-21) (.empty) (.empty))))) (.node (-10) (.node (-15) (.node (-17) (.node (-18) (.node (-19) (.empty) (.empty)) (.empty)) (.node (-16) (.empty) (.empty))) (.node (-12) (.node (-13) (.node (-14) (.empty) (.empty)) (.empty)) (.node (-11) (.empty) (.empty)))) (.node (-5) (.node (-7) (.node (-8) (.node (-9) (.empty) (.empty)) (.empty)) (.node (-6) (.empty) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 20 (.node 10 (.node 5 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 4 (.empty) (.empty))) (.node 8 (.node 7 (.node 6 (.empty) (.empty)) (.empty)) (.node 9 (.empty) (.empty)))) (.node 15 (.node 13 (.node 12 (.node 11 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty))) (.node 18 (.node 17 (.node 16 (.empty) (.empty)) (.empty)) (.node 19 (.empty) (.empty))))) (.node 34 (.node 25 (.node 23 (.node 22 (.node 21 (.empty) (.empty)) (.empty)) (.node 24 (.empty) (.empty))) (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty)))) (.node 44 (.node 40 (.node 38 (.node 36 (.empty) (.empty)) (.empty)) (.node 42 (.empty) (.empty))) (.node 50 (.node 48 (.node 46 (.empty) (.empty)) (.empty)) (.node 78 (.empty) (.empty))))))
def B79 : List Int := [-78, -50, -48, -46, -44, -42, -40, -26, -25]
def T79 : CertTree := .leafClique [[-78, 78, 0], [-50, 50, 28, -28], [-48, 48, -30, 30, 2, -2], [-46, 46, -32, 32, -4, 4], [-44, 44, 34, -34, -6, 6], [-42, 42, -36, 36, -8, 8], [-40, 40, -38, 38, -10, 10], [1, -26, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, -24, -22, -20, -18, -16, -14, -12], [26, -9, -11, -13, -7, -15, -17, -19, -5, -21, -3, -23, -25, -1, 24, 22, 20, 18, 16, 14, 12]]

theorem A79_card : A79.length = 79 := rfl
theorem TA79_list : TA79.toList = A79 := rfl
theorem A79_nodup : A79.Nodup := isStrictlySortedBool_nodup A79 (by decide)
theorem B79_len : B79.length = 9 := rfl
theorem B79_nodup : B79.Nodup := isStrictlySortedBool_nodup B79 (by decide)
theorem B79_sub : ∀ x ∈ B79, x ∈ A79 := all_itree_mem A79 B79 TA79 TA79_list (by decide)
theorem B79_sumAvoiding : IsSumAvoiding A79 B79 := isSumAvoidingBool_sound A79 B79 (by decide)
theorem T79_valid : checkCertTree A79 TA79 A79 9 T79 = true := by decide

theorem A79_exact_M : HasExactMaxSumAvoiding A79 9 :=
  ⟨⟨B79, B79_nodup, B79_sub, B79_sumAvoiding, B79_len⟩, certTree_upper_bound A79 TA79 TA79_list 9 T79 T79_valid⟩

def A80 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 2, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA80 : ITree := .node (-1) (.node (-36) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-56) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-60) (.empty) (.empty))) (.node (-44) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty)) (.node (-40) (.empty) (.empty))))) (.node (-14) (.node (-22) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-24) (.empty) (.empty))) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-12) (.empty) (.empty)) (.empty)) (.node (-8) (.empty) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-2) (.empty) (.empty)))))) (.node 40 (.node 14 (.node 6 (.node 4 (.node 2 (.node 0 (.empty) (.empty)) (.empty)) (.node 5 (.empty) (.empty))) (.node 10 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 12 (.empty) (.empty)))) (.node 24 (.node 20 (.node 18 (.node 16 (.empty) (.empty)) (.empty)) (.node 22 (.empty) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))))) (.node 96 (.node 60 (.node 52 (.node 48 (.node 44 (.empty) (.empty)) (.empty)) (.node 56 (.empty) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B80 : List Int := [-336, -208, -192, -176, -112, -104, -60, -30, -15]
def T80 : CertTree := .leafClique [[336, -336, 0], [-1, 7, 5, -3, -5, -9, -15], [-208, 208, 128, -128], [192, -192, -144, 144, -16, 16], [-176, 176, 160, -160, 32, -32], [30, 18, -30, -18, -22, 22, -14, 14, -6, -2, -10, 2, 10, 6], [-112, 112, 96, -96, -80, 80, 64, -64, 48, -48], [-104, 104, 88, -88, -72, 72, -56, 56, 40, -40, -24, 24, -8, 8], [-60, 60, 52, -52, -44, 44, -36, 36, 28, -28, 20, -20, 4, -12, -4, 12]]

theorem A80_card : A80.length = 80 := rfl
theorem TA80_list : TA80.toList = A80 := rfl
theorem A80_nodup : A80.Nodup := isStrictlySortedBool_nodup A80 (by decide)
theorem B80_len : B80.length = 9 := rfl
theorem B80_nodup : B80.Nodup := isStrictlySortedBool_nodup B80 (by decide)
theorem B80_sub : ∀ x ∈ B80, x ∈ A80 := all_itree_mem A80 B80 TA80 TA80_list (by decide)
theorem B80_sumAvoiding : IsSumAvoiding A80 B80 := isSumAvoidingBool_sound A80 B80 (by decide)
theorem T80_valid : checkCertTree A80 TA80 A80 9 T80 = true := by decide

theorem A80_exact_M : HasExactMaxSumAvoiding A80 9 :=
  ⟨⟨B80, B80_nodup, B80_sub, B80_sumAvoiding, B80_len⟩, certTree_upper_bound A80 TA80 TA80_list 9 T80 T80_valid⟩

def A81 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 2, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 30, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA81 : ITree := .node (-2) (.node (-36) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-56) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-60) (.empty) (.empty))) (.node (-44) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty)) (.node (-40) (.empty) (.empty))))) (.node (-15) (.node (-24) (.node (-30) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty)) (.node (-28) (.empty) (.empty))) (.node (-18) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty)) (.node (-16) (.empty) (.empty)))) (.node (-8) (.node (-10) (.node (-12) (.node (-14) (.empty) (.empty)) (.empty)) (.node (-9) (.empty) (.empty))) (.node (-4) (.node (-5) (.node (-6) (.empty) (.empty)) (.empty)) (.node (-3) (.empty) (.empty)))))) (.node 40 (.node 14 (.node 6 (.node 2 (.node 0 (.node (-1) (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 10 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 12 (.empty) (.empty)))) (.node 24 (.node 20 (.node 18 (.node 16 (.empty) (.empty)) (.empty)) (.node 22 (.empty) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))))) (.node 96 (.node 60 (.node 52 (.node 48 (.node 44 (.empty) (.empty)) (.empty)) (.node 56 (.empty) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B81 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T81 : CertTree := .leafClique [[-336, 336, 0], [7, 5, -1, -3, -5, -9, -15], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, 160, -160, 32, -32], [-34, -30, 18, -18, 30, 22, -22, -14, 14, 10, 2, 6, -6, -2, -10], [-112, 112, 96, -96, -80, 80, 64, -64, 48, -48], [-104, 104, 88, -88, -72, 72, 56, -56, -40, 40, 24, -24, 8, -8], [60, -60, 52, -52, 44, -44, 36, -36, 28, -28, 20, -20, -12, 12, 4, -4]]

theorem A81_card : A81.length = 81 := rfl
theorem TA81_list : TA81.toList = A81 := rfl
theorem A81_nodup : A81.Nodup := isStrictlySortedBool_nodup A81 (by decide)
theorem B81_len : B81.length = 9 := rfl
theorem B81_nodup : B81.Nodup := isStrictlySortedBool_nodup B81 (by decide)
theorem B81_sub : ∀ x ∈ B81, x ∈ A81 := all_itree_mem A81 B81 TA81 TA81_list (by decide)
theorem B81_sumAvoiding : IsSumAvoiding A81 B81 := isSumAvoidingBool_sound A81 B81 (by decide)
theorem T81_valid : checkCertTree A81 TA81 A81 9 T81 = true := by decide

theorem A81_exact_M : HasExactMaxSumAvoiding A81 9 :=
  ⟨⟨B81, B81_nodup, B81_sub, B81_sumAvoiding, B81_len⟩, certTree_upper_bound A81 TA81 TA81_list 9 T81 T81_valid⟩

def A82 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 2, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA82 : ITree := .node (-1) (.node (-36) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-56) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-60) (.empty) (.empty))) (.node (-44) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty)) (.node (-40) (.empty) (.empty))))) (.node (-14) (.node (-22) (.node (-30) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty)) (.node (-24) (.node (-28) (.empty) (.empty)) (.empty))) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-12) (.empty) (.empty)) (.empty)) (.node (-8) (.empty) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-2) (.empty) (.empty)))))) (.node 40 (.node 16 (.node 7 (.node 4 (.node 2 (.node 0 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 10 (.node 8 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty)))) (.node 28 (.node 22 (.node 20 (.node 18 (.empty) (.empty)) (.empty)) (.node 24 (.empty) (.empty))) (.node 34 (.node 32 (.node 30 (.empty) (.empty)) (.empty)) (.node 36 (.empty) (.empty))))) (.node 96 (.node 60 (.node 52 (.node 48 (.node 44 (.empty) (.empty)) (.empty)) (.node 56 (.empty) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B82 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T82 : CertTree := .leafClique [[336, -336, 0], [-1, 7, 5, -3, -5, -9, -15], [-208, 208, 128, -128], [192, -192, -144, 144, -16, 16], [-176, 176, -160, 160, -32, 32], [-112, 112, -96, 96, -80, 80, -64, 64, -48, 48], [104, -104, 88, -88, 72, -72, 56, -56, 40, -40, 24, -24, -8, 8], [34, -34, -30, 18, -18, 30, 22, -22, 14, -14, -2, -6, 2, -10, 6, 10], [-60, 60, 52, -52, -44, 44, -36, 36, 28, -28, 20, -20, -4, 12, -12, 4]]

theorem A82_card : A82.length = 82 := rfl
theorem TA82_list : TA82.toList = A82 := rfl
theorem A82_nodup : A82.Nodup := isStrictlySortedBool_nodup A82 (by decide)
theorem B82_len : B82.length = 9 := rfl
theorem B82_nodup : B82.Nodup := isStrictlySortedBool_nodup B82 (by decide)
theorem B82_sub : ∀ x ∈ B82, x ∈ A82 := all_itree_mem A82 B82 TA82 TA82_list (by decide)
theorem B82_sumAvoiding : IsSumAvoiding A82 B82 := isSumAvoidingBool_sound A82 B82 (by decide)
theorem T82_valid : checkCertTree A82 TA82 A82 9 T82 = true := by decide

theorem A82_exact_M : HasExactMaxSumAvoiding A82 9 :=
  ⟨⟨B82, B82_nodup, B82_sub, B82_sumAvoiding, B82_len⟩, certTree_upper_bound A82 TA82 TA82_list 9 T82 T82_valid⟩

def A83 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 2, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA83 : ITree := .node (-1) (.node (-36) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-56) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-60) (.empty) (.empty))) (.node (-44) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty)) (.node (-40) (.empty) (.empty))))) (.node (-14) (.node (-22) (.node (-30) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty)) (.node (-24) (.node (-28) (.empty) (.empty)) (.empty))) (.node (-16) (.node (-18) (.node (-20) (.empty) (.empty)) (.empty)) (.node (-15) (.empty) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-12) (.empty) (.empty)) (.empty)) (.node (-8) (.empty) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-2) (.empty) (.empty)))))) (.node 36 (.node 15 (.node 7 (.node 4 (.node 2 (.node 0 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 10 (.node 8 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty)))) (.node 24 (.node 20 (.node 18 (.node 16 (.empty) (.empty)) (.empty)) (.node 22 (.empty) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 34 (.empty) (.empty))))) (.node 96 (.node 60 (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 56 (.node 52 (.empty) (.empty)) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B83 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T83 : CertTree := .leafClique [[336, -336, 0], [-1, 15, 7, 5, -3, -5, -9, -15], [-208, 208, 128, -128], [192, -192, -144, 144, 16, -16], [-176, 176, -160, 160, -32, 32], [112, -112, -96, 96, -80, 80, -64, 64, 48, -48], [104, -104, -88, 88, 72, -72, -56, 56, 40, -40, -24, 24, -8, 8], [-34, 34, 18, 22, 30, -18, -22, -30, -14, 14, 6, 2, -2, -6, 10, -10], [-60, 60, -52, 52, -44, 44, 36, -36, 28, -28, 20, -20, 4, 12, -4, -12]]

theorem A83_card : A83.length = 83 := rfl
theorem TA83_list : TA83.toList = A83 := rfl
theorem A83_nodup : A83.Nodup := isStrictlySortedBool_nodup A83 (by decide)
theorem B83_len : B83.length = 9 := rfl
theorem B83_nodup : B83.Nodup := isStrictlySortedBool_nodup B83 (by decide)
theorem B83_sub : ∀ x ∈ B83, x ∈ A83 := all_itree_mem A83 B83 TA83 TA83_list (by decide)
theorem B83_sumAvoiding : IsSumAvoiding A83 B83 := isSumAvoidingBool_sound A83 B83 (by decide)
theorem T83_valid : checkCertTree A83 TA83 A83 9 T83 = true := by decide

theorem A83_exact_M : HasExactMaxSumAvoiding A83 9 :=
  ⟨⟨B83, B83_nodup, B83_sub, B83_sumAvoiding, B83_len⟩, certTree_upper_bound A83 TA83 TA83_list 9 T83 T83_valid⟩

def A84 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -6, -5, -4, -3, -2, -1, 0, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA84 : ITree := .node 0 (.node (-34) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-52) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-56) (.node (-60) (.empty) (.empty)) (.empty))) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))))) (.node (-12) (.node (-20) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.empty) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 36 (.node 15 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 10 (.node 8 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty)))) (.node 24 (.node 20 (.node 18 (.node 16 (.empty) (.empty)) (.empty)) (.node 22 (.empty) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 34 (.empty) (.empty))))) (.node 96 (.node 60 (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 56 (.node 52 (.empty) (.empty)) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B84 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T84 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, 128, -128], [15, 7, 5, 3, -1, -3, -5, -9, -15], [-192, 192, -144, 144, -16, 16], [-176, 176, 160, -160, -32, 32], [-112, 112, 96, -96, -80, 80, 64, -64, 48, -48], [34, -34, 30, 22, -22, -30, 14, 18, -14, -18, -2, -10, 10, 6, -6, 2], [-104, 104, 88, -88, -72, 72, -56, 56, 40, -40, 24, -24, -8, 8], [60, -60, 52, -52, 44, -44, -36, 36, -28, 28, 20, -20, -12, 12, 4, -4]]

theorem A84_card : A84.length = 84 := rfl
theorem TA84_list : TA84.toList = A84 := rfl
theorem A84_nodup : A84.Nodup := isStrictlySortedBool_nodup A84 (by decide)
theorem B84_len : B84.length = 9 := rfl
theorem B84_nodup : B84.Nodup := isStrictlySortedBool_nodup B84 (by decide)
theorem B84_sub : ∀ x ∈ B84, x ∈ A84 := all_itree_mem A84 B84 TA84 TA84_list (by decide)
theorem B84_sumAvoiding : IsSumAvoiding A84 B84 := isSumAvoidingBool_sound A84 B84 (by decide)
theorem T84_valid : checkCertTree A84 TA84 A84 9 T84 = true := by decide

theorem A84_exact_M : HasExactMaxSumAvoiding A84 9 :=
  ⟨⟨B84, B84_nodup, B84_sub, B84_sumAvoiding, B84_len⟩, certTree_upper_bound A84 TA84 TA84_list 9 T84 T84_valid⟩

def A85 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA85 : ITree := .node (-1) (.node (-34) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-52) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-56) (.node (-60) (.empty) (.empty)) (.empty))) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))))) (.node (-12) (.node (-20) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty)))) (.node (-6) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-7) (.empty) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-2) (.empty) (.empty)))))) (.node 36 (.node 14 (.node 6 (.node 3 (.node 2 (.node 0 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 10 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 12 (.empty) (.empty)))) (.node 24 (.node 18 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 22 (.node 20 (.empty) (.empty)) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 34 (.empty) (.empty))))) (.node 96 (.node 60 (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 56 (.node 52 (.empty) (.empty)) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B85 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T85 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [7, -15, -9, -7, -5, -3, -1, 3, 5, 15], [192, -192, -144, 144, -16, 16], [176, -176, 160, -160, 32, -32], [-112, 112, -96, 96, 80, -80, -64, 64, 48, -48], [-104, 104, -88, 88, 72, -72, -56, 56, 40, -40, 24, -24, -8, 8], [-34, 34, -30, 30, 22, -22, 18, -18, -14, 14, -10, 10, 6, -6, 2, -2], [60, -60, 52, -52, 44, -44, -36, 36, 28, -28, -20, 20, -12, -4, 12, 4]]

theorem A85_card : A85.length = 85 := rfl
theorem TA85_list : TA85.toList = A85 := rfl
theorem A85_nodup : A85.Nodup := isStrictlySortedBool_nodup A85 (by decide)
theorem B85_len : B85.length = 9 := rfl
theorem B85_nodup : B85.Nodup := isStrictlySortedBool_nodup B85 (by decide)
theorem B85_sub : ∀ x ∈ B85, x ∈ A85 := all_itree_mem A85 B85 TA85 TA85_list (by decide)
theorem B85_sumAvoiding : IsSumAvoiding A85 B85 := isSumAvoidingBool_sound A85 B85 (by decide)
theorem T85_valid : checkCertTree A85 TA85 A85 9 T85 = true := by decide

theorem A85_exact_M : HasExactMaxSumAvoiding A85 9 :=
  ⟨⟨B85, B85_nodup, B85_sub, B85_sumAvoiding, B85_len⟩, certTree_upper_bound A85 TA85 TA85_list 9 T85 T85_valid⟩

def A86 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA86 : ITree := .node 0 (.node (-34) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-52) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-56) (.node (-60) (.empty) (.empty)) (.empty))) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))))) (.node (-12) (.node (-20) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 36 (.node 15 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 12 (.node 10 (.node 8 (.empty) (.empty)) (.empty)) (.node 14 (.empty) (.empty)))) (.node 26 (.node 20 (.node 18 (.node 16 (.empty) (.empty)) (.empty)) (.node 24 (.node 22 (.empty) (.empty)) (.empty))) (.node 32 (.node 30 (.node 28 (.empty) (.empty)) (.empty)) (.node 34 (.empty) (.empty))))) (.node 96 (.node 60 (.node 48 (.node 44 (.node 40 (.empty) (.empty)) (.empty)) (.node 56 (.node 52 (.empty) (.empty)) (.empty))) (.node 80 (.node 72 (.node 64 (.empty) (.empty)) (.empty)) (.node 88 (.empty) (.empty)))) (.node 160 (.node 128 (.node 112 (.node 104 (.empty) (.empty)) (.empty)) (.node 144 (.empty) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B86 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T86 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [3, 15, 7, 5, -1, -3, -5, -7, -9, -15], [-192, 192, -144, 144, -16, 16], [-176, 176, 160, -160, 32, -32], [-112, 112, -96, 96, -80, 80, -64, 64, -48, 48], [-104, 104, -88, 88, 72, -72, -56, 56, 40, -40, -24, 24, -8, 8], [34, -34, 26, -30, 30, 18, -18, 22, -22, 14, -14, 10, -6, 6, -10, -2, 2], [60, -60, -52, 52, 44, -44, 36, -36, 28, -28, -20, 20, -12, 12, -4, 4]]

theorem A86_card : A86.length = 86 := rfl
theorem TA86_list : TA86.toList = A86 := rfl
theorem A86_nodup : A86.Nodup := isStrictlySortedBool_nodup A86 (by decide)
theorem B86_len : B86.length = 9 := rfl
theorem B86_nodup : B86.Nodup := isStrictlySortedBool_nodup B86 (by decide)
theorem B86_sub : ∀ x ∈ B86, x ∈ A86 := all_itree_mem A86 B86 TA86 TA86_list (by decide)
theorem B86_sumAvoiding : IsSumAvoiding A86 B86 := isSumAvoidingBool_sound A86 B86 (by decide)
theorem T86_valid : checkCertTree A86 TA86 A86 9 T86 = true := by decide

theorem A86_exact_M : HasExactMaxSumAvoiding A86 9 :=
  ⟨⟨B86, B86_nodup, B86_sub, B86_sumAvoiding, B86_len⟩, certTree_upper_bound A86 TA86 TA86_list 9 T86 T86_valid⟩

def A87 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA87 : ITree := .node 0 (.node (-34) (.node (-88) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-96) (.empty) (.empty)))) (.node (-52) (.node (-64) (.node (-72) (.node (-80) (.empty) (.empty)) (.empty)) (.node (-56) (.node (-60) (.empty) (.empty)) (.empty))) (.node (-40) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty)) (.node (-36) (.empty) (.empty))))) (.node (-12) (.node (-20) (.node (-28) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 34 (.node 14 (.node 6 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 10 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 12 (.empty) (.empty)))) (.node 24 (.node 18 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 22 (.node 20 (.empty) (.empty)) (.empty))) (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))))) (.node 88 (.node 56 (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 52 (.node 48 (.empty) (.empty)) (.empty))) (.node 72 (.node 64 (.node 60 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B87 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T87 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [7, -15, -9, -7, -5, -3, -1, 1, 3, 5, 15], [176, -176, 160, -160, 32, -32], [-112, 112, 96, -96, -80, 80, 64, -64, -48, 48], [-104, 104, 88, -88, 72, -72, 56, -56, 40, -40, -24, 24, -8, 8], [-60, 60, -52, 52, 44, -44, 36, -36, -28, 28, 20, -20, -12, 12, 4, -4], [34, -34, 26, 30, -30, -18, 22, 18, -22, -14, 14, 10, -10, 6, -6, 2, -2]]

theorem A87_card : A87.length = 87 := rfl
theorem TA87_list : TA87.toList = A87 := rfl
theorem A87_nodup : A87.Nodup := isStrictlySortedBool_nodup A87 (by decide)
theorem B87_len : B87.length = 9 := rfl
theorem B87_nodup : B87.Nodup := isStrictlySortedBool_nodup B87 (by decide)
theorem B87_sub : ∀ x ∈ B87, x ∈ A87 := all_itree_mem A87 B87 TA87 TA87_list (by decide)
theorem B87_sumAvoiding : IsSumAvoiding A87 B87 := isSumAvoidingBool_sound A87 B87 (by decide)
theorem T87_valid : checkCertTree A87 TA87 A87 9 T87 = true := by decide

theorem A87_exact_M : HasExactMaxSumAvoiding A87 9 :=
  ⟨⟨B87, B87_nodup, B87_sub, B87_sumAvoiding, B87_len⟩, certTree_upper_bound A87 TA87 TA87_list 9 T87 T87_valid⟩

def A88 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA88 : ITree := .node 1 (.node (-32) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-34) (.empty) (.empty))))) (.node (-10) (.node (-18) (.node (-24) (.node (-28) (.node (-30) (.empty) (.empty)) (.empty)) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-15) (.node (-16) (.empty) (.empty)) (.empty)) (.node (-12) (.empty) (.empty)))) (.node (-4) (.node (-7) (.node (-8) (.node (-9) (.empty) (.empty)) (.empty)) (.node (-5) (.node (-6) (.empty) (.empty)) (.empty))) (.node (-1) (.node (-2) (.node (-3) (.empty) (.empty)) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 34 (.node 14 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.empty) (.empty)))) (.node 24 (.node 18 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 22 (.node 20 (.empty) (.empty)) (.empty))) (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))))) (.node 88 (.node 56 (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 52 (.node 48 (.empty) (.empty)) (.empty))) (.node 72 (.node 64 (.node 60 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B88 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T88 : CertTree := .branch (0) (.leafClique []) (.branch (-336) (.leafClique [[-208, -128, 112, 96, 80, 64, 48, 32, 16], [-192, -144, 104, 88, -16], [-176, -160, 72, -32], [-112, -96, -80, -64, -48, 56, 40, 24, 8], [-15, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 15], [-104, -88, -72, -56, -40, -24, -8, 44, 60, 52], [-60, -52, -44, -36, 36, 28, -28, 20, -20, -12, 12, 4, -4], [-34, 34, -30, 26, 22, -22, 18, -18, 14, -14, 30, 10, -10, -6, 6, 2, -2]]) (.branch (-128) (.leafClique [[-192, -144], [-176, -160], [-112, -96, 60, 52], [-104, -88, -72, -56, -40, -24, -8, 44, 8], [-60, -52, -44, -36, -28, 36, 28, -20, 20, -12, 12, -4, 4], [-15, -9, 15, 9, -7, 7, -1, 1, -5, 3, -3, 5], [-34, -30, 34, -22, 26, -18, 30, 18, -14, 22, 14, -10, 10, -6, -2, 2, 6]]) (.leafClique [[336, -208], [208, -192, -144, 128, -16], [192, -176, -160, 144, -32, 16], [176, 160, -112, -96, -80, -64, -48, 32], [5, 15, 9, 7, 3, 1, -1, -3, -5, -7, -9, -15], [112, -104, 96, -88, -72, 80, -56, 64, -40, 48, -24, -8], [104, 88, -60, 72, -52, -44, 56, 40, 24, 8], [34, -34, 26, 30, -30, 22, -22, -18, 18, 14, -14, 10, -10, 6, -6, 2, -2], [60, 52, 44, 36, -36, 28, -28, 20, -20, 12, -12, -4, 4]])))

theorem A88_card : A88.length = 88 := rfl
theorem TA88_list : TA88.toList = A88 := rfl
theorem A88_nodup : A88.Nodup := isStrictlySortedBool_nodup A88 (by decide)
theorem B88_len : B88.length = 9 := rfl
theorem B88_nodup : B88.Nodup := isStrictlySortedBool_nodup B88 (by decide)
theorem B88_sub : ∀ x ∈ B88, x ∈ A88 := all_itree_mem A88 B88 TA88 TA88_list (by decide)
theorem B88_sumAvoiding : IsSumAvoiding A88 B88 := isSumAvoidingBool_sound A88 B88 (by decide)
theorem T88_valid : checkCertTree A88 TA88 A88 9 T88 = true := by decide

theorem A88_exact_M : HasExactMaxSumAvoiding A88 9 :=
  ⟨⟨B88, B88_nodup, B88_sub, B88_sumAvoiding, B88_len⟩, certTree_upper_bound A88 TA88 TA88_list 9 T88 T88_valid⟩

def A89 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA89 : ITree := .node 0 (.node (-32) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-34) (.empty) (.empty))))) (.node (-12) (.node (-20) (.node (-26) (.node (-28) (.node (-30) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-14) (.empty) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 34 (.node 14 (.node 6 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 12 (.node 10 (.empty) (.empty)) (.empty)))) (.node 24 (.node 18 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 22 (.node 20 (.empty) (.empty)) (.empty))) (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))))) (.node 88 (.node 56 (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 52 (.node 48 (.empty) (.empty)) (.empty))) (.node 72 (.node 64 (.node 60 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B89 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T89 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, 160, -160, -32, 32], [7, -15, -9, -7, -5, -3, -1, 1, 3, 5, 9, 15], [-112, 112, 96, -96, -80, 80, 64, -64, -48, 48], [-104, 104, 88, -88, 72, -72, 56, -56, -40, 40, 24, -24, -8, 8], [60, -60, -52, 52, -44, 44, 36, -36, -28, 28, 20, -20, -12, 12, 4, -4], [-34, 34, -26, 26, -30, 30, -22, 22, -18, 18, 14, -14, -10, 10, 2, -6, 6, -2]]

theorem A89_card : A89.length = 89 := rfl
theorem TA89_list : TA89.toList = A89 := rfl
theorem A89_nodup : A89.Nodup := isStrictlySortedBool_nodup A89 (by decide)
theorem B89_len : B89.length = 9 := rfl
theorem B89_nodup : B89.Nodup := isStrictlySortedBool_nodup B89 (by decide)
theorem B89_sub : ∀ x ∈ B89, x ∈ A89 := all_itree_mem A89 B89 TA89 TA89_list (by decide)
theorem B89_sumAvoiding : IsSumAvoiding A89 B89 := isSumAvoidingBool_sound A89 B89 (by decide)
theorem T89_valid : checkCertTree A89 TA89 A89 9 T89 = true := by decide

theorem A89_exact_M : HasExactMaxSumAvoiding A89 9 :=
  ⟨⟨B89, B89_nodup, B89_sub, B89_sumAvoiding, B89_len⟩, certTree_upper_bound A89 TA89 TA89_list 9 T89 T89_valid⟩

def A90 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -11, -10, -9, -8, -7, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA90 : ITree := .node 1 (.node (-32) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-34) (.empty) (.empty))))) (.node (-11) (.node (-20) (.node (-26) (.node (-28) (.node (-30) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-4) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-1) (.node (-2) (.node (-3) (.empty) (.empty)) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 34 (.node 14 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 24 (.node 18 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 22 (.node 20 (.empty) (.empty)) (.empty))) (.node 30 (.node 28 (.node 26 (.empty) (.empty)) (.empty)) (.node 32 (.empty) (.empty))))) (.node 88 (.node 56 (.node 44 (.node 40 (.node 36 (.empty) (.empty)) (.empty)) (.node 52 (.node 48 (.empty) (.empty)) (.empty))) (.node 72 (.node 64 (.node 60 (.empty) (.empty)) (.empty)) (.node 80 (.empty) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B90 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T90 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, 144, -144, -16, 16], [-176, 176, 160, -160, -32, 32], [-15, 3, -11, -9, -7, -3, -1, 1, 5, 7, 9, 11, 15], [-112, 112, -96, 96, 80, -80, 64, -64, 48, -48], [-104, 104, -88, 88, 72, -72, -56, 56, 40, -40, 24, -24, -8, 8], [-60, 60, 52, -52, 44, -44, -36, 36, -28, 28, -20, 20, 12, -12, 4, -4], [-34, 34, -30, 30, 26, -26, -22, 22, -18, 18, -14, 14, -10, 10, -6, 6, 2, -2]]

theorem A90_card : A90.length = 90 := rfl
theorem TA90_list : TA90.toList = A90 := rfl
theorem A90_nodup : A90.Nodup := isStrictlySortedBool_nodup A90 (by decide)
theorem B90_len : B90.length = 9 := rfl
theorem B90_nodup : B90.Nodup := isStrictlySortedBool_nodup B90 (by decide)
theorem B90_sub : ∀ x ∈ B90, x ∈ A90 := all_itree_mem A90 B90 TA90 TA90_list (by decide)
theorem B90_sumAvoiding : IsSumAvoiding A90 B90 := isSumAvoidingBool_sound A90 B90 (by decide)
theorem T90_valid : checkCertTree A90 TA90 A90 9 T90 = true := by decide

theorem A90_exact_M : HasExactMaxSumAvoiding A90 9 :=
  ⟨⟨B90, B90_nodup, B90_sub, B90_sumAvoiding, B90_len⟩, certTree_upper_bound A90 TA90 TA90_list 9 T90 T90_valid⟩

def A91 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA91 : ITree := .node 0 (.node (-32) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-34) (.empty) (.empty))))) (.node (-11) (.node (-20) (.node (-26) (.node (-28) (.node (-30) (.empty) (.empty)) (.empty)) (.node (-22) (.node (-24) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-18) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 32 (.node 12 (.node 6 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 11 (.node 10 (.empty) (.empty)) (.empty)))) (.node 22 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 20 (.node 18 (.empty) (.empty)) (.empty))) (.node 28 (.node 26 (.node 24 (.empty) (.empty)) (.empty)) (.node 30 (.empty) (.empty))))) (.node 88 (.node 52 (.node 40 (.node 36 (.node 34 (.empty) (.empty)) (.empty)) (.node 48 (.node 44 (.empty) (.empty)) (.empty))) (.node 64 (.node 60 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.node 72 (.empty) (.empty)) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B91 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T91 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, 128, -128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, 32, -32], [15, -5, -7, -9, -11, -15, -3, -1, 1, 3, 5, 11, 7, 9], [-112, 112, -96, 96, -80, 80, -64, 64, -48, 48], [-104, 104, 88, -88, 72, -72, -56, 56, -40, 40, -24, 24, -8, 8], [60, -60, 52, -52, 44, -44, -36, 36, 28, -28, 20, -20, -12, 12, -4, 4], [34, -34, -30, 30, -26, 26, 22, -22, 18, -18, 14, -14, 10, -10, 6, -6, 2, -2]]

theorem A91_card : A91.length = 91 := rfl
theorem TA91_list : TA91.toList = A91 := rfl
theorem A91_nodup : A91.Nodup := isStrictlySortedBool_nodup A91 (by decide)
theorem B91_len : B91.length = 9 := rfl
theorem B91_nodup : B91.Nodup := isStrictlySortedBool_nodup B91 (by decide)
theorem B91_sub : ∀ x ∈ B91, x ∈ A91 := all_itree_mem A91 B91 TA91 TA91_list (by decide)
theorem B91_sumAvoiding : IsSumAvoiding A91 B91 := isSumAvoidingBool_sound A91 B91 (by decide)
theorem T91_valid : checkCertTree A91 TA91 A91 9 T91 = true := by decide

theorem A91_exact_M : HasExactMaxSumAvoiding A91 9 :=
  ⟨⟨B91, B91_nodup, B91_sub, B91_sumAvoiding, B91_len⟩, certTree_upper_bound A91 TA91 TA91_list 9 T91 T91_valid⟩

def A92 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA92 : ITree := .node 1 (.node (-30) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty))))) (.node (-11) (.node (-18) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-15) (.node (-16) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)))) (.node (-4) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-1) (.node (-2) (.node (-3) (.empty) (.empty)) (.empty)) (.node 0 (.empty) (.empty)))))) (.node 32 (.node 13 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 22 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 20 (.node 18 (.empty) (.empty)) (.empty))) (.node 28 (.node 26 (.node 24 (.empty) (.empty)) (.empty)) (.node 30 (.empty) (.empty))))) (.node 88 (.node 52 (.node 40 (.node 36 (.node 34 (.empty) (.empty)) (.empty)) (.node 48 (.node 44 (.empty) (.empty)) (.empty))) (.node 64 (.node 60 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.node 72 (.empty) (.empty)) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B92 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T92 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, 16, -16], [-176, 176, -160, 160, 32, -32], [-15, 7, -13, -11, -9, -7, -3, -1, 1, 3, 5, 9, 11, 13, 15], [112, -112, -96, 96, 80, -80, 64, -64, 48, -48], [-104, 104, -88, 88, -72, 72, 56, -56, -40, 40, 24, -24, -8, 8], [60, -60, 52, -52, -44, 44, 36, -36, -28, 28, -20, 20, 12, -12, 4, -4], [34, -34, -30, 30, -26, 26, 22, -22, -18, 18, -14, 14, -10, 10, -6, 6, 2, -2]]

theorem A92_card : A92.length = 92 := rfl
theorem TA92_list : TA92.toList = A92 := rfl
theorem A92_nodup : A92.Nodup := isStrictlySortedBool_nodup A92 (by decide)
theorem B92_len : B92.length = 9 := rfl
theorem B92_nodup : B92.Nodup := isStrictlySortedBool_nodup B92 (by decide)
theorem B92_sub : ∀ x ∈ B92, x ∈ A92 := all_itree_mem A92 B92 TA92 TA92_list (by decide)
theorem B92_sumAvoiding : IsSumAvoiding A92 B92 := isSumAvoidingBool_sound A92 B92 (by decide)
theorem T92_valid : checkCertTree A92 TA92 A92 9 T92 = true := by decide

theorem A92_exact_M : HasExactMaxSumAvoiding A92 9 :=
  ⟨⟨B92, B92_nodup, B92_sub, B92_sumAvoiding, B92_len⟩, certTree_upper_bound A92 TA92 TA92_list 9 T92 T92_valid⟩

def A93 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA93 : ITree := .node 0 (.node (-30) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty))))) (.node (-11) (.node (-18) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-15) (.node (-16) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node (-1) (.empty) (.empty)))))) (.node 32 (.node 12 (.node 6 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 11 (.node 10 (.empty) (.empty)) (.empty)))) (.node 20 (.node 15 (.node 14 (.node 13 (.empty) (.empty)) (.empty)) (.node 18 (.node 16 (.empty) (.empty)) (.empty))) (.node 26 (.node 24 (.node 22 (.empty) (.empty)) (.empty)) (.node 30 (.node 28 (.empty) (.empty)) (.empty))))) (.node 88 (.node 52 (.node 40 (.node 36 (.node 34 (.empty) (.empty)) (.empty)) (.node 48 (.node 44 (.empty) (.empty)) (.empty))) (.node 64 (.node 60 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.node 72 (.empty) (.empty)) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B93 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -15]
def T93 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, 16, -16], [-176, 176, -160, 160, 32, -32], [-112, 112, -96, 96, 80, -80, 64, -64, -48, 48], [104, -104, -88, 88, -72, 72, -56, 56, -40, 40, -24, 24, -8, 8], [1, -5, -3, -7, -9, -11, -13, -15, -1, 3, 5, 7, 9, 11, 13, 15], [60, -60, 52, -52, 44, -44, 36, -36, -28, 28, -20, 20, -12, 12, -4, 4], [34, -34, -30, 30, -26, 26, 22, -22, 18, -18, 14, -14, 10, -10, 6, -6, -2, 2]]

theorem A93_card : A93.length = 93 := rfl
theorem TA93_list : TA93.toList = A93 := rfl
theorem A93_nodup : A93.Nodup := isStrictlySortedBool_nodup A93 (by decide)
theorem B93_len : B93.length = 9 := rfl
theorem B93_nodup : B93.Nodup := isStrictlySortedBool_nodup B93 (by decide)
theorem B93_sub : ∀ x ∈ B93, x ∈ A93 := all_itree_mem A93 B93 TA93 TA93_list (by decide)
theorem B93_sumAvoiding : IsSumAvoiding A93 B93 := isSumAvoidingBool_sound A93 B93 (by decide)
theorem T93_valid : checkCertTree A93 TA93 A93 9 T93 = true := by decide

theorem A93_exact_M : HasExactMaxSumAvoiding A93 9 :=
  ⟨⟨B93, B93_nodup, B93_sub, B93_sumAvoiding, B93_len⟩, certTree_upper_bound A93 TA93 TA93_list 9 T93 T93_valid⟩

def A94 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -17, -16, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA94 : ITree := .node 1 (.node (-30) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty))))) (.node (-11) (.node (-18) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node 0 (.node (-1) (.empty) (.empty)) (.empty)))))) (.node 32 (.node 13 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 20 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 18 (.node 17 (.empty) (.empty)) (.empty))) (.node 26 (.node 24 (.node 22 (.empty) (.empty)) (.empty)) (.node 30 (.node 28 (.empty) (.empty)) (.empty))))) (.node 88 (.node 52 (.node 40 (.node 36 (.node 34 (.empty) (.empty)) (.empty)) (.node 48 (.node 44 (.empty) (.empty)) (.empty))) (.node 64 (.node 60 (.node 56 (.empty) (.empty)) (.empty)) (.node 80 (.node 72 (.empty) (.empty)) (.empty)))) (.node 160 (.node 112 (.node 104 (.node 96 (.empty) (.empty)) (.empty)) (.node 144 (.node 128 (.empty) (.empty)) (.empty))) (.node 208 (.node 192 (.node 176 (.empty) (.empty)) (.empty)) (.node 336 (.empty) (.empty))))))
def B94 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -17]
def T94 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, 16, -16], [-176, 176, -160, 160, 32, -32], [-112, 112, 96, -96, -80, 80, -64, 64, -48, 48], [-104, 104, 88, -88, -72, 72, 56, -56, -40, 40, 24, -24, 8, -8], [-9, 7, -7, -5, -3, -1, 1, 3, 5, 9, 11, 13, 15, 17, -11, -13, -17], [60, -60, -52, 52, 44, -44, 36, -36, 28, -28, 20, -20, 12, -12, 4, -4], [34, -34, 30, -30, 26, -26, -22, 22, 18, -18, 14, -14, 10, -10, 6, -6, 2, -2]]

theorem A94_card : A94.length = 94 := rfl
theorem TA94_list : TA94.toList = A94 := rfl
theorem A94_nodup : A94.Nodup := isStrictlySortedBool_nodup A94 (by decide)
theorem B94_len : B94.length = 9 := rfl
theorem B94_nodup : B94.Nodup := isStrictlySortedBool_nodup B94 (by decide)
theorem B94_sub : ∀ x ∈ B94, x ∈ A94 := all_itree_mem A94 B94 TA94 TA94_list (by decide)
theorem B94_sumAvoiding : IsSumAvoiding A94 B94 := isSumAvoidingBool_sound A94 B94 (by decide)
theorem T94_valid : checkCertTree A94 TA94 A94 9 T94 = true := by decide

theorem A94_exact_M : HasExactMaxSumAvoiding A94 9 :=
  ⟨⟨B94, B94_nodup, B94_sub, B94_sumAvoiding, B94_len⟩, certTree_upper_bound A94 TA94 TA94_list 9 T94 T94_valid⟩

def A95 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA95 : ITree := .node 0 (.node (-30) (.node (-80) (.node (-144) (.node (-192) (.node (-208) (.node (-336) (.empty) (.empty)) (.empty)) (.node (-160) (.node (-176) (.empty) (.empty)) (.empty))) (.node (-104) (.node (-112) (.node (-128) (.empty) (.empty)) (.empty)) (.node (-88) (.node (-96) (.empty) (.empty)) (.empty)))) (.node (-48) (.node (-60) (.node (-64) (.node (-72) (.empty) (.empty)) (.empty)) (.node (-52) (.node (-56) (.empty) (.empty)) (.empty))) (.node (-36) (.node (-40) (.node (-44) (.empty) (.empty)) (.empty)) (.node (-32) (.node (-34) (.empty) (.empty)) (.empty))))) (.node (-12) (.node (-18) (.node (-24) (.node (-26) (.node (-28) (.empty) (.empty)) (.empty)) (.node (-20) (.node (-22) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-13) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-11) (.empty) (.empty)) (.empty)) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty)))))) (.node 30 (.node 12 (.node 6 (.node 3 (.node 2 (.node 1 (.empty) (.empty)) (.empty)) (.node 5 (.node 4 (.empty) (.empty)) (.empty))) (.node 9 (.node 8 (.node 7 (.empty) (.empty)) (.empty)) (.node 11 (.node 10 (.empty) (.empty)) (.empty)))) (.node 18 (.node 15 (.node 14 (.node 13 (.empty) (.empty)) (.empty)) (.node 17 (.node 16 (.empty) (.empty)) (.empty))) (.node 24 (.node 22 (.node 20 (.empty) (.empty)) (.empty)) (.node 28 (.node 26 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 34 (.node 32 (.empty) (.empty)) (.empty)) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B95 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -17]
def T95 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, 32, -32], [-112, 112, 96, -96, -80, 80, -64, 64, -48, 48], [104, -104, 88, -88, 72, -72, 56, -56, -40, 40, -24, 24, 8, -8], [60, -60, -52, 52, 44, -44, 36, -36, -28, 28, 20, -20, 12, -12, 4, -4], [5, 3, 7, 9, 1, 11, -1, 13, -3, 17, -5, -7, 15, -9, -11, -13, -15, -17], [34, -34, -30, 30, -26, 26, 22, -22, 18, -18, 14, -14, 10, -10, -6, 6, -2, 2]]

theorem A95_card : A95.length = 95 := rfl
theorem TA95_list : TA95.toList = A95 := rfl
theorem A95_nodup : A95.Nodup := isStrictlySortedBool_nodup A95 (by decide)
theorem B95_len : B95.length = 9 := rfl
theorem B95_nodup : B95.Nodup := isStrictlySortedBool_nodup B95 (by decide)
theorem B95_sub : ∀ x ∈ B95, x ∈ A95 := all_itree_mem A95 B95 TA95 TA95_list (by decide)
theorem B95_sumAvoiding : IsSumAvoiding A95 B95 := isSumAvoidingBool_sound A95 B95 (by decide)
theorem T95_valid : checkCertTree A95 TA95 A95 9 T95 = true := by decide

theorem A95_exact_M : HasExactMaxSumAvoiding A95 9 :=
  ⟨⟨B95, B95_nodup, B95_sub, B95_sumAvoiding, B95_len⟩, certTree_upper_bound A95 TA95 TA95_list 9 T95 T95_valid⟩

def A96 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -19, -18, -17, -16, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA96 : ITree := .node 1 (.node (-28) (.node (-72) (.node (-128) (.node (-176) (.node (-208) (.node (-336) (.empty) (.empty)) (.node (-192) (.empty) (.empty))) (.node (-144) (.node (-160) (.empty) (.empty)) (.empty))) (.node (-96) (.node (-104) (.node (-112) (.empty) (.empty)) (.empty)) (.node (-80) (.node (-88) (.empty) (.empty)) (.empty)))) (.node (-44) (.node (-56) (.node (-60) (.node (-64) (.empty) (.empty)) (.empty)) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty))) (.node (-34) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty)) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty))))) (.node (-11) (.node (-18) (.node (-22) (.node (-24) (.node (-26) (.empty) (.empty)) (.empty)) (.node (-19) (.node (-20) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node 0 (.node (-1) (.empty) (.empty)) (.empty)))))) (.node 30 (.node 13 (.node 7 (.node 4 (.node 3 (.node 2 (.empty) (.empty)) (.empty)) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 19 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 18 (.node 17 (.empty) (.empty)) (.empty))) (.node 24 (.node 22 (.node 20 (.empty) (.empty)) (.empty)) (.node 28 (.node 26 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 34 (.node 32 (.empty) (.empty)) (.empty)) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B96 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -19]
def T96 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, -32, 32], [-112, 112, -96, 96, 80, -80, 64, -64, -48, 48], [-104, 104, -88, 88, 72, -72, 56, -56, -40, 40, -24, 24, -8, 8], [-60, 60, 52, -52, -44, 44, -36, 36, 28, -28, 20, -20, -12, 12, 4, -4], [-34, 34, -30, 30, -26, 26, -22, 22, 18, -18, -14, 14, -10, 10, -6, 6, 2, -2], [-19, 19, -1, 1, 3, 5, 9, 11, 13, 15, 17, 7, -3, -13, -11, -9, -17, -7, -5]]

theorem A96_card : A96.length = 96 := rfl
theorem TA96_list : TA96.toList = A96 := rfl
theorem A96_nodup : A96.Nodup := isStrictlySortedBool_nodup A96 (by decide)
theorem B96_len : B96.length = 9 := rfl
theorem B96_nodup : B96.Nodup := isStrictlySortedBool_nodup B96 (by decide)
theorem B96_sub : ∀ x ∈ B96, x ∈ A96 := all_itree_mem A96 B96 TA96 TA96_list (by decide)
theorem B96_sumAvoiding : IsSumAvoiding A96 B96 := isSumAvoidingBool_sound A96 B96 (by decide)
theorem T96_valid : checkCertTree A96 TA96 A96 9 T96 = true := by decide

theorem A96_exact_M : HasExactMaxSumAvoiding A96 9 :=
  ⟨⟨B96, B96_nodup, B96_sub, B96_sumAvoiding, B96_len⟩, certTree_upper_bound A96 TA96 TA96_list 9 T96 T96_valid⟩

def A97 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA97 : ITree := .node 0 (.node (-28) (.node (-72) (.node (-128) (.node (-176) (.node (-208) (.node (-336) (.empty) (.empty)) (.node (-192) (.empty) (.empty))) (.node (-144) (.node (-160) (.empty) (.empty)) (.empty))) (.node (-96) (.node (-104) (.node (-112) (.empty) (.empty)) (.empty)) (.node (-80) (.node (-88) (.empty) (.empty)) (.empty)))) (.node (-44) (.node (-56) (.node (-60) (.node (-64) (.empty) (.empty)) (.empty)) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty))) (.node (-34) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty)) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty))))) (.node (-12) (.node (-18) (.node (-22) (.node (-24) (.node (-26) (.empty) (.empty)) (.empty)) (.node (-19) (.node (-20) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-13) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-11) (.empty) (.empty)) (.empty)) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty)))))) (.node 30 (.node 13 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 19 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 18 (.node 17 (.empty) (.empty)) (.empty))) (.node 24 (.node 22 (.node 20 (.empty) (.empty)) (.empty)) (.node 28 (.node 26 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 34 (.node 32 (.empty) (.empty)) (.empty)) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B97 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -19]
def T97 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, 32, -32], [-112, 112, 96, -96, -80, 80, 64, -64, 48, -48], [104, -104, 88, -88, -72, 72, 56, -56, -40, 40, 24, -24, -8, 8], [-60, 60, -52, 52, 44, -44, 36, -36, -28, 28, 20, -20, -12, 12, 4, -4], [-34, 34, 30, -30, 26, -26, 22, -22, 18, -18, -14, 14, -10, 10, -6, 6, -2, 2], [19, -19, 9, 17, 7, 5, 3, 11, 1, -1, 15, 13, -3, -5, -7, -9, -11, -13, -15, -17]]

theorem A97_card : A97.length = 97 := rfl
theorem TA97_list : TA97.toList = A97 := rfl
theorem A97_nodup : A97.Nodup := isStrictlySortedBool_nodup A97 (by decide)
theorem B97_len : B97.length = 9 := rfl
theorem B97_nodup : B97.Nodup := isStrictlySortedBool_nodup B97 (by decide)
theorem B97_sub : ∀ x ∈ B97, x ∈ A97 := all_itree_mem A97 B97 TA97 TA97_list (by decide)
theorem B97_sumAvoiding : IsSumAvoiding A97 B97 := isSumAvoidingBool_sound A97 B97 (by decide)
theorem T97_valid : checkCertTree A97 TA97 A97 9 T97 = true := by decide

theorem A97_exact_M : HasExactMaxSumAvoiding A97 9 :=
  ⟨⟨B97, B97_nodup, B97_sub, B97_sumAvoiding, B97_len⟩, certTree_upper_bound A97 TA97 TA97_list 9 T97 T97_valid⟩

def A98 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -21, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA98 : ITree := .node 0 (.node (-28) (.node (-72) (.node (-128) (.node (-176) (.node (-208) (.node (-336) (.empty) (.empty)) (.node (-192) (.empty) (.empty))) (.node (-144) (.node (-160) (.empty) (.empty)) (.empty))) (.node (-96) (.node (-104) (.node (-112) (.empty) (.empty)) (.empty)) (.node (-80) (.node (-88) (.empty) (.empty)) (.empty)))) (.node (-44) (.node (-56) (.node (-60) (.node (-64) (.empty) (.empty)) (.empty)) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty))) (.node (-34) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty)) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty))))) (.node (-12) (.node (-18) (.node (-21) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-19) (.node (-20) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-13) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-11) (.empty) (.empty)) (.empty)) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty)))))) (.node 30 (.node 14 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 13 (.node 12 (.empty) (.empty)) (.empty)))) (.node 20 (.node 17 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 19 (.node 18 (.empty) (.empty)) (.empty))) (.node 24 (.node 22 (.node 21 (.empty) (.empty)) (.empty)) (.node 28 (.node 26 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 34 (.node 32 (.empty) (.empty)) (.empty)) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B98 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -21, -17]
def T98 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, -32, 32], [-112, 112, 96, -96, 80, -80, 64, -64, -48, 48], [-104, 104, 88, -88, -72, 72, -56, 56, -40, 40, -24, 24, -8, 8], [60, -60, 52, -52, -44, 44, 36, -36, -28, 28, 20, -20, 12, -12, 4, -4], [-21, 21, -19, 19, 1, 7, 3, 13, 5, 9, 15, -1, -3, -5, -7, -9, -11, -13, -15], [-17, 17, -2, 2], [-34, 34, 30, -30, 26, -26, 22, -22, -18, 18, -14, 14, -10, 10, 6, -6]]

theorem A98_card : A98.length = 98 := rfl
theorem TA98_list : TA98.toList = A98 := rfl
theorem A98_nodup : A98.Nodup := isStrictlySortedBool_nodup A98 (by decide)
theorem B98_len : B98.length = 10 := rfl
theorem B98_nodup : B98.Nodup := isStrictlySortedBool_nodup B98 (by decide)
theorem B98_sub : ∀ x ∈ B98, x ∈ A98 := all_itree_mem A98 B98 TA98 TA98_list (by decide)
theorem B98_sumAvoiding : IsSumAvoiding A98 B98 := isSumAvoidingBool_sound A98 B98 (by decide)
theorem T98_valid : checkCertTree A98 TA98 A98 10 T98 = true := by decide

theorem A98_exact_M : HasExactMaxSumAvoiding A98 10 :=
  ⟨⟨B98, B98_nodup, B98_sub, B98_sumAvoiding, B98_len⟩, certTree_upper_bound A98 TA98 TA98_list 10 T98 T98_valid⟩

def A99 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -21, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA99 : ITree := .node 0 (.node (-28) (.node (-72) (.node (-128) (.node (-176) (.node (-208) (.node (-336) (.empty) (.empty)) (.node (-192) (.empty) (.empty))) (.node (-144) (.node (-160) (.empty) (.empty)) (.empty))) (.node (-96) (.node (-104) (.node (-112) (.empty) (.empty)) (.empty)) (.node (-80) (.node (-88) (.empty) (.empty)) (.empty)))) (.node (-44) (.node (-56) (.node (-60) (.node (-64) (.empty) (.empty)) (.empty)) (.node (-48) (.node (-52) (.empty) (.empty)) (.empty))) (.node (-34) (.node (-36) (.node (-40) (.empty) (.empty)) (.empty)) (.node (-30) (.node (-32) (.empty) (.empty)) (.empty))))) (.node (-12) (.node (-18) (.node (-21) (.node (-24) (.node (-26) (.empty) (.empty)) (.node (-22) (.empty) (.empty))) (.node (-19) (.node (-20) (.empty) (.empty)) (.empty))) (.node (-15) (.node (-16) (.node (-17) (.empty) (.empty)) (.empty)) (.node (-13) (.node (-14) (.empty) (.empty)) (.empty)))) (.node (-6) (.node (-9) (.node (-10) (.node (-11) (.empty) (.empty)) (.empty)) (.node (-7) (.node (-8) (.empty) (.empty)) (.empty))) (.node (-3) (.node (-4) (.node (-5) (.empty) (.empty)) (.empty)) (.node (-1) (.node (-2) (.empty) (.empty)) (.empty)))))) (.node 28 (.node 13 (.node 7 (.node 4 (.node 2 (.node 1 (.empty) (.empty)) (.node 3 (.empty) (.empty))) (.node 6 (.node 5 (.empty) (.empty)) (.empty))) (.node 10 (.node 9 (.node 8 (.empty) (.empty)) (.empty)) (.node 12 (.node 11 (.empty) (.empty)) (.empty)))) (.node 19 (.node 16 (.node 15 (.node 14 (.empty) (.empty)) (.empty)) (.node 18 (.node 17 (.empty) (.empty)) (.empty))) (.node 22 (.node 21 (.node 20 (.empty) (.empty)) (.empty)) (.node 26 (.node 24 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 32 (.node 30 (.empty) (.empty)) (.node 34 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B99 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -21, -17]
def T99 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, 32, -32], [-112, 112, 96, -96, -80, 80, 64, -64, -48, 48], [-104, 104, 88, -88, -72, 72, 56, -56, -40, 40, -24, 24, 8, -8], [60, -60, -52, 52, -44, 44, -36, 36, -28, 28, 20, -20, 12, -12, 4, -4], [-34, 34, 30, -30, -26, 26, 22, -22, -18, 18, -14, 14, -10, 10, 6, -6, -2, 2], [21, -21, 19, -19, 11, -9, -11, -7, -13, 15, -15, 13, 9, 7, -1, -5, -3, 1, 3, 5], [-17, 17]]

theorem A99_card : A99.length = 99 := rfl
theorem TA99_list : TA99.toList = A99 := rfl
theorem A99_nodup : A99.Nodup := isStrictlySortedBool_nodup A99 (by decide)
theorem B99_len : B99.length = 10 := rfl
theorem B99_nodup : B99.Nodup := isStrictlySortedBool_nodup B99 (by decide)
theorem B99_sub : ∀ x ∈ B99, x ∈ A99 := all_itree_mem A99 B99 TA99 TA99_list (by decide)
theorem B99_sumAvoiding : IsSumAvoiding A99 B99 := isSumAvoidingBool_sound A99 B99 (by decide)
theorem T99_valid : checkCertTree A99 TA99 A99 10 T99 = true := by decide

theorem A99_exact_M : HasExactMaxSumAvoiding A99 10 :=
  ⟨⟨B99, B99_nodup, B99_sub, B99_sumAvoiding, B99_len⟩, certTree_upper_bound A99 TA99 TA99_list 10 T99 T99_valid⟩

def A100 : List Int := [-336, -208, -192, -176, -160, -144, -128, -112, -104, -96, -88, -80, -72, -64, -60, -56, -52, -48, -44, -40, -36, -34, -32, -30, -28, -26, -24, -22, -21, -20, -19, -18, -17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 30, 32, 34, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 128, 144, 160, 176, 192, 208, 336]
def TA100 : ITree := .node 1 (.node (-26) (.node (-72) (.node (-128) (.node (-176) (.node (-208) (.node (-336) (.empty) (.empty)) (.node (-192) (.empty) (.empty))) (.node (-144) (.node (-160) (.empty) (.empty)) (.empty))) (.node (-96) (.node (-104) (.node (-112) (.empty) (.empty)) (.empty)) (.node (-80) (.node (-88) (.empty) (.empty)) (.empty)))) (.node (-40) (.node (-52) (.node (-60) (.node (-64) (.empty) (.empty)) (.node (-56) (.empty) (.empty))) (.node (-44) (.node (-48) (.empty) (.empty)) (.empty))) (.node (-32) (.node (-34) (.node (-36) (.empty) (.empty)) (.empty)) (.node (-28) (.node (-30) (.empty) (.empty)) (.empty))))) (.node (-11) (.node (-17) (.node (-20) (.node (-22) (.node (-24) (.empty) (.empty)) (.node (-21) (.empty) (.empty))) (.node (-18) (.node (-19) (.empty) (.empty)) (.empty))) (.node (-14) (.node (-15) (.node (-16) (.empty) (.empty)) (.empty)) (.node (-12) (.node (-13) (.empty) (.empty)) (.empty)))) (.node (-5) (.node (-8) (.node (-9) (.node (-10) (.empty) (.empty)) (.empty)) (.node (-6) (.node (-7) (.empty) (.empty)) (.empty))) (.node (-2) (.node (-3) (.node (-4) (.empty) (.empty)) (.empty)) (.node 0 (.node (-1) (.empty) (.empty)) (.empty)))))) (.node 28 (.node 14 (.node 8 (.node 5 (.node 3 (.node 2 (.empty) (.empty)) (.node 4 (.empty) (.empty))) (.node 7 (.node 6 (.empty) (.empty)) (.empty))) (.node 11 (.node 10 (.node 9 (.empty) (.empty)) (.empty)) (.node 13 (.node 12 (.empty) (.empty)) (.empty)))) (.node 20 (.node 17 (.node 16 (.node 15 (.empty) (.empty)) (.empty)) (.node 19 (.node 18 (.empty) (.empty)) (.empty))) (.node 23 (.node 22 (.node 21 (.empty) (.empty)) (.empty)) (.node 26 (.node 24 (.empty) (.empty)) (.empty))))) (.node 80 (.node 48 (.node 36 (.node 32 (.node 30 (.empty) (.empty)) (.node 34 (.empty) (.empty))) (.node 44 (.node 40 (.empty) (.empty)) (.empty))) (.node 60 (.node 56 (.node 52 (.empty) (.empty)) (.empty)) (.node 72 (.node 64 (.empty) (.empty)) (.empty)))) (.node 144 (.node 104 (.node 96 (.node 88 (.empty) (.empty)) (.empty)) (.node 128 (.node 112 (.empty) (.empty)) (.empty))) (.node 192 (.node 176 (.node 160 (.empty) (.empty)) (.empty)) (.node 336 (.node 208 (.empty) (.empty)) (.empty))))))
def B100 : List Int := [-336, -208, -192, -176, -112, -104, -60, -34, -21, -17]
def T100 : CertTree := .leafClique [[-336, 336, 0], [-208, 208, -128, 128], [-192, 192, -144, 144, -16, 16], [-176, 176, -160, 160, 32, -32], [-112, 112, 96, -96, -80, 80, 64, -64, 48, -48], [-104, 104, 88, -88, -72, 72, -56, 56, -40, 40, 24, -24, 8, -8], [60, -60, -52, 52, -44, 44, 36, -36, -28, 28, 20, -20, -12, 12, 4, -4], [-34, 34, -30, 30, 26, -26, -22, 22, 18, -18, 14, -14, -10, 10, -6, 6, -2, 2], [23, 21, -21, -19, -15, -9, -11, 11, 13, 9, -13, 5, -7, -5, -3, -1, 1, 3, 7], [19, -17, 17, 15]]

theorem A100_card : A100.length = 100 := rfl
theorem TA100_list : TA100.toList = A100 := rfl
theorem A100_nodup : A100.Nodup := isStrictlySortedBool_nodup A100 (by decide)
theorem B100_len : B100.length = 10 := rfl
theorem B100_nodup : B100.Nodup := isStrictlySortedBool_nodup B100 (by decide)
theorem B100_sub : ∀ x ∈ B100, x ∈ A100 := all_itree_mem A100 B100 TA100 TA100_list (by decide)
theorem B100_sumAvoiding : IsSumAvoiding A100 B100 := isSumAvoidingBool_sound A100 B100 (by decide)
theorem T100_valid : checkCertTree A100 TA100 A100 10 T100 = true := by decide

theorem A100_exact_M : HasExactMaxSumAvoiding A100 10 :=
  ⟨⟨B100, B100_nodup, B100_sub, B100_sumAvoiding, B100_len⟩, certTree_upper_bound A100 TA100 TA100_list 10 T100 T100_valid⟩

theorem all_49_new_witnesses_certified :
    (A52.length = 52 ∧ A52.Nodup ∧ HasExactMaxSumAvoiding A52 7) ∧
    (A53.length = 53 ∧ A53.Nodup ∧ HasExactMaxSumAvoiding A53 7) ∧
    (A54.length = 54 ∧ A54.Nodup ∧ HasExactMaxSumAvoiding A54 7) ∧
    (A55.length = 55 ∧ A55.Nodup ∧ HasExactMaxSumAvoiding A55 7) ∧
    (A56.length = 56 ∧ A56.Nodup ∧ HasExactMaxSumAvoiding A56 7) ∧
    (A57.length = 57 ∧ A57.Nodup ∧ HasExactMaxSumAvoiding A57 7) ∧
    (A58.length = 58 ∧ A58.Nodup ∧ HasExactMaxSumAvoiding A58 7) ∧
    (A59.length = 59 ∧ A59.Nodup ∧ HasExactMaxSumAvoiding A59 7) ∧
    (A60.length = 60 ∧ A60.Nodup ∧ HasExactMaxSumAvoiding A60 8) ∧
    (A61.length = 61 ∧ A61.Nodup ∧ HasExactMaxSumAvoiding A61 8) ∧
    (A62.length = 62 ∧ A62.Nodup ∧ HasExactMaxSumAvoiding A62 8) ∧
    (A63.length = 63 ∧ A63.Nodup ∧ HasExactMaxSumAvoiding A63 8) ∧
    (A64.length = 64 ∧ A64.Nodup ∧ HasExactMaxSumAvoiding A64 8) ∧
    (A65.length = 65 ∧ A65.Nodup ∧ HasExactMaxSumAvoiding A65 8) ∧
    (A66.length = 66 ∧ A66.Nodup ∧ HasExactMaxSumAvoiding A66 8) ∧
    (A67.length = 67 ∧ A67.Nodup ∧ HasExactMaxSumAvoiding A67 8) ∧
    (A68.length = 68 ∧ A68.Nodup ∧ HasExactMaxSumAvoiding A68 8) ∧
    (A69.length = 69 ∧ A69.Nodup ∧ HasExactMaxSumAvoiding A69 8) ∧
    (A70.length = 70 ∧ A70.Nodup ∧ HasExactMaxSumAvoiding A70 8) ∧
    (A71.length = 71 ∧ A71.Nodup ∧ HasExactMaxSumAvoiding A71 8) ∧
    (A72.length = 72 ∧ A72.Nodup ∧ HasExactMaxSumAvoiding A72 8) ∧
    (A73.length = 73 ∧ A73.Nodup ∧ HasExactMaxSumAvoiding A73 8) ∧
    (A74.length = 74 ∧ A74.Nodup ∧ HasExactMaxSumAvoiding A74 8) ∧
    (A75.length = 75 ∧ A75.Nodup ∧ HasExactMaxSumAvoiding A75 8) ∧
    (A76.length = 76 ∧ A76.Nodup ∧ HasExactMaxSumAvoiding A76 8) ∧
    (A77.length = 77 ∧ A77.Nodup ∧ HasExactMaxSumAvoiding A77 8) ∧
    (A78.length = 78 ∧ A78.Nodup ∧ HasExactMaxSumAvoiding A78 9) ∧
    (A79.length = 79 ∧ A79.Nodup ∧ HasExactMaxSumAvoiding A79 9) ∧
    (A80.length = 80 ∧ A80.Nodup ∧ HasExactMaxSumAvoiding A80 9) ∧
    (A81.length = 81 ∧ A81.Nodup ∧ HasExactMaxSumAvoiding A81 9) ∧
    (A82.length = 82 ∧ A82.Nodup ∧ HasExactMaxSumAvoiding A82 9) ∧
    (A83.length = 83 ∧ A83.Nodup ∧ HasExactMaxSumAvoiding A83 9) ∧
    (A84.length = 84 ∧ A84.Nodup ∧ HasExactMaxSumAvoiding A84 9) ∧
    (A85.length = 85 ∧ A85.Nodup ∧ HasExactMaxSumAvoiding A85 9) ∧
    (A86.length = 86 ∧ A86.Nodup ∧ HasExactMaxSumAvoiding A86 9) ∧
    (A87.length = 87 ∧ A87.Nodup ∧ HasExactMaxSumAvoiding A87 9) ∧
    (A88.length = 88 ∧ A88.Nodup ∧ HasExactMaxSumAvoiding A88 9) ∧
    (A89.length = 89 ∧ A89.Nodup ∧ HasExactMaxSumAvoiding A89 9) ∧
    (A90.length = 90 ∧ A90.Nodup ∧ HasExactMaxSumAvoiding A90 9) ∧
    (A91.length = 91 ∧ A91.Nodup ∧ HasExactMaxSumAvoiding A91 9) ∧
    (A92.length = 92 ∧ A92.Nodup ∧ HasExactMaxSumAvoiding A92 9) ∧
    (A93.length = 93 ∧ A93.Nodup ∧ HasExactMaxSumAvoiding A93 9) ∧
    (A94.length = 94 ∧ A94.Nodup ∧ HasExactMaxSumAvoiding A94 9) ∧
    (A95.length = 95 ∧ A95.Nodup ∧ HasExactMaxSumAvoiding A95 9) ∧
    (A96.length = 96 ∧ A96.Nodup ∧ HasExactMaxSumAvoiding A96 9) ∧
    (A97.length = 97 ∧ A97.Nodup ∧ HasExactMaxSumAvoiding A97 9) ∧
    (A98.length = 98 ∧ A98.Nodup ∧ HasExactMaxSumAvoiding A98 10) ∧
    (A99.length = 99 ∧ A99.Nodup ∧ HasExactMaxSumAvoiding A99 10) ∧
    (A100.length = 100 ∧ A100.Nodup ∧ HasExactMaxSumAvoiding A100 10) :=
  ⟨⟨A52_card, A52_nodup, A52_exact_M⟩,
   ⟨A53_card, A53_nodup, A53_exact_M⟩,
   ⟨A54_card, A54_nodup, A54_exact_M⟩,
   ⟨A55_card, A55_nodup, A55_exact_M⟩,
   ⟨A56_card, A56_nodup, A56_exact_M⟩,
   ⟨A57_card, A57_nodup, A57_exact_M⟩,
   ⟨A58_card, A58_nodup, A58_exact_M⟩,
   ⟨A59_card, A59_nodup, A59_exact_M⟩,
   ⟨A60_card, A60_nodup, A60_exact_M⟩,
   ⟨A61_card, A61_nodup, A61_exact_M⟩,
   ⟨A62_card, A62_nodup, A62_exact_M⟩,
   ⟨A63_card, A63_nodup, A63_exact_M⟩,
   ⟨A64_card, A64_nodup, A64_exact_M⟩,
   ⟨A65_card, A65_nodup, A65_exact_M⟩,
   ⟨A66_card, A66_nodup, A66_exact_M⟩,
   ⟨A67_card, A67_nodup, A67_exact_M⟩,
   ⟨A68_card, A68_nodup, A68_exact_M⟩,
   ⟨A69_card, A69_nodup, A69_exact_M⟩,
   ⟨A70_card, A70_nodup, A70_exact_M⟩,
   ⟨A71_card, A71_nodup, A71_exact_M⟩,
   ⟨A72_card, A72_nodup, A72_exact_M⟩,
   ⟨A73_card, A73_nodup, A73_exact_M⟩,
   ⟨A74_card, A74_nodup, A74_exact_M⟩,
   ⟨A75_card, A75_nodup, A75_exact_M⟩,
   ⟨A76_card, A76_nodup, A76_exact_M⟩,
   ⟨A77_card, A77_nodup, A77_exact_M⟩,
   ⟨A78_card, A78_nodup, A78_exact_M⟩,
   ⟨A79_card, A79_nodup, A79_exact_M⟩,
   ⟨A80_card, A80_nodup, A80_exact_M⟩,
   ⟨A81_card, A81_nodup, A81_exact_M⟩,
   ⟨A82_card, A82_nodup, A82_exact_M⟩,
   ⟨A83_card, A83_nodup, A83_exact_M⟩,
   ⟨A84_card, A84_nodup, A84_exact_M⟩,
   ⟨A85_card, A85_nodup, A85_exact_M⟩,
   ⟨A86_card, A86_nodup, A86_exact_M⟩,
   ⟨A87_card, A87_nodup, A87_exact_M⟩,
   ⟨A88_card, A88_nodup, A88_exact_M⟩,
   ⟨A89_card, A89_nodup, A89_exact_M⟩,
   ⟨A90_card, A90_nodup, A90_exact_M⟩,
   ⟨A91_card, A91_nodup, A91_exact_M⟩,
   ⟨A92_card, A92_nodup, A92_exact_M⟩,
   ⟨A93_card, A93_nodup, A93_exact_M⟩,
   ⟨A94_card, A94_nodup, A94_exact_M⟩,
   ⟨A95_card, A95_nodup, A95_exact_M⟩,
   ⟨A96_card, A96_nodup, A96_exact_M⟩,
   ⟨A97_card, A97_nodup, A97_exact_M⟩,
   ⟨A98_card, A98_nodup, A98_exact_M⟩,
   ⟨A99_card, A99_nodup, A99_exact_M⟩,
   ⟨A100_card, A100_nodup, A100_exact_M⟩⟩

end Erdos787NewWitnesses
