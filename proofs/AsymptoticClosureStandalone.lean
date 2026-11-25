/-
  AsymptoticClosureStandalone.lean
  Pure Lean 4 (Init-only, zero Mathlib, zero `sorry`, zero external axioms, zero `native_decide`).

  Formalizes newly proved unconditional asymptotic & structural theorems for Erdős Problem #787:
  1. Exact positive-part / negative-part preservation of sum-avoidance: M(A₊) ≤ M(A), M(A₋) ≤ M(A).
  2. Greedy maximum-to-minimum dyadic concentration: any positive set A with M(A) ≤ k satisfies
     |A| ≤ k * (max_{v ∈ A} |A ∩ (v, 2v)| + 1).
  3. Unconditional Dyadic Shell Cascade: greedy max-degree bound (|V| ≤ k * (D + 1)),
     top shell |A ∩ (M/2, M]| ≤ k, and shell recursion |A_j| ≤ k * (|A_{j-1}| + 1) ≤ (k + 1)^(j + 1).
  4. Single-Sphere Non-Extremality: every spherical vector set (`normSq u = R^2 > 0`, fixed dim d)
     satisfies |S| ≤ 2^d * M(S), ruling out single-sphere subpolynomial constructions.
  5. Multi-Scale 2-Adic Lattice Ball Upper-Bound Construction (Ruzsa's construction in Z^d and D_d):
     - Exact parallelogram norm-drop in Z^d (drop ≥ 1) and checkerboard D_d (drop ≥ 2 via 2^d cosets).
     - Carry-free radix embedding into strictly positive integers Z₊ with exact cardinality
       |A| ≥ (3 * d * t^2 + 1) * (2 * t + 1)^d and exact sum-avoiding cap ≤ (4 * d * t^2) * 2^d.
     - Explicit super-quadratic polynomial growth beating `k^2 + 3k - 11` at `(d = 6, t = 7)`
       and explicit quasi-polynomial growth `K = 8 * m * 2^(4m)` while `|A| ≥ 2^(2 * m^2 + 4m)`.
-/

namespace Erdos787AsymptoticClosure

/-! ### 1. Self-Contained Init Helpers -/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hn : 0 ≤ -x := by omega
    have heq : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
    rw [heq]
    exact Int.mul_nonneg hn hn

theorem int_sq_ge_one (x : Int) (hx : x ≠ 0) : 1 ≤ x * x := by
  by_cases hp : 0 < x
  · have h1 : (1 : Int) ≤ x := by omega
    have h0 : (0 : Int) ≤ 1 := by omega
    exact Int.mul_le_mul h1 h1 h0 (by omega)
  · have hn : (1 : Int) ≤ -x := by omega
    have h0 : (0 : Int) ≤ 1 := by omega
    have heq : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
    rw [heq]
    exact Int.mul_le_mul hn hn h0 (by omega)

def eraseOne {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | a :: as => if a = x then as else a :: eraseOne x as

theorem mem_eraseOne_of_ne {α : Type} [DecidableEq α] {x y : α} {L : List α}
    (hne : y ≠ x) (hy : y ∈ L) : y ∈ eraseOne x L := by
  induction L with
  | nil => cases hy
  | cons a t ih =>
    simp only [eraseOne]
    by_cases ha : a = x
    · subst ha
      simp only [ite_true]
      rcases List.mem_cons.mp hy with rfl | ht
      · exact absurd rfl hne
      · exact ht
    · simp only [ha, ite_false]
      rcases List.mem_cons.mp hy with rfl | ht
      · simp
      · exact List.mem_cons_of_mem a (ih ht)

theorem length_eraseOne_of_mem {α : Type} [DecidableEq α] {x : α} {L : List α}
    (hx : x ∈ L) : (eraseOne x L).length + 1 = L.length := by
  induction L with
  | nil => cases hx
  | cons a t ih =>
    simp only [eraseOne]
    by_cases ha : a = x
    · simp [ha]
    · simp only [ha, ite_false]
      rcases List.mem_cons.mp hx with rfl | ht
      · exact absurd rfl ha
      · have ih' := ih ht
        simp only [List.length_cons]
        omega

theorem nodup_length_le_of_inj {α β : Type} [DecidableEq β] (L : List α) (M : List β)
    (hL : L.Nodup) (f : α → β)
    (hf_mem : ∀ x ∈ L, f x ∈ M)
    (hf_inj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) :
    L.length ≤ M.length := by
  induction L generalizing M with
  | nil => simp
  | cons a t ih =>
    have hnd : t.Nodup := (List.nodup_cons.mp hL).2
    have hanot : a ∉ t := (List.nodup_cons.mp hL).1
    have hfa : f a ∈ M := hf_mem a (by simp)
    let M' := eraseOne (f a) M
    have hsub : ∀ x ∈ t, f x ∈ M' := by
      intro x hx
      have hxM : f x ∈ M := hf_mem x (List.mem_cons_of_mem a hx)
      have hne : f x ≠ f a := by
        intro heq
        have hxa := hf_inj x (List.mem_cons_of_mem a hx) a (by simp) heq
        exact hanot (hxa ▸ hx)
      exact mem_eraseOne_of_ne hne hxM
    have hinj' : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y :=
      fun x hx y hy => hf_inj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    have ih_t := ih M' hnd hsub hinj'
    have hlen_M' : M'.length + 1 = M.length := length_eraseOne_of_mem hfa
    simp only [List.length_cons]
    omega

theorem filter_sublist_length_le {α : Type} (p q : α → Bool) (L : List α) :
    ((L.filter p).filter q).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    by_cases hp : p a = true <;> by_cases hq : q a = true
    · simp only [List.filter_cons, hp, hq, ite_true, List.length_cons]
      exact Nat.succ_le_succ ih
    · have hqf : q a = false := Bool.eq_false_iff.mpr hq
      simp only [List.filter_cons, hp, hqf, ite_true]
      exact ih
    · have hpf : p a = false := Bool.eq_false_iff.mpr hp
      simp only [List.filter_cons, hpf, hq, ite_true, List.length_cons]
      exact Nat.le_trans ih (Nat.le_succ _)
    · have hpf : p a = false := Bool.eq_false_iff.mpr hp
      have hqf : q a = false := Bool.eq_false_iff.mpr hq
      simp only [List.filter_cons, hpf, hqf]
      exact ih

theorem filter_compl_split {α : Type} (p : α → Bool) (L : List α) :
    L.length = (L.filter p).length + (L.filter (fun x => !(p x))).length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    by_cases hp : p a = true
    · simp [hp, List.length_cons]
      omega
    · have hf : p a = false := Bool.eq_false_iff.mpr hp
      simp [hf, List.length_cons]
      omega

theorem nodup_map_on {α β : Type} (f : α → β) (L : List α)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) (hL : L.Nodup) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have hnd : t.Nodup := (List.nodup_cons.mp hL).2
    have hnot : a ∉ t := (List.nodup_cons.mp hL).1
    have ih' := ih (fun x hx y hy => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih'⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨y, hy, heq⟩
    have := hinj y (List.mem_cons_of_mem a hy) a (by simp) heq
    subst this
    exact hnot hy

theorem nodup_append {α : Type} (L1 L2 : List α)
    (h1 : L1.Nodup) (h2 : L2.Nodup) (hdisj : ∀ x ∈ L1, x ∉ L2) :
    (L1 ++ L2).Nodup := by
  induction L1 with
  | nil => simp; exact h2
  | cons a t ih =>
    have h1t : t.Nodup := (List.nodup_cons.mp h1).2
    have hanot : a ∉ t := (List.nodup_cons.mp h1).1
    have hdisj' : ∀ x ∈ t, x ∉ L2 := fun x hx => hdisj x (List.mem_cons_of_mem a hx)
    have ih' := ih h1t hdisj'
    simp only [List.cons_append, List.nodup_cons, List.mem_append]
    refine ⟨?_, ih'⟩
    rintro (ht | hl2)
    · exact hanot ht
    · exact hdisj a (by simp) hl2

theorem nodup_flatMap_aux {α β : Type} (f : α → List β) (L : List α)
    (hL : L.Nodup)
    (heach : ∀ a ∈ L, (f a).Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ z ∈ f a, z ∉ f b) :
    (L.flatMap f).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ht_nd : t.Nodup := (List.nodup_cons.mp hL).2
    have hanot : a ∉ t := (List.nodup_cons.mp hL).1
    have ih' := ih ht_nd (fun x hx => heach x (List.mem_cons_of_mem a hx))
      (fun x hx y hy hne => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hne)
    simp only [List.flatMap_cons]
    apply nodup_append _ _ (heach a (by simp)) ih'
    intro z hza hzt
    rcases List.mem_flatMap.mp hzt with ⟨b, hb, hzb⟩
    have hne : a ≠ b := fun heq => hanot (heq ▸ hb)
    exact hdisj a (by simp) b (List.mem_cons_of_mem a hb) hne z hza hzb

/-! ### 2. Positive/Negative Decomposition of Sum-Avoidance -/

def IsSumAvoiding (A B : List Int) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ≠ y → (x + y) ∉ A

def MaxSumAvoidingAtMost (A : List Int) (k : Nat) : Prop :=
  ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ A) → IsSumAvoiding A B → B.length ≤ k

def posPart (A : List Int) : List Int :=
  A.filter (fun x => decide (0 < x))

def negPart (A : List Int) : List Int :=
  A.filter (fun x => decide (x < 0))

theorem posPart_preserves_sum_avoiding (A B : List Int)
    (hBsub : ∀ x ∈ B, x ∈ posPart A)
    (hBsa : IsSumAvoiding (posPart A) B) : IsSumAvoiding A B := by
  intro x hx y hy hne hsum
  have hx_pos : 0 < x := of_decide_eq_true (List.mem_filter.mp (hBsub x hx)).2
  have hy_pos : 0 < y := of_decide_eq_true (List.mem_filter.mp (hBsub y hy)).2
  have hsum_mem : x + y ∈ posPart A :=
    List.mem_filter.mpr ⟨hsum, decide_eq_true (Int.add_pos hx_pos hy_pos)⟩
  exact hBsa x hx y hy hne hsum_mem

theorem posPart_maxSumAvoidingAtMost (A : List Int) (k : Nat)
    (hA : MaxSumAvoidingAtMost A k) : MaxSumAvoidingAtMost (posPart A) k := by
  intro B hBnd hBsub hBsa
  apply hA B hBnd
  · intro x hx
    exact (List.mem_filter.mp (hBsub x hx)).1
  · exact posPart_preserves_sum_avoiding A B hBsub hBsa

theorem negPart_preserves_sum_avoiding (A B : List Int)
    (hBsub : ∀ x ∈ B, x ∈ negPart A)
    (hBsa : IsSumAvoiding (negPart A) B) : IsSumAvoiding A B := by
  intro x hx y hy hne hsum
  have hx_neg : x < 0 := of_decide_eq_true (List.mem_filter.mp (hBsub x hx)).2
  have hy_neg : y < 0 := of_decide_eq_true (List.mem_filter.mp (hBsub y hy)).2
  have hsum_mem : x + y ∈ negPart A :=
    List.mem_filter.mpr ⟨hsum, decide_eq_true (by omega)⟩
  exact hBsa x hx y hy hne hsum_mem

theorem negPart_maxSumAvoidingAtMost (A : List Int) (k : Nat)
    (hA : MaxSumAvoidingAtMost A k) : MaxSumAvoidingAtMost (negPart A) k := by
  intro B hBnd hBsub hBsa
  apply hA B hBnd
  · intro x hx
    exact (List.mem_filter.mp (hBsub x hx)).1
  · exact negPart_preserves_sum_avoiding A B hBsub hBsa

theorem length_le_pos_neg_zero (A : List Int) (hA : A.Nodup) :
    A.length ≤ (posPart A).length + (negPart A).length + 1 := by
  induction A with
  | nil => simp [posPart, negPart]
  | cons a t ih =>
    have hnd : t.Nodup := (List.nodup_cons.mp hA).2
    have hnot : a ∉ t := (List.nodup_cons.mp hA).1
    have ih' := ih hnd
    by_cases ha_pos : 0 < a
    · have hp : (posPart (a :: t)).length = (posPart t).length + 1 := by
        simp [posPart, ha_pos]
      have hn : (negPart (a :: t)).length = (negPart t).length := by
        have hnf : ¬(a < 0) := by omega
        simp [negPart, hnf]
      simp only [List.length_cons]
      omega
    · by_cases ha_neg : a < 0
      · have hp : (posPart (a :: t)).length = (posPart t).length := by
          simp [posPart, ha_pos]
        have hn : (negPart (a :: t)).length = (negPart t).length + 1 := by
          simp [negPart, ha_neg]
        simp only [List.length_cons]
        omega
      · have ha0 : a = 0 := by omega
        subst ha0
        have ht_le : t.length ≤ (posPart t).length + (negPart t).length := by
          clear ih' ih hA hnd ha_pos ha_neg
          induction t with
          | nil => simp [posPart, negPart]
          | cons b s ihs =>
            have hb0 : b ≠ 0 := fun heq => hnot (by subst heq; simp)
            have hs_not : 0 ∉ s := fun hm => hnot (List.mem_cons_of_mem b hm)
            have hs_le := ihs hs_not
            by_cases hbp : 0 < b
            · have hp : (posPart (b :: s)).length = (posPart s).length + 1 := by simp [posPart, hbp]
              have hn : (negPart (b :: s)).length = (negPart s).length := by
                have : ¬(b < 0) := by omega
                simp [negPart, this]
              simp only [List.length_cons]
              omega
            · have hbn : b < 0 := by omega
              have hp : (posPart (b :: s)).length = (posPart s).length := by simp [posPart, hbp]
              have hn : (negPart (b :: s)).length = (negPart s).length + 1 := by simp [negPart, hbn]
              simp only [List.length_cons]
              omega
        have hp0 : (posPart ((0 : Int) :: t)).length = (posPart t).length := by
          have : ¬((0 : Int) < 0) := by omega
          simp [posPart, this]
        have hn0 : (negPart ((0 : Int) :: t)).length = (negPart t).length := by
          have : ¬((0 : Int) < 0) := by omega
          simp [negPart, this]
        simp only [List.length_cons]
        omega

/-! ### 3. Dyadic Shell Cascade & Dyadic Down-Degree Concentration -/

def topShell (A : List Int) (M : Int) : List Int :=
  A.filter (fun x => decide (M < 2 * x))

theorem dyadic_top_shell_le (A : List Int) (M : Int) (k : Nat)
    (hA_nd : A.Nodup)
    (hA_le : ∀ x ∈ A, x ≤ M)
    (halpha : MaxSumAvoidingAtMost A k) :
    (topShell A M).length ≤ k := by
  apply halpha (topShell A M) (hA_nd.filter _)
  · intro x hx
    exact (List.mem_filter.mp hx).1
  · intro x hx y hy _hne hsum
    have hx_gt : M < 2 * x := of_decide_eq_true (List.mem_filter.mp hx).2
    have hy_gt : M < 2 * y := of_decide_eq_true (List.mem_filter.mp hy).2
    have hsum_le : x + y ≤ M := hA_le (x + y) hsum
    omega

theorem greedy_maxDeg_indep_aux (adj : Int → Int → Bool)
    (hirr : ∀ x, adj x x = false) (hsymm : ∀ x y, adj x y = adj y x) :
    ∀ (N : Nat) (V : List Int), V.length ≤ N → V.Nodup → ∀ (D k : Nat),
      (∀ v ∈ V, (V.filter (adj v)).length ≤ D) →
      (∀ I : List Int, I.Nodup → (∀ x ∈ I, x ∈ V) →
        (∀ x ∈ I, ∀ y ∈ I, adj x y = false) → I.length ≤ k) →
      V.length ≤ k * (D + 1) := by
  intro N
  induction N with
  | zero =>
    intro V hlen _ D k _ _
    have h0 : V.length = 0 := by omega
    rw [h0]
    exact Nat.zero_le _
  | succ N ih =>
    intro V hlen hnd D k hdeg halpha
    cases V with
    | nil => simp
    | cons v t =>
      have hv_nd : t.Nodup := (List.nodup_cons.mp hnd).2
      have hnot_v : v ∉ t := (List.nodup_cons.mp hnd).1
      by_cases hk0 : k = 0
      · exfalso
        have h1 := halpha [v] (by simp) (by simp) (by
          intro x hx y hy
          simp only [List.mem_singleton] at hx hy
          rw [hx, hy]
          exact hirr v)
        simp at h1
        omega
      · let t' := t.filter (fun u => !(adj v u))
        have ht'_len_le : t'.length ≤ N := by
          have : t'.length ≤ t.length := List.length_filter_le _ _
          simp only [List.length_cons] at hlen
          omega
        have ht'_nd : t'.Nodup := hv_nd.filter _
        have hdeg' : ∀ u ∈ t', (t'.filter (adj u)).length ≤ D := by
          intro u hu
          have hu_V : u ∈ v :: t := List.mem_cons_of_mem v (List.mem_filter.mp hu).1
          have hsub_filt : (t'.filter (adj u)).length ≤ (t.filter (adj u)).length :=
            filter_sublist_length_le _ _ _
          have hstep2 : (t.filter (adj u)).length ≤ ((v :: t).filter (adj u)).length := by
            simp only [List.filter_cons]
            cases adj u v <;> simp
          exact Nat.le_trans hsub_filt (Nat.le_trans hstep2 (hdeg u hu_V))
        have halpha' : ∀ I : List Int, I.Nodup → (∀ x ∈ I, x ∈ t') →
            (∀ x ∈ I, ∀ y ∈ I, adj x y = false) → I.length ≤ k - 1 := by
          intro I hInd hIsub hIadj
          have hv_notin_I : v ∉ I := fun hm =>
            hnot_v (List.mem_filter.mp (hIsub v hm)).1
          have hI'nd : (v :: I).Nodup := List.nodup_cons.mpr ⟨hv_notin_I, hInd⟩
          have hI'sub : ∀ x ∈ v :: I, x ∈ v :: t := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hxt
            · simp
            · exact List.mem_cons_of_mem v (List.mem_filter.mp (hIsub x hxt)).1
          have hI'adj : ∀ x ∈ v :: I, ∀ y ∈ v :: I, adj x y = false := by
            intro x hx y hy
            rcases List.mem_cons.mp hx with hxv | hxt <;> rcases List.mem_cons.mp hy with hyv | hyt
            · rw [hxv, hyv]; exact hirr v
            · rw [hxv]
              have hf := (List.mem_filter.mp (hIsub y hyt)).2
              simp only [Bool.not_eq_true'] at hf
              exact hf
            · rw [hyv]
              have hf := (List.mem_filter.mp (hIsub x hxt)).2
              simp only [Bool.not_eq_true'] at hf
              rw [hsymm x v]
              exact hf
            · exact hIadj x hxt y hyt
          have hk_le := halpha (v :: I) hI'nd hI'sub hI'adj
          simp only [List.length_cons] at hk_le
          omega
        have hIH := ih t' ht'_len_le ht'_nd D (k - 1) hdeg' halpha'
        have hsplit : t.length = (t.filter (adj v)).length + t'.length :=
          filter_compl_split (adj v) t
        have hrm_le : (t.filter (adj v)).length ≤ D := by
          have hv_deg := hdeg v (by simp)
          simp only [List.filter_cons, hirr v] at hv_deg
          exact hv_deg
        have hmul : k * (D + 1) = (k - 1) * (D + 1) + (D + 1) := by
          cases k with
          | zero => contradiction
          | succ k' => simp [Nat.succ_mul]
        simp only [List.length_cons]
        omega

theorem greedy_maxDeg_indep_bound (adj : Int → Int → Bool)
    (hirr : ∀ x, adj x x = false) (hsymm : ∀ x y, adj x y = adj y x)
    (V : List Int) (hnd : V.Nodup) (D k : Nat)
    (hdeg : ∀ v ∈ V, (V.filter (adj v)).length ≤ D)
    (halpha : ∀ I : List Int, I.Nodup → (∀ x ∈ I, x ∈ V) →
      (∀ x ∈ I, ∀ y ∈ I, adj x y = false) → I.length ≤ k) :
    V.length ≤ k * (D + 1) :=
  greedy_maxDeg_indep_aux adj hirr hsymm V.length V (Nat.le_refl _) hnd D k hdeg halpha

def dyadicSlice (A : List Int) (L : Int) : List Int :=
  A.filter (fun x => decide (L < x ∧ x ≤ 2 * L))

theorem dyadic_shell_cascade_step (A : List Int) (hA : A.Nodup) (L : Int) (k : Nat)
    (halpha : MaxSumAvoidingAtMost A k) :
    (dyadicSlice A L).length ≤ k * ((dyadicSlice A (2 * L)).length + 1) := by
  let S := dyadicSlice A L
  let U := dyadicSlice A (2 * L)
  let adj : Int → Int → Bool := fun u v => decide (u ≠ v ∧ u + v ∈ A)
  have hirr : ∀ x, adj x x = false := by intro x; simp [adj]
  have hsymm : ∀ x y, adj x y = adj y x := by
    intro x y
    by_cases h : x = y
    · subst h; simp [adj]
    · have h' : y ≠ x := fun e => h e.symm
      by_cases hm : x + y ∈ A
      · have hm' : y + x ∈ A := by rwa [Int.add_comm]
        simp [adj, h, h', hm, hm']
      · have hm' : y + x ∉ A := by intro hp; exact hm (by rwa [Int.add_comm] at hp)
        simp [adj, h, h', hm, hm']
  have hS_nd : S.Nodup := hA.filter _
  have hdeg : ∀ u ∈ S, (S.filter (adj u)).length ≤ U.length := by
    intro u hu
    have hu_b := of_decide_eq_true (List.mem_filter.mp hu).2
    apply nodup_length_le_of_inj _ U (hS_nd.filter _) (fun v => u + v)
    · intro v hv
      have hv_f := List.mem_filter.mp hv
      have hv_S := hv_f.1
      have hv_b := of_decide_eq_true (List.mem_filter.mp hv_S).2
      have hadj := of_decide_eq_true hv_f.2
      exact List.mem_filter.mpr ⟨hadj.2, decide_eq_true (by omega)⟩
    · intro v1 _ v2 _ heq; omega
  have hS_alpha : ∀ I : List Int, I.Nodup → (∀ x ∈ I, x ∈ S) →
      (∀ x ∈ I, ∀ y ∈ I, adj x y = false) → I.length ≤ k := by
    intro I hInd hIsub hIadj
    apply halpha I hInd
    · intro x hx
      exact (List.mem_filter.mp (hIsub x hx)).1
    · intro x hx y hy hne hsum
      have hf := hIadj x hx y hy
      have : adj x y = true := decide_eq_true ⟨hne, hsum⟩
      rw [this] at hf
      contradiction
  exact greedy_maxDeg_indep_bound adj hirr hsymm S hS_nd U.length k hdeg hS_alpha

theorem dyadic_shell_power_bound (k : Nat) (s : Nat → Nat)
    (hs0 : s 0 ≤ k) (hstep : ∀ j, s (j + 1) ≤ k * (s j + 1)) :
    ∀ j, s j ≤ (k + 1) ^ (j + 1) := by
  intro j
  induction j with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_one]
    omega
  | succ j ih =>
    have h1 := hstep j
    have h2 : k * (s j + 1) ≤ k * ((k + 1) ^ (j + 1) + 1) :=
      Nat.mul_le_mul_left k (Nat.succ_le_succ ih)
    have h3 : k * ((k + 1) ^ (j + 1) + 1) ≤ (k + 1) * (k + 1) ^ (j + 1) := by
      have hk_le : k ≤ (k + 1) ^ (j + 1) := by
        have hpos1 : 0 < k + 1 := by omega
        have hp := Nat.pow_le_pow_right hpos1 (show 1 ≤ j + 1 by omega)
        simp only [Nat.pow_one] at hp
        have hle : k ≤ k + 1 := by omega
        exact Nat.le_trans hle hp
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
      omega
    have h3' : k * ((k + 1) ^ (j + 1) + 1) ≤ (k + 1) ^ (j + 1 + 1) := by
      have heq : (k + 1) ^ (j + 1 + 1) = (k + 1) * (k + 1) ^ (j + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [heq]
      exact h3
    exact Nat.le_trans h1 (Nat.le_trans h2 h3')

theorem dyadic_concentration_desc_aux :
    ∀ (N : Nat) (rem full : List Int),
      rem.length ≤ N → rem.Nodup → rem.Pairwise (· > ·) →
      (∀ x ∈ rem, 0 < x ∧ x ∈ full) →
      ∀ (D k : Nat),
      (∀ v ∈ rem, (full.filter (fun z => decide (v < z ∧ z < 2 * v))).length ≤ D) →
      (∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ rem) → IsSumAvoiding full B → B.length ≤ k) →
      rem.length ≤ k * (D + 1) := by
  intro N
  induction N with
  | zero =>
    intro rem _ hlen _ _ _ D k _ _
    have h0 : rem.length = 0 := by omega
    rw [h0]
    exact Nat.zero_le _
  | succ N ih =>
    intro rem full hlen hnd hpw hsub D k hD halpha
    cases rem with
    | nil => simp
    | cons v t =>
      by_cases hk0 : k = 0
      · exfalso
        have h1 := halpha [v] (by simp) (by simp) (fun x hx y hy hne => by
          simp only [List.mem_singleton] at hx hy
          rw [hx, hy] at hne
          exact absurd rfl hne)
        simp at h1
        omega
      · let elim := t.filter (fun u => decide (v + u ∈ full))
        let rem' := t.filter (fun u => !(decide (v + u ∈ full)))
        have hnd_t : t.Nodup := (List.nodup_cons.mp hnd).2
        have hpw_t : t.Pairwise (· > ·) := (List.pairwise_cons.mp hpw).2
        have hv_gt_t : ∀ u ∈ t, v > u := (List.pairwise_cons.mp hpw).1
        have hrem'_len : rem'.length ≤ N := by
          have : rem'.length ≤ t.length := List.length_filter_le _ _
          simp only [List.length_cons] at hlen
          omega
        have hrem'_nd : rem'.Nodup := hnd_t.filter _
        have hrem'_pw : rem'.Pairwise (· > ·) := hpw_t.filter _
        have hrem'_sub : ∀ x ∈ rem', 0 < x ∧ x ∈ full := fun x hx =>
          hsub x (List.mem_cons_of_mem v (List.mem_filter.mp hx).1)
        have hD' : ∀ u ∈ rem', (full.filter (fun z => decide (u < z ∧ z < 2 * u))).length ≤ D :=
          fun u hu => hD u (List.mem_cons_of_mem v (List.mem_filter.mp hu).1)
        have halpha' : ∀ B : List Int, B.Nodup → (∀ x ∈ B, x ∈ rem') →
            IsSumAvoiding full B → B.length ≤ k - 1 := by
          intro B hBnd hBsub hBsa
          have hv_notin : v ∉ B := fun hm =>
            (List.nodup_cons.mp hnd).1 (List.mem_filter.mp (hBsub v hm)).1
          have hB'nd : (v :: B).Nodup := List.nodup_cons.mpr ⟨hv_notin, hBnd⟩
          have hB'sub : ∀ x ∈ v :: B, x ∈ v :: t := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hxt
            · simp
            · exact List.mem_cons_of_mem v (List.mem_filter.mp (hBsub x hxt)).1
          have hB'sa : IsSumAvoiding full (v :: B) := by
            intro x hx y hy hne hsum
            rcases List.mem_cons.mp hx with hxv | hxt <;> rcases List.mem_cons.mp hy with hyv | hyt
            · rw [hxv, hyv] at hne; exact hne rfl
            · rw [hxv] at hsum
              have hf := (List.mem_filter.mp (hBsub y hyt)).2
              have ht : decide (v + y ∈ full) = true := decide_eq_true hsum
              rw [ht] at hf; cases hf
            · rw [hyv, Int.add_comm] at hsum
              have hf := (List.mem_filter.mp (hBsub x hxt)).2
              have ht : decide (v + x ∈ full) = true := decide_eq_true hsum
              rw [ht] at hf; cases hf
            · exact hBsa x hxt y hyt hne hsum
          have hk_le := halpha (v :: B) hB'nd hB'sub hB'sa
          simp only [List.length_cons] at hk_le
          omega
        have hIH := ih rem' full hrem'_len hrem'_nd hrem'_pw hrem'_sub D (k - 1) hD' halpha'
        have helim_le : elim.length ≤ D := by
          have hv_D := hD v (by simp)
          apply Nat.le_trans _ hv_D
          apply nodup_length_le_of_inj elim _ (hnd_t.filter _) (fun u => v + u)
          · intro u hu
            have hu_f := List.mem_filter.mp hu
            have hu_t := hu_f.1
            have hu_pos : 0 < u := (hsub u (List.mem_cons_of_mem v hu_t)).1
            have hu_lt : u < v := hv_gt_t u hu_t
            have hmem : v + u ∈ full := of_decide_eq_true hu_f.2
            exact List.mem_filter.mpr ⟨hmem, decide_eq_true (by omega)⟩
          · intro u1 _ u2 _ heq; omega
        have hsplit : t.length = elim.length + rem'.length :=
          filter_compl_split (fun u => decide (v + u ∈ full)) t
        have hmul : k * (D + 1) = (k - 1) * (D + 1) + (D + 1) := by
          cases k with
          | zero => contradiction
          | succ k' => simp [Nat.succ_mul]
        simp only [List.length_cons]
        omega

theorem dyadic_concentration_bound (A : List Int) (hnd : A.Nodup) (hpw : A.Pairwise (· > ·))
    (hpos : ∀ x ∈ A, 0 < x) (D k : Nat)
    (hD : ∀ v ∈ A, (A.filter (fun z => decide (v < z ∧ z < 2 * v))).length ≤ D)
    (halpha : MaxSumAvoidingAtMost A k) :
    A.length ≤ k * (D + 1) :=
  dyadic_concentration_desc_aux A.length A A (Nat.le_refl _) hnd hpw
    (fun x hx => ⟨hpos x hx, hx⟩) D k hD halpha

/-! ### 4. Vector Algebra, Norm-Squared, and Single-Sphere Non-Extremality -/

def vecAdd : List Int → List Int → List Int
  | x :: xs, y :: ys => (x + y) :: vecAdd xs ys
  | _, _ => []

def vecSub : List Int → List Int → List Int
  | x :: xs, y :: ys => (x - y) :: vecSub xs ys
  | _, _ => []

def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

def normSq (u : List Int) : Int :=
  dot u u

theorem vecAdd_length (u v : List Int) (h : u.length = v.length) :
    (vecAdd u v).length = u.length := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h ⊢
      have ih' := ih ys (by omega)
      simp [vecAdd, ih']

theorem vecSub_length (u v : List Int) (h : u.length = v.length) :
    (vecSub u v).length = u.length := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h ⊢
      have ih' := ih ys (by omega)
      simp [vecSub, ih']

theorem dot_comm (u v : List Int) : dot u v = dot v u := by
  induction u generalizing v with
  | nil => cases v <;> simp [dot]
  | cons a xs ih =>
    cases v with
    | nil => simp [dot]
    | cons b ys =>
      simp only [dot]
      rw [Int.mul_comm a b, ih ys]

theorem normSq_nonneg (u : List Int) : 0 ≤ normSq u := by
  unfold normSq
  induction u with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [dot]
    have hx : 0 ≤ x * x := int_sq_nonneg x
    omega

theorem normSq_eq_zero_iff (u : List Int) : normSq u = 0 ↔ ∀ x ∈ u, x = 0 := by
  unfold normSq
  induction u with
  | nil => simp [dot]
  | cons x xs ih =>
    simp only [dot, List.mem_cons]
    have hx : 0 ≤ x * x := int_sq_nonneg x
    have hxs : 0 ≤ dot xs xs := normSq_nonneg xs
    constructor
    · intro heq y hy
      have hx2 : x * x = 0 := by omega
      have hxs0 : dot xs xs = 0 := by omega
      have hx0 : x = 0 := (Int.mul_eq_zero.mp hx2).elim id id
      rcases hy with rfl | hmem
      · exact hx0
      · exact (ih.mp hxs0) y hmem
    · intro hall
      have hx0 : x = 0 := hall x (Or.inl rfl)
      have hxs0 : dot xs xs = 0 := ih.mpr (fun y hy => hall y (Or.inr hy))
      simp [hx0, hxs0]

theorem normSq_pos_of_ne_zero (u : List Int) (hne : ∃ x ∈ u, x ≠ 0) : 1 ≤ normSq u := by
  have hge : 0 ≤ normSq u := normSq_nonneg u
  have hne0 : normSq u ≠ 0 := by
    intro h0
    have hall := (normSq_eq_zero_iff u).mp h0
    rcases hne with ⟨x, hx, hnx⟩
    exact hnx (hall x hx)
  omega

theorem normSq_vecAdd (u v : List Int) (hlen : u.length = v.length) :
    normSq (vecAdd u v) = normSq u + normSq v + 2 * dot u v := by
  induction u generalizing v with
  | nil => cases v with | nil => simp [normSq, vecAdd, dot] | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      have ih' := ih ys (by omega)
      simp only [normSq, vecAdd, dot] at ih' ⊢
      have halg : (a + b) * (a + b) = a * a + b * b + 2 * (a * b) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
        omega
      omega

def signOrthantTag (u : List Int) : List Bool :=
  u.map (fun x => decide (0 ≤ x))

theorem signOrthantTag_length (u : List Int) : (signOrthantTag u).length = u.length := by
  simp [signOrthantTag]

theorem dot_nonneg_of_same_signOrthant (u v : List Int) (hlen : u.length = v.length)
    (htag : signOrthantTag u = signOrthantTag v) : 0 ≤ dot u v := by
  induction u generalizing v with
  | nil => cases v with | nil => simp [dot] | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      simp only [signOrthantTag, List.map_cons, List.cons.injEq] at htag
      have ih' := ih ys (by omega) htag.2
      simp only [dot]
      have hab : 0 ≤ a * b := by
        by_cases ha : 0 ≤ a
        · have hb : 0 ≤ b := of_decide_eq_true (by rw [← htag.1]; exact decide_eq_true ha)
          exact Int.mul_nonneg ha hb
        · have hb' : ¬(0 ≤ b) := by
            intro hb
            have h1 := htag.1
            rw [decide_eq_false ha, decide_eq_true hb] at h1
            contradiction
          have hneg : (-a) * (-b) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
          have heq : a * b = (-a) * (-b) := (Int.neg_mul_neg a b).symm
          omega
      omega

def allBoolTags : Nat → List (List Bool)
  | 0 => [[]]
  | d + 1 =>
    (allBoolTags d).map (fun bs => true :: bs) ++
    (allBoolTags d).map (fun bs => false :: bs)

theorem allBoolTags_length (d : Nat) : (allBoolTags d).length = 2 ^ d := by
  induction d with
  | zero => simp [allBoolTags]
  | succ d ih =>
    simp only [allBoolTags, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem mem_allBoolTags (d : Nat) (bs : List Bool) (hlen : bs.length = d) :
    bs ∈ allBoolTags d := by
  induction d generalizing bs with
  | zero =>
    cases bs with
    | nil => simp [allBoolTags]
    | cons _ _ => simp at hlen
  | succ d ih =>
    cases bs with
    | nil => simp at hlen
    | cons b rest =>
      simp only [List.length_cons] at hlen
      have hmem := ih rest (by omega)
      cases b
      · simp only [allBoolTags, List.mem_append, List.mem_map]
        exact Or.inr ⟨rest, hmem, rfl⟩
      · simp only [allBoolTags, List.mem_append, List.mem_map]
        exact Or.inl ⟨rest, hmem, rfl⟩

theorem allBoolTags_nodup (d : Nat) : (allBoolTags d).Nodup := by
  induction d with
  | zero => simp [allBoolTags]
  | succ d ih =>
    simp only [allBoolTags]
    apply nodup_append
    · exact nodup_map_on _ _ (fun a _ b _ h => by injection h) ih
    · exact nodup_map_on _ _ (fun a _ b _ h => by injection h) ih
    · intro z h1 h2
      rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
      rcases List.mem_map.mp h2 with ⟨_, _, heq⟩
      injection heq with hfirst
      cases hfirst

theorem pigeonhole_bool_tag_size {α : Type}
    (K : Nat) (L : List α) (tags : List (List Bool))
    (f : α → List Bool)
    (hcover : ∀ u ∈ L, f u ∈ tags)
    (hbucket : ∀ t ∈ tags, (L.filter (fun u => decide (f u = t))).length ≤ K) :
    L.length ≤ tags.length * K := by
  induction tags generalizing L with
  | nil =>
    cases L with
    | nil => simp
    | cons a _ =>
      have hmem := hcover a (by simp)
      cases hmem
  | cons t ts ih =>
    let here := L.filter (fun u => decide (f u = t))
    let rest := L.filter (fun u => !(decide (f u = t)))
    have hsplit : L.length = here.length + rest.length :=
      filter_compl_split (fun u => decide (f u = t)) L
    have hhere : here.length ≤ K := hbucket t (by simp)
    have hrest_cov : ∀ u ∈ rest, f u ∈ ts := by
      intro u hu
      have hu_f := List.mem_filter.mp hu
      rcases List.mem_cons.mp (hcover u hu_f.1) with heq | hts
      · exfalso; have := hu_f.2; simp [heq] at this
      · exact hts
    have hrest_buck : ∀ t' ∈ ts, (rest.filter (fun u => decide (f u = t'))).length ≤ K := by
      intro t' ht'
      have h1 : (rest.filter (fun u => decide (f u = t'))).length ≤
          (L.filter (fun u => decide (f u = t'))).length :=
        filter_sublist_length_le _ _ _
      exact Nat.le_trans h1 (hbucket t' (List.mem_cons_of_mem t ht'))
    have hih := ih rest hrest_cov hrest_buck
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem pigeonhole_duplicate_tag {α : Type} (L : List α) (tags : List (List Bool))
    (hL : L.Nodup) (f : α → List Bool)
    (hcover : ∀ u ∈ L, f u ∈ tags)
    (hgt : tags.length < L.length) :
    ∃ u ∈ L, ∃ v ∈ L, u ≠ v ∧ f u = f v := by
  induction tags generalizing L with
  | nil =>
    cases L with
    | nil => simp at hgt
    | cons a _ => exact absurd (hcover a (by simp)) (by simp)
  | cons t ts ih =>
    let here := L.filter (fun u => decide (f u = t))
    let rest := L.filter (fun u => !(decide (f u = t)))
    by_cases hbig : 1 < here.length
    · cases hfilt : here with
      | nil => simp [hfilt] at hbig
      | cons a tail =>
        cases tail with
        | nil => simp [hfilt] at hbig
        | cons b _ =>
          have hnd_h : here.Nodup := hL.filter _
          rw [hfilt] at hnd_h
          have hne : a ≠ b := fun heq => (List.nodup_cons.mp hnd_h).1 (by subst heq; simp)
          have ha_m : a ∈ here := by rw [hfilt]; simp
          have hb_m : b ∈ here := by rw [hfilt]; simp
          have haL := (List.mem_filter.mp ha_m).1
          have hbL := (List.mem_filter.mp hb_m).1
          have hfa : f a = t := of_decide_eq_true (List.mem_filter.mp ha_m).2
          have hfb : f b = t := of_decide_eq_true (List.mem_filter.mp hb_m).2
          exact ⟨a, haL, b, hbL, hne, hfa.trans hfb.symm⟩
    · have hsplit : L.length = here.length + rest.length :=
        filter_compl_split (fun u => decide (f u = t)) L
      have hrest_gt : ts.length < rest.length := by
        simp only [List.length_cons] at hgt
        omega
      have hrest_cov : ∀ u ∈ rest, f u ∈ ts := by
        intro u hu
        have hu_f := List.mem_filter.mp hu
        rcases List.mem_cons.mp (hcover u hu_f.1) with heq | hts
        · exfalso; have := hu_f.2; simp [heq] at this
        · exact hts
      rcases ih rest (hL.filter _) hrest_cov hrest_gt with ⟨u, hu, v, hv, hne, hfeq⟩
      exact ⟨u, (List.mem_filter.mp hu).1, v, (List.mem_filter.mp hv).1, hne, hfeq⟩

theorem single_sphere_orthant_lower_bound (d K : Nat) (Rsq : Int) (hR : 0 < Rsq)
    (S : List (List Int)) (hS_nd : S.Nodup)
    (hdim : ∀ u ∈ S, u.length = d)
    (hsphere : ∀ u ∈ S, normSq u = Rsq)
    (halpha : ∀ B : List (List Int), B.Nodup → (∀ x ∈ B, x ∈ S) →
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → vecAdd x y ∉ S) → B.length ≤ K) :
    S.length ≤ 2 ^ d * K := by
  rw [← allBoolTags_length d]
  apply pigeonhole_bool_tag_size K S (allBoolTags d) signOrthantTag
  · intro u hu
    apply mem_allBoolTags d
    rw [signOrthantTag_length]
    exact hdim u hu
  · intro t _
    let B := S.filter (fun u => decide (signOrthantTag u = t))
    apply halpha B (hS_nd.filter _)
    · intro x hx; exact (List.mem_filter.mp hx).1
    · intro x hx y hy _hne hsum
      have hx_f := List.mem_filter.mp hx
      have hy_f := List.mem_filter.mp hy
      have hx_S := hx_f.1
      have hy_S := hy_f.1
      have hdim_eq : x.length = y.length := (hdim x hx_S).trans (hdim y hy_S).symm
      have htag_eq : signOrthantTag x = signOrthantTag y :=
        (of_decide_eq_true hx_f.2).trans (of_decide_eq_true hy_f.2).symm
      have hdot : 0 ≤ dot x y := dot_nonneg_of_same_signOrthant x y hdim_eq htag_eq
      have hn1 : normSq x = Rsq := hsphere x hx_S
      have hn2 : normSq y = Rsq := hsphere y hy_S
      have hn_sum : normSq (vecAdd x y) = Rsq := hsphere (vecAdd x y) hsum
      have hexp := normSq_vecAdd x y hdim_eq
      rw [hn1, hn2, hn_sum] at hexp
      omega

/-! ### 5. Exact Parallelogram Identity, 2-Adic Norm Drop, and Checkerboard D_d Refinement -/

theorem sq_sum_add_sub (da db : Int) :
    (da + db) * (da + db) + (da - db) * (da - db) = 2 * (da * da) + 2 * (db * db) := by
  have h1 : (da + db) * (da + db) = da * da + 2 * (da * db) + db * db := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm db da]; omega
  have h2 : (da - db) * (da - db) = da * da - 2 * (da * db) + db * db := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm db da]; omega
  omega

def midVec : List Int → List Int → List Int
  | x :: xs, y :: ys => ((x + y) / 2) :: midVec xs ys
  | _, _ => []

def halfDiffVec : List Int → List Int → List Int
  | x :: xs, y :: ys => ((x - y) / 2) :: halfDiffVec xs ys
  | _, _ => []

def parityVec (u : List Int) : List Bool :=
  u.map (fun x => decide (x % 2 = 0))

theorem parityVec_length (u : List Int) : (parityVec u).length = u.length := by
  simp [parityVec]

theorem midVec_length (u v : List Int) (h : u.length = v.length) :
    (midVec u v).length = u.length := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h ⊢
      have ih' := ih ys (by omega)
      simp [midVec, ih']

theorem int_same_mod2_split (a b : Int) (h : decide (a % 2 = 0) = decide (b % 2 = 0)) :
    2 * ((a + b) / 2) = a + b ∧ 2 * ((a - b) / 2) = a - b := by
  by_cases ha : a % 2 = 0
  · have hb : b % 2 = 0 := by
      have : decide (b % 2 = 0) = true := by rw [← h]; exact decide_eq_true ha
      exact of_decide_eq_true this
    omega
  · have hb : b % 2 ≠ 0 := by
      intro hbe
      have h1 := decide_eq_false ha
      have h2 := decide_eq_true hbe
      rw [h1, h2] at h
      contradiction
    omega

theorem parallelogram_even_identity (u v : List Int)
    (hlen : u.length = v.length) (hpar : parityVec u = parityVec v) :
    vecAdd (midVec u v) (midVec u v) = vecAdd u v ∧
    2 * normSq (midVec u v) + 2 * normSq (halfDiffVec u v) = normSq u + normSq v := by
  induction u generalizing v with
  | nil => cases v with | nil => simp [vecAdd, midVec, halfDiffVec, normSq, dot] | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      simp only [parityVec, List.map_cons, List.cons.injEq] at hpar
      have ih' := ih ys (by omega) hpar.2
      have hsplit := int_same_mod2_split a b hpar.1
      have hm_eq : (a + b) / 2 + (a + b) / 2 = a + b := by omega
      have h1d : 2 * (((a + b) / 2) * ((a + b) / 2)) + 2 * (((a - b) / 2) * ((a - b) / 2)) =
          a * a + b * b := by
        have hs := sq_sum_add_sub a b
        have hs1 : (a + b) * (a + b) = 4 * (((a + b) / 2) * ((a + b) / 2)) := by
          have ha2 : a + b = 2 * ((a + b) / 2) := by omega
          have hcalc : (2 * ((a + b) / 2)) * (2 * ((a + b) / 2)) = 4 * (((a + b) / 2) * ((a + b) / 2)) := by
            rw [Int.mul_assoc, Int.mul_left_comm ((a + b) / 2) 2 ((a + b) / 2), ← Int.mul_assoc 2 2 _]; rfl
          rwa [← ha2] at hcalc
        have hs2 : (a - b) * (a - b) = 4 * (((a - b) / 2) * ((a - b) / 2)) := by
          have hd2 : a - b = 2 * ((a - b) / 2) := by omega
          have hcalc : (2 * ((a - b) / 2)) * (2 * ((a - b) / 2)) = 4 * (((a - b) / 2) * ((a - b) / 2)) := by
            rw [Int.mul_assoc, Int.mul_left_comm ((a - b) / 2) 2 ((a - b) / 2), ← Int.mul_assoc 2 2 _]; rfl
          rwa [← hd2] at hcalc
        omega
      constructor
      · simp only [midVec, vecAdd]
        rw [hm_eq, ih'.1]
      · simp only [midVec, halfDiffVec, normSq, dot] at ih' ⊢
        omega

theorem halfDiff_ne_zero_of_ne (u v : List Int) (hlen : u.length = v.length)
    (hpar : parityVec u = parityVec v) (hne : u ≠ v) :
    ∃ x ∈ halfDiffVec u v, x ≠ 0 := by
  induction u generalizing v with
  | nil => cases v with | nil => exact absurd rfl hne | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      simp only [parityVec, List.map_cons, List.cons.injEq] at hpar
      have hsplit := int_same_mod2_split a b hpar.1
      by_cases hab : a = b
      · subst hab
        have hxs_ne : xs ≠ ys := fun e => hne (by subst e; rfl)
        rcases ih ys (by omega) hpar.2 hxs_ne with ⟨z, hz, hnz⟩
        exact ⟨z, List.mem_cons_of_mem _ hz, hnz⟩
      · refine ⟨(a - b) / 2, by simp [halfDiffVec], ?_⟩
        intro hz
        have : a - b = 0 := by omega
        exact hab (by omega)

theorem normSq_mid_drop_ge1 (u v : List Int) (s : Nat)
    (hlen : u.length = v.length) (hpar : parityVec u = parityVec v) (hne : u ≠ v)
    (hu : normSq u ≤ (s : Int)) (hv : normSq v ≤ (s : Int)) :
    normSq (midVec u v) ≤ (s : Int) - 1 := by
  have hid := (parallelogram_even_identity u v hlen hpar).2
  have hh_ne := halfDiff_ne_zero_of_ne u v hlen hpar hne
  have hh_ge1 : 1 ≤ normSq (halfDiffVec u v) := normSq_pos_of_ne_zero _ hh_ne
  omega

def sumList : List Int → Int
  | [] => 0
  | x :: xs => x + sumList xs

theorem normSq_eq_1_odd_sum (h : List Int) (h1 : normSq h = 1) :
    sumList h = 1 ∨ sumList h = -1 := by
  induction h with
  | nil => simp [normSq, dot] at h1
  | cons x xs ih =>
    simp only [normSq, dot] at h1
    have hxs_nn : 0 ≤ normSq xs := normSq_nonneg xs
    unfold normSq at hxs_nn
    have hx2_nn : 0 ≤ x * x := int_sq_nonneg x
    by_cases hx0 : x = 0
    · subst hx0
      simp only [Int.zero_mul, Int.zero_add] at h1
      have ih' := ih h1
      simp only [sumList, Int.zero_add]
      exact ih'
    · have hx2_ge1 : 1 ≤ x * x := int_sq_ge_one x hx0
      have hxs0 : normSq xs = 0 := by unfold normSq; omega
      have hxs_all0 := (normSq_eq_zero_iff xs).mp hxs0
      have hsum0 : sumList xs = 0 := by
        clear h1 hx2_ge1 hx2_nn hx0 hxs_nn hxs0 ih
        induction xs with
        | nil => rfl
        | cons z zs ihz =>
          have hz0 : z = 0 := hxs_all0 z (by simp)
          have hzs0 : sumList zs = 0 := ihz (fun w hw => hxs_all0 w (List.mem_cons_of_mem z hw))
          simp [sumList, hz0, hzs0]
      have hx2_1 : x * x = 1 := by unfold normSq at hxs0; omega
      have hx_pm1 : x = 1 ∨ x = -1 := by
        by_cases h1x : x ≥ 2
        · have : x * x ≥ 4 := Int.mul_le_mul h1x h1x (by omega) (by omega)
          omega
        · by_cases hmx : x ≤ -2
          · have heq : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
            have hge2 : -x ≥ 2 := by omega
            have : (-x) * (-x) ≥ 4 := Int.mul_le_mul hge2 hge2 (by omega) (by omega)
            omega
          · omega
      simp only [sumList, hsum0, Int.add_zero]
      exact hx_pm1

theorem checkerboard_Dd_normSq_drop (u v : List Int) (s : Nat)
    (hlen : u.length = v.length) (hpar : parityVec u = parityVec v) (hne : u ≠ v)
    (hd_even : sumList (halfDiffVec u v) % 2 = 0)
    (hu : normSq u ≤ (s : Int)) (hv : normSq v ≤ (s : Int)) :
    normSq (midVec u v) ≤ (s : Int) - 2 := by
  have hid := (parallelogram_even_identity u v hlen hpar).2
  have hh_ne := halfDiff_ne_zero_of_ne u v hlen hpar hne
  have hh_ge1 : 1 ≤ normSq (halfDiffVec u v) := normSq_pos_of_ne_zero _ hh_ne
  have hh_ne1 : normSq (halfDiffVec u v) ≠ 1 := by
    intro h1
    rcases normSq_eq_1_odd_sum _ h1 with hp | hm <;> omega
  have hh_ge2 : 2 ≤ normSq (halfDiffVec u v) := by omega
  omega

/-! ### 6. Carry-Free Positive Radix Embedding -/

def evalRadix (Q : Int) : List Int → Int
  | [] => 0
  | a :: as => a + Q * evalRadix Q as

theorem evalRadix_vecAdd (Q : Int) (u v : List Int) (h : u.length = v.length) :
    evalRadix Q (vecAdd u v) = evalRadix Q u + evalRadix Q v := by
  induction u generalizing v with
  | nil => cases v with | nil => simp [evalRadix, vecAdd] | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h
      have ih' := ih ys (by omega)
      simp only [evalRadix, vecAdd, ih', Int.mul_add]
      omega

theorem evalRadix_vecSub (Q : Int) (u v : List Int) (h : u.length = v.length) :
    evalRadix Q (vecSub u v) = evalRadix Q u - evalRadix Q v := by
  induction u generalizing v with
  | nil => cases v with | nil => simp [evalRadix, vecSub] | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h
      have ih' := ih ys (by omega)
      simp only [evalRadix, vecSub, ih', Int.mul_sub]
      omega

theorem evalRadix_pos (Q : Int) (hQ : 0 < Q) (u : List Int)
    (hne : u ≠ []) (hpos : ∀ x ∈ u, 0 < x) : 0 < evalRadix Q u := by
  induction u with
  | nil => exact absurd rfl hne
  | cons a xs ih =>
    have ha : 0 < a := hpos a (by simp)
    cases xs with
    | nil => simp [evalRadix]; exact ha
    | cons b ys =>
      have hxs : 0 < evalRadix Q (b :: ys) := ih (by simp) (fun z hz => hpos z (List.mem_cons_of_mem a hz))
      have hmul : 0 < Q * evalRadix Q (b :: ys) := Int.mul_pos hQ hxs
      change 0 < a + Q * evalRadix Q (b :: ys)
      omega

theorem mul_bound_eq_zero (Q k x : Int) (hQ : 0 < Q) (hx_lo : -Q < x) (hx_hi : x < Q)
    (heq : x + Q * k = 0) : x = 0 ∧ k = 0 := by
  by_cases hk0 : k = 0
  · subst hk0; simp at heq; exact ⟨heq, rfl⟩
  · by_cases hkp : 1 ≤ k
    · have : Q ≤ Q * k := by
        have := Int.mul_le_mul_of_nonneg_left hkp (by omega : (0 : Int) ≤ Q)
        simpa using this
      omega
    · have hkn : k ≤ -1 := by omega
      have : Q * k ≤ -Q := by
        have := Int.mul_le_mul_of_nonneg_left hkn (by omega : (0 : Int) ≤ Q)
        simpa [Int.mul_neg] using this
      omega

theorem evalRadix_zero_iff (Q : Int) (hQ : 0 < Q) (d : List Int)
    (hb : ∀ x ∈ d, -Q < x ∧ x < Q) (h0 : evalRadix Q d = 0) :
    ∀ x ∈ d, x = 0 := by
  induction d with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
    simp only [evalRadix] at h0
    have ha := hb a (by simp)
    have hsplit := mul_bound_eq_zero Q (evalRadix Q xs) a hQ ha.1 ha.2 h0
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hm
    · exact hsplit.1
    · exact ih (fun z hz => hb z (List.mem_cons_of_mem a hz)) hsplit.2 x hm

theorem vecSub_zero_eq (u v : List Int) (hlen : u.length = v.length)
    (hz : ∀ x ∈ vecSub u v, x = 0) : u = v := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      have hab : a - b = 0 := hz (a - b) (by simp [vecSub])
      have hxs : xs = ys := ih ys (by omega) (fun z hzm => hz z (List.mem_cons_of_mem _ hzm))
      have : a = b := by omega
      subst this; rw [hxs]

theorem evalRadix_inj_pos (Q M : Int) (hQM : 2 * M < Q) (hM : 0 ≤ M)
    (u v : List Int) (hlen : u.length = v.length)
    (hu : ∀ x ∈ u, 0 ≤ x ∧ x ≤ M) (hv : ∀ x ∈ v, 0 ≤ x ∧ x ≤ M)
    (heq : evalRadix Q u = evalRadix Q v) : u = v := by
  have hQ : 0 < Q := by omega
  have h0 : evalRadix Q (vecSub u v) = 0 := by rw [evalRadix_vecSub Q u v hlen]; omega
  have hb : ∀ x ∈ vecSub u v, -Q < x ∧ x < Q := by
    clear heq h0
    induction u generalizing v with
    | nil => cases v with | nil => intro x hx; cases hx | cons _ _ => simp at hlen
    | cons a xs ih =>
      cases v with
      | nil => simp at hlen
      | cons b ys =>
        simp only [List.length_cons] at hlen
        have ha := hu a (by simp)
        have hb0 := hv b (by simp)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hm
        · omega
        · exact ih ys (by omega) (fun z hz => hu z (List.mem_cons_of_mem a hz))
            (fun z hz => hv z (List.mem_cons_of_mem b hz)) x hm
  exact vecSub_zero_eq u v hlen (evalRadix_zero_iff Q hQ _ hb h0)

theorem vecAdd_bounds_le (u v : List Int) (M : Int) (h : u.length = v.length)
    (hu : ∀ x ∈ u, 0 ≤ x ∧ x ≤ M) (hv : ∀ x ∈ v, 0 ≤ x ∧ x ≤ M) :
    ∀ z ∈ vecAdd u v, 0 ≤ z ∧ z ≤ 2 * M := by
  induction u generalizing v with
  | nil => cases v with | nil => intro z hz; cases hz | cons _ _ => simp at h
  | cons a xs ih =>
    cases v with
    | nil => simp at h
    | cons b ys =>
      simp only [List.length_cons] at h
      have ha := hu a (by simp)
      have hb0 := hv b (by simp)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hm
      · exact ⟨by omega, by omega⟩
      · exact ih ys (by omega) (fun c hc => hu c (List.mem_cons_of_mem a hc))
          (fun c hc => hv c (List.mem_cons_of_mem b hc)) z hm

theorem vecSub_bounds_Q (s w : List Int) (Q M : Int) (hQM : 2 * M < Q)
    (hlen : s.length = w.length)
    (hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ 2 * M) (hw : ∀ x ∈ w, 0 ≤ x ∧ x ≤ M) :
    ∀ x ∈ vecSub s w, -Q < x ∧ x < Q := by
  induction s generalizing w with
  | nil => cases w with | nil => intro x hx; cases hx | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases w with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons] at hlen
      have ha := hs a (by simp)
      have hb0 := hw b (by simp)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hm
      · omega
      · exact ih ys (by omega) (fun c hc => hs c (List.mem_cons_of_mem a hc))
          (fun c hc => hw c (List.mem_cons_of_mem b hc)) x hm

theorem evalRadix_sum_iff (Q M : Int) (hQM : 2 * M < Q) (hM : 0 ≤ M)
    (u v w : List Int) (huv : u.length = v.length) (huw : u.length = w.length)
    (hu : ∀ x ∈ u, 0 ≤ x ∧ x ≤ M) (hv : ∀ x ∈ v, 0 ≤ x ∧ x ≤ M) (hw : ∀ x ∈ w, 0 ≤ x ∧ x ≤ M) :
    evalRadix Q u + evalRadix Q v = evalRadix Q w ↔ vecAdd u v = w := by
  constructor
  · intro heq
    have hsum_len : (vecAdd u v).length = w.length := by rw [vecAdd_length u v huv, huw]
    have hQ : 0 < Q := by omega
    have h0 : evalRadix Q (vecSub (vecAdd u v) w) = 0 := by
      rw [evalRadix_vecSub Q (vecAdd u v) w hsum_len, evalRadix_vecAdd Q u v huv]
      omega
    have hub := vecAdd_bounds_le u v M huv hu hv
    have hb := vecSub_bounds_Q (vecAdd u v) w Q M hQM hsum_len hub hw
    exact vecSub_zero_eq (vecAdd u v) w hsum_len (evalRadix_zero_iff Q hQ _ hb h0)
  · intro heq
    rw [← evalRadix_vecAdd Q u v huv, heq]

/-! ### 7. Ruzsa Multi-Scale 2-Adic Lattice Ball Construction in Z₊ -/

def intRangeSym (m : Nat) : List Int :=
  (List.range (2 * m + 1)).map (fun (i : Nat) => (i : Int) - (m : Int))

theorem intRangeSym_length (m : Nat) : (intRangeSym m).length = 2 * m + 1 := by
  simp [intRangeSym]

theorem intRangeSym_nodup (m : Nat) : (intRangeSym m).Nodup := by
  apply nodup_map_on
  · intro a _ b _ h; omega
  · exact List.nodup_range

theorem mem_intRangeSym_iff (m : Nat) (x : Int) :
    x ∈ intRangeSym m ↔ -(m : Int) ≤ x ∧ x ≤ (m : Int) := by
  simp only [intRangeSym, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, _, rfl⟩
    have : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg i
    have : (i : Int) < ((2 * m + 1 : Nat) : Int) := by
      exact Int.ofNat_lt.mpr ‹_›
    omega
  · intro h
    have hsum_nn : 0 ≤ x + (m : Int) := by omega
    refine ⟨Int.toNat (x + (m : Int)), ?_, ?_⟩
    · have hlt : (Int.toNat (x + (m : Int)) : Int) ≤ 2 * (m : Int) := by
        rw [Int.ofNat_toNat]
        omega
      omega
    · rw [Int.ofNat_toNat]
      omega

def cubeVecs : Nat → Nat → List (List Int)
  | 0, _ => [[]]
  | d + 1, m =>
    (intRangeSym m).flatMap (fun x => (cubeVecs d m).map (fun xs => x :: xs))

theorem list_sum_const (k n : Nat) (L : List Nat) (hlen : L.length = n)
    (hall : ∀ a ∈ L, a = k) : L.sum = n * k := by
  induction L generalizing n with
  | nil => simp at hlen; subst hlen; simp
  | cons a t ih =>
    cases n with
    | zero => simp at hlen
    | succ n' =>
      simp only [List.length_cons] at hlen
      have ha : a = k := hall a (by simp)
      have iht := ih n' (by omega) (fun b hb => hall b (List.mem_cons_of_mem a hb))
      simp only [List.sum_cons, Nat.succ_mul]
      omega

theorem cubeVecs_length (d m : Nat) : (cubeVecs d m).length = (2 * m + 1) ^ d := by
  induction d with
  | zero => simp [cubeVecs]
  | succ d ih =>
    simp only [cubeVecs, List.length_flatMap]
    have hsum := list_sum_const ((2 * m + 1) ^ d) (2 * m + 1)
      ((intRangeSym m).map (fun x => ((cubeVecs d m).map (fun xs => x :: xs)).length))
      (by rw [List.length_map, intRangeSym_length])
      (fun a ha => by rcases List.mem_map.mp ha with ⟨x, _, rfl⟩; simp [ih])
    rw [hsum, Nat.pow_succ, Nat.mul_comm]

theorem cubeVecs_nodup (d m : Nat) : (cubeVecs d m).Nodup := by
  induction d with
  | zero => simp [cubeVecs]
  | succ d ih =>
    simp only [cubeVecs]
    apply nodup_flatMap_aux _ _ (intRangeSym_nodup m)
    · intro x _
      exact nodup_map_on _ _ (fun a _ b _ h => by injection h) ih
    · intro a _ b _ hne z hza hzb
      rcases List.mem_map.mp hza with ⟨_, _, rfl⟩
      rcases List.mem_map.mp hzb with ⟨_, _, heq⟩
      injection heq with hfirst
      exact hne hfirst.symm

theorem mem_cubeVecs_iff (d m : Nat) (v : List Int) :
    v ∈ cubeVecs d m ↔ v.length = d ∧ ∀ x ∈ v, -(m : Int) ≤ x ∧ x ≤ (m : Int) := by
  induction d generalizing v with
  | zero =>
    simp only [cubeVecs, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · intro rfl; exact ⟨rfl, fun x hx => by cases hx⟩
    · intro ⟨h0, _⟩; exact h0
  | succ d ih =>
    simp only [cubeVecs, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, xs, hxs, rfl⟩
      have hxb := (mem_intRangeSym_iff m x).mp hx
      have hxsb := (ih xs).mp hxs
      refine ⟨by simp [hxsb.1], ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hzm
      · exact hxb
      · exact hxsb.2 z hzm
    · rintro ⟨hlen, hbd⟩
      cases v with
      | nil => simp at hlen
      | cons x xs =>
        simp only [List.length_cons] at hlen
        have hx := (mem_intRangeSym_iff m x).mpr (hbd x (by simp))
        have hxs := (ih xs).mpr ⟨by omega, fun z hz => hbd z (List.mem_cons_of_mem x hz)⟩
        exact ⟨x, hx, xs, hxs, rfl⟩

theorem normSq_le_cube (d m : Nat) (v : List Int) (hlen : v.length = d)
    (hb : ∀ x ∈ v, -(m : Int) ≤ x ∧ x ≤ (m : Int)) :
    normSq v ≤ (d : Int) * ((m : Int) * (m : Int)) := by
  induction d generalizing v with
  | zero =>
    cases v with
    | nil => simp [normSq, dot]
    | cons _ _ => simp at hlen
  | succ d ih =>
    cases v with
    | nil => simp at hlen
    | cons x xs =>
      simp only [List.length_cons] at hlen
      have hxs := ih xs (by omega) (fun z hz => hb z (List.mem_cons_of_mem x hz))
      have hx := hb x (by simp)
      have hx2 : x * x ≤ (m : Int) * (m : Int) := by
        by_cases hp : 0 ≤ x
        · exact Int.mul_le_mul hx.2 hx.2 hp (by omega)
        · have hneg : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
          rw [hneg]
          exact Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      simp only [normSq, dot] at hxs ⊢
      have hstep : ((d + 1 : Nat) : Int) * ((m : Int) * (m : Int)) =
          (m : Int) * (m : Int) + (d : Int) * ((m : Int) * (m : Int)) := by
        have : ((d + 1 : Nat) : Int) = (d : Int) + 1 := by omega
        rw [this, Int.add_mul, Int.one_mul]; omega
      omega

theorem coord_abs_le_of_normSq_le (v : List Int) (r : Nat) (hn : normSq v ≤ (r : Int)) :
    ∀ x ∈ v, -(r : Int) ≤ x ∧ x ≤ (r : Int) := by
  intro x hx
  have hx2 : x * x ≤ normSq v := by
    clear hn
    induction v with
    | nil => cases hx
    | cons y ys ih =>
      have hy_nn : 0 ≤ y * y := int_sq_nonneg y
      have hys_nn : 0 ≤ normSq ys := normSq_nonneg ys
      unfold normSq at hys_nn
      rcases List.mem_cons.mp hx with rfl | hm
      · unfold normSq dot; omega
      · have ih' := ih hm
        unfold normSq dot
        unfold normSq at ih'
        omega
  have hr_sq : x * x ≤ (r : Int) := by omega
  have hmul : ((r : Int) + 1) * ((r : Int) + 1) = (r : Int) * (r : Int) + 2 * (r : Int) + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one]; omega
  have hr2 : 0 ≤ (r : Int) * (r : Int) := int_sq_nonneg _
  have hup : x ≤ (r : Int) := by
    by_cases hgt : (r : Int) + 1 ≤ x
    · have hm : ((r : Int) + 1) * ((r : Int) + 1) ≤ x * x :=
        Int.mul_le_mul hgt hgt (by omega) (by omega)
      omega
    · omega
  have hlo : -(r : Int) ≤ x := by
    by_cases hlt : (r : Int) + 1 ≤ -x
    · have heq : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
      have hm : ((r : Int) + 1) * ((r : Int) + 1) ≤ (-x) * (-x) :=
        Int.mul_le_mul hlt hlt (by omega) (by omega)
      omega
    · omega
  exact ⟨hlo, hup⟩

def ballVecs (d r s : Nat) : List (List Int) :=
  (cubeVecs d r).filter (fun v => decide (normSq v ≤ (s : Int)))

theorem mem_ballVecs_iff (d r s : Nat) (hs : s ≤ r) (v : List Int) :
    v ∈ ballVecs d r s ↔ v.length = d ∧ normSq v ≤ (s : Int) := by
  simp only [ballVecs, List.mem_filter, mem_cubeVecs_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hlen, _⟩, hn⟩; exact ⟨hlen, hn⟩
  · rintro ⟨hlen, hn⟩
    refine ⟨⟨hlen, ?_⟩, hn⟩
    exact coord_abs_le_of_normSq_le v r (by omega)

def scaleShiftVec (i C : Nat) (v : List Int) : List Int :=
  v.map (fun x => ((2 ^ i : Nat) : Int) * ((C : Int) + x))

theorem scaleShiftVec_length (i C : Nat) (v : List Int) :
    (scaleShiftVec i C v).length = v.length := by
  simp [scaleShiftVec]

theorem scaleShiftVec_inj (i C : Nat) :
    ∀ u v : List Int, scaleShiftVec i C u = scaleShiftVec i C v → u = v := by
  intro u v h
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp [scaleShiftVec] at h
  | cons a xs ih =>
    cases v with
    | nil => simp [scaleShiftVec] at h
    | cons b ys =>
      simp only [scaleShiftVec, List.map_cons, List.cons.injEq] at h
      have hpow : (0 : Int) < ((2 ^ i : Nat) : Int) :=
        Int.natCast_pos.mpr (Nat.pow_pos (by omega : 0 < 2))
      have hab : a = b := by
        have hmul : ((2 ^ i : Nat) : Int) * ((C : Int) + a) = ((2 ^ i : Nat) : Int) * ((C : Int) + b) := h.1
        rw [Int.mul_add, Int.mul_add] at hmul
        have hzero : ((2 ^ i : Nat) : Int) * (a - b) = 0 := by
          rw [Int.mul_sub]
          omega
        rcases Int.mul_eq_zero.mp hzero with h2 | hd
        · omega
        · omega
      rw [hab, ih ys h.2]

theorem scaleShiftVec_add_mid (i C : Nat) (u v : List Int)
    (hadd : vecAdd (midVec u v) (midVec u v) = vecAdd u v) :
    vecAdd (scaleShiftVec i C u) (scaleShiftVec i C v) =
      scaleShiftVec (i + 1) C (midVec u v) := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => rfl
  | cons a xs ih =>
    cases v with
    | nil => rfl
    | cons b ys =>
      simp only [midVec, vecAdd, List.cons.injEq] at hadd
      simp only [scaleShiftVec, midVec, vecAdd, List.map_cons, List.cons.injEq]
      constructor
      · have hp : ((2 ^ (i + 1) : Nat) : Int) = 2 * ((2 ^ i : Nat) : Int) := by
          rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]; rfl
        have hm : (a + b) / 2 + (a + b) / 2 = a + b := hadd.1
        rw [hp]
        have h1 : ((2 ^ i : Nat) : Int) * ((C : Int) + a) + ((2 ^ i : Nat) : Int) * ((C : Int) + b) =
            ((2 ^ i : Nat) : Int) * (2 * (C : Int) + (a + b)) := by
          rw [Int.mul_add, Int.mul_add, Int.mul_add]
          have hmul2 : ((2 ^ i : Nat) : Int) * (2 * (C : Int)) = 2 * (((2 ^ i : Nat) : Int) * (C : Int)) := by
            rw [Int.mul_left_comm]
          have hmula : ((2 ^ i : Nat) : Int) * (a + b) =
              ((2 ^ i : Nat) : Int) * a + ((2 ^ i : Nat) : Int) * b := Int.mul_add _ _ _
          omega
        have h2 : 2 * ((2 ^ i : Nat) : Int) * ((C : Int) + (a + b) / 2) =
            ((2 ^ i : Nat) : Int) * (2 * ((C : Int) + (a + b) / 2)) := by
          rw [Int.mul_assoc 2 ((2 ^ i : Nat) : Int) _, Int.mul_left_comm 2 ((2 ^ i : Nat) : Int) _]
        rw [h1, h2]
        congr 1
        omega
      · exact ih ys hadd.2

def ruzsaLayer (d r i : Nat) : List (List Int) :=
  (ballVecs d r (r - i)).map (scaleShiftVec i (4 * r + 1))

def ruzsaVecs (d r : Nat) : List (List Int) :=
  (List.range (r + 1)).flatMap (ruzsaLayer d r)

theorem ruzsaLayer_bounds (d r i : Nat) (w : List Int) (hw : w ∈ ruzsaLayer d r i) :
    w.length = d ∧ ∀ z ∈ w,
      ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) ≤ z ∧
      z ≤ ((2 ^ i : Nat) : Int) * (5 * (r : Int) + 1) := by
  rcases List.mem_map.mp hw with ⟨v, hv, rfl⟩
  have hv_c := (mem_cubeVecs_iff d r v).mp (List.mem_filter.mp hv).1
  refine ⟨by rw [scaleShiftVec_length, hv_c.1], ?_⟩
  intro z hz
  rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
  have hx_b := hv_c.2 x hx
  have h2_pos : (0 : Int) ≤ ((2 ^ i : Nat) : Int) := Int.natCast_nonneg _
  have hlo : 3 * (r : Int) + 1 ≤ ((4 * r + 1 : Nat) : Int) + x := by omega
  have hhi : ((4 * r + 1 : Nat) : Int) + x ≤ 5 * (r : Int) + 1 := by omega
  exact ⟨Int.mul_le_mul_of_nonneg_left hlo h2_pos,
         Int.mul_le_mul_of_nonneg_left hhi h2_pos⟩

theorem ruzsaLayer_disjoint (d r i j : Nat) (hd : 1 ≤ d) (hij : i < j)
    (w : List Int) (hi : w ∈ ruzsaLayer d r i) (hj : w ∈ ruzsaLayer d r j) : False := by
  have bi := ruzsaLayer_bounds d r i w hi
  have bj := ruzsaLayer_bounds d r j w hj
  cases w with
  | nil => have hlen0 := bi.1; simp at hlen0; omega
  | cons z _ =>
    have hzi := (bi.2 z (by simp)).2
    have hzj := (bj.2 z (by simp)).1
    have hpow : 2 * 2 ^ i ≤ 2 ^ j := by
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hij
      rw [Nat.pow_succ, Nat.mul_comm] at hp
      exact hp
    have hpow_int : 2 * ((2 ^ i : Nat) : Int) ≤ ((2 ^ j : Nat) : Int) := by
      have := Int.ofNat_le.mpr hpow
      simpa [Int.natCast_mul] using this
    have hpos3 : (0 : Int) ≤ 3 * (r : Int) + 1 := by omega
    have hmul : 2 * ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) ≤
        ((2 ^ j : Nat) : Int) * (3 * (r : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_right hpow_int hpos3
    have hpow_pos : (1 : Int) ≤ ((2 ^ i : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_pos (by omega : 0 < 2))
    have hdiff : ((2 ^ i : Nat) : Int) * ((r : Int) + 1) ≥ 1 := by
      have h1 : (1 : Int) * ((r : Int) + 1) ≤ ((2 ^ i : Nat) : Int) * ((r : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right hpow_pos (by omega)
      omega
    have hexp : 2 * ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) =
        ((2 ^ i : Nat) : Int) * (5 * (r : Int) + 1) + ((2 ^ i : Nat) : Int) * ((r : Int) + 1) := by
      have hsub : 2 * (3 * (r : Int) + 1) = (5 * (r : Int) + 1) + ((r : Int) + 1) := by omega
      rw [Int.mul_assoc 2 ((2 ^ i : Nat) : Int) _, Int.mul_left_comm 2 ((2 ^ i : Nat) : Int) _,
        hsub, Int.mul_add]
    omega

theorem ruzsaLayer_nodup (d r i : Nat) : (ruzsaLayer d r i).Nodup := by
  apply nodup_map_on
  · intro u _ v _ h; exact scaleShiftVec_inj i (4 * r + 1) u v h
  · exact (cubeVecs_nodup d r).filter _

theorem ruzsaVecs_nodup (d r : Nat) (hd : 1 ≤ d) : (ruzsaVecs d r).Nodup := by
  unfold ruzsaVecs
  apply nodup_flatMap_aux _ _ List.nodup_range
  · intro i _; exact ruzsaLayer_nodup d r i
  · intro i _ j _ hne w hwi hwj
    by_cases hlt : i < j
    · exact ruzsaLayer_disjoint d r i j hd hlt w hwi hwj
    · have hgt : j < i := by omega
      exact ruzsaLayer_disjoint d r j i hd hgt w hwj hwi

theorem normSq_ge_len_of_all_odd (v : List Int) (heq : parityVec v = List.replicate v.length false) :
    (v.length : Int) ≤ normSq v := by
  induction v with
  | nil => simp [normSq, dot]
  | cons a xs ih =>
    simp only [List.length_cons, parityVec, List.map_cons, List.replicate_succ, List.cons.injEq] at heq ⊢
    have ha_odd : a % 2 ≠ 0 := by
      intro h0
      have h1 := decide_eq_true h0
      rw [h1] at heq
      cases heq.1
    have ha0 : a ≠ 0 := fun h0 => ha_odd (by subst h0; simp)
    have ha2 : 1 ≤ a * a := int_sq_ge_one a ha0
    have ih' := ih heq.2
    simp only [normSq, dot] at ih' ⊢
    omega

theorem ballVecs_1_misses_allOdd (d r : Nat) (hd : 2 ≤ d)
    (v : List Int) (hv : v ∈ ballVecs d r 1) :
    parityVec v ≠ List.replicate d false := by
  intro heq
  have hv_mem := List.mem_filter.mp hv
  have hv_len : v.length = d := ((mem_cubeVecs_iff d r v).mp hv_mem.1).1
  have hn1 : normSq v ≤ (1 : Int) := of_decide_eq_true hv_mem.2
  have heq' : parityVec v = List.replicate v.length false := by rwa [hv_len]
  have hge := normSq_ge_len_of_all_odd v heq'
  omega

def allBoolTagsMinusAllFalse (d : Nat) : List (List Bool) :=
  (allBoolTags d).filter (fun bs => !(decide (bs = List.replicate d false)))

theorem allBoolTagsMinus_length (d : Nat) :
    (allBoolTagsMinusAllFalse d).length + 1 = 2 ^ d := by
  have hmem : List.replicate d false ∈ allBoolTags d :=
    mem_allBoolTags d (List.replicate d false) (List.length_replicate)
  have hnd : (allBoolTags d).Nodup := allBoolTags_nodup d
  have hsplit : (allBoolTags d).length =
      ((allBoolTags d).filter (fun bs => decide (bs = List.replicate d false))).length +
      (allBoolTagsMinusAllFalse d).length := by
    unfold allBoolTagsMinusAllFalse
    generalize allBoolTags d = L
    clear hnd hmem
    induction L with
    | nil => simp
    | cons a s ih =>
      simp only [List.filter_cons, List.length_cons] at ih ⊢
      cases decide (a = List.replicate d false) <;> simp <;> omega
  have h1 : ((allBoolTags d).filter (fun bs => decide (bs = List.replicate d false))).length = 1 := by
    have hsub : ∀ z ∈ (allBoolTags d).filter (fun bs => decide (bs = List.replicate d false)),
        z ∈ [List.replicate d false] := by
      intro z hz
      have := of_decide_eq_true (List.mem_filter.mp hz).2
      simp [this]
    have hle := nodup_length_le_of_inj _ [List.replicate d false] (hnd.filter _) id hsub (fun _ _ _ _ h => h)
    have hge : 1 ≤ ((allBoolTags d).filter (fun bs => decide (bs = List.replicate d false))).length :=
      List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩)
    simp at hle
    omega
  rw [allBoolTags_length] at hsplit
  omega

def sumLayerCount (B : List (List Int)) (d r : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumLayerCount B d r m + (B.filter (fun w => decide (w ∈ ruzsaLayer d r m))).length

theorem sumLayerCount_succ (B : List (List Int)) (d r m : Nat) :
    sumLayerCount B d r (m + 1) =
      sumLayerCount B d r m + (B.filter (fun w => decide (w ∈ ruzsaLayer d r m))).length := rfl

def findLayerPreim (d r i : Nat) (w : List Int) : List Int :=
  match ((ballVecs d r (r - i)).filter (fun v => decide (scaleShiftVec i (4 * r + 1) v = w))) with
  | v :: _ => v
  | [] => []

theorem findLayerPreim_spec (d r i : Nat) (v : List Int) (hv : v ∈ ballVecs d r (r - i)) :
    findLayerPreim d r i (scaleShiftVec i (4 * r + 1) v) = v := by
  unfold findLayerPreim
  cases hf : (ballVecs d r (r - i)).filter (fun z => decide (scaleShiftVec i (4 * r + 1) z = scaleShiftVec i (4 * r + 1) v)) with
  | nil =>
    exfalso
    have : v ∈ (ballVecs d r (r - i)).filter (fun z => decide (scaleShiftVec i (4 * r + 1) z = scaleShiftVec i (4 * r + 1) v)) :=
      List.mem_filter.mpr ⟨hv, decide_eq_true rfl⟩
    rw [hf] at this
    exact List.not_mem_nil this
  | cons v0 _ =>
    have hm0 : v0 ∈ (ballVecs d r (r - i)).filter (fun z => decide (scaleShiftVec i (4 * r + 1) z = scaleShiftVec i (4 * r + 1) v)) :=
      hf ▸ List.mem_cons_self
    exact scaleShiftVec_inj i (4 * r + 1) v0 v (of_decide_eq_true (List.mem_filter.mp hm0).2)

theorem ruzsaVecs_sum_avoiding_bound (d r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (B : List (List Int)) (hBnd : B.Nodup) (hBsub : ∀ w ∈ B, w ∈ ruzsaVecs d r)
    (hBsa : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → vecAdd u v ∉ ruzsaVecs d r) :
    B.length ≤ r * 2 ^ d := by
  have hB_eq : B.length ≤ sumLayerCount B d r (r + 1) := by
    have hcov : ∀ w ∈ B, ∃ i ∈ List.range (r + 1), w ∈ ruzsaLayer d r i := by
      intro w hw
      have hm := hBsub w hw
      simp only [ruzsaVecs, List.mem_flatMap] at hm
      exact hm
    have hle_sum : ∀ m ≤ r + 1,
        (B.filter (fun w => (List.range m).any (fun i => decide (w ∈ ruzsaLayer d r i)))).length ≤
          sumLayerCount B d r m := by
      intro m _
      induction m with
      | zero => simp [sumLayerCount]
      | succ m ih =>
        simp only [sumLayerCount, List.range_succ, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false]
        have ih' := ih (by omega)
        let p : List Int → Bool := fun w => (List.range m).any (fun i => decide (w ∈ ruzsaLayer d r i))
        let q : List Int → Bool := fun w => decide (w ∈ ruzsaLayer d r m)
        have hpart : (B.filter (fun w => p w || q w)).length ≤
            (B.filter p).length + (B.filter q).length := by
          clear ih ih' hcov hBnd hBsub hBsa
          induction B with
          | nil => simp
          | cons a t iht =>
            by_cases hp : p a = true <;> by_cases hq : q a = true
            · simp [hp, hq] at iht ⊢; omega
            · have hqf : q a = false := Bool.eq_false_iff.mpr hq
              simp [hp, hqf] at iht ⊢; omega
            · have hpf : p a = false := Bool.eq_false_iff.mpr hp
              simp [hpf, hq] at iht ⊢; omega
            · have hpf : p a = false := Bool.eq_false_iff.mpr hp
              have hqf : q a = false := Bool.eq_false_iff.mpr hq
              simp [hpf, hqf] at iht ⊢; omega
        exact Nat.le_trans hpart (Nat.add_le_add_right ih' _)
    have hall_filt : B.filter (fun w => (List.range (r + 1)).any (fun i => decide (w ∈ ruzsaLayer d r i))) = B := by
      apply List.filter_eq_self.mpr
      intro w hw
      rcases hcov w hw with ⟨i, hi, hwi⟩
      exact List.any_eq_true.mpr ⟨i, hi, decide_eq_true hwi⟩
    have htop := hle_sum (r + 1) (Nat.le_refl _)
    rw [hall_filt] at htop
    exact htop
  have hlayer_lt : ∀ i, i < r - 1 →
      (B.filter (fun w => decide (w ∈ ruzsaLayer d r i))).length ≤ 2 ^ d := by
    intro i hi
    by_cases hgt : 2 ^ d < (B.filter (fun w => decide (w ∈ ruzsaLayer d r i))).length
    · exfalso
      let Bi := B.filter (fun w => decide (w ∈ ruzsaLayer d r i))
      have hgt' : (allBoolTags d).length < Bi.length := by rw [allBoolTags_length]; exact hgt
      let tagFn : List Int → List Bool := fun w => parityVec (findLayerPreim d r i w)
      have htag_cov : ∀ w ∈ Bi, tagFn w ∈ allBoolTags d := by
        intro w hw
        have hwm : w ∈ ruzsaLayer d r i := of_decide_eq_true (List.mem_filter.mp hw).2
        rcases List.mem_map.mp hwm with ⟨v, hv, rfl⟩
        apply mem_allBoolTags d
        simp only [tagFn, findLayerPreim_spec d r i v hv, parityVec_length]
        exact ((mem_cubeVecs_iff d r v).mp (List.mem_filter.mp hv).1).1
      rcases pigeonhole_duplicate_tag Bi (allBoolTags d) (hBnd.filter _) tagFn htag_cov hgt' with
        ⟨w1, hw1, w2, hw2, hne_w, htag_eq⟩
      have hw1B := (List.mem_filter.mp hw1).1
      have hw2B := (List.mem_filter.mp hw2).1
      have hw1L := of_decide_eq_true (List.mem_filter.mp hw1).2
      have hw2L := of_decide_eq_true (List.mem_filter.mp hw2).2
      rcases List.mem_map.mp hw1L with ⟨u, hu_b, hu_eq⟩
      rcases List.mem_map.mp hw2L with ⟨v, hv_b, hv_eq⟩
      rw [← hu_eq] at htag_eq hw1B hne_w
      rw [← hv_eq] at htag_eq hw2B hne_w
      simp only [tagFn, findLayerPreim_spec d r i u hu_b, findLayerPreim_spec d r i v hv_b] at htag_eq
      have huv_ne : u ≠ v := fun e => hne_w (by subst e; rfl)
      have hu_b' := (mem_ballVecs_iff d r (r - i) (Nat.sub_le _ _) u).mp hu_b
      have hv_b' := (mem_ballVecs_iff d r (r - i) (Nat.sub_le _ _) v).mp hv_b
      have hlen_uv : u.length = v.length := hu_b'.1.trans hv_b'.1.symm
      have hm_norm := normSq_mid_drop_ge1 u v (r - i) hlen_uv htag_eq huv_ne hu_b'.2 hv_b'.2
      have hm_mem : midVec u v ∈ ballVecs d r (r - (i + 1)) := by
        apply (mem_ballVecs_iff d r (r - (i + 1)) (Nat.sub_le _ _) (midVec u v)).mpr
        refine ⟨by rw [midVec_length u v hlen_uv, hu_b'.1], by omega⟩
      have hid := (parallelogram_even_identity u v hlen_uv htag_eq).1
      have hadd_in : vecAdd (scaleShiftVec i (4 * r + 1) u) (scaleShiftVec i (4 * r + 1) v) ∈ ruzsaVecs d r := by
        rw [scaleShiftVec_add_mid i (4 * r + 1) u v hid]
        simp only [ruzsaVecs, List.mem_flatMap, List.mem_range, ruzsaLayer, List.mem_map]
        exact ⟨i + 1, by omega, midVec u v, hm_mem, rfl⟩
      exact hBsa _ hw1B _ hw2B hne_w hadd_in
    · exact Nat.le_of_not_lt hgt
  have hlayer_rm1 :
      (B.filter (fun w => decide (w ∈ ruzsaLayer d r (r - 1)))).length ≤ 2 ^ d - 1 := by
    by_cases hgt : 2 ^ d - 1 < (B.filter (fun w => decide (w ∈ ruzsaLayer d r (r - 1)))).length
    · exfalso
      let Bi := B.filter (fun w => decide (w ∈ ruzsaLayer d r (r - 1)))
      have hgt' : (allBoolTagsMinusAllFalse d).length < Bi.length := by
        have hlen_m := allBoolTagsMinus_length d
        have h2pos : 1 ≤ 2 ^ d := Nat.pow_pos (by omega : 0 < 2)
        have hgt_bi : 2 ^ d - 1 < Bi.length := hgt
        omega
      let tagFn : List Int → List Bool := fun w => parityVec (findLayerPreim d r (r - 1) w)
      have htag_cov : ∀ w ∈ Bi, tagFn w ∈ allBoolTagsMinusAllFalse d := by
        intro w hw
        have hwm : w ∈ ruzsaLayer d r (r - 1) := of_decide_eq_true (List.mem_filter.mp hw).2
        rcases List.mem_map.mp hwm with ⟨v, hv, rfl⟩
        have heq1 : r - (r - 1) = 1 := by omega
        have hv1 : v ∈ ballVecs d r 1 := by rwa [heq1] at hv
        have hlen : v.length = d := ((mem_cubeVecs_iff d r v).mp (List.mem_filter.mp hv).1).1
        have hnot_all : parityVec v ≠ List.replicate d false := ballVecs_1_misses_allOdd d r hd v hv1
        have hmem_all : parityVec v ∈ allBoolTags d := mem_allBoolTags d _ (by rw [parityVec_length, hlen])
        simp only [tagFn, findLayerPreim_spec d r (r - 1) v hv]
        exact List.mem_filter.mpr ⟨hmem_all, by simp [hnot_all]⟩
      rcases pigeonhole_duplicate_tag Bi (allBoolTagsMinusAllFalse d) (hBnd.filter _) tagFn htag_cov hgt' with
        ⟨w1, hw1, w2, hw2, hne_w, htag_eq⟩
      have hw1B := (List.mem_filter.mp hw1).1
      have hw2B := (List.mem_filter.mp hw2).1
      have hw1L := of_decide_eq_true (List.mem_filter.mp hw1).2
      have hw2L := of_decide_eq_true (List.mem_filter.mp hw2).2
      rcases List.mem_map.mp hw1L with ⟨u, hu_b, hu_eq⟩
      rcases List.mem_map.mp hw2L with ⟨v, hv_b, hv_eq⟩
      rw [← hu_eq] at htag_eq hw1B hne_w
      rw [← hv_eq] at htag_eq hw2B hne_w
      simp only [tagFn, findLayerPreim_spec d r (r - 1) u hu_b,
        findLayerPreim_spec d r (r - 1) v hv_b] at htag_eq
      have huv_ne : u ≠ v := fun e => hne_w (by subst e; rfl)
      have hu_b' := (mem_ballVecs_iff d r (r - (r - 1)) (Nat.sub_le _ _) u).mp hu_b
      have hv_b' := (mem_ballVecs_iff d r (r - (r - 1)) (Nat.sub_le _ _) v).mp hv_b
      have hlen_uv : u.length = v.length := hu_b'.1.trans hv_b'.1.symm
      have hm_norm := normSq_mid_drop_ge1 u v (r - (r - 1)) hlen_uv htag_eq huv_ne hu_b'.2 hv_b'.2
      have hm_mem : midVec u v ∈ ballVecs d r (r - r) := by
        apply (mem_ballVecs_iff d r (r - r) (Nat.sub_le _ _) (midVec u v)).mpr
        refine ⟨by rw [midVec_length u v hlen_uv, hu_b'.1], by omega⟩
      have hid := (parallelogram_even_identity u v hlen_uv htag_eq).1
      have hadd_in : vecAdd (scaleShiftVec (r - 1) (4 * r + 1) u)
          (scaleShiftVec (r - 1) (4 * r + 1) v) ∈ ruzsaVecs d r := by
        have hrr : (r - 1) + 1 = r := by omega
        rw [scaleShiftVec_add_mid (r - 1) (4 * r + 1) u v hid, hrr]
        simp only [ruzsaVecs, List.mem_flatMap, List.mem_range, ruzsaLayer, List.mem_map]
        exact ⟨r, by omega, midVec u v, hm_mem, rfl⟩
      exact hBsa _ hw1B _ hw2B hne_w hadd_in
    · exact Nat.le_of_not_lt hgt
  have hlayer_r :
      (B.filter (fun w => decide (w ∈ ruzsaLayer d r r))).length ≤ 1 := by
    let Br := B.filter (fun w => decide (w ∈ ruzsaLayer d r r))
    have hsub_r : ∀ w ∈ Br, w ∈ [scaleShiftVec r (4 * r + 1) (List.replicate d 0)] := by
      intro w hw
      have hwm := of_decide_eq_true (List.mem_filter.mp hw).2
      rcases List.mem_map.mp hwm with ⟨v, hv, rfl⟩
      have hv_b := (mem_ballVecs_iff d r (r - r) (Nat.sub_le _ _) v).mp hv
      have hrr0 : r - r = 0 := Nat.sub_self r
      rw [hrr0] at hv_b
      have hn_nn : 0 ≤ normSq v := normSq_nonneg v
      have hn0 : normSq v = 0 := by omega
      have hall0 := (normSq_eq_zero_iff v).mp hn0
      have hveq : v = List.replicate d 0 := by
        apply List.ext_getElem
        · rw [hv_b.1, List.length_replicate]
        · intro idx hi _
          have hm : v[idx] ∈ v := List.getElem_mem hi
          rw [hall0 _ hm, List.getElem_replicate]
      rw [hveq]
      simp
    have hle := nodup_length_le_of_inj Br [scaleShiftVec r (4 * r + 1) (List.replicate d 0)]
      (hBnd.filter _) id hsub_r (fun _ _ _ _ h => h)
    simpa using hle
  have hsum_pref : ∀ m, m ≤ r - 1 → sumLayerCount B d r m ≤ m * 2 ^ d := by
    intro m hm
    induction m with
    | zero => simp [sumLayerCount]
    | succ m ih =>
      have h1 := ih (by omega)
      have h2 := hlayer_lt m (by omega)
      simp only [sumLayerCount, Nat.succ_mul]
      omega
  have hpref_rm1 := hsum_pref (r - 1) (Nat.le_refl _)
  have hsr : sumLayerCount B d r r = sumLayerCount B d r (r - 1) +
      (B.filter (fun w => decide (w ∈ ruzsaLayer d r (r - 1)))).length := by
    cases hr_eq : r with
    | zero => omega
    | succ r' => rfl
  have hsr1 : sumLayerCount B d r (r + 1) = sumLayerCount B d r r +
      (B.filter (fun w => decide (w ∈ ruzsaLayer d r r))).length := rfl
  have h2pos : 1 ≤ 2 ^ d := Nat.pow_pos (by omega : 0 < 2)
  have hr_eq : (r - 1) * 2 ^ d + 2 ^ d = r * 2 ^ d := by
    cases hr' : r with
    | zero => omega
    | succ r' => simp [Nat.succ_mul]
  omega

def ruzsaBase (r : Nat) : Int :=
  2 * ((2 ^ r : Nat) : Int) * (5 * (r : Int) + 1) + 1

def ruzsaIntSet (d r : Nat) : List Int :=
  (ruzsaVecs d r).map (evalRadix (ruzsaBase r))

def findIntPreim (Q : Int) (vecs : List (List Int)) (x : Int) : List Int :=
  match vecs.filter (fun w => decide (evalRadix Q w = x)) with
  | w :: _ => w
  | [] => []

theorem ruzsaIntSet_props (d r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r) :
    (ruzsaIntSet d r).Nodup ∧
    (∀ x ∈ ruzsaIntSet d r, 0 < x) ∧
    MaxSumAvoidingAtMost (ruzsaIntSet d r) (r * 2 ^ d) := by
  let M : Int := ((2 ^ r : Nat) : Int) * (5 * (r : Int) + 1)
  let Q : Int := ruzsaBase r
  have hM_nn : 0 ≤ M :=
    Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hQ_eq : Q = 2 * M + 1 := by
    simp only [Q, M, ruzsaBase]
    rw [Int.mul_assoc 2 _ _]
  have hQM : 2 * M < Q := by omega
  have hQpos : 0 < Q := by omega
  have hw_bounds : ∀ w ∈ ruzsaVecs d r, w.length = d ∧ ∀ z ∈ w, 1 ≤ z ∧ z ≤ M := by
    intro w hw
    rcases (List.mem_flatMap.mp hw) with ⟨i, hi, hwi⟩
    have hi_le : i ≤ r := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    have hb := ruzsaLayer_bounds d r i w hwi
    refine ⟨hb.1, ?_⟩
    intro z hz
    have hzb := hb.2 z hz
    have h2i_ge1 : (1 : Int) ≤ ((2 ^ i : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_pos (by omega : 0 < 2))
    have h2i_le_2r : ((2 ^ i : Nat) : Int) ≤ ((2 ^ r : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hi_le)
    have hmul_le : ((2 ^ i : Nat) : Int) * (5 * (r : Int) + 1) ≤ M :=
      Int.mul_le_mul_of_nonneg_right h2i_le_2r (by omega)
    have hlo_ge1 : 1 ≤ ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) := by
      have : (1 : Int) * (3 * (r : Int) + 1) ≤ ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right h2i_ge1 (by omega)
      omega
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_map_on
    · intro u hu v hv heq
      have hu_b := hw_bounds u hu
      have hv_b := hw_bounds v hv
      exact evalRadix_inj_pos Q M hQM hM_nn u v (hu_b.1.trans hv_b.1.symm)
        (fun z hz => ⟨by have := (hu_b.2 z hz).1; omega, (hu_b.2 z hz).2⟩)
        (fun z hz => ⟨by have := (hv_b.2 z hz).1; omega, (hv_b.2 z hz).2⟩) heq
    · exact ruzsaVecs_nodup d r (by omega)
  · intro x hx
    rcases List.mem_map.mp hx with ⟨w, hw, rfl⟩
    have hwb := hw_bounds w hw
    have hne : w ≠ [] := by intro e; rw [e] at hwb; simp at hwb; omega
    exact evalRadix_pos Q hQpos w hne (fun z hz => by have := (hwb.2 z hz).1; omega)
  · intro B hBnd hBsub hBsa
    let preim := findIntPreim Q (ruzsaVecs d r)
    have hpreim_spec : ∀ x ∈ B, preim x ∈ ruzsaVecs d r ∧ evalRadix Q (preim x) = x := by
      intro x hx
      have hxm : x ∈ ruzsaIntSet d r := hBsub x hx
      rcases List.mem_map.mp hxm with ⟨w0, hw0, hweq⟩
      unfold preim findIntPreim
      cases hf : (ruzsaVecs d r).filter (fun w => decide (evalRadix Q w = x)) with
      | nil =>
        exfalso
        have hw0_in : w0 ∈ (ruzsaVecs d r).filter (fun w => decide (evalRadix Q w = x)) :=
          List.mem_filter.mpr ⟨hw0, decide_eq_true hweq⟩
        rw [hf] at hw0_in
        exact List.not_mem_nil hw0_in
      | cons w1 _ =>
        have hm1 := List.mem_filter.mp (hf ▸ List.mem_cons_self)
        exact ⟨hm1.1, of_decide_eq_true hm1.2⟩
    let Bvec := B.map preim
    have hBv_nd : Bvec.Nodup := by
      apply nodup_map_on _ _ _ hBnd
      intro x hx y hy heq
      have hx_s := hpreim_spec x hx
      have hy_s := hpreim_spec y hy
      rw [← hx_s.2, ← hy_s.2, heq]
    have hBv_sub : ∀ w ∈ Bvec, w ∈ ruzsaVecs d r := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
      exact (hpreim_spec x hx).1
    have hBv_sa : ∀ u ∈ Bvec, ∀ v ∈ Bvec, u ≠ v → vecAdd u v ∉ ruzsaVecs d r := by
      intro u hu v hv huv_ne hsum
      rcases List.mem_map.mp hu with ⟨x, hx, rfl⟩
      rcases List.mem_map.mp hv with ⟨y, hy, rfl⟩
      have hxy_ne : x ≠ y := fun e => huv_ne (by subst e; rfl)
      have hxs := hpreim_spec x hx
      have hys := hpreim_spec y hy
      have hub := hw_bounds _ hxs.1
      have hvb := hw_bounds _ hys.1
      have hev_sum : evalRadix Q (vecAdd (preim x) (preim y)) = x + y := by
        rw [evalRadix_vecAdd Q _ _ (hub.1.trans hvb.1.symm), hxs.2, hys.2]
      have hxy_in : x + y ∈ ruzsaIntSet d r := by
        rw [← hev_sum]
        exact List.mem_map.mpr ⟨vecAdd (preim x) (preim y), hsum, rfl⟩
      exact hBsa x hx y hy hxy_ne hxy_in
    have hbound := ruzsaVecs_sum_avoiding_bound d r hd hr Bvec hBv_nd hBv_sub hBv_sa
    simpa [Bvec] using hbound

theorem range_add_split (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (fun k => a + k) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc]

theorem ruzsaIntSet_length_ge (d t : Nat) (hd : 2 ≤ d) (_ht : 1 ≤ t) :
    (3 * d * t ^ 2 + 1) * (2 * t + 1) ^ d ≤ (ruzsaIntSet d (4 * d * t ^ 2)).length := by
  let r := 4 * d * t ^ 2
  have hmap_len : (ruzsaIntSet d r).length = (ruzsaVecs d r).length := by simp [ruzsaIntSet]
  rw [hmap_len]
  have h3eq : 3 * d * t ^ 2 = 3 * (d * t ^ 2) := Nat.mul_assoc 3 d (t ^ 2)
  have h4eq : r = 4 * (d * t ^ 2) := Nat.mul_assoc 4 d (t ^ 2)
  have h3le4 : 3 * d * t ^ 2 ≤ r := by rw [h3eq, h4eq]; omega
  have hlayer_ge : ∀ i, i ≤ 3 * d * t ^ 2 → (2 * t + 1) ^ d ≤ (ruzsaLayer d r i).length := by
    intro i hi
    rw [← cubeVecs_length d t]
    unfold ruzsaLayer
    rw [List.length_map]
    apply nodup_length_le_of_inj _ _ (cubeVecs_nodup d t) id
    · intro v hv
      have hvc := (mem_cubeVecs_iff d t v).mp hv
      have hnorm := normSq_le_cube d t v hvc.1 hvc.2
      have hi' : i ≤ 3 * (d * t ^ 2) := by rwa [← h3eq]
      have hr_sub : d * t ^ 2 ≤ r - i := by rw [h4eq]; omega
      have hnorm_le : normSq v ≤ ((r - i : Nat) : Int) := by
        have h1 : (d : Int) * ((t : Int) * (t : Int)) = ((d * t ^ 2 : Nat) : Int) := by
          simp [Nat.pow_two]
        have h2 : ((d * t ^ 2 : Nat) : Int) ≤ ((r - i : Nat) : Int) := Int.ofNat_le.mpr hr_sub
        omega
      have hc_r : v ∈ cubeVecs d r := by
        apply (mem_cubeVecs_iff d r v).mpr
        refine ⟨hvc.1, ?_⟩
        have ht_le_r : t ≤ r := by
          have ht_le_t2 : t ≤ t ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_self t
          have hdt : 2 * t ≤ d * t ^ 2 := by
            have := Nat.mul_le_mul hd ht_le_t2
            omega
          rw [h4eq]; omega
        intro z hz
        have hzb := hvc.2 z hz
        omega
      exact List.mem_filter.mpr ⟨hc_r, decide_eq_true hnorm_le⟩
    · intro u _ v _ h; exact h
  have hsub_range : ∀ m, m ≤ 3 * d * t ^ 2 + 1 →
      m * (2 * t + 1) ^ d ≤ ((List.range m).flatMap (ruzsaLayer d r)).length := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := ih (by omega)
      have h2 := hlayer_ge m (by omega)
      rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Nat.succ_mul]
      omega
  have hle_full : ((List.range (3 * d * t ^ 2 + 1)).flatMap (ruzsaLayer d r)).length ≤
      (ruzsaVecs d r).length := by
    unfold ruzsaVecs
    let a := 3 * d * t ^ 2 + 1
    let b := r - 3 * d * t ^ 2
    have hab : a + b = r + 1 := by omega
    have hsp := range_add_split a b
    rw [hab] at hsp
    rw [hsp, List.flatMap_append, List.length_append]
    exact Nat.le_add_right _ _
  exact Nat.le_trans (hsub_range (3 * d * t ^ 2 + 1) (Nat.le_refl _)) hle_full

/-- Super-Quadratic Parametric Family in ℤ₊. -/
theorem ruzsa_superquadratic_family (d t : Nat) (hd : 2 ≤ d) (ht : 1 ≤ t) :
    ∃ A : List Int, A.Nodup ∧ (∀ x ∈ A, 0 < x) ∧
      (3 * d * t ^ 2 + 1) * (2 * t + 1) ^ d ≤ A.length ∧
      MaxSumAvoidingAtMost A (4 * d * t ^ 2 * 2 ^ d) := by
  have hr : 1 ≤ 4 * d * t ^ 2 := by
    have htp : 1 ≤ t ^ 2 := Nat.pow_pos (by omega : 0 < t)
    have hdt : 1 ≤ d * t ^ 2 := Nat.mul_pos (by omega) htp
    rw [Nat.mul_assoc 4 d (t ^ 2)]
    omega
  have hp := ruzsaIntSet_props d (4 * d * t ^ 2) hd hr
  exact ⟨ruzsaIntSet d (4 * d * t ^ 2), hp.1, hp.2.1, ruzsaIntSet_length_ge d t hd ht, hp.2.2⟩

/-- Explicit Super-Quadratic Corollary: Ruzsa lattice construction strictly exceeds
    the quadratic bound `k^2 + 3k - 11` already at explicit `(d = 6, t = 7)`. -/
theorem ruzsa_beats_quadratic_explicit :
    ∃ (k : Nat) (A : List Int),
      A.Nodup ∧ (∀ x ∈ A, 0 < x) ∧ MaxSumAvoidingAtMost A k ∧
      k * k + 3 * k - 11 < A.length := by
  rcases ruzsa_superquadratic_family 6 7 (by omega) (by omega) with ⟨A, hnd, hpos, hlen, halpha⟩
  refine ⟨4 * 6 * 7 ^ 2 * 2 ^ 6, A, hnd, hpos, halpha, ?_⟩
  have hnum : (4 * 6 * 7 ^ 2 * 2 ^ 6) * (4 * 6 * 7 ^ 2 * 2 ^ 6) +
      3 * (4 * 6 * 7 ^ 2 * 2 ^ 6) - 11 < (3 * 6 * 7 ^ 2 + 1) * (2 * 7 + 1) ^ 6 := by decide
  omega

/-- Pure `Nat` Quasi-Polynomial Theorem (`n_max(K) ≥ exp(Ω((log K)^2))`). -/
theorem ruzsa_quasipolynomial_nat (m : Nat) (hm : 1 ≤ m) :
    ∃ A : List Int, A.Nodup ∧ (∀ x ∈ A, 0 < x) ∧
      2 ^ (2 * m ^ 2 + 4 * m) ≤ A.length ∧
      MaxSumAvoidingAtMost A (8 * m * 2 ^ (4 * m)) := by
  have hd : 2 ≤ 2 * m := by omega
  have ht : 1 ≤ 2 ^ m := Nat.pow_pos (by omega : 0 < 2)
  rcases ruzsa_superquadratic_family (2 * m) (2 ^ m) hd ht with ⟨A, hnd, hpos, hlen, halpha⟩
  have hK : 4 * (2 * m) * (2 ^ m) ^ 2 * 2 ^ (2 * m) = 8 * m * 2 ^ (4 * m) := by
    have hp2 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
      rw [Nat.pow_two, ← Nat.pow_add, show m + m = 2 * m by omega]
    rw [hp2, Nat.mul_assoc (4 * (2 * m)), ← Nat.pow_add, show 2 * m + 2 * m = 4 * m by omega]
    rw [← Nat.mul_assoc 4 2 m]
  have hN : 2 ^ (2 * m ^ 2 + 4 * m) ≤ (3 * (2 * m) * (2 ^ m) ^ 2 + 1) * (2 * 2 ^ m + 1) ^ (2 * m) := by
    have h1 : 2 ^ (2 * m) ≤ (3 * (2 * m) * (2 ^ m) ^ 2 + 1) := by
      have hm1 : 1 ≤ 3 * (2 * m) := by omega
      have hsq : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by
        rw [Nat.pow_two, ← Nat.pow_add, show m + m = 2 * m by omega]
      rw [hsq]
      have : 1 * (2 ^ m) ^ 2 ≤ (3 * (2 * m)) * (2 ^ m) ^ 2 := Nat.mul_le_mul_right _ hm1
      omega
    have h2 : 2 ^ (2 * m ^ 2 + 2 * m) ≤ (2 * 2 ^ m + 1) ^ (2 * m) := by
      have hbase : 2 ^ (m + 1) ≤ 2 * 2 ^ m + 1 := by
        rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have hpow := Nat.pow_le_pow_left hbase (2 * m)
      rw [← Nat.pow_mul] at hpow
      have hexp : (m + 1) * (2 * m) = 2 * m ^ 2 + 2 * m := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_two, Nat.mul_left_comm m 2 m, ← Nat.mul_assoc 2 m m]
      rw [hexp] at hpow
      exact hpow
    have hadd_exp : 2 * m ^ 2 + 4 * m = 2 * m + (2 * m ^ 2 + 2 * m) := by omega
    rw [hadd_exp, Nat.pow_add]
    exact Nat.mul_le_mul h1 h2
  rw [hK] at halpha
  exact ⟨A, hnd, hpos, Nat.le_trans hN hlen, halpha⟩

/-! ### 9. Checkerboard `D_d` Multi-Scale Construction & Tight Explicit Crossover -/

def parityInit : List Int → List Bool
  | [] => []
  | [_] => []
  | x :: xs => decide (x % 2 = 0) :: parityInit xs

theorem parityInit_length (v : List Int) : (parityInit v).length = v.length - 1 := by
  induction v with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b ys => simp [parityInit, ih]

def ddCosetTag (v : List Int) : List Bool :=
  parityInit v ++ [decide ((sumList v / 2) % 2 = 0)]

theorem ddCosetTag_length (v : List Int) (hv : 1 ≤ v.length) :
    (ddCosetTag v).length = v.length := by
  simp only [ddCosetTag, List.length_append, List.length_cons, List.length_nil, parityInit_length]
  omega

theorem parityVec_eq_of_init_sum (u v : List Int) (hlen : u.length = v.length)
    (hinit : parityInit u = parityInit v) (hsum : sumList u % 2 = sumList v % 2) :
    parityVec u = parityVec v := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          simp only [sumList, Int.add_zero] at hsum
          simp only [parityVec, List.map_cons, List.map_nil, List.cons.injEq, and_true]
          by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;> simp [ha, hb] <;> omega
        | cons _ _ => simp at hlen
      | cons x xs' =>
        cases ys with
        | nil => simp at hlen
        | cons y ys' =>
          simp only [parityInit, List.cons.injEq] at hinit
          have hpar_ab : a % 2 = b % 2 := by
            have hd := hinit.1
            by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;> simp [ha, hb] at hd <;> omega
          have hsum_tl : sumList (x :: xs') % 2 = sumList (y :: ys') % 2 := by
            have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
            have h2 : sumList (x :: xs') % 2 = 0 ∨ sumList (x :: xs') % 2 = 1 := by omega
            have h3 : sumList (y :: ys') % 2 = 0 ∨ sumList (y :: ys') % 2 = 1 := by omega
            have hsum' : (a + sumList (x :: xs')) % 2 = (b + sumList (y :: ys')) % 2 := hsum
            have hsu : (a + sumList (x :: xs')) % 2 =
                (a % 2 + sumList (x :: xs') % 2) % 2 := Int.add_emod a _ 2
            have hsv : (b + sumList (y :: ys')) % 2 =
                (b % 2 + sumList (y :: ys') % 2) % 2 := Int.add_emod b _ 2
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> omega
          have hlen_tl : (x :: xs').length = (y :: ys').length := by
            simp only [List.length_cons] at hlen ⊢
            omega
          have htail := ih (y :: ys') hlen_tl hinit.2 hsum_tl
          simp only [parityVec, List.map_cons]
          have htl : List.map (fun x => decide (x % 2 = 0)) xs' =
              List.map (fun x => decide (x % 2 = 0)) ys' := by
            simp only [parityVec, List.map_cons, List.cons.injEq] at htail
            exact htail.2
          have hxy : decide (x % 2 = 0) = decide (y % 2 = 0) := by
            simp only [parityVec, List.map_cons, List.cons.injEq] at htail
            exact htail.1
          simp [hinit.1, hxy, htl]

theorem sumList_add_halfDiff (u v : List Int) (hlen : u.length = v.length)
    (hpar : parityVec u = parityVec v) :
    sumList u = sumList v + 2 * sumList (halfDiffVec u v) := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [parityVec, List.map_cons, List.cons.injEq] at hpar
      simp only [List.length_cons] at hlen
      have hsp := int_same_mod2_split a b hpar.1
      have htl := ih ys (by omega) hpar.2
      simp only [sumList, halfDiffVec]
      omega

theorem sumList_add_mid (u v : List Int) (hlen : u.length = v.length)
    (hpar : parityVec u = parityVec v) :
    sumList u + sumList v = 2 * sumList (midVec u v) := by
  induction u generalizing v with
  | nil => cases v with | nil => rfl | cons _ _ => simp at hlen
  | cons a xs ih =>
    cases v with
    | nil => simp at hlen
    | cons b ys =>
      simp only [parityVec, List.map_cons, List.cons.injEq] at hpar
      simp only [List.length_cons] at hlen
      have hsp := int_same_mod2_split a b hpar.1
      have htl := ih ys (by omega) hpar.2
      simp only [sumList, midVec]
      omega

theorem dd_same_coset_drop (u v : List Int) (s : Nat) (_hs : 1 ≤ s)
    (hlen : u.length = v.length)
    (hsu : sumList u % 2 = 0) (hsv : sumList v % 2 = 0)
    (htag : ddCosetTag u = ddCosetTag v) (hne : u ≠ v)
    (hu : normSq u ≤ (2 * s : Int)) (hv : normSq v ≤ (2 * s : Int)) :
    normSq (midVec u v) ≤ (2 * (s - 1) : Int) ∧ sumList (midVec u v) % 2 = 0 ∧
    vecAdd (midVec u v) (midVec u v) = vecAdd u v := by
  have hlen_init_u : (parityInit u).length = u.length - 1 := parityInit_length u
  have hlen_init_v : (parityInit v).length = v.length - 1 := parityInit_length v
  have ha := List.append_inj htag (by rw [hlen_init_u, hlen_init_v, hlen])
  have hinit_eq : parityInit u = parityInit v := ha.1
  have hdiv2_eq : decide ((sumList u / 2) % 2 = 0) = decide ((sumList v / 2) % 2 = 0) := by
    have hs1 := ha.2
    simp only [List.cons.injEq, and_true] at hs1
    exact hs1
  have hpar := parityVec_eq_of_init_sum u v hlen hinit_eq (by omega)
  have hhd_eq := sumList_add_halfDiff u v hlen hpar
  have hm_eq := sumList_add_mid u v hlen hpar
  have hdiv_mod : (sumList u / 2) % 2 = (sumList v / 2) % 2 := by
    by_cases h1 : (sumList u / 2) % 2 = 0 <;> by_cases h2 : (sumList v / 2) % 2 = 0 <;>
      simp [h1, h2] at hdiv2_eq <;> omega
  have hhd_even : sumList (halfDiffVec u v) % 2 = 0 := by omega
  have hm_even : sumList (midVec u v) % 2 = 0 := by omega
  have hdrop := checkerboard_Dd_normSq_drop u v (2 * s) hlen hpar hne hhd_even hu hv
  have hid := (parallelogram_even_identity u v hlen hpar).1
  refine ⟨by omega, hm_even, hid⟩

def ddBallVecs (d r s : Nat) : List (List Int) :=
  (ballVecs d r (2 * s)).filter (fun v => decide (sumList v % 2 = 0))

theorem mem_ddBallVecs_iff (d r s : Nat) (h2s : 2 * s ≤ r) (v : List Int) :
    v ∈ ddBallVecs d r s ↔ v.length = d ∧ normSq v ≤ (2 * s : Int) ∧ sumList v % 2 = 0 := by
  simp only [ddBallVecs, List.mem_filter, mem_ballVecs_iff d r (2 * s) h2s v, decide_eq_true_eq]
  push_cast
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

def ddLayer (d L i : Nat) : List (List Int) :=
  (ddBallVecs d (2 * L) (L - i)).map (scaleShiftVec i (4 * (2 * L) + 1))

def ddVecs (d L : Nat) : List (List Int) :=
  (List.range (L + 1)).flatMap (ddLayer d L)

theorem ddLayer_subset_ruzsaLayer (d L i : Nat) (hi : i ≤ L) :
    ∀ w ∈ ddLayer d L i, w ∈ ruzsaLayer d (2 * L) i := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨v, hv, rfl⟩
  have hv_m := (mem_ddBallVecs_iff d (2 * L) (L - i) (by omega) v).mp hv
  apply List.mem_map.mpr
  refine ⟨v, (mem_ballVecs_iff d (2 * L) (2 * L - i) (Nat.sub_le _ _) v).mpr ⟨hv_m.1, by omega⟩, rfl⟩

theorem ddLayer_disjoint (d L i j : Nat) (hd : 1 ≤ d) (hij : i < j) (hj : j ≤ L) :
    ∀ w, w ∈ ddLayer d L i → w ∈ ddLayer d L j → False := by
  intro w hi_m hj_m
  exact ruzsaLayer_disjoint d (2 * L) i j hd hij w
    (ddLayer_subset_ruzsaLayer d L i (by omega) w hi_m)
    (ddLayer_subset_ruzsaLayer d L j hj w hj_m)

theorem ddLayer_nodup (d L i : Nat) : (ddLayer d L i).Nodup := by
  apply nodup_map_on
  · intro u _ v _ heq; exact scaleShiftVec_inj i _ u v heq
  · exact ((cubeVecs_nodup d (2 * L)).filter _).filter _

theorem ddVecs_nodup (d L : Nat) (hd : 1 ≤ d) : (ddVecs d L).Nodup := by
  unfold ddVecs
  apply nodup_flatMap_aux _ _ List.nodup_range
  · intro i _; exact ddLayer_nodup d L i
  · intro i hi j hj _ w hwi hwj
    have hi_le : i ≤ L := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    have hj_le : j ≤ L := Nat.lt_succ_iff.mp (List.mem_range.mp hj)
    by_cases hlt : i < j
    · exact ddLayer_disjoint d L i j hd hlt hj_le w hwi hwj
    · exact ddLayer_disjoint d L j i hd (by omega) hi_le w hwj hwi

def sumDdLayerCount (B : List (List Int)) (d L : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumDdLayerCount B d L m + (B.filter (fun w => decide (w ∈ ddLayer d L m))).length

def findDdPreim (d L i : Nat) (w : List Int) : List Int :=
  match ((ddBallVecs d (2 * L) (L - i)).filter (fun v => decide (scaleShiftVec i (4 * (2 * L) + 1) v = w))) with
  | v :: _ => v
  | [] => []

theorem findDdPreim_spec (d L i : Nat) (v : List Int) (hv : v ∈ ddBallVecs d (2 * L) (L - i)) :
    findDdPreim d L i (scaleShiftVec i (4 * (2 * L) + 1) v) = v := by
  unfold findDdPreim
  cases hf : (ddBallVecs d (2 * L) (L - i)).filter
      (fun z => decide (scaleShiftVec i (4 * (2 * L) + 1) z = scaleShiftVec i (4 * (2 * L) + 1) v)) with
  | nil =>
    exfalso
    have : v ∈ (ddBallVecs d (2 * L) (L - i)).filter
        (fun z => decide (scaleShiftVec i (4 * (2 * L) + 1) z = scaleShiftVec i (4 * (2 * L) + 1) v)) :=
      List.mem_filter.mpr ⟨hv, decide_eq_true rfl⟩
    rw [hf] at this
    exact List.not_mem_nil this
  | cons v0 _ =>
    have hm0 := List.mem_filter.mp (hf ▸ List.mem_cons_self)
    exact scaleShiftVec_inj i _ v0 v (of_decide_eq_true hm0.2)

theorem ddVecs_sum_avoiding_bound (d L : Nat) (hd : 2 ≤ d) (hL : 1 ≤ L)
    (B : List (List Int)) (hBnd : B.Nodup) (hBsub : ∀ w ∈ B, w ∈ ddVecs d L)
    (hBsa : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → vecAdd u v ∉ ddVecs d L) :
    B.length ≤ L * 2 ^ d + 1 := by
  have hB_eq : B.length ≤ sumDdLayerCount B d L (L + 1) := by
    have hcov : ∀ w ∈ B, ∃ i ∈ List.range (L + 1), w ∈ ddLayer d L i := by
      intro w hw
      have hm := hBsub w hw
      simp only [ddVecs, List.mem_flatMap] at hm
      exact hm
    have hle_sum : ∀ m ≤ L + 1,
        (B.filter (fun w => (List.range m).any (fun i => decide (w ∈ ddLayer d L i)))).length ≤
          sumDdLayerCount B d L m := by
      intro m _
      induction m with
      | zero => simp [sumDdLayerCount]
      | succ m ih =>
        simp only [sumDdLayerCount, List.range_succ, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false]
        have ih' := ih (by omega)
        let p : List Int → Bool := fun w => (List.range m).any (fun i => decide (w ∈ ddLayer d L i))
        let q : List Int → Bool := fun w => decide (w ∈ ddLayer d L m)
        have hpart : (B.filter (fun w => p w || q w)).length ≤
            (B.filter p).length + (B.filter q).length := by
          clear ih ih' hcov hBnd hBsub hBsa
          induction B with
          | nil => simp
          | cons a t iht =>
            by_cases hp : p a = true <;> by_cases hq : q a = true
            · simp [hp, hq] at iht ⊢; omega
            · have hqf : q a = false := Bool.eq_false_iff.mpr hq
              simp [hp, hqf] at iht ⊢; omega
            · have hpf : p a = false := Bool.eq_false_iff.mpr hp
              simp [hpf, hq] at iht ⊢; omega
            · have hpf : p a = false := Bool.eq_false_iff.mpr hp
              have hqf : q a = false := Bool.eq_false_iff.mpr hq
              simp [hpf, hqf] at iht ⊢; omega
        exact Nat.le_trans hpart (Nat.add_le_add_right ih' _)
    have hall_filt : B.filter (fun w => (List.range (L + 1)).any (fun i => decide (w ∈ ddLayer d L i))) = B := by
      apply List.filter_eq_self.mpr
      intro w hw
      rcases hcov w hw with ⟨i, hi, hwi⟩
      exact List.any_eq_true.mpr ⟨i, hi, decide_eq_true hwi⟩
    have htop := hle_sum (L + 1) (Nat.le_refl _)
    rw [hall_filt] at htop
    exact htop
  have hlayer_lt : ∀ i, i < L →
      (B.filter (fun w => decide (w ∈ ddLayer d L i))).length ≤ 2 ^ d := by
    intro i hi
    by_cases hgt : 2 ^ d < (B.filter (fun w => decide (w ∈ ddLayer d L i))).length
    · exfalso
      let Bi := B.filter (fun w => decide (w ∈ ddLayer d L i))
      have hgt' : (allBoolTags d).length < Bi.length := by rw [allBoolTags_length]; exact hgt
      let tagFn : List Int → List Bool := fun w => ddCosetTag (findDdPreim d L i w)
      have htag_cov : ∀ w ∈ Bi, tagFn w ∈ allBoolTags d := by
        intro w hw
        have hwm : w ∈ ddLayer d L i := of_decide_eq_true (List.mem_filter.mp hw).2
        rcases List.mem_map.mp hwm with ⟨v, hv, rfl⟩
        apply mem_allBoolTags d
        have hv_m := (mem_ddBallVecs_iff d (2 * L) (L - i) (by omega) v).mp hv
        dsimp only [tagFn]
        rw [findDdPreim_spec d L i v hv, ddCosetTag_length v (by omega), hv_m.1]
      rcases pigeonhole_duplicate_tag Bi (allBoolTags d) (hBnd.filter _) tagFn htag_cov hgt' with
        ⟨w1, hw1, w2, hw2, hne_w, htag_eq⟩
      have hw1B := (List.mem_filter.mp hw1).1
      have hw2B := (List.mem_filter.mp hw2).1
      have hw1L := of_decide_eq_true (List.mem_filter.mp hw1).2
      have hw2L := of_decide_eq_true (List.mem_filter.mp hw2).2
      rcases List.mem_map.mp hw1L with ⟨u, hu_b, hu_eq⟩
      rcases List.mem_map.mp hw2L with ⟨v, hv_b, hv_eq⟩
      rw [← hu_eq] at htag_eq hw1B hne_w
      rw [← hv_eq] at htag_eq hw2B hne_w
      dsimp only [tagFn] at htag_eq
      rw [findDdPreim_spec d L i u hu_b, findDdPreim_spec d L i v hv_b] at htag_eq
      have huv_ne : u ≠ v := fun e => hne_w (by subst e; rfl)
      have hu_m := (mem_ddBallVecs_iff d (2 * L) (L - i) (by omega) u).mp hu_b
      have hv_m := (mem_ddBallVecs_iff d (2 * L) (L - i) (by omega) v).mp hv_b
      have hlen_uv : u.length = v.length := hu_m.1.trans hv_m.1.symm
      have hdrop := dd_same_coset_drop u v (L - i) (by omega) hlen_uv
        hu_m.2.2 hv_m.2.2 htag_eq huv_ne hu_m.2.1 hv_m.2.1
      have hm_mem : midVec u v ∈ ddBallVecs d (2 * L) (L - (i + 1)) := by
        apply (mem_ddBallVecs_iff d (2 * L) (L - (i + 1)) (by omega) (midVec u v)).mpr
        refine ⟨by rw [midVec_length u v hlen_uv, hu_m.1], ?_, hdrop.2.1⟩
        have hs1 : ((L - (i + 1) : Nat) : Int) = ((L - i - 1 : Nat) : Int) := by omega
        omega
      have hadd_in : vecAdd (scaleShiftVec i (4 * (2 * L) + 1) u)
          (scaleShiftVec i (4 * (2 * L) + 1) v) ∈ ddVecs d L := by
        rw [scaleShiftVec_add_mid i (4 * (2 * L) + 1) u v hdrop.2.2]
        simp only [ddVecs, List.mem_flatMap, List.mem_range, ddLayer, List.mem_map]
        exact ⟨i + 1, by omega, midVec u v, hm_mem, rfl⟩
      exact hBsa _ hw1B _ hw2B hne_w hadd_in
    · exact Nat.le_of_not_lt hgt
  have hlayer_L : (B.filter (fun w => decide (w ∈ ddLayer d L L))).length ≤ 1 := by
    let BL := B.filter (fun w => decide (w ∈ ddLayer d L L))
    have hsub_L : ∀ w ∈ BL, w ∈ [scaleShiftVec L (4 * (2 * L) + 1) (List.replicate d 0)] := by
      intro w hw
      have hwm := of_decide_eq_true (List.mem_filter.mp hw).2
      rcases List.mem_map.mp hwm with ⟨v, hv, rfl⟩
      have hv_m := (mem_ddBallVecs_iff d (2 * L) (L - L) (by omega) v).mp hv
      have hll0 : L - L = 0 := Nat.sub_self L
      rw [hll0] at hv_m
      have hn_nn : 0 ≤ normSq v := normSq_nonneg v
      have hn0 : normSq v = 0 := by omega
      have hall0 := (normSq_eq_zero_iff v).mp hn0
      have hveq : v = List.replicate d 0 := by
        apply List.ext_getElem
        · rw [hv_m.1, List.length_replicate]
        · intro idx hi _
          have hm : v[idx] ∈ v := List.getElem_mem hi
          rw [hall0 _ hm, List.getElem_replicate]
      rw [hveq]
      simp
    have hle := nodup_length_le_of_inj BL [scaleShiftVec L (4 * (2 * L) + 1) (List.replicate d 0)]
      (hBnd.filter _) id hsub_L (fun _ _ _ _ h => h)
    simpa using hle
  have hsum_pref : ∀ m, m ≤ L → sumDdLayerCount B d L m ≤ m * 2 ^ d := by
    intro m hm
    induction m with
    | zero => simp [sumDdLayerCount]
    | succ m ih =>
      have h1 := ih (by omega)
      have h2 := hlayer_lt m (by omega)
      simp only [sumDdLayerCount, Nat.succ_mul]
      omega
  have hpref_L := hsum_pref L (Nat.le_refl _)
  have hsr1 : sumDdLayerCount B d L (L + 1) = sumDdLayerCount B d L L +
      (B.filter (fun w => decide (w ∈ ddLayer d L L))).length := rfl
  omega

def ddIntSet (d L : Nat) : List Int :=
  (ddVecs d L).map (evalRadix (ruzsaBase (2 * L)))

theorem ddIntSet_props (d L : Nat) (hd : 2 ≤ d) (hL : 1 ≤ L) :
    (ddIntSet d L).Nodup ∧
    (∀ x ∈ ddIntSet d L, 0 < x) ∧
    MaxSumAvoidingAtMost (ddIntSet d L) (L * 2 ^ d + 1) := by
  let r := 2 * L
  let M : Int := ((2 ^ L : Nat) : Int) * (5 * (r : Int) + 1)
  let Q : Int := ruzsaBase r
  have hM_nn : 0 ≤ M := Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hQ_ge : 2 * M < Q := by
    have h2L_le_2r : ((2 ^ L : Nat) : Int) ≤ ((2 ^ r : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))
    have hmul : M ≤ ((2 ^ r : Nat) : Int) * (5 * (r : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_right h2L_le_2r (by omega)
    simp only [Q, ruzsaBase]
    have h2m : 2 * (((2 ^ r : Nat) : Int) * (5 * (r : Int) + 1)) =
        2 * ((2 ^ r : Nat) : Int) * (5 * (r : Int) + 1) := (Int.mul_assoc 2 _ _).symm
    omega
  have hQpos : 0 < Q := by omega
  have hw_bounds : ∀ w ∈ ddVecs d L, w.length = d ∧ ∀ z ∈ w, 1 ≤ z ∧ z ≤ M := by
    intro w hw
    rcases (List.mem_flatMap.mp hw) with ⟨i, hi, hwi⟩
    have hi_le : i ≤ L := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    have hwr : w ∈ ruzsaLayer d r i := ddLayer_subset_ruzsaLayer d L i hi_le w hwi
    have hb := ruzsaLayer_bounds d r i w hwr
    refine ⟨hb.1, ?_⟩
    intro z hz
    have hzb := hb.2 z hz
    have h2i_ge1 : (1 : Int) ≤ ((2 ^ i : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_pos (by omega : 0 < 2))
    have h2i_le_2L : ((2 ^ i : Nat) : Int) ≤ ((2 ^ L : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hi_le)
    have hmul_le : ((2 ^ i : Nat) : Int) * (5 * (r : Int) + 1) ≤ M :=
      Int.mul_le_mul_of_nonneg_right h2i_le_2L (by omega)
    have hlo_ge1 : 1 ≤ ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) := by
      have : (1 : Int) * (3 * (r : Int) + 1) ≤ ((2 ^ i : Nat) : Int) * (3 * (r : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right h2i_ge1 (by omega)
      omega
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_map_on
    · intro u hu v hv heq
      have hu_b := hw_bounds u hu
      have hv_b := hw_bounds v hv
      exact evalRadix_inj_pos Q M hQ_ge hM_nn u v (hu_b.1.trans hv_b.1.symm)
        (fun z hz => ⟨by have := (hu_b.2 z hz).1; omega, (hu_b.2 z hz).2⟩)
        (fun z hz => ⟨by have := (hv_b.2 z hz).1; omega, (hv_b.2 z hz).2⟩) heq
    · exact ddVecs_nodup d L (by omega)
  · intro x hx
    rcases List.mem_map.mp hx with ⟨w, hw, rfl⟩
    have hwb := hw_bounds w hw
    have hne : w ≠ [] := by intro e; rw [e] at hwb; simp at hwb; omega
    exact evalRadix_pos Q hQpos w hne (fun z hz => by have := (hwb.2 z hz).1; omega)
  · intro B hBnd hBsub hBsa
    let preim := findIntPreim Q (ddVecs d L)
    have hpreim_spec : ∀ x ∈ B, preim x ∈ ddVecs d L ∧ evalRadix Q (preim x) = x := by
      intro x hx
      have hxm : x ∈ ddIntSet d L := hBsub x hx
      rcases List.mem_map.mp hxm with ⟨w0, hw0, hweq⟩
      unfold preim findIntPreim
      cases hf : (ddVecs d L).filter (fun w => decide (evalRadix Q w = x)) with
      | nil =>
        exfalso
        have hw0_in : w0 ∈ (ddVecs d L).filter (fun w => decide (evalRadix Q w = x)) :=
          List.mem_filter.mpr ⟨hw0, decide_eq_true hweq⟩
        rw [hf] at hw0_in
        exact List.not_mem_nil hw0_in
      | cons w1 _ =>
        have hm1 := List.mem_filter.mp (hf ▸ List.mem_cons_self)
        exact ⟨hm1.1, of_decide_eq_true hm1.2⟩
    let Bvec := B.map preim
    have hBv_nd : Bvec.Nodup := by
      apply nodup_map_on _ _ _ hBnd
      intro x hx y hy heq
      have hx_s := hpreim_spec x hx
      have hy_s := hpreim_spec y hy
      rw [← hx_s.2, ← hy_s.2, heq]
    have hBv_sub : ∀ w ∈ Bvec, w ∈ ddVecs d L := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨x, hx, rfl⟩
      exact (hpreim_spec x hx).1
    have hBv_sa : ∀ u ∈ Bvec, ∀ v ∈ Bvec, u ≠ v → vecAdd u v ∉ ddVecs d L := by
      intro u hu v hv huv_ne hsum
      rcases List.mem_map.mp hu with ⟨x, hx, rfl⟩
      rcases List.mem_map.mp hv with ⟨y, hy, rfl⟩
      have hxy_ne : x ≠ y := fun e => huv_ne (by subst e; rfl)
      have hxs := hpreim_spec x hx
      have hys := hpreim_spec y hy
      have hub := hw_bounds _ hxs.1
      have hvb := hw_bounds _ hys.1
      have hev_sum : evalRadix Q (vecAdd (preim x) (preim y)) = x + y := by
        rw [evalRadix_vecAdd Q _ _ (hub.1.trans hvb.1.symm), hxs.2, hys.2]
      have hxy_in : x + y ∈ ddIntSet d L := by
        rw [← hev_sum]
        exact List.mem_map.mpr ⟨vecAdd (preim x) (preim y), hsum, rfl⟩
      exact hBsa x hx y hy hxy_ne hxy_in
    have hbound := ddVecs_sum_avoiding_bound d L hd hL Bvec hBv_nd hBv_sub hBv_sa
    simpa [Bvec] using hbound

def ddWeight (k : Nat) : Nat := if k = 0 then 1 else 2

def ddCountAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, maxS, curSq, w, L =>
    if curSq ≤ maxS && curSq % 2 = 0 then w * (L + 1 - curSq / 2) else 0
  | d + 1, maxS, curSq, w, L =>
    (List.range 9).foldl (fun acc k =>
      let ns := curSq + k * k
      if ns > maxS then acc else acc + ddCountAux d maxS ns (w * ddWeight k) L) 0

theorem dd5_count_l37_eq : ddCountAux 5 74 0 1 37 = 1438294 := by decide

def signedChoices (k : Nat) : List Int :=
  if k = 0 then [0] else [-(k : Int), (k : Int)]

theorem signedChoices_nodup (k : Nat) : (signedChoices k).Nodup := by
  unfold signedChoices
  split
  · simp
  · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩⟩
    simp only [List.mem_singleton]
    omega

theorem signedChoices_len (k : Nat) : (signedChoices k).length = ddWeight k := by
  unfold signedChoices ddWeight
  split <;> simp

theorem signedChoices_mem (k : Nat) (x : Int) (hx : x ∈ signedChoices k) :
    x * x = ((k * k : Nat) : Int) ∧ (-(k : Int) ≤ x ∧ x ≤ (k : Int)) := by
  unfold signedChoices at hx
  split at hx
  · rename_i hk0
    subst hk0
    simp only [List.mem_singleton] at hx
    subst hx
    simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · refine ⟨?_, by omega, by omega⟩
      rw [Int.neg_mul_neg]; push_cast; rfl
    · exact ⟨by push_cast; rfl, by omega, by omega⟩

theorem foldl_add_const (L : List α) (c : Nat) (f : α → Nat) :
    L.foldl (fun acc a => acc + f a) c = c + L.foldl (fun acc a => acc + f a) 0 := by
  induction L generalizing c with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (c + f a), ih (f a), Nat.add_assoc]

theorem ddCountAux_mul (d maxS curSq w L : Nat) :
    ddCountAux d maxS curSq w L = w * ddCountAux d maxS curSq 1 L := by
  induction d generalizing curSq w with
  | zero =>
    unfold ddCountAux
    split <;> simp
  | succ d ih =>
    unfold ddCountAux
    suffices h : ∀ (ks : List Nat) (acc : Nat),
        ks.foldl (fun a k => let ns := curSq + k * k; if ns > maxS then a else a + ddCountAux d maxS ns (w * ddWeight k) L) (w * acc) =
        w * ks.foldl (fun a k => let ns := curSq + k * k; if ns > maxS then a else a + ddCountAux d maxS ns (1 * ddWeight k) L) acc by
      simpa using h (List.range 9) 0
    intro ks acc
    induction ks generalizing acc with
    | nil => rfl
    | cons k rest ihr =>
      simp only [List.foldl_cons]
      by_cases hgt : curSq + k * k > maxS
      · simp only [hgt, ↓reduceIte]; exact ihr acc
      · simp only [hgt, ↓reduceIte]
        rw [ih (curSq + k * k) (w * ddWeight k), ih (curSq + k * k) (1 * ddWeight k), Nat.one_mul]
        have heq : w * acc + w * ddWeight k * ddCountAux d maxS (curSq + k * k) 1 L =
            w * (acc + ddWeight k * ddCountAux d maxS (curSq + k * k) 1 L) := by
          rw [Nat.mul_add, Nat.mul_assoc w (ddWeight k) _]
        rw [heq]
        exact ihr _

theorem int_sq_mod2_eq (x : Int) : x * x % 2 = 0 ↔ x % 2 = 0 := by
  have h : (x * x) % 2 = ((x % 2) * (x % 2)) % 2 := Int.mul_emod x x 2
  have hm : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hm with h0 | h1
  · simp [h, h0]
  · simp [h, h1]

theorem normSq_mod2_eq_sumList (v : List Int) : normSq v % 2 = 0 ↔ sumList v % 2 = 0 := by
  induction v with
  | nil => simp [normSq, dot, sumList]
  | cons x xs ih =>
    simp only [normSq, dot, sumList] at ih ⊢
    have hx := int_sq_mod2_eq x
    have h1 : (x * x + normSq xs) % 2 = ((x * x) % 2 + normSq xs % 2) % 2 := Int.add_emod _ _ 2
    have h2 : (x + sumList xs) % 2 = (x % 2 + sumList xs % 2) % 2 := Int.add_emod _ _ 2
    omega

def listSum {α : Type} (L : List α) (f : α → Nat) : Nat :=
  L.foldl (fun acc x => acc + f x) 0

theorem listSum_cons {α : Type} (a : α) (xs : List α) (f : α → Nat) :
    listSum (a :: xs) f = f a + listSum xs f := by
  simp only [listSum, List.foldl_cons, Nat.zero_add]
  exact foldl_add_const xs (f a) f

theorem listSum_append {α : Type} (L1 L2 : List α) (f : α → Nat) :
    listSum (L1 ++ L2) f = listSum L1 f + listSum L2 f := by
  induction L1 with
  | nil => simp [listSum]
  | cons a xs ih => simp [listSum_cons, ih, Nat.add_assoc]

theorem listSum_map {α β : Type} (L : List α) (g : α → β) (f : β → Nat) :
    listSum (L.map g) f = listSum L (fun x => f (g x)) := by
  induction L with
  | nil => simp [listSum]
  | cons a xs ih => simp [listSum_cons, ih]

theorem listSum_flatMap {α β : Type} (L : List α) (g : α → List β) (f : β → Nat) :
    listSum (L.flatMap g) f = listSum L (fun x => listSum (g x) f) := by
  induction L with
  | nil => simp [listSum]
  | cons a xs ih => simp [List.flatMap_cons, listSum_append, listSum_cons, ih]

theorem listSum_const {α : Type} (L : List α) (c : Nat) :
    listSum L (fun _ => c) = L.length * c := by
  induction L with
  | nil => simp [listSum]
  | cons a xs ih => simp [listSum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem listSum_filter {α : Type} (L : List α) (p : α → Bool) (f : α → Nat) :
    listSum (L.filter p) f = listSum L (fun x => if p x then f x else 0) := by
  induction L with
  | nil => simp [listSum]
  | cons a xs ih =>
    by_cases h : p a = true
    · simp [h, listSum_cons, ih]
    · have hf : p a = false := Bool.eq_false_iff.mpr h
      simp [hf, listSum_cons, ih]

theorem listSum_swap_filter {α β : Type} (Is : List β) (U : List α) (P : β → α → Bool) :
    listSum Is (fun i => (U.filter (P i)).length) =
    listSum U (fun u => (Is.filter (fun i => P i u)).length) := by
  induction Is with
  | nil =>
    simp only [listSum, List.foldl_nil, List.filter_nil, List.length_nil]
    have hz : ∀ L : List α, listSum L (fun _ => 0) = 0 := fun L => by rw [listSum_const, Nat.mul_zero]
    exact (hz U).symm
  | cons i rest ih =>
    rw [listSum_cons, ih]
    clear ih
    induction U with
    | nil => simp [listSum]
    | cons u us ihu =>
      rw [listSum_cons, listSum_cons]
      by_cases h : P i u = true <;> simp [h] <;> omega

theorem nodup_eq_len_of_iff {α : Type} [DecidableEq α] (L1 L2 : List α)
    (h1 : L1.Nodup) (h2 : L2.Nodup) (hiff : ∀ x, x ∈ L1 ↔ x ∈ L2) :
    L1.length = L2.length := by
  have hle1 := nodup_length_le_of_inj L1 L2 h1 id (fun x hx => (hiff x).mp hx) (fun _ _ _ _ heq => heq)
  have hle2 := nodup_length_le_of_inj L2 L1 h2 id (fun x hx => (hiff x).mpr hx) (fun _ _ _ _ heq => heq)
  omega

theorem listSum_le_of_sub {α : Type} (L1 L2 : List α) [DecidableEq α]
    (hnd1 : L1.Nodup) (hsub : ∀ x ∈ L1, x ∈ L2) (f : α → Nat) :
    listSum L1 f ≤ listSum L2 f := by
  induction L1 generalizing L2 with
  | nil => simp [listSum]
  | cons a xs ih =>
    rw [List.nodup_cons] at hnd1
    have haL2 := hsub a (by simp)
    have hsub' : ∀ x ∈ xs, x ∈ eraseOne a L2 := fun x hx =>
      mem_eraseOne_of_ne (fun he => hnd1.1 (by subst he; exact hx)) (hsub x (List.mem_cons_of_mem a hx))
    have ih' := ih (eraseOne a L2) hnd1.2 hsub'
    have hsumL2 : listSum L2 f = f a + listSum (eraseOne a L2) f := by
      clear ih ih' hsub' hsub hnd1
      induction L2 with
      | nil => cases haL2
      | cons b bs ihb =>
        simp only [eraseOne]
        by_cases hba : b = a
        · subst hba; simp [listSum_cons]
        · have hbm : a ∈ bs := by rcases List.mem_cons.mp haL2 with rfl | hb; exact False.elim (hba rfl); exact hb
          simp only [hba, ite_false, listSum_cons, ihb hbm]
          omega
    rw [listSum_cons, hsumL2]
    omega

theorem ddBall_sum_layers_eq (d L : Nat) (v : List Int) (hv : v ∈ ddBallVecs d (2 * L) L) :
    ((List.range (L + 1)).filter (fun i => decide (v ∈ ddBallVecs d (2 * L) (L - i)))).length =
      L + 1 - (normSq v).toNat / 2 := by
  have hvm := (mem_ddBallVecs_iff d (2 * L) L (Nat.le_refl (2 * L)) v).mp hv
  have hnn : 0 ≤ normSq v := normSq_nonneg v
  have hn_ev := (normSq_mod2_eq_sumList v).mpr hvm.2.2
  have hm_nat : (normSq v).toNat ≤ 2 * L := by omega
  have hm_even : (normSq v).toNat % 2 = 0 := by omega
  let m := (normSq v).toNat / 2
  have hm_div : 2 * m = (normSq v).toNat := by omega
  have hlt : L + 1 - m ≤ L + 1 := Nat.sub_le _ _
  have hsub_rng : ∀ a : Nat, a ≤ L + 1 →
      (List.range a).filter (fun i => decide (v ∈ ddBallVecs d (2 * L) (L - i))) =
      List.range (min a (L + 1 - m)) := by
    intro a ha
    induction a with
    | zero => simp
    | succ a iha =>
      rw [List.range_succ, List.filter_append, iha (by omega)]
      by_cases hle : a ≤ L - m
      · have hm1 : min a (L + 1 - m) = a := by omega
        have hm2 : min (a + 1) (L + 1 - m) = a + 1 := by omega
        have hin : v ∈ ddBallVecs d (2 * L) (L - a) := by
          apply (mem_ddBallVecs_iff d (2 * L) (L - a) (by omega) v).mpr
          refine ⟨hvm.1, ?_, hvm.2.2⟩
          omega
        simp [hm1, hm2, hin, List.range_succ]
      · have hm1 : min a (L + 1 - m) = L + 1 - m := by omega
        have hm2 : min (a + 1) (L + 1 - m) = L + 1 - m := by omega
        have hout : v ∉ ddBallVecs d (2 * L) (L - a) := by
          intro hin
          have h2 := ((mem_ddBallVecs_iff d (2 * L) (L - a) (by omega) v).mp hin).2.1
          omega
        simp [hm1, hm2, hout]
  rw [hsub_rng (L + 1) (Nat.le_refl _), Nat.min_eq_right hlt, List.length_range]

def box8 : Nat → List (List Int)
  | 0 => [[]]
  | d + 1 => (List.range 9).flatMap (fun k => (signedChoices k).flatMap (fun x => (box8 d).map (x :: ·)))

theorem box8_nodup (d : Nat) : (box8 d).Nodup := by
  induction d with
  | zero => simp [box8]
  | succ d ih =>
    unfold box8
    apply nodup_flatMap_aux _ _ List.nodup_range
    · intro k _
      apply nodup_flatMap_aux _ _ (signedChoices_nodup k)
      · intro x _
        apply nodup_map_on
        · intro u _ v _ heq; exact (List.cons.inj heq).2
        · exact ih
      · intro x _ y _ hne z hzx hzy
        rcases List.mem_map.mp hzx with ⟨u, _, rfl⟩
        rcases List.mem_map.mp hzy with ⟨v, _, hv⟩
        exact hne (List.cons.inj hv).1.symm
    · intro k1 _ k2 _ hne z hz1 hz2
      rcases List.mem_flatMap.mp hz1 with ⟨x1, hx1, hm1⟩
      rcases List.mem_flatMap.mp hz2 with ⟨x2, hx2, hm2⟩
      rcases List.mem_map.mp hm1 with ⟨u1, _, rfl⟩
      rcases List.mem_map.mp hm2 with ⟨u2, _, hu2⟩
      have hxeq : x1 = x2 := ((List.cons.inj hu2).1).symm
      subst hxeq
      have h1 := (signedChoices_mem k1 x1 hx1).1
      have h2 := (signedChoices_mem k2 x1 hx2).1
      have hk1k2 : k1 * k1 = k2 * k2 := by omega
      have hlt_sq : ∀ a b : Nat, a < b → a * a < b * b := fun a b h =>
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt h))
          (Nat.mul_lt_mul_of_pos_right h (Nat.lt_of_le_of_lt (Nat.zero_le a) h))
      by_cases h12 : k1 < k2
      · exact absurd hk1k2 (Nat.ne_of_lt (hlt_sq k1 k2 h12))
      · by_cases h21 : k2 < k1
        · exact absurd hk1k2.symm (Nat.ne_of_lt (hlt_sq k2 k1 h21))
        · exact hne (by omega)

theorem box8_len_eq (d : Nat) : ∀ v ∈ box8 d, v.length = d := by
  intro v hv
  induction d generalizing v with
  | zero => simp [box8] at hv; subst hv; rfl
  | succ d ih =>
    unfold box8 at hv
    rcases List.mem_flatMap.mp hv with ⟨k, _, hvk⟩
    rcases List.mem_flatMap.mp hvk with ⟨x, _, hvx⟩
    rcases List.mem_map.mp hvx with ⟨tl, htl, rfl⟩
    simp [ih tl htl]

theorem box8_subset_cube (d R : Nat) (hR : 8 ≤ R) :
    ∀ v ∈ box8 d, v ∈ cubeVecs d R := by
  intro v hv
  induction d generalizing v with
  | zero => simp [box8] at hv; subst hv; simp [cubeVecs]
  | succ d ih =>
    unfold box8 at hv
    rcases List.mem_flatMap.mp hv with ⟨k, hk, hvk⟩
    have hk_le : k ≤ 8 := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
    rcases List.mem_flatMap.mp hvk with ⟨x, hx, hvx⟩
    rcases List.mem_map.mp hvx with ⟨tl, htl, rfl⟩
    have hxm := (signedChoices_mem k x hx).2
    have hxc : x ∈ intRangeSym R := (mem_intRangeSym_iff R x).mpr ⟨by omega, by omega⟩
    have htlc := ih tl htl
    simp only [cubeVecs, List.mem_flatMap, List.mem_map]
    exact ⟨x, hxc, tl, htlc, rfl⟩

theorem box8_sum_eq_ddCountAux (d L : Nat) (prefixSq : Nat) :
    listSum (box8 d) (fun v =>
      if prefixSq + (normSq v).toNat ≤ 2 * L ∧ (prefixSq + (normSq v).toNat) % 2 = 0
      then L + 1 - (prefixSq + (normSq v).toNat) / 2
      else 0) =
    ddCountAux d (2 * L) prefixSq 1 L := by
  induction d generalizing prefixSq with
  | zero =>
    have hn0 : normSq [] = 0 := rfl
    simp only [box8, listSum, List.foldl_cons, List.foldl_nil, Nat.zero_add, hn0,
      Int.toNat_zero, Nat.add_zero, ddCountAux, Nat.one_mul]
    by_cases h1 : prefixSq ≤ 2 * L <;> by_cases h2 : prefixSq % 2 = 0 <;> simp [h1, h2]
  | succ d ih =>
    simp only [box8, listSum_flatMap, listSum_map, ddCountAux]
    have hfold : ∀ (ks : List Nat) (acc : Nat),
        acc + listSum ks (fun k => listSum (signedChoices k) (fun x =>
          listSum (box8 d) (fun tl =>
            if prefixSq + (normSq (x :: tl)).toNat ≤ 2 * L ∧
               (prefixSq + (normSq (x :: tl)).toNat) % 2 = 0
            then L + 1 - (prefixSq + (normSq (x :: tl)).toNat) / 2 else 0))) =
        ks.foldl (fun a k =>
          let ns := prefixSq + k * k
          if ns > 2 * L then a else a + ddCountAux d (2 * L) ns (1 * ddWeight k) L) acc := by
      intro ks
      induction ks with
      | nil => intro acc; simp [listSum]
      | cons k rest ihr =>
        intro acc
        simp only [List.foldl_cons, listSum_cons]
        have hterm : listSum (signedChoices k) (fun x => listSum (box8 d) (fun tl =>
            if prefixSq + (normSq (x :: tl)).toNat ≤ 2 * L ∧
               (prefixSq + (normSq (x :: tl)).toNat) % 2 = 0
            then L + 1 - (prefixSq + (normSq (x :: tl)).toNat) / 2 else 0)) =
            if prefixSq + k * k > 2 * L then 0 else ddCountAux d (2 * L) (prefixSq + k * k) (1 * ddWeight k) L := by
          have hx_eq : ∀ x ∈ signedChoices k, listSum (box8 d) (fun tl =>
              if prefixSq + (normSq (x :: tl)).toNat ≤ 2 * L ∧
                 (prefixSq + (normSq (x :: tl)).toNat) % 2 = 0
              then L + 1 - (prefixSq + (normSq (x :: tl)).toNat) / 2 else 0) =
              if prefixSq + k * k > 2 * L then 0 else ddCountAux d (2 * L) (prefixSq + k * k) 1 L := by
            intro x hx
            have hsq := (signedChoices_mem k x hx).1
            have hnorm : ∀ tl : List Int, (normSq (x :: tl)).toNat = k * k + (normSq tl).toNat := by
              intro tl
              have hnc : normSq (x :: tl) = x * x + normSq tl := rfl
              have hnn : 0 ≤ normSq tl := normSq_nonneg tl
              rw [hnc]
              omega
            have heq_f : (fun tl : List Int =>
                if prefixSq + (normSq (x :: tl)).toNat ≤ 2 * L ∧
                   (prefixSq + (normSq (x :: tl)).toNat) % 2 = 0
                then L + 1 - (prefixSq + (normSq (x :: tl)).toNat) / 2 else 0) =
                (fun tl : List Int =>
                  if (prefixSq + k * k) + (normSq tl).toNat ≤ 2 * L ∧
                     ((prefixSq + k * k) + (normSq tl).toNat) % 2 = 0
                  then L + 1 - ((prefixSq + k * k) + (normSq tl).toNat) / 2 else 0) := by
              funext tl
              rw [hnorm tl, Nat.add_assoc]
            rw [heq_f]
            by_cases hgt : prefixSq + k * k > 2 * L
            · have hz : ∀ tl : List Int,
                  (if (prefixSq + k * k) + (normSq tl).toNat ≤ 2 * L ∧
                      ((prefixSq + k * k) + (normSq tl).toNat) % 2 = 0
                   then L + 1 - ((prefixSq + k * k) + (normSq tl).toNat) / 2 else 0) = 0 := by
                intro tl; split <;> omega
              simp only [hz, listSum_const, Nat.mul_zero, hgt, ↓reduceIte]
            · simp only [hgt, ↓reduceIte]
              exact ih (prefixSq + k * k)
          have heq_sum : listSum (signedChoices k) (fun x => listSum (box8 d) (fun tl =>
              if prefixSq + (normSq (x :: tl)).toNat ≤ 2 * L ∧
                 (prefixSq + (normSq (x :: tl)).toNat) % 2 = 0
              then L + 1 - (prefixSq + (normSq (x :: tl)).toNat) / 2 else 0)) =
              listSum (signedChoices k) (fun _ =>
                if prefixSq + k * k > 2 * L then 0 else ddCountAux d (2 * L) (prefixSq + k * k) 1 L) := by
            generalize (signedChoices k) = S at hx_eq
            induction S with
            | nil => simp [listSum]
            | cons a s ihs =>
              rw [listSum_cons, listSum_cons, hx_eq a (by simp), ihs (fun z hz => hx_eq z (List.mem_cons_of_mem a hz))]
          rw [heq_sum, listSum_const, signedChoices_len]
          by_cases hgt : prefixSq + k * k > 2 * L
          · simp [hgt]
          · simp only [hgt, ↓reduceIte]
            rw [Nat.one_mul]
            exact (ddCountAux_mul d (2 * L) (prefixSq + k * k) (ddWeight k) L).symm
        rw [hterm]
        by_cases hgt : prefixSq + k * k > 2 * L
        · simp only [hgt, ↓reduceIte, Nat.zero_add]
          exact ihr acc
        · simp only [hgt, ↓reduceIte]
          rw [← Nat.add_assoc]
          exact ihr _
    simpa [Nat.one_mul] using hfold (List.range 9) 0

theorem ddCountAux_le_ddVecs (d L : Nat) (hL : 4 ≤ L) :
    ddCountAux d (2 * L) 0 1 L ≤ (ddVecs d L).length := by
  have hlen_vecs : (ddVecs d L).length =
      listSum (List.range (L + 1)) (fun i => (ddBallVecs d (2 * L) (L - i)).length) := by
    simp only [ddVecs, List.length_flatMap, ddLayer, List.length_map]
    clear hL
    induction (List.range (L + 1)) with
    | nil => simp [listSum]
    | cons a xs ih => simp [List.map_cons, List.sum_cons, listSum_cons, ih]
  have hsub_len : ∀ i ∈ List.range (L + 1),
      (ddBallVecs d (2 * L) (L - i)).length =
      ((ddBallVecs d (2 * L) L).filter (fun v => decide (v ∈ ddBallVecs d (2 * L) (L - i)))).length := by
    intro i hi
    have hi_le : i ≤ L := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    apply nodup_eq_len_of_iff _ _ ((cubeVecs_nodup d (2 * L)).filter _ |>.filter _)
      (((cubeVecs_nodup d (2 * L)).filter _ |>.filter _).filter _)
    intro v
    constructor
    · intro hv
      apply List.mem_filter.mpr
      have hm := (mem_ddBallVecs_iff d (2 * L) (L - i) (by omega) v).mp hv
      have hmL := (mem_ddBallVecs_iff d (2 * L) L (Nat.le_refl (2 * L)) v).mpr ⟨hm.1, by omega, hm.2.2⟩
      exact ⟨hmL, decide_eq_true hv⟩
    · intro hv
      exact of_decide_eq_true (List.mem_filter.mp hv).2
  have hsum_filt : (ddVecs d L).length =
      listSum (ddBallVecs d (2 * L) L) (fun v => L + 1 - (normSq v).toNat / 2) := by
    rw [hlen_vecs]
    have heq_f : listSum (List.range (L + 1)) (fun i => (ddBallVecs d (2 * L) (L - i)).length) =
        listSum (List.range (L + 1)) (fun i =>
          ((ddBallVecs d (2 * L) L).filter (fun v => decide (v ∈ ddBallVecs d (2 * L) (L - i)))).length) := by
      generalize List.range (L + 1) = Rs at hsub_len
      clear hlen_vecs hL
      induction Rs with
      | nil => simp [listSum]
      | cons r rs ih =>
        rw [listSum_cons, listSum_cons, hsub_len r (by simp), ih (fun i hi => hsub_len i (List.mem_cons_of_mem r hi))]
    rw [heq_f, listSum_swap_filter]
    have heq_v : ∀ v ∈ ddBallVecs d (2 * L) L,
        ((List.range (L + 1)).filter (fun i => decide (v ∈ ddBallVecs d (2 * L) (L - i)))).length =
          L + 1 - (normSq v).toNat / 2 := fun v hv => ddBall_sum_layers_eq d L v hv
    generalize ddBallVecs d (2 * L) L = Us at heq_v
    clear heq_f hsub_len hlen_vecs hL
    induction Us with
    | nil => simp [listSum]
    | cons u us ih =>
      rw [listSum_cons, listSum_cons, heq_v u (by simp), ih (fun v hv => heq_v v (List.mem_cons_of_mem u hv))]
  have hcube_sum : (ddVecs d L).length =
      listSum (cubeVecs d (2 * L)) (fun v =>
        if (normSq v).toNat ≤ 2 * L ∧ (normSq v).toNat % 2 = 0
        then L + 1 - (normSq v).toNat / 2 else 0) := by
    rw [hsum_filt]
    unfold ddBallVecs ballVecs
    have hfilt_eq : ((cubeVecs d (2 * L)).filter (fun v => decide (normSq v ≤ ((2 * L : Nat) : Int)))).filter
        (fun v => decide (sumList v % 2 = 0)) =
        (cubeVecs d (2 * L)).filter (fun v =>
          decide ((normSq v).toNat ≤ 2 * L ∧ (normSq v).toNat % 2 = 0)) := by
      clear hsum_filt hsub_len hlen_vecs hL
      induction (cubeVecs d (2 * L)) with
      | nil => simp
      | cons a xs ih =>
        have hnn := normSq_nonneg a
        have hm2 := normSq_mod2_eq_sumList a
        have ha1 : ((normSq a).toNat ≤ 2 * L) ↔ normSq a ≤ ((2 * L : Nat) : Int) := by omega
        have ha2 : ((normSq a).toNat % 2 = 0) ↔ sumList a % 2 = 0 := by omega
        by_cases h1 : normSq a ≤ ((2 * L : Nat) : Int) <;> by_cases h2 : sumList a % 2 = 0
        · have h1' : (normSq a).toNat ≤ 2 * L := ha1.mpr h1
          have h2' : (normSq a).toNat % 2 = 0 := ha2.mpr h2
          simp only [List.filter_cons, decide_eq_true h1, decide_eq_true h2,
            decide_eq_true (And.intro h1' h2'), ite_true, ih]
        · have h2' : ¬ ((normSq a).toNat ≤ 2 * L ∧ (normSq a).toNat % 2 = 0) := fun h => mt ha2.mp h2 h.2
          simp only [List.filter_cons, decide_eq_true h1, decide_eq_false h2,
            decide_eq_false h2', Bool.false_eq_true, ite_true, ite_false, ih]
        · have h1' : ¬ ((normSq a).toNat ≤ 2 * L ∧ (normSq a).toNat % 2 = 0) := fun h => mt ha1.mp h1 h.1
          simp only [List.filter_cons, decide_eq_false h1, decide_eq_false h1',
            Bool.false_eq_true, ite_false, ih]
        · have h1' : ¬ ((normSq a).toNat ≤ 2 * L ∧ (normSq a).toNat % 2 = 0) := fun h => mt ha1.mp h1 h.1
          simp only [List.filter_cons, decide_eq_false h1, decide_eq_false h1',
            Bool.false_eq_true, ite_false, ih]
    rw [hfilt_eq, listSum_filter]
    congr 1
    funext v
    by_cases h : ((normSq v).toNat ≤ 2 * L ∧ (normSq v).toNat % 2 = 0) <;> simp [h]
  rw [hcube_sum, ← box8_sum_eq_ddCountAux d L 0]
  simp only [Nat.zero_add]
  exact listSum_le_of_sub (box8 d) (cubeVecs d (2 * L)) (box8_nodup d)
    (box8_subset_cube d (2 * L) (by omega)) _

/-- Tight Checkerboard `D_5` Crossover (`L = 37`): `k = 1185`, `|A| ≥ 1,438,294 > 1,407,769 = k^2 + 3k - 11`,
    nearly 4,000× smaller `|A|` than the unsharpened `ℤ^6` threshold (`5.6 × 10^9`). -/
theorem dd_beats_quadratic_explicit :
    ∃ (k : Nat) (A : List Int),
      A.Nodup ∧ (∀ x ∈ A, 0 < x) ∧ MaxSumAvoidingAtMost A k ∧
      k * k + 3 * k - 11 < A.length := by
  have hp := ddIntSet_props 5 37 (by omega) (by omega)
  have hlen_map : (ddIntSet 5 37).length = (ddVecs 5 37).length := by simp [ddIntSet]
  have hcnt := ddCountAux_le_ddVecs 5 37 (by omega)
  rw [dd5_count_l37_eq] at hcnt
  have hlt : (37 * 2 ^ 5 + 1) * (37 * 2 ^ 5 + 1) + 3 * (37 * 2 ^ 5 + 1) - 11 < 1438294 := by decide
  exact ⟨37 * 2 ^ 5 + 1, ddIntSet 5 37, hp.1, hp.2.1, hp.2.2, by omega⟩

end Erdos787AsymptoticClosure
