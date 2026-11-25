/-!
# Threshold45Standalone.lean
### Exact Pure Lean 4 Formal Proof of `n_max(4) = 21`

Self-contained formalization using **Pure Lean 4** (`Init` / `Std` only, zero Mathlib, zero `sorry`).

Proof Architecture:
1. Partition any duplicate-free integer list `A` of length ≥ 22 into positive part `posPart A`,
   reflected negative part `negPart A`, and `{0}`, showing `max (posPart A).length (negPart A).length ≥ 11`.
2. Reduce `pos_le_10_of_no_5` to the 11 largest elements `x 0 < x 1 < ... < x 10` of `P`.
3. Encode trichotomy, order monotonicity, unique pair sums, edge definitions, and no-4-independent-set
   constraints as a 3,324-clause `Nat`-literal CNF with O(1) arithmetic variable decoding.
4. Certify 5 exact Gordan/Farkas LP cores unconditionally via `farkasSpec_sound` (integer linear
   combinations of positive gaps `d t > 0`) checked by `decide`.
5. Replay a 483-step trimmed Hinted-RUP proof in a binary `ClauseTree` verified by `decide`,
   deriving the empty clause `[]` (`False`).
6. Pair with clique-partition certificate `Cs21` for `A21` to conclude `n_max_4_exact : n_max(4) = 21`.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Erdos787Threshold4

/-! ==================================================================== -/
/-! ### Section 1: Sum-Avoiding Basics & Partition Infrastructure        -/
/-! ==================================================================== -/

def IsSumAvoiding (A B : List Int) : Prop :=
  ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → (b1 + b2) ∉ A

theorem isSumAvoiding_congr_mem {A B1 B2 : List Int} (h : ∀ z, z ∈ B1 ↔ z ∈ B2) :
    IsSumAvoiding A B1 ↔ IsSumAvoiding A B2 := by
  constructor
  · intro h1 b1 hb1 b2 hb2 hne
    exact h1 b1 ((h b1).2 hb1) b2 ((h b2).2 hb2) hne
  · intro h2 b1 hb1 b2 hb2 hne
    exact h2 b1 ((h b1).1 hb1) b2 ((h b2).1 hb2) hne

theorem exists_sublist_of_subset :
    ∀ (A B : List Int), B.Nodup → (∀ x ∈ B, x ∈ A) →
      ∃ B' : List Int, B'.Sublist A ∧ B'.Nodup ∧ B'.length = B.length ∧ (∀ z, z ∈ B' ↔ z ∈ B)
  | [], B, _, hSub => by
    match B with
    | [] => exact ⟨[], List.Sublist.slnil, List.nodup_nil, rfl, fun _ => Iff.rfl⟩
    | b :: _ => exact absurd (hSub b (by simp)) (by simp)
  | a :: as, B, hNd, hSub => by
    by_cases ha : a ∈ B
    · let Brest := B.erase a
      have hRestNd : Brest.Nodup := List.Nodup.erase a hNd
      have hNotMem : a ∉ Brest := List.Nodup.not_mem_erase hNd
      have hRestSub : ∀ x ∈ Brest, x ∈ as := by
        intro x hx
        have hMemB : x ∈ B := List.mem_of_mem_erase hx
        have hne : x ≠ a := fun h => hNotMem (h ▸ hx)
        rcases List.mem_cons.1 (hSub x hMemB) with hEq | hInAs
        · exact absurd hEq hne
        · exact hInAs
      obtain ⟨B', hB'sub, hB'nd, hB'len, hB'iff⟩ := exists_sublist_of_subset as Brest hRestNd hRestSub
      have haNotB' : a ∉ B' := fun hIn => hNotMem ((hB'iff a).1 hIn)
      refine ⟨a :: B', List.Sublist.cons_cons a hB'sub, List.nodup_cons.2 ⟨haNotB', hB'nd⟩, ?_, ?_⟩
      · have hLenErase : Brest.length = B.length - 1 := List.length_erase_of_mem ha
        have hPos : 0 < B.length := List.length_pos_of_mem ha
        simp only [List.length_cons, hB'len]
        omega
      · intro z
        simp only [List.mem_cons, hB'iff]
        constructor
        · rintro (rfl | hz)
          · exact ha
          · exact List.mem_of_mem_erase hz
        · intro hz
          by_cases hza : z = a
          · exact Or.inl hza
          · exact Or.inr ((List.mem_erase_of_ne hza).2 hz)
    · have hSubAs : ∀ x ∈ B, x ∈ as := by
        intro x hx
        rcases List.mem_cons.1 (hSub x hx) with rfl | hInAs
        · exact absurd hx ha
        · exact hInAs
      obtain ⟨B', hB'sub, hB'nd, hB'len, hB'iff⟩ := exists_sublist_of_subset as B hNd hSubAs
      exact ⟨B', List.Sublist.cons a hB'sub, hB'nd, hB'len, hB'iff⟩

def IsStrictlySorted (L : List Int) : Prop := List.Pairwise (· < ·) L
def IsStrictlyDesc (L : List Int) : Prop := List.Pairwise (· > ·) L

def sortAsc (A : List Int) : List Int :=
  A.mergeSort (fun a b => decide (a ≤ b))

theorem sortAsc_mem (A : List Int) (x : Int) : x ∈ sortAsc A ↔ x ∈ A := List.mem_mergeSort
theorem sortAsc_length (A : List Int) : (sortAsc A).length = A.length := List.length_mergeSort A
theorem sortAsc_nodup (A : List Int) (hNodup : A.Nodup) : (sortAsc A).Nodup :=
  (List.mergeSort_perm A _).nodup_iff.2 hNodup

private theorem sortAsc_pairwise_le (A : List Int) :
    List.Pairwise (· ≤ ·) (sortAsc A) := by
  have h := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
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

theorem isStrictlyDesc_reverse {L : List Int} (h : IsStrictlySorted L) :
    IsStrictlyDesc L.reverse := by
  rw [IsStrictlyDesc, List.pairwise_reverse]
  exact h

def posPart (A : List Int) : List Int := A.filter (· > 0)
def negPart (A : List Int) : List Int := (A.filter (· < 0)).map (- ·)

theorem posPart_mem_iff (A : List Int) (x : Int) : x ∈ posPart A ↔ x ∈ A ∧ x > 0 := by simp [posPart]

theorem negPart_mem_iff (A : List Int) (x : Int) : x ∈ negPart A ↔ (-x) ∈ A ∧ x > 0 := by
  simp only [negPart, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩; refine ⟨?_, by omega⟩; simpa using ha
  · rintro ⟨hx, hpos⟩; exact ⟨-x, ⟨hx, by omega⟩, by omega⟩

theorem posPart_nodup (A : List Int) (hNodup : A.Nodup) : (posPart A).Nodup :=
  (List.filter_sublist).nodup hNodup

theorem negPart_nodup (A : List Int) (hNodup : A.Nodup) : (negPart A).Nodup :=
  ((List.filter_sublist).nodup hNodup).map (- ·) (fun _ _ hne hneg => hne (by omega))

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
      simp [hp, hn, hz] at ⊢ ih; omega
    · by_cases hn : a < 0
      · have hz : a ≠ 0 := by omega
        simp [hp, hn, hz] at ⊢ ih; omega
      · have ha0 : a = 0 := by omega
        subst ha0; simp at ⊢ ih; omega

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

theorem pos_sum_avoiding_lift (A B : List Int)
    (hSub : ∀ x ∈ B, x ∈ posPart A) (hAvoid : IsSumAvoiding (posPart A) B) :
    IsSumAvoiding A B := by
  intro b1 hb1 b2 hb2 hne hsum
  have h1pos : b1 > 0 := ((posPart_mem_iff A b1).1 (hSub b1 hb1)).2
  have h2pos : b2 > 0 := ((posPart_mem_iff A b2).1 (hSub b2 hb2)).2
  have hsum_pos : b1 + b2 ∈ posPart A := (posPart_mem_iff A (b1 + b2)).2 ⟨hsum, by omega⟩
  exact hAvoid b1 hb1 b2 hb2 hne hsum_pos

theorem neg_sum_avoiding_lift (A B : List Int)
    (hSub : ∀ x ∈ B, x ∈ negPart A) (hAvoid : IsSumAvoiding (negPart A) B) :
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
    rw [heq]; exact hsum
  exact hAvoid b1 hb1 b2 hb2 hbne ((negPart_mem_iff A (b1 + b2)).2 ⟨hsum_neg, by omega⟩)


/-! ==================================================================== -/
/-! ### Section 2: Nat-Literal SAT, ClauseTree, & Hinted-RUP Engine     -/
/-! ==================================================================== -/

abbrev Clause := List Nat
abbrev Valuation := Nat → Bool

def natNeg (l : Nat) : Nat :=
  if l % 2 == 0 then l + 1 else l - 1

def evalLit (v : Valuation) (l : Nat) : Bool :=
  if l % 2 == 0 then v (l / 2) else !(v (l / 2))

theorem evalLit_neg (v : Valuation) (l : Nat) : evalLit v (natNeg l) = !(evalLit v l) := by
  unfold natNeg evalLit
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) % 2 ≠ 0 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]

def evalClause (v : Valuation) (c : Clause) : Bool :=
  c.any (evalLit v)

theorem evalClause_nil (v : Valuation) : evalClause v [] = false := rfl

theorem evalClause_mem_iff (v : Valuation) (c : Clause) :
    evalClause v c = true ↔ ∃ l ∈ c, evalLit v l = true :=
  List.any_eq_true

inductive ClauseTree where
  | empty
  | leaf (c : Clause)
  | node (leftSize : Nat) (l r : ClauseTree)

def ClauseTree.size : ClauseTree → Nat
  | .empty => 0
  | .leaf _ => 1
  | .node ls _ r => ls + r.size

def ClauseTree.get? : ClauseTree → Nat → Option Clause
  | .empty, _ => none
  | .leaf c, 0 => some c
  | .leaf _, _ + 1 => none
  | .node ls l r, i => if i < ls then l.get? i else r.get? (i - ls)

def mergeTreeLevel : List ClauseTree → List ClauseTree
  | [] => []
  | [x] => [x]
  | x :: y :: rest => (.node x.size x y) :: mergeTreeLevel rest

def buildTreeFuel : Nat → List ClauseTree → ClauseTree
  | 0, x :: _ => x
  | 0, [] => .empty
  | _ + 1, [] => .empty
  | _ + 1, [x] => x
  | f + 1, xs => buildTreeFuel f (mergeTreeLevel xs)

def buildClauseTree (cs : List Clause) : ClauseTree :=
  buildTreeFuel (cs.length + 1) (cs.map ClauseTree.leaf)

def hasNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if x == y then true else hasNat x ys

theorem hasNat_sound (x : Nat) : ∀ xs, hasNat x xs = true → x ∈ xs
  | [], h => by simp [hasNat] at h
  | y :: ys, h => by
    unfold hasNat at h
    split at h
    · rename_i heq
      rw [beq_iff_eq.1 heq]; simp
    · exact List.mem_cons_of_mem y (hasNat_sound x ys h)

structure Known4 where
  b0 : List Nat
  b1 : List Nat
  b2 : List Nat
  b3 : List Nat

def Known4.empty : Known4 := ⟨[], [], [], []⟩

def Known4.has (x q : Nat) (s : Known4) : Bool :=
  match q % 4 with
  | 0 => hasNat x s.b0
  | 1 => hasNat x s.b1
  | 2 => hasNat x s.b2
  | _ => hasNat x s.b3

def Known4.ins (x q : Nat) (s : Known4) : Known4 :=
  match q % 4 with
  | 0 => { s with b0 := x :: s.b0 }
  | 1 => { s with b1 := x :: s.b1 }
  | 2 => { s with b2 := x :: s.b2 }
  | _ => { s with b3 := x :: s.b3 }

def Known4.AllTrue (v : Valuation) (s : Known4) : Prop :=
  (∀ k ∈ s.b0, evalLit v k = true) ∧
  (∀ k ∈ s.b1, evalLit v k = true) ∧
  (∀ k ∈ s.b2, evalLit v k = true) ∧
  (∀ k ∈ s.b3, evalLit v k = true)

theorem Known4.empty_allTrue (v : Valuation) : Known4.empty.AllTrue v := by
  simp [Known4.empty, Known4.AllTrue]

theorem Known4.has_sound (v : Valuation) (s : Known4) (hAll : s.AllTrue v)
    (x q : Nat) (h : s.has x q = true) : evalLit v x = true := by
  unfold Known4.has at h
  split at h
  · exact hAll.1 x (hasNat_sound x s.b0 h)
  · exact hAll.2.1 x (hasNat_sound x s.b1 h)
  · exact hAll.2.2.1 x (hasNat_sound x s.b2 h)
  · exact hAll.2.2.2 x (hasNat_sound x s.b3 h)

theorem Known4.ins_sound (v : Valuation) (s : Known4) (hAll : s.AllTrue v)
    (x q : Nat) (hx : evalLit v x = true) : (s.ins x q).AllTrue v := by
  unfold Known4.ins Known4.AllTrue
  split
  · refine ⟨fun k hk => (List.mem_cons.1 hk).elim (· ▸ hx) (hAll.1 k), hAll.2.1, hAll.2.2.1, hAll.2.2.2⟩
  · refine ⟨hAll.1, fun k hk => (List.mem_cons.1 hk).elim (· ▸ hx) (hAll.2.1 k), hAll.2.2.1, hAll.2.2.2⟩
  · refine ⟨hAll.1, hAll.2.1, fun k hk => (List.mem_cons.1 hk).elim (· ▸ hx) (hAll.2.2.1 k), hAll.2.2.2⟩
  · refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, fun k hk => (List.mem_cons.1 hk).elim (· ▸ hx) (hAll.2.2.2 k)⟩

structure Known16 where
  g0 : Known4
  g1 : Known4
  g2 : Known4
  g3 : Known4

def Known16.empty : Known16 := ⟨Known4.empty, Known4.empty, Known4.empty, Known4.empty⟩

def Known16.has (x : Nat) (s : Known16) : Bool :=
  let q := x / 2
  match (q / 4) % 4 with
  | 0 => s.g0.has x q
  | 1 => s.g1.has x q
  | 2 => s.g2.has x q
  | _ => s.g3.has x q

def Known16.ins (x : Nat) (s : Known16) : Known16 :=
  let q := x / 2
  match (q / 4) % 4 with
  | 0 => { s with g0 := s.g0.ins x q }
  | 1 => { s with g1 := s.g1.ins x q }
  | 2 => { s with g2 := s.g2.ins x q }
  | _ => { s with g3 := s.g3.ins x q }

def Known16.insNegList (s : Known16) : List Nat → Known16
  | [] => s
  | x :: xs => Known16.insNegList (s.ins (natNeg x)) xs

def Known16.AllTrue (v : Valuation) (s : Known16) : Prop :=
  s.g0.AllTrue v ∧ s.g1.AllTrue v ∧ s.g2.AllTrue v ∧ s.g3.AllTrue v

theorem Known16.empty_allTrue (v : Valuation) : Known16.empty.AllTrue v :=
  ⟨Known4.empty_allTrue v, Known4.empty_allTrue v, Known4.empty_allTrue v, Known4.empty_allTrue v⟩

theorem Known16.has_sound (v : Valuation) (s : Known16) (hAll : s.AllTrue v)
    (x : Nat) (h : s.has x = true) : evalLit v x = true := by
  unfold Known16.has at h
  dsimp only at h
  split at h
  · exact Known4.has_sound v s.g0 hAll.1 x (x / 2) h
  · exact Known4.has_sound v s.g1 hAll.2.1 x (x / 2) h
  · exact Known4.has_sound v s.g2 hAll.2.2.1 x (x / 2) h
  · exact Known4.has_sound v s.g3 hAll.2.2.2 x (x / 2) h

theorem Known16.ins_sound (v : Valuation) (s : Known16) (hAll : s.AllTrue v)
    (x : Nat) (hx : evalLit v x = true) : (s.ins x).AllTrue v := by
  unfold Known16.ins Known16.AllTrue
  dsimp only
  split
  · exact ⟨Known4.ins_sound v s.g0 hAll.1 x (x / 2) hx, hAll.2.1, hAll.2.2.1, hAll.2.2.2⟩
  · exact ⟨hAll.1, Known4.ins_sound v s.g1 hAll.2.1 x (x / 2) hx, hAll.2.2.1, hAll.2.2.2⟩
  · exact ⟨hAll.1, hAll.2.1, Known4.ins_sound v s.g2 hAll.2.2.1 x (x / 2) hx, hAll.2.2.2⟩
  · exact ⟨hAll.1, hAll.2.1, hAll.2.2.1, Known4.ins_sound v s.g3 hAll.2.2.2 x (x / 2) hx⟩

theorem Known16.insNegList_sound (v : Valuation) :
    ∀ (cs : List Nat) (s : Known16), s.AllTrue v → (∀ c ∈ cs, evalLit v c = false) → (s.insNegList cs).AllTrue v
  | [], s, hAll, _ => hAll
  | c :: cs, s, hAll, hF => by
    unfold Known16.insNegList
    have hc : evalLit v (natNeg c) = true := by
      rw [evalLit_neg, hF c (by simp)]
      rfl
    exact Known16.insNegList_sound v cs (s.ins (natNeg c)) (Known16.ins_sound v s hAll (natNeg c) hc)
      (fun x hx => hF x (List.mem_cons_of_mem c hx))

def scanUnit (s : Known16) (unit : Option Nat) : List Nat → Option (Option Nat)
  | [] => some unit
  | u :: us =>
    if s.has (natNeg u) then scanUnit s unit us
    else match unit with
      | none => scanUnit s (some u) us
      | some _ => none

theorem scanUnit_sound (v : Valuation) (s : Known16) (hAll : s.AllTrue v) :
    ∀ (cs : List Nat) (unit : Option Nat) (res : Option Nat),
      scanUnit s unit cs = some res →
      (∃ u ∈ cs, evalLit v u = true) ∨ (∃ w, unit = some w ∧ evalLit v w = true) →
      ∃ w, res = some w ∧ evalLit v w = true
  | [], unit, res, hScan, hDisj => by
    unfold scanUnit at hScan
    injection hScan with hEq
    rw [← hEq]
    rcases hDisj with ⟨u, hu, _⟩ | hw
    · cases hu
    · exact hw
  | u :: us, unit, res, hScan, hDisj => by
    unfold scanUnit at hScan
    cases hb : s.has (natNeg u)
    · rw [hb] at hScan
      cases unit with
      | none =>
        dsimp only at hScan
        apply scanUnit_sound v s hAll us (some u) res hScan
        rcases hDisj with ⟨x, hx, hxt⟩ | ⟨w, hw, _⟩
        · rcases List.mem_cons.1 hx with rfl | hxs
          · exact Or.inr ⟨x, rfl, hxt⟩
          · exact Or.inl ⟨x, hxs, hxt⟩
        · cases hw
      | some w0 => cases hScan
    · rw [hb] at hScan
      have hNegT : evalLit v (natNeg u) = true := Known16.has_sound v s hAll (natNeg u) hb
      have hFalseU : evalLit v u = false := by
        rw [evalLit_neg] at hNegT
        cases hu : evalLit v u <;> simp [hu] at hNegT ⊢
      apply scanUnit_sound v s hAll us unit res hScan
      rcases hDisj with ⟨x, hx, hxt⟩ | hw
      · rcases List.mem_cons.1 hx with rfl | hxs
        · rw [hxt] at hFalseU; cases hFalseU
        · exact Or.inl ⟨x, hxs, hxt⟩
      · exact Or.inr hw

def checkHintStep (tree : ClauseTree) (cl : Clause) (hints : List Nat) : Bool :=
  let knownInit := Known16.empty.insNegList cl
  let rec go (known : Known16) : List Nat → Bool
    | [] => false
    | hid :: rest =>
      match tree.get? hid with
      | none => false
      | some hc =>
        match scanUnit known none hc with
        | some none => true
        | some (some w) => go (known.ins w) rest
        | none => false
  go knownInit hints

private theorem checkHintStep_go_sound (v : Valuation) (tree : ClauseTree) (limit : Nat)
    (hTree : ∀ hid hc, hid < limit → tree.get? hid = some hc → evalClause v hc = true) :
    ∀ (hints : List Nat) (known : Known16),
      hints.all (fun h => decide (h < limit)) = true →
      known.AllTrue v →
      checkHintStep.go tree known hints = true →
      False
  | [], _, _, _, hGo => by simp [checkHintStep.go] at hGo
  | hid :: rest, known, hLim, hKn, hGo => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hLim
    unfold checkHintStep.go at hGo
    cases hGet : tree.get? hid with
    | none => rw [hGet] at hGo; simp at hGo
    | some hc =>
      rw [hGet] at hGo; dsimp only at hGo
      have hHcTrue : evalClause v hc = true := hTree hid hc hLim.1 hGet
      cases hScan : scanUnit known none hc with
      | none => rw [hScan] at hGo; simp at hGo
      | some res =>
        have hW := scanUnit_sound v known hKn hc none res hScan (Or.inl ((evalClause_mem_iff v hc).1 hHcTrue))
        cases res with
        | none => rcases hW with ⟨_, hc0, _⟩; cases hc0
        | some w =>
          rcases hW with ⟨_, hEqW, hwTrue⟩
          injection hEqW with hww
          subst hww
          rw [hScan] at hGo; dsimp only at hGo
          exact checkHintStep_go_sound v tree limit hTree rest (known.ins w) hLim.2
            (Known16.ins_sound v known hKn w hwTrue) hGo

theorem checkHintStep_sound (v : Valuation) (tree : ClauseTree) (limit : Nat)
    (hTree : ∀ hid hc, hid < limit → tree.get? hid = some hc → evalClause v hc = true)
    (cl : Clause) (hints : List Nat)
    (hLim : hints.all (fun h => decide (h < limit)) = true)
    (hStep : checkHintStep tree cl hints = true) :
    evalClause v cl = true := by
  by_cases hEv : evalClause v cl = true
  · exact hEv
  · exfalso
    have hFalseAll : ∀ l ∈ cl, evalLit v l = false := by
      intro l hl
      by_cases hlt : evalLit v l = true
      · exact absurd ((evalClause_mem_iff v cl).2 ⟨l, hl, hlt⟩) hEv
      · cases hb : evalLit v l <;> simp_all
    exact checkHintStep_go_sound v tree limit hTree hints (Known16.empty.insNegList cl) hLim
      (Known16.insNegList_sound v cl Known16.empty (Known16.empty_allTrue v) hFalseAll) hStep

def checkPrefixIndices (tree : ClauseTree) (idx : Nat) : List Clause → Bool
  | [] => true
  | c :: cs => (tree.get? idx == some c) && checkPrefixIndices tree (idx + 1) cs

theorem checkPrefixIndices_sound (tree : ClauseTree) :
    ∀ (cs : List Clause) (start idx : Nat) (hc : Clause),
      checkPrefixIndices tree start cs = true →
      start ≤ idx → idx < start + cs.length →
      tree.get? idx = some hc → hc ∈ cs
  | [], _, _, _, _, _, hHi, _ => by simp at hHi; omega
  | c :: cs, start, idx, hc, hChk, hLo, hHi, hGet => by
    simp only [checkPrefixIndices, Bool.and_eq_true, beq_iff_eq] at hChk
    by_cases hEq : idx = start
    · subst hEq
      rw [hChk.1] at hGet
      injection hGet with hEqC
      rw [hEqC]; simp
    · have hGt : start + 1 ≤ idx := by omega
      have hLt : idx < (start + 1) + cs.length := by simp at hHi; omega
      have hMem := checkPrefixIndices_sound tree cs (start + 1) idx hc hChk.2 hGt hLt hGet
      exact List.mem_cons_of_mem c hMem

def checkProofSteps (tree : ClauseTree) (idx : Nat) : List (Clause × List Nat) → Bool
  | [] => true
  | (cl, hints) :: rest =>
    (tree.get? idx == some cl) &&
    (hints.all (fun h => decide (h < idx))) &&
    checkHintStep tree cl hints &&
    checkProofSteps tree (idx + 1) rest

theorem checkProofSteps_sound (v : Valuation) (tree : ClauseTree) :
    ∀ (steps : List (Clause × List Nat)) (idx : Nat),
      (∀ hid hc, hid < idx → tree.get? hid = some hc → evalClause v hc = true) →
      checkProofSteps tree idx steps = true →
      ∀ hid hc, hid < idx + steps.length → tree.get? hid = some hc → evalClause v hc = true
  | [], idx, hInv, _, hid, hc, hLt, hGet => hInv hid hc (by simpa using hLt) hGet
  | (cl, hints) :: rest, idx, hInv, hChk, hid, hc, hLt, hGet => by
    simp only [checkProofSteps, Bool.and_eq_true, beq_iff_eq] at hChk
    have hAtIdx := hChk.1.1.1
    have hLim := hChk.1.1.2
    have hStep := hChk.1.2
    have hRest := hChk.2
    have hClTrue : evalClause v cl = true :=
      checkHintStep_sound v tree idx hInv cl hints hLim hStep
    have hInvNext : ∀ j jc, j < idx + 1 → tree.get? j = some jc → evalClause v jc = true := by
      intro j jc hj hgj
      by_cases hjIdx : j = idx
      · subst hjIdx; rw [hAtIdx] at hgj; injection hgj with hEq; rw [← hEq]; exact hClTrue
      · exact hInv j jc (by omega) hgj
    have hLt' : hid < (idx + 1) + rest.length := by simp at hLt; omega
    exact checkProofSteps_sound v tree rest (idx + 1) hInvNext hRest hid hc hLt' hGet


/-! ==================================================================== -/
/-! ### Section 3: O(1) Arithmetic Variable Semantics & Generators       -/
/-! ==================================================================== -/

def mVal : Nat := 11

inductive VarSpec where
  | eq (i j l : Nat)
  | gt (i j l : Nat)
  | lt (i j l : Nat)
  | edge (a b : Nat)
  deriving BEq, DecidableEq

def eqVar (i j l : Nat) : Nat := 1 + 3 * (i * 121 + j * 11 + l)
def gtVar (i j l : Nat) : Nat := 2 + 3 * (i * 121 + j * 11 + l)
def ltVar (i j l : Nat) : Nat := 3 + 3 * (i * 121 + j * 11 + l)
def edgeVar (a b : Nat) : Nat := 4000 + a * 10 + b

def pLit (v : Nat) : Nat := 2 * v
def nLit (v : Nat) : Nat := 2 * v + 1

def specOfVar (v : Nat) : Option VarSpec :=
  if v == 0 then none
  else if v ≤ 3993 then
    let k := v - 1
    let idx := k / 3
    let i := idx / 121
    let j := (idx / 11) % 11
    let l := idx % 11
    if i < j && j < l then
      match k % 3 with
      | 0 => some (.eq i j l)
      | 1 => some (.gt i j l)
      | _ => some (.lt i j l)
    else none
  else if 4000 ≤ v && v < 4100 then
    let p := v - 4000
    let a := p / 10
    let b := p % 10
    if a < b then some (.edge a b) else none
  else none

def specOfLit (l : Nat) : Option (Bool × VarSpec) :=
  (specOfVar (l / 2)).map (l % 2 == 0, ·)

def evalVarSpec (x : Nat → Int) : VarSpec → Bool
  | .eq i j l => decide (x i + x j = x l)
  | .gt i j l => decide (x i + x j > x l)
  | .lt i j l => decide (x i + x j < x l)
  | .edge a b => (List.range mVal).any fun l => decide (b < l ∧ x a + x b = x l)

def mkValuation (x : Nat → Int) : Valuation := fun v =>
  match specOfVar v with
  | some sp => evalVarSpec x sp
  | none => false

theorem evalLit_mkValuation (x : Nat → Int) (l : Nat) (sgn : Bool) (sp : VarSpec)
    (h : specOfLit l = some (sgn, sp)) :
    evalLit (mkValuation x) l = (if sgn then evalVarSpec x sp else !(evalVarSpec x sp)) := by
  unfold specOfLit at h
  cases hsp : specOfVar (l / 2) with
  | none => simp [hsp] at h
  | some vsp =>
    simp [hsp] at h
    rcases h with ⟨rfl, rfl⟩
    unfold evalLit mkValuation
    by_cases hl : l % 2 = 0
    · simp [hl, hsp]
    · simp [hl, hsp]

def triples11 : List (Nat × Nat × Nat) :=
  (List.range mVal).flatMap fun i =>
    (List.range mVal).flatMap fun j =>
      if i < j then
        (List.range mVal).flatMap fun l =>
          if j < l then [(i, j, l)] else []
      else []

def genTriClauses : List Clause :=
  triples11.flatMap fun (i, j, l) =>
    let e := eqVar i j l; let g := gtVar i j l; let lt := ltVar i j l
    [[nLit e, nLit g], [nLit e, nLit lt], [nLit g, nLit lt]]

def genMonoClauses : List Clause :=
  triples11.flatMap fun (i, j, l) =>
    let e := eqVar i j l; let g := gtVar i j l; let lt := ltVar i j l
    let c1 := if l > j + 1 then [[nLit e, pLit (gtVar i j (l - 1))], [nLit g, pLit (gtVar i j (l - 1))]] else []
    let c2 := if l + 1 < mVal then [[nLit e, pLit (ltVar i j (l + 1))], [nLit lt, pLit (ltVar i j (l + 1))]] else []
    let c3 := if i + 1 < j then
      [[nLit e, pLit (gtVar (i + 1) j l)], [nLit g, pLit (gtVar (i + 1) j l)],
       [nLit (eqVar (i + 1) j l), pLit lt], [nLit (ltVar (i + 1) j l), pLit lt]] else []
    let c4 := if j + 1 < l then
      [[nLit e, pLit (gtVar i (j + 1) l)], [nLit g, pLit (gtVar i (j + 1) l)],
       [nLit (eqVar i (j + 1) l), pLit lt], [nLit (ltVar i (j + 1) l), pLit lt]] else []
    let c5 := if i + 1 == j && j + 1 < l then
      [[nLit e, pLit (gtVar (i + 1) (j + 1) l)], [nLit g, pLit (gtVar (i + 1) (j + 1) l)],
       [nLit (eqVar (i + 1) (j + 1) l), pLit lt], [nLit (ltVar (i + 1) (j + 1) l), pLit lt]] else []
    c1 ++ c2 ++ c3 ++ c4 ++ c5

def genUniqClauses : List Clause :=
  (List.range mVal).flatMap fun l =>
    if 2 ≤ l then
      (List.range l).flatMap fun xv =>
        let cands := (List.range l).filterMap fun y =>
          if y != xv then some (eqVar (min xv y) (max xv y) l) else none
        (List.range cands.length).flatMap fun p =>
          (List.range cands.length).flatMap fun q =>
            if p < q then [[nLit cands[p]!, nLit cands[q]!]] else []
    else []

def genEdgeClauses : List Clause :=
  (List.range (mVal - 1)).flatMap fun a =>
    (List.range (mVal - 1)).flatMap fun b =>
      if a < b then
        let rest := (List.range mVal).filterMap fun l =>
          if b < l then some (pLit (eqVar a b l)) else none
        [nLit (edgeVar a b) :: rest]
      else []

def genNo4Clauses : List Clause :=
  let n := mVal - 1
  (List.range n).flatMap fun s0 =>
    (List.range n).flatMap fun s1 =>
      if s0 < s1 then
        (List.range n).flatMap fun s2 =>
          if s1 < s2 then
            (List.range n).flatMap fun s3 =>
              if s2 < s3 then
                [[pLit (edgeVar s0 s1), pLit (edgeVar s0 s2), pLit (edgeVar s0 s3),
                  pLit (edgeVar s1 s2), pLit (edgeVar s1 s3), pLit (edgeVar s2 s3)]]
              else []
          else []
      else []

def baseCNF11 : List Clause :=
  genTriClauses ++ genMonoClauses ++ genUniqClauses ++ genEdgeClauses ++ genNo4Clauses

/-! #### Structural Clause Validators -/

def isValidTriPair : Bool × VarSpec → Bool × VarSpec → Bool
  | (false, .eq i1 j1 l1), (false, .gt i2 j2 l2) => i1 == i2 && j1 == j2 && l1 == l2
  | (false, .eq i1 j1 l1), (false, .lt i2 j2 l2) => i1 == i2 && j1 == j2 && l1 == l2
  | (false, .gt i1 j1 l1), (false, .lt i2 j2 l2) => i1 == i2 && j1 == j2 && l1 == l2
  | _, _ => false

def isValidTriClause : Clause → Bool
  | [la, lb] =>
    match specOfLit la, specOfLit lb with
    | some pa, some pb => isValidTriPair pa pb
    | _, _ => false
  | _ => false

theorem isValidTriClause_sound (x : Nat → Int) (c : Clause) (h : isValidTriClause c = true) :
    evalClause (mkValuation x) c = true := by
  match c with
  | [la, lb] =>
    simp only [isValidTriClause] at h
    cases ha : specOfLit la with
    | none => simp [ha] at h
    | some pa =>
      cases hb : specOfLit lb with
      | none => simp [ha, hb] at h
      | some pb =>
        simp [ha, hb] at h
        rcases pa with ⟨sa, spa⟩; rcases pb with ⟨sb, spb⟩
        cases sa <;> cases sb <;> cases spa <;> cases spb <;> simp [isValidTriPair, and_assoc] at h
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb false _ hb
          by_cases he : x i1 + x j1 = x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec, he]
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb false _ hb
          by_cases he : x i1 + x j1 = x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec, he]
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb false _ hb
          by_cases hg : x i1 + x j1 > x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec]; omega
  | [] | [_] | _ :: _ :: _ :: _ => simp [isValidTriClause] at h

def isValidMonoPair : Bool × VarSpec → Bool × VarSpec → Bool
  | (false, .eq i1 j1 l1), (true, .gt i2 j2 l2) =>
    i1 ≤ i2 && j1 ≤ j2 && l2 ≤ l1 && (i1 < i2 || j1 < j2 || l2 < l1) &&
    i2 < mVal && j2 < mVal && l1 < mVal
  | (false, .gt i1 j1 l1), (true, .gt i2 j2 l2) =>
    i1 ≤ i2 && j1 ≤ j2 && l2 ≤ l1 && (i1 < i2 || j1 < j2 || l2 < l1) &&
    i2 < mVal && j2 < mVal && l1 < mVal
  | (false, .eq i1 j1 l1), (true, .lt i2 j2 l2) =>
    i2 ≤ i1 && j2 ≤ j1 && l1 ≤ l2 && (i2 < i1 || j2 < j1 || l1 < l2) &&
    i1 < mVal && j1 < mVal && l2 < mVal
  | (false, .lt i1 j1 l1), (true, .lt i2 j2 l2) =>
    i2 ≤ i1 && j2 ≤ j1 && l1 ≤ l2 && (i2 < i1 || j2 < j1 || l1 < l2) &&
    i1 < mVal && j1 < mVal && l2 < mVal
  | _, _ => false

def isValidMonoClause : Clause → Bool
  | [la, lb] =>
    match specOfLit la, specOfLit lb with
    | some pa, some pb => isValidMonoPair pa pb
    | _, _ => false
  | _ => false

theorem mono_le_of_strict (x : Nat → Int)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b) :
    ∀ a b, a ≤ b → b < mVal → x a ≤ x b := by
  intro a b hab hb
  by_cases heq : a = b
  · subst heq; omega
  · have := hInc a b (by omega) hb; omega

theorem isValidMonoClause_sound (x : Nat → Int)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b)
    (c : Clause) (h : isValidMonoClause c = true) :
    evalClause (mkValuation x) c = true := by
  have hLe := mono_le_of_strict x hInc
  match c with
  | [la, lb] =>
    simp only [isValidMonoClause] at h
    cases ha : specOfLit la with
    | none => simp [ha] at h
    | some pa =>
      cases hb : specOfLit lb with
      | none => simp [ha, hb] at h
      | some pb =>
        simp [ha, hb] at h
        rcases pa with ⟨sa, spa⟩; rcases pb with ⟨sb, spb⟩
        cases sa <;> cases sb <;> cases spa <;> cases spb <;> simp [isValidMonoPair, and_assoc] at h
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨hi, hj, hl, hdiff, hi2, hj2, hl1⟩
          have xi := hLe _ _ hi hi2; have xj := hLe _ _ hj hj2; have xl := hLe _ _ hl hl1
          have hStrict : x i1 + x j1 - x l1 < x i2 + x j2 - x l2 := by
            rcases hdiff with (h1 | h2) | h3
            · have := hInc _ _ h1 hi2; omega
            · have := hInc _ _ h2 hj2; omega
            · have := hInc _ _ h3 hl1; omega
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb true _ hb
          by_cases heq : x i1 + x j1 = x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec, heq]
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨hi, hj, hl, hdiff, hi1, hj1, hl2⟩
          have xi := hLe _ _ hi hi1; have xj := hLe _ _ hj hj1; have xl := hLe _ _ hl hl2
          have hStrict : x i2 + x j2 - x l2 < x i1 + x j1 - x l1 := by
            rcases hdiff with (h1 | h2) | h3
            · have := hInc _ _ h1 hi1; omega
            · have := hInc _ _ h2 hj1; omega
            · have := hInc _ _ h3 hl2; omega
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb true _ hb
          by_cases heq : x i1 + x j1 = x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec, heq]
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨hi, hj, hl, hdiff, hi2, hj2, hl1⟩
          have xi := hLe _ _ hi hi2; have xj := hLe _ _ hj hj2; have xl := hLe _ _ hl hl1
          have hStrict : x i1 + x j1 - x l1 < x i2 + x j2 - x l2 := by
            rcases hdiff with (h1 | h2) | h3
            · have := hInc _ _ h1 hi2; omega
            · have := hInc _ _ h2 hj2; omega
            · have := hInc _ _ h3 hl1; omega
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb true _ hb
          by_cases hgt : x i1 + x j1 > x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec]; omega
        · rename_i i1 j1 l1 i2 j2 l2
          rcases h with ⟨hi, hj, hl, hdiff, hi1, hj1, hl2⟩
          have xi := hLe _ _ hi hi1; have xj := hLe _ _ hj hj1; have xl := hLe _ _ hl hl2
          have hStrict : x i2 + x j2 - x l2 < x i1 + x j1 - x l1 := by
            rcases hdiff with (h1 | h2) | h3
            · have := hInc _ _ h1 hi1; omega
            · have := hInc _ _ h2 hj1; omega
            · have := hInc _ _ h3 hl2; omega
          rw [evalClause_mem_iff]
          have eva := evalLit_mkValuation x la false _ ha
          have evb := evalLit_mkValuation x lb true _ hb
          by_cases hlt : x i1 + x j1 < x l1
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec]; omega
          · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec]; omega
  | [] | [_] | _ :: _ :: _ :: _ => simp [isValidMonoClause] at h

def isValidUniqPair : Bool × VarSpec → Bool × VarSpec → Bool
  | (false, .eq i1 j1 l1), (false, .eq i2 j2 l2) =>
    i1 < j1 && j1 < l1 && l1 < mVal &&
    i2 < j2 && j2 < l2 && l2 < mVal &&
    l1 == l2 &&
    ((i1 == i2 && j1 != j2) || (i1 == j2 && j1 != i2) ||
     (j1 == i2 && i1 != j2) || (j1 == j2 && i1 != i2))
  | _, _ => false

def isValidUniqClause : Clause → Bool
  | [la, lb] =>
    match specOfLit la, specOfLit lb with
    | some pa, some pb => isValidUniqPair pa pb
    | _, _ => false
  | _ => false

theorem isValidUniqClause_sound (x : Nat → Int)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b)
    (c : Clause) (h : isValidUniqClause c = true) :
    evalClause (mkValuation x) c = true := by
  have hNe : ∀ a b, a ≠ b → a < mVal → b < mVal → x a ≠ x b := by
    intro a b hne ha hb heq
    by_cases hlt : a < b
    · have := hInc a b hlt hb; omega
    · have := hInc b a (by omega) ha; omega
  match c with
  | [la, lb] =>
    simp only [isValidUniqClause] at h
    cases ha : specOfLit la with
    | none => simp [ha] at h
    | some pa =>
      cases hb : specOfLit lb with
      | none => simp [ha, hb] at h
      | some pb =>
        simp [ha, hb] at h
        rcases pa with ⟨sa, spa⟩; rcases pb with ⟨sb, spb⟩
        cases sa <;> cases sb <;> cases spa <;> cases spb <;> simp [isValidUniqPair, and_assoc] at h
        rename_i i1 j1 l1 i2 j2 l2
        rcases h with ⟨hi1, hj1, hl1, hi2, hj2, hl2, rfl, hpair⟩
        rw [evalClause_mem_iff]
        have eva := evalLit_mkValuation x la false _ ha
        have evb := evalLit_mkValuation x lb false _ hb
        by_cases heq1 : x i1 + x j1 = x l1
        · by_cases heq2 : x i2 + x j2 = x l1
          · exfalso
            rcases hpair with ((⟨rfl, hjne⟩ | ⟨heq, hjne⟩) | ⟨heq, hine⟩) | ⟨rfl, hine⟩
            · exact hNe j1 j2 hjne (by omega) (by omega) (by omega)
            · rw [heq] at heq1; exact hNe j1 i2 hjne (by omega) (by omega) (by omega)
            · rw [heq] at heq1; exact hNe i1 j2 hine (by omega) (by omega) (by omega)
            · exact hNe i1 i2 hine (by omega) (by omega) (by omega)
          · refine ⟨lb, by simp, ?_⟩; simp [evb, evalVarSpec, heq2]
        · refine ⟨la, by simp, ?_⟩; simp [eva, evalVarSpec, heq1]
  | [] | [_] | _ :: _ :: _ :: _ => simp [isValidUniqClause] at h

def isValidEdgeClause : Clause → Bool
  | la :: rest =>
    match specOfLit la with
    | some (false, .edge a b) =>
      b < mVal &&
      (List.range mVal).all fun l =>
        if b < l then rest.any (fun lit => decide (specOfLit lit = some (true, .eq a b l))) else true
    | _ => false
  | [] => false

theorem isValidEdgeClause_sound (x : Nat → Int) (c : Clause) (h : isValidEdgeClause c = true) :
    evalClause (mkValuation x) c = true := by
  match c with
  | [] => simp [isValidEdgeClause] at h
  | la :: rest =>
    simp only [isValidEdgeClause] at h
    cases ha : specOfLit la with
    | none => simp [ha] at h
    | some pa =>
      simp [ha] at h
      rcases pa with ⟨sa, spa⟩
      match sa, spa with
      | false, .edge a b =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
        rw [evalClause_mem_iff]
        have eva := evalLit_mkValuation x la false (.edge a b) ha
        by_cases hedge : evalVarSpec x (.edge a b) = true
        · unfold evalVarSpec at hedge
          rw [List.any_eq_true] at hedge
          rcases hedge with ⟨l, hlRange, hCond⟩
          simp only [decide_eq_true_eq] at hCond
          have hCheck := h.2 l (List.mem_range.1 hlRange)
          simp only [hCond.1, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at hCheck
          rcases hCheck with ⟨lit, hLitMem, hLitEq⟩
          have evLit := evalLit_mkValuation x lit true (.eq a b l) hLitEq
          refine ⟨lit, List.mem_cons_of_mem la hLitMem, ?_⟩
          simp [evLit, evalVarSpec, hCond.2]
        · refine ⟨la, by simp, ?_⟩
          have hf : evalVarSpec x (.edge a b) = false := by cases hb : evalVarSpec x (.edge a b) <;> simp_all
          simp [eva, hf]
      | true, .eq _ _ _ | true, .edge _ _ | false, .eq _ _ _ => simp at h

def asEdgeLit (l : Nat) : Option (Nat × Nat) :=
  match specOfLit l with
  | some (true, .edge a b) => some (a, b)
  | _ => none

theorem asEdgeLit_sound (x : Nat → Int) (l a b : Nat) (h : asEdgeLit l = some (a, b)) :
    evalLit (mkValuation x) l = evalVarSpec x (.edge a b) := by
  unfold asEdgeLit at h
  cases hs : specOfLit l with
  | none => simp [hs] at h
  | some p =>
    rcases p with ⟨sgn, sp⟩
    cases sgn <;> cases sp <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact evalLit_mkValuation x l true _ hs

def isValidNo4Clause : Clause → Bool
  | [l01, l02, l03, l12, l13, l23] =>
    match asEdgeLit l01, asEdgeLit l02, asEdgeLit l03, asEdgeLit l12, asEdgeLit l13, asEdgeLit l23 with
    | some (a0, b0), some (a1, b1), some (a2, b2), some (a3, b3), some (a4, b4), some (a5, b5) =>
      a0 < b0 && b0 < b3 && b3 < b4 && b4 < mVal - 1 &&
      a1 == a0 && a2 == a0 && a3 == b0 && a4 == b0 && a5 == b3 &&
      b1 == b3 && b2 == b4 && b5 == b4
    | _, _, _, _, _, _ => false
  | _ => false

theorem isValidNo4Clause_sound (x : Nat → Int)
    (hEdge4 : ∀ s0 s1 s2 s3, s0 < s1 → s1 < s2 → s2 < s3 → s3 < mVal - 1 →
      evalVarSpec x (.edge s0 s1) = true ∨ evalVarSpec x (.edge s0 s2) = true ∨
      evalVarSpec x (.edge s0 s3) = true ∨ evalVarSpec x (.edge s1 s2) = true ∨
      evalVarSpec x (.edge s1 s3) = true ∨ evalVarSpec x (.edge s2 s3) = true)
    (c : Clause) (h : isValidNo4Clause c = true) :
    evalClause (mkValuation x) c = true := by
  match c with
  | [l01, l02, l03, l12, l13, l23] =>
    simp only [isValidNo4Clause] at h
    cases h01 : asEdgeLit l01 with | none => simp [h01] at h | some p01 =>
    cases h02 : asEdgeLit l02 with | none => simp [h01, h02] at h | some p02 =>
    cases h03 : asEdgeLit l03 with | none => simp [h01, h02, h03] at h | some p03 =>
    cases h12 : asEdgeLit l12 with | none => simp [h01, h02, h03, h12] at h | some p12 =>
    cases h13 : asEdgeLit l13 with | none => simp [h01, h02, h03, h12, h13] at h | some p13 =>
    cases h23 : asEdgeLit l23 with | none => simp [h01, h02, h03, h12, h13, h23] at h | some p23 =>
    rcases p01 with ⟨a0, b0⟩; rcases p02 with ⟨a1, b1⟩; rcases p03 with ⟨a2, b2⟩
    rcases p12 with ⟨a3, b3⟩; rcases p13 with ⟨a4, b4⟩; rcases p23 with ⟨a5, b5⟩
    simp [h01, h02, h03, h12, h13, h23, and_assoc] at h
    rcases h with ⟨h01lt, h12lt, h23lt, h3lt, ha1, ha2, ha3, ha4, ha5, hb1, hb2, hb5⟩
    rw [evalClause_mem_iff]
    have e01 := asEdgeLit_sound x l01 a0 b0 h01
    have e02 := asEdgeLit_sound x l02 a1 b1 h02; rw [ha1, hb1] at e02
    have e03 := asEdgeLit_sound x l03 a2 b2 h03; rw [ha2, hb2] at e03
    have e12 := asEdgeLit_sound x l12 a3 b3 h12; rw [ha3] at e12
    have e13 := asEdgeLit_sound x l13 a4 b4 h13; rw [ha4] at e13
    have e23 := asEdgeLit_sound x l23 a5 b5 h23; rw [ha5, hb5] at e23
    rcases hEdge4 a0 b0 b3 b4 h01lt h12lt h23lt h3lt with hE | hE | hE | hE | hE | hE
    · exact ⟨l01, by simp, e01.trans hE⟩
    · exact ⟨l02, by simp, e02.trans hE⟩
    · exact ⟨l03, by simp, e03.trans hE⟩
    · exact ⟨l12, by simp, e12.trans hE⟩
    · exact ⟨l13, by simp, e13.trans hE⟩
    · exact ⟨l23, by simp, e23.trans hE⟩
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp [isValidNo4Clause] at h


/-! ==================================================================== -/
/-! ### Section 4: Exact Farkas Certificate Soundness (`farkasSpec_sound`) -/
/-! ==================================================================== -/

def gap (x : Nat → Int) : Nat → Int
  | 0 => x 0
  | t + 1 => x (t + 1) - x t

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

private theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun t => f t + g t) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp [sumRange, ih]; omega

private theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun t => f t - g t) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp [sumRange, ih]; omega

private theorem sumRange_const_mul (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun t => c * f t) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih]
    rw [Int.mul_add]

private theorem sumRange_ext (n : Nat) (f g : Nat → Int) (h : ∀ t, t < n → f t = g t) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange]
    rw [ih (fun t ht => h t (by omega)), h k (by omega)]

private theorem sumRange_nonneg (n : Nat) (f : Nat → Int) (h : ∀ t, t < n → 0 ≤ f t) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    have h1 := ih (fun t ht => h t (by omega))
    have h2 := h k (by omega)
    simp [sumRange]; omega

private theorem sumRange_le_zero (n : Nat) (f : Nat → Int) (h : ∀ t, t < n → f t ≤ 0) :
    sumRange n f ≤ 0 := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    have h1 := ih (fun t ht => h t (by omega))
    have h2 := h k (by omega)
    simp [sumRange]; omega

private theorem sumRange_pos_of_pos (n : Nat) (f : Nat → Int)
    (hNonneg : ∀ t, t < n → 0 ≤ f t) (t0 : Nat) (ht0 : t0 < n) (hPos : 0 < f t0) :
    0 < sumRange n f := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumRange]
    by_cases heq : t0 = k
    · subst heq
      have h1 := sumRange_nonneg t0 f (fun t ht => hNonneg t (by omega))
      omega
    · have h1 := ih (fun t ht => hNonneg t (by omega)) (by omega)
      have h2 := hNonneg k (by omega)
      omega

private theorem sumRange_gaps_eq (x : Nat → Int) :
    ∀ n k, k < n → sumRange n (fun t => if t ≤ k then gap x t else 0) = x k
  | 0, _, hk => by omega
  | n + 1, k, hk => by
    simp only [sumRange]
    by_cases hkn : k = n
    · subst hkn
      cases k with
      | zero => simp [sumRange, gap]
      | succ m =>
        have hih := sumRange_gaps_eq x (m + 1) m (by omega)
        have hEq : sumRange (m + 1) (fun t => if t ≤ m + 1 then gap x t else 0) =
            sumRange (m + 1) (fun t => if t ≤ m then gap x t else 0) := by
          apply sumRange_ext
          intro t ht
          have h1 : t ≤ m + 1 := by omega
          have h2 : t ≤ m := by omega
          simp [h1, h2]
        rw [hEq, hih]
        simp [gap]; omega
    · have hkl : k < n := by omega
      have hNot : ¬ (n ≤ k) := by omega
      simp [hNot, sumRange_gaps_eq x n k hkl]

def rowCoeff (i j l t : Nat) : Int :=
  (if t ≤ i then 1 else 0) - (if j + 1 ≤ t ∧ t ≤ l then 1 else 0)

private theorem rowCoeff_gaps_sum (x : Nat → Int) (i j l : Nat)
    (hij : i < j) (hjl : j < l) (hlm : l < mVal) :
    sumRange mVal (fun t => rowCoeff i j l t * gap x t) = x i + x j - x l := by
  have hi := sumRange_gaps_eq x mVal i (by omega)
  have hj := sumRange_gaps_eq x mVal j (by omega)
  have hl := sumRange_gaps_eq x mVal l (by omega)
  have hDiff : sumRange mVal (fun t => rowCoeff i j l t * gap x t) =
      sumRange mVal (fun t => if t ≤ i then gap x t else 0) -
      (sumRange mVal (fun t => if t ≤ l then gap x t else 0) -
       sumRange mVal (fun t => if t ≤ j then gap x t else 0)) := by
    rw [← sumRange_sub, ← sumRange_sub]
    apply sumRange_ext
    intro t _
    unfold rowCoeff
    by_cases hti : t ≤ i <;> by_cases htj : t ≤ j <;> by_cases htl : t ≤ l <;>
      by_cases hjt : j + 1 ≤ t <;>
      simp [hti, htj, htl, hjt, Int.one_mul, Int.zero_mul] <;> omega
  rw [hDiff, hi, hj, hl]
  omega

abbrev FarkasSpec := List (Int × Nat × Nat × Nat × Nat)

def colSum : FarkasSpec → Nat → Int
  | [], _ => 0
  | (y, _, i, j, l) :: rest, t => y * rowCoeff i j l t + colSum rest t

def coreClauseOfSpec (spec : FarkasSpec) : Clause :=
  spec.map fun (_, lit, _, _, _) => lit

def verifyFarkasSpec (spec : FarkasSpec) : Bool :=
  (spec.all fun (_, lit, i, j, l) =>
    decide (i < j ∧ j < l ∧ l < mVal) &&
    decide (specOfLit lit = some (false, .eq i j l))) &&
  ((List.range mVal).all fun t => decide (0 ≤ colSum spec t)) &&
  decide (0 < sumRange mVal (colSum spec))

private theorem colSum_gaps_zero (x : Nat → Int) :
    ∀ spec : FarkasSpec,
      (∀ p ∈ spec, p.2.2.1 < p.2.2.2.1 ∧ p.2.2.2.1 < p.2.2.2.2 ∧ p.2.2.2.2 < mVal ∧
        x p.2.2.1 + x p.2.2.2.1 = x p.2.2.2.2) →
      sumRange mVal (fun t => colSum spec t * gap x t) = 0
  | [], _ => by
    have : sumRange mVal (fun t => colSum [] t * gap x t) = sumRange mVal (fun _ => 0) :=
      sumRange_ext mVal _ _ (fun _ _ => by simp [colSum])
    rw [this]
    clear this
    induction mVal with
    | zero => rfl
    | succ k ih => simp [sumRange, ih]
  | (y, lit, i, j, l) :: rest, h => by
    have hHead := h (y, lit, i, j, l) (by simp)
    dsimp only at hHead
    have hRest : sumRange mVal (fun t => colSum rest t * gap x t) = 0 :=
      colSum_gaps_zero x rest (fun p hp => h p (by simp [hp]))
    have hSplit : sumRange mVal (fun t => colSum ((y, lit, i, j, l) :: rest) t * gap x t) =
        sumRange mVal (fun t => y * (rowCoeff i j l t * gap x t)) +
        sumRange mVal (fun t => colSum rest t * gap x t) := by
      rw [← sumRange_add]
      apply sumRange_ext
      intro t _
      simp only [colSum]
      rw [Int.add_mul, Int.mul_assoc]
    rw [hSplit, sumRange_const_mul, rowCoeff_gaps_sum x i j l hHead.1 hHead.2.1 hHead.2.2.1, hRest]
    have hZero : x i + x j - x l = 0 := by omega
    rw [hZero]; simp

theorem farkasSpec_sound (x : Nat → Int)
    (hPos0 : 0 < x 0)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b)
    (spec : FarkasSpec) (hVer : verifyFarkasSpec spec = true) :
    evalClause (mkValuation x) (coreClauseOfSpec spec) = true := by
  by_cases hEv : evalClause (mkValuation x) (coreClauseOfSpec spec) = true
  · exact hEv
  · exfalso
    unfold verifyFarkasSpec at hVer
    rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true, decide_eq_true_eq] at hVer
    have hTriples := hVer.1.1
    have hCols := hVer.1.2
    have hSumPos := hVer.2
    have hAllEq : ∀ p ∈ spec, p.2.2.1 < p.2.2.2.1 ∧ p.2.2.2.1 < p.2.2.2.2 ∧ p.2.2.2.2 < mVal ∧
        x p.2.2.1 + x p.2.2.2.1 = x p.2.2.2.2 := by
      intro ⟨y, lit, i, j, l⟩ hp
      have hSpecItem := hTriples (y, lit, i, j, l) hp
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hSpecItem
      refine ⟨hSpecItem.1.1, hSpecItem.1.2.1, hSpecItem.1.2.2, ?_⟩
      have hLitMem : lit ∈ coreClauseOfSpec spec := by
        rw [coreClauseOfSpec, List.mem_map]
        exact ⟨(y, lit, i, j, l), hp, rfl⟩
      have hLitFalse : evalLit (mkValuation x) lit = false := by
        by_cases hlt : evalLit (mkValuation x) lit = true
        · exact absurd ((evalClause_mem_iff _ _).2 ⟨_, hLitMem, hlt⟩) hEv
        · cases hb : evalLit (mkValuation x) lit <;> simp_all
      have eva := evalLit_mkValuation x lit false (.eq i j l) hSpecItem.2
      rw [eva] at hLitFalse
      simp only [evalVarSpec] at hLitFalse
      by_cases heq : x i + x j = x l
      · exact heq
      · simp [heq] at hLitFalse
    have hZero := colSum_gaps_zero x spec hAllEq
    have hColNonneg : ∀ t, t < mVal → 0 ≤ colSum spec t := fun t ht => by
      have := hCols t (List.mem_range.2 ht)
      exact of_decide_eq_true this
    have hExPos : ∃ t0, t0 < mVal ∧ 0 < colSum spec t0 := by
      by_cases hex : ∃ t0, t0 < mVal ∧ 0 < colSum spec t0
      · exact hex
      · exfalso
        have hAllLe : ∀ t, t < mVal → colSum spec t ≤ 0 := fun t ht => by
          by_cases hp : 0 < colSum spec t
          · exact absurd ⟨t, ht, hp⟩ hex
          · omega
        have := sumRange_le_zero mVal (colSum spec) hAllLe
        omega
    rcases hExPos with ⟨t0, ht0, hColPos⟩
    have hGapPos : ∀ t, t < mVal → 0 < gap x t := fun t ht => by
      cases t with
      | zero => simp [gap]; exact hPos0
      | succ k => simp [gap]; have := hInc k (k + 1) (by omega) ht; omega
    have hTermNonneg : ∀ t, t < mVal → 0 ≤ colSum spec t * gap x t := fun t ht =>
      Int.mul_nonneg (hColNonneg t ht) (by have := hGapPos t ht; omega)
    have hTermPos : 0 < colSum spec t0 * gap x t0 :=
      Int.mul_pos hColPos (hGapPos t0 ht0)
    have hPosTotal := sumRange_pos_of_pos mVal (fun t => colSum spec t * gap x t) hTermNonneg t0 ht0 hTermPos
    omega


/-! ==================================================================== -/
/-! ### Section 5: Certified Cores, Base CNF, & 483-Step RUP Proof       -/
/-! ==================================================================== -/

def cores5 : List FarkasSpec := [
  [(-1, 513, 0, 7, 8), (-1, 585, 0, 8, 9), (1, 879, 1, 2, 3), (1, 951, 1, 3, 4), (-1, 1827, 2, 5, 7), (1, 3291, 4, 5, 9)],
  [(-1, 1689, 2, 3, 6), (1, 2487, 3, 4, 7), (1, 2559, 3, 5, 8), (-1, 5013, 6, 9, 10), (1, 5673, 7, 8, 10), (-1, 3291, 4, 5, 9)],
  [(-1, 1101, 1, 5, 7), (1, 2037, 2, 8, 9), (1, 5013, 6, 9, 10), (-1, 5673, 7, 8, 10)],
  [(-1, 885, 1, 2, 4), (1, 1311, 1, 8, 9), (1, 1827, 2, 5, 7), (-1, 3291, 4, 5, 9)],
  [(-1, 153, 0, 2, 3), (-1, 225, 0, 3, 4), (1, 1239, 1, 7, 8), (1, 1311, 1, 8, 9), (1, 1827, 2, 5, 7), (-1, 3291, 4, 5, 9)]
]

def coreClauses5 : List Clause := cores5.map coreClauseOfSpec

def rupSteps : List (Clause × List Nat) := [
  ([4071,380,8011,8091,3284,4084,4090], [435,1809,1810,1814,1825,1826,1837,2263,3099,390,1662,2177,1462,1186,822,826,838,849,850,861,3073]),
  ([3273,2558,8071,2564,2570], [390,1661,1662,1665,3094]),
  ([4869,5667,6465], [465,492,1946,1973,1974,1977,1978,1989,2075,2450,2453,2455,2670,2674,2677,3053,3058,3062,3065,3092,3098,3103,3105,3107,3112,1821,1822,1825,1826,1837,1890,1894,1905,3101,3313,1681,1682,1689,1690,1701,1754,1758,1769,3096,3303,3330,1481,1482,1489,1490,1501,1554,1558,1569,3090,3099,3283,393,1669,2269,3088,3094,345,1461]),
  ([3279,8113,5667,6465], [393,394,483,492,1669,1670,1677,1678,1689,1690,1701,1807,1811,2029,2030,2033,2075,2269,2670,2674,2677,2679,3053,3058,3062,3065,3067,3092,3098,3103,3107,3110,3112,3331,1470,1477,1478,1489,1490,1501,1957,1958,1961,1982,1989,3104,3108,438,439,1857,1858,1865,1866,1877,1898,1905,1943,3100,3105,3316,1762,1769,3101,417,1562,1569,1753,2448,3090,3096,3283,3303,3088,3094,345,1461]),
  ([3273,8114,5667,6465], [390,483,492,1661,1662,1665,1666,1677,1678,1689,1690,1701,2030,2075,2182,2670,2674,3053,3058,3065,3092,3094,3098,3107,3112,3303,1462,1465,1466,1477,1478,1489,1490,1501,1982,3088,3283,1898,1762,1769,3096,372,1553,1554,1558,1569,3090]),
  ([3285,8113,4082,4088], [397,1804,1811,1823,3104]),
  ([3417,5667,6465], [417,418,483,492,1753,1754,1757,1758,1769,1862,1892,1975,2029,2030,2033,2075,2448,2670,3053,3058,3067,3092,3096,3098,3108,3110,3112,3306,1554,1558,1569,1721,1722,1729,1730,1741,3090,3095,3286,360,1513,1514,1517,1518,1529,1530,1541,3089]),
  ([2619,8053,1904,1910], [360,1513,1514,1517,3089]),
  ([2625,8093,3356,3362], [364,1712,1715,1723,3100]),
  ([2619,5667,6465], [361,483,492,1715,1716,1851,2029,2030,2033,2075,2677,2679,3062,3065,3067,3103,3107,3110,3112,3331,3335,1957,1958,1961,1982,1989,3108,1869,1870,1877,1898,1905,3101,3316,3100,409,1859,1864,1891,3104,3105,3320]),
  ([5667,6465], [483,492,2029,2030,2033,2075,2674,2677,2679,3058,3062,3065,3067,3098,3103,3107,3110,3112,3331,3335,3338,1957,1958,1961,1982,1989,3108,1833,1834,1837,1869,1870,1877,1898,1905,3101,3316,3337,1733,1734,1741,1762,1769,3095,3306,3096,373,1756,1891,3105,3313,3320,3332,3333,3334,3099]),
  ([2691,2632,8134,6465], [372,492,1533,1534,1541,1553,1554,1557,1558,1569,1726,2075,2443,3047,3053,3067,3085,3090,3092,3110,3112,3286,1257,1258,1265,1278,1281,1282,1293,1521,3083,3089,3251,297,1237,1238,1241,3082]),
  ([1893,1244,518,452,1178,3356,8093,8134,6465], [297,492,1237,1238,1241,1242,1254,1265,2072,2075,2275,3040,3047,3067,3077,3082,3085,3110,3112,3251,874,877,878,890,901,2040,3074,3195,1992,1908,1772,1572,1295,3083,225,913,914,918,929,3075]),
  ([1899,3356,8093,3362], [301,1512,1516,1524,1715,1723,3100]),
  ([2632,3356,8093,8075,8134,6465], [492,1533,1534,1541,2072,2075,3040,3047,3053,3067,3077,3085,3092,3110,3112,3340,1257,1258,1265,2040,893,894,901,1968,1992,1879,1908,3342,1771,3096,375,1561,1562,1569,2655,2661,3341,1286,1293,3089,3286,922,929,3090,309,1277,1526,2437,3075,3083,3195,3251,1245,3082,213,873,874,877,3074]),
  ([2634,8075,2702], [1720,1727,1739,3096]),
  ([3357,4148,8134,6465], [412,492,1856,1859,1860,1864,1871,1872,1876,1891,1904,1919,1920,1935,1960,2003,2031,2071,2072,3029,3031,3106,3109,3111,2040,1967,1991,3104,3105,3319]),
  ([8075,8134,6465], [492,2071,2072,3026,3031,3339,2040,3111,1992,1907,1908,1771,3344,368,3340,3096,376,1752,1755,1763,1764,1768,1783,1784,1899,1920,2003,3101,3102,3109,3315,3343,3345]),
  ([441,3356,8093,8073,4090], [106,876,1240,1515,1516,1715,1879,3100,3337,408,1722,1729,1730,1741,3095]),
  ([447,3356,8093,3362], [109,872,876,884,1240,1248,1516,1524,1715,1723,3100]),
  ([453,2624,8073,2636], [112,880,884,896,1236,1240,1260,1515,1535,3095]),
  ([2628,3356,8093,3362], [1712,1715,1723,3100]),
  ([1239,8015,524], [225,913,914,917,3075]),
  ([8114,1238,1100,1826,1112,2552,1838,1106,2564,1832,2558,8074,6465], [492,2072,2075,3047,3053,3058,3065,3085,3092,3098,3107,3112,3303,2040,1968,1992,1844,1908,1703,1772,3094,345,1461,1462,1466,1478,1490,1501,1571,1572,2179,3088,3283,1186,1190,1202,1214,1225,1295,3081,3248,3083,229,1276,1279,1287,3090]),
  ([3356,8093,8134,6465], [492,2072,2075,3040,3047,3058,3067,3077,3085,3098,3110,3112,3346,2040,3306,1968,1991,1992,3347,1879,1908,3337,3348,3350,365,1522,1685,1686,1689,1729,1730,1741,1772,3095,3349,360,361,1245,1246,1253,1254,1265,1481,1482,1489,1572,1673,1674,1715,2280,3082,3100,3251,409,882,890,901,1205,1206,1213,1295,1296,1469,1470,1864,1891,3074,3195,931,1193,3351,3352,3083,3105,450,1285,1562,1762,1898]),
  ([3357,8134,6465], [412,1876,1899,3345]),
  ([4149,8134,6465], [450,492,1897,1898,1905,1954,2075,2668,3053,3058,3062,3067,3092,3098,3103,3110,3112,3346,3354,1762,1870,3306,3353,1562,1569,1733,1734,1741,3316,1533,1534,1541,3101,417,1862,2448,3090,3286,3336,1721,3095]),
  ([2619,8134,6465], [360,492,1514,1673,1674,1677,1678,1689,1717,1718,1730,1741,2072,2075,2276,2280,3040,3047,3058,3067,3077,3085,3098,3110,3112,3346,3355,1238,1241,1242,1253,1254,1265,1469,1470,1477,1478,1489,2040,3082,3251,3306,3349,874,877,878,890,901,1193,1194,1201,1202,1213,1991,1992,3074,3195,1908,1772,1572,1295,1296,931,3351,3352,3083,3105,229,1276,1280,1556,1756,1891]),
  ([2634,8095,3428], [1720,1728,1740,1755,1763,3101]),
  ([8015,8134,6465], [492,2072,2075,3047,3053,3058,3062,3067,3085,3092,3098,3103,3110,3112,3346,3354,3356,2040,3306,3353,1992,3316,1907,1908,3357,367,368,1533,1534,1541,1741,1772,3095,363,364,1257,1258,1265,1521,1571,1572,1728,1755,2422,3101,1295,1296,2656,2662,2667,931,3075,3351,118,916,1279,3083,3090,3251,3286,3082,3089,297,1237]),
  ([8134,6465], [492,2072,2075,3040,3047,3053,3058,3062,3067,3077,3085,3092,3098,3103,3110,3112,3346,3354,3356,3358,2040,3195,3306,3353,1992,3316,1907,1908,3357,367,368,1533,1534,1541,1741,1772,3095,363,364,1257,1258,1265,1521,1571,1572,1728,1755,2417,2422,3101,893,894,901,1295,2662,2667,3074,106,875,876,1239,3082,3089,3251,3286,3083,3090,309,1277]),
  ([369,2558,8031,2564,8071,1112,1106,3298], [91,823,824,1188,1463,1703,3094,348,1470,2265,3081,1194,1202,1214,1225]),
  ([375,8031,1239,1118], [94,820,823,831,1251,2329,3081,208,1204,1212]),
  ([8031,1838,2564,8011,8071,8051,1239,3298], [225,1250,1704,2329,1210,1213,1214,1225,1503,3361,841,842,849,850,861,3073,3360,91,351,823,824,1187,1481,3081,3088,285,1193]),
  ([8113,8011,8071,8091,386,4084,380,4082,4882], [1833,1834,1837,1961,1962,3334,1693,1694,1701,3329,1494,3104,1218,2410,3330,854,861,3099,393,1669,2262,3073,3094,345,821,1186,1462]),
  ([2553,1820,1838,8051,1844], [348,1469,1470,1477,3088]),
  ([1239,8014,6465], [225,226,492,1249,1250,1253,1254,1265,1279,1280,1555,1556,1755,1756,1891,1892,1975,2072,2075,3040,3047,3053,3058,3062,3065,3067,3077,3085,3092,3098,3103,3107,3110,3112,3359,1210,2039,2040,3108,468,841,842,849,850,861,1957,1958,1981,1982,1989,2669,2673,2676,3105,3192,1833,1834,1837,1838,1898,1905,3101,3313,1693,1694,1701,1762,1769,3096,3303,3363,1493,1494,1501,1562,1569,3090,3283,3362,3246,3082,213,1198,829,3073,91,824,1187,1188,1463,1464,1663,3364,3094,352,1668,1671,1683,3099]),
  ([2559,3272,6465], [352,492,1668,1671,1672,1676,1683,1684,1688,1715,1723,1811,1823,1824,1947,2072,3062,3065,3067,3103,3107,3110,3359,2039,3108,468,1957,1958,1961,2648,3104,1833,1834,1837,1870,1877,3099,3100,3311]),
  ([3285,2566,2564,8031,8114,369,6465], [91,396,397,492,823,1494,1681,1804,1811,1823,1824,1826,1838,1947,2072,2075,2402,3058,3065,3067,3098,3107,3110,3112,3359,1217,1218,1225,2039,3081,3108,3360,202,468,1200,1240,1515,1957,1958,1961,1982,2645,2673,3104,3301,3303,1870,1898,1734,1741,1762,1769,3095,3096,372,1725]),
  ([8093,4084,8112,2564,8031,369,6465], [91,823,824,1187,1869,1870,1877,3053,3065,3067,3092,3107,3110,3342,3350,365,1522,1529,1530,1541,1686,1481,1482,1489,1490,1501,1205,1206,1213,1214,1225,3081,202,1195,1200,1239,3088,3089,3281]),
  ([4084,8112,2564,8031,8114,369,6465], [91,823,824,1188,1464,1663,1833,1834,1837,3062,3065,3067,3103,3107,3110,3368,1694,3311,3367,1494,3099,1217,1218,1225,1671,2266,3081,205,1192,1196,1472]),
  ([4086,6465], [492,1940,1947,1959,2072,3359,2039,3108]),
  ([4869,8113,8011,8114,380,6465], [465,492,1945,1946,1949,1950,1961,1962,1974,2075,2455,3062,3065,3103,3104,3107,3112,3334,1890,1893,1894,1905,3101,3313,3329]),
  ([3417,2696,1970,2564,8114,369,6465], [91,417,492,824,1187,1188,1463,1464,1663,1753,1754,1758,1769,1862,2075,2448,3053,3058,3065,3092,3096,3098,3107,3112,3303,3366,1554,1558,1569,1818,3090,3283,1682,1690,1701,3094,348,1469,1470,1477,1478,1489,1490,1501,3088]),
  ([2564,8031,8011,8114,369,6465], [90,91,492,823,824,826,837,1188,1464,1663,2072,2075,3062,3065,3103,3107,3112,3359,3370,442,443,1833,1834,1837,1961,1962,2039,2040,3369,3371,1694,1992,3108,3334,1494,1907,2669,2673,2676,3372,1217,1218,1225,3101,3313,3329,3099,3104,2266,2403,3081]),
  ([8114,369,8034,8014,6465], [492,2075,3040,3047,3065,3077,3085,3107,3112,3192,3248,3370,3373,443,1693,1834]),
  ([3280,2474,1748,1766,2492,8069,8049,6465], [1621,1622,1626,1637,1638,1649,3093,330,1405,1406,1413,1414,1426,1437,1438,1449,3087]),
  ([4875,8115,369,8014,6465], [90,91,468,492,769,770,773,774,785,786,797,798,809,824,1188,1464,1663,1957,1958,1961,1981,1982,1989,2075,2648,2669,2673,2676,3040,3053,3058,3062,3065,3067,3077,3092,3098,3103,3105,3107,3110,3112,447,1833,1834,1837,1870,1877,1889,1890,1894,1905,1941,1942,2413,2449,2452,3101,3186,1754,1758,1769,1822,1857,3072,3096,3297,73,760,1123,1124,1399,1554,1558,1569,1633,1634,3090,3277,1429,3375,393,395,1807,1811,3099,3100,3104,3311]),
  ([369,8034,8014,6465], [492,2072,3359,3374,3376,2039,3108,465,1973,1974,1977,1978,1989,3105]),
  ([4149,6465], [451,492,1972,1975,1983,2072,3359,2039,3108]),
  ([3287,8091,6465], [396,398,1803,1804,3370,443,1799,1833,1834,1837,3099]),
  ([1834,8031,8011,368,6465], [1205,1206,1213,1214,1225,841,842,849,850,861,3073,94,820,823,831,3081]),
  ([8114,8034,8014,6465], [492,2075,3040,3047,3062,3065,3067,3077,3085,3103,3107,3110,3112,3192,3248,3370,3377,3380,290,442,443,1468,1472,1476,1484,1488,1516,1524,1660,1663,1671,1672,1683,1684,1715,1723,1811,1823,1833,1834,1837,1869,1870,1877,1961,3099,3100,3104,3311]),
  ([2474,3280,314,8069,8049,1766,8009,2492,6465], [1621,1622,1626,1637,1638,1649,3093,3375,264,1122,2119,2166,758,762,773,774,786,797,798,809,3072]),
  ([3280,314,8069,8049,1766,8009,2492,6465], [3382,327,1397,1398,1401,1402,1413,1414,1426,1437,1438,1449,3087]),
  ([8014,1244,6465], [492,2072,2075,3040,3053,3058,3062,3065,3067,3077,3092,3098,3103,3107,3110,3112,3359,3365,3370,3378,442,443,1833,1834,1837,1869,1870,1877,1961,2039,2040,1991,1992,1907,1908,1771,1772,1571,1572,1295,3083,3381,3105,447,448,1889,1890,1893,1941,1942,1975,2413,2449,2452,3101,3108,3186,1754,1757,1822,1857,2669,3090,3096,3277,3297,1633,1634,1429,1430,1154,789,3383,393,395,1799,1807,1811,3099,3100,3104,3311]),
  ([4143,8015,6465], [448,492,1891,1975,2072,2440,3359,1756,2039,3108,1556,2658,3075,124,920,924,1276,1280]),
  ([2553,1106,8051,8031,6465], [348,1469,1470,1477,1478,1489,1490,1501,2265,3088,282,1185,1186,1190,1202,1213,1214,1225,3081]),
  ([3286,8071,8051,8031,6465], [1681,1682,1689,1690,1701,1481,1482,1489,1490,1501,1205,3386,3094,345,1461,1462,1465,3088]),
  ([3287,6465], [398,1804,1807,1811,1819,1823,3062,3065,3067,3103,3107,3110,3370,3379,442,443,1869,1870,1877,1961,3100,3104,3311]),
  ([4875,8075,8015,3430], [1771,2658,2673,3096,1555,2438,3075,124,920,924,1276,1280]),
  ([8075,8015,6465], [492,2072,3359,2039,2040,1992,1908,3389,1771,3108,1975,2453,3096,376,1752,1756,1892]),
  ([4869,8055,8015,2704], [1571,1975,2450,3090,313,1552,1556,1756,1892]),
  ([1244,6465], [492,2072,2075,3047,3053,3058,3065,3085,3092,3098,3107,3112,3359,3378,3384,3385,3388,3390,2039,2040,1991,1992,3105,3303,1908,1772,1571,1572,1295,1296,931,3351,3083,3248,3387,3283,3391,3108,2658,2669,3075,3090,309,913,1278]),
  ([6465], [492,2072,3359,3392,229,1276,1280,1288,1556,1564,1756,1764,1892,1900,1975,1983,2039,3108]),
  ([8179], [3113,3393]),
  ([4881,1245,8114,8158,8118], [229,472,1276,1279,1280,1287,1288,1292,1307,1308,1555,1563,1564,1583,1584,1764,1784,1900,1919,1984,2031,2041,2042,2073,2979,2984,3090,3096,3111,3113,3322,3106,3014,3019,3091,3097,3288,3308,3092,3098,387,1595]),
  ([8156,8138,8134,4940,4214,8114,8158,8118], [3394,3322,3323,3106,3109,477,2007]),
  ([1095,2558,3291,8071,1844,2570,8051], [199,399,1187,1188,1463,1693,2611,3094,3364]),
  ([1107,1838,1844,8051], [205,1192,1195,1196,1207,1459,3088]),
  ([1101,1832,1838,1844,8051], [202,1184,1187,1195,3088]),
  ([3288,3362,8093,4088,8113], [1804,1807,1811,1819,1823,3100,3104,441,1869]),
  ([8078,1245,8070,8114,8158,8118], [229,1276,1280,1288,1292,1308,1555,1563,1583,1584,1784,1919,3303,3394,3096,379,1777,1778,1790,1925,3097,3106,3304]),
  ([1245,8070,8031,8114,8158,8118], [228,229,1262,1276,1279,1280,1287,1288,1292,1308,1556,1564,1584,1755,1756,1763,1764,1784,1892,1900,1919,1920,1975,1983,1984,2003,2031,2508,3395,3401,1222,1225,3098,3108,387,388,1595,1792,1797,1798,1934,2017,3092,3103,3110,3320,3396,1776,3111,486,1571,1748,2040,2989,3090,3101,3283,3313,3316,1708,1967,1968,1503,1843,1879,3400,397,398,1682,1825,1481,1482,1489,3398,3399,3081,199,1187,1188,1464,1663,3088,3099,393,1469,1670]),
  ([8051,8031,8091,3284,3286,2110], [1682,1825,1826,1837,1481,1482,1489,1490,1501,3398,3399,1206,1213,1214,1225,3081,199,1187,1188,1464,1663,3088,3099,393,1469,1670]),
  ([5673,8055,8050,4214,2835,8118], [387,388,486,487,1595,1798,1934,2017,2051,2073,2980,3003,3010,3016,3028,3035,3042,3077,3085,3092,3106,3110,3113,3284,3091,318,319,1305,1565,1584,1784,1920,2003,2682,3076,3084,3090,3109,3196,3252,309,1526,1245,1246,1253,1254,1265,3082,213,873,874,877,878,889,890,901,3074]),
  ([1965,8134,2835,1244,8158], [309,388,1277,1278,1282,1293,1526,1798,1934,2017,2437,3035,3042,3077,3083,3085,3110,3251,914,917,918,929,1245,1246,1253,1254,1265,3075,3082,3195,213,873,874,877,878,889,890,901,3074]),
  ([8050,1964,8134,4214,2835,8114,8158,8118], [387,388,1595,1792,1798,1934,2017,3092,3110,3283,3404,1776,1571,3090,313,1564,1568,1584,1764,1784,1900,1920,1984,2003,2031,3111,3396]),
  ([8091,3284,8051,8134,3286,2835,1244,8114,8158,8118], [387,388,1596,1682,1792,1798,1825,1826,1837,1934,2017,3035,3042,3077,3085,3110,3403,1481,1482,1489,1490,1501,1776,3248,1206,1572,841,842,849,850,861,1295,3083,225,913,914,917,918,929,1250,3075,3192,3195,881,882,889,890,901,3074,105,833,3073,91,824,1187,1188,1464,1663,3088,3099,393,1469,1670]),
  ([4941,5672,8014,2835,8158], [387,388,475,1596,1798,1934,2018,2047,2062,2077,2686,3035,3077,3111,3113,3197,1320,3076,951,956]),
  ([5667,8095,3416], [2031,2677,3101,424,1896,1900,1984]),
  ([3561,8118,5667,1239,8158], [225,226,432,433,483,913,914,917,918,929,1249,1250,1253,1254,1265,1280,1556,1756,1892,1928,1934,1975,2017,2018,2029,2030,2033,2045,2046,2049,2062,2077,2693,3036,3043,3075,3077,3085,3108,3109,3110,3113,3195,881,882,889,890,901,1788,3074,106,875,1588,3082,3252,1311,3084]),
  ([8011,8071,8118,5667,1239,8158], [225,226,483,1250,1279,1280,1556,1755,1756,1891,1892,1975,2029,2030,2033,2034,2046,2670,2679,2693,2707,3108,3394,3409,3410,1210,1957,1958,1982,1989,2002,2005,3103,3105,3106,3313,841,842,849,1834,1838,1898,1918,3363,1693,1694,1762,1782,3320,1493,1562,1569,1582,3090,3110,1306,1309,3045,3051,3084,3085,3092,3249,3283,3362]),
  ([8078,8118,5667,1239,8158], [225,226,483,913,914,917,918,929,1279,1280,1555,1556,1755,1756,1891,1892,1975,2029,2030,2033,2670,2674,2679,3075,3108,3409,3410,1958,1982,1989,3103,3105,1869,1870,1877,1898,1733,1734,1741,1762,1769,3096,3303,3411,1533,1534,1541,1562,1569,3090,3192,3077,133,958,1321,1322,1598,1798,1934,2017,3092,3110,3286,3306,3316,3336,3337,3095]),
  ([2835,5667,1239,8158], [225,226,387,388,483,913,914,917,918,929,1250,1280,1281,1556,1595,1755,1756,1792,1797,1798,1891,1892,1933,1934,1975,2017,2018,2029,2030,2033,2046,2062,2077,2679,2698,2707,3035,3075,3077,3092,3103,3107,3108,3110,3113,3195,3409,881,882,889,890,901,1587,1957,1958,1961,1982,1989,2002,2005,3074,3091,3105,3106,3284,3313,3316,3320,3334,3407,106,398,876,1240,1516,1715,1819,1869,1870,1877,3100]),
  ([5667,1239,8158], [225,226,483,913,914,917,918,929,1250,1280,1555,1556,1755,1756,1892,1975,2029,2030,2033,2674,3075,3108,3409,3413,881,882,889,890,901,1958,1962,1982,3098,3412,1869,1898,3107,462,463,1762,1769,1931,2017,3037,3077,3096,3103,3110,3195,3306,3316,3347,3074]),
  ([3423,8055,1964], [1763,2667,3090,316,1560,1564]),
  ([3429,5666,4142], [424,1896,1899,1904,1909,1910,1914,1919,1925,1930,1933,1934,1994,2018,2041,2042,2061,2073,3105,3106,3107,3111,3112,3113,3322]),
  ([5013,8011,5673,8116,8118,1239,2037], [225,318,487,1250,1305,1306,1309,2073,2329,3045,3084,3085,3113,3249,3326,1210,1213,1214,1225,3081,3361,198,821,822,826,837,838,849,850,861,3073]),
  ([4221,1239,8078,2037,8158], [225,226,319,459,460,913,914,917,918,929,1280,1555,1556,1583,1584,1755,1756,1783,1784,1891,1920,1923,1996,2004,2010,2047,2053,2054,2073,2682,3001,3019,3075,3076,3097,3102,3111,3113,3197,3308,3416,1908,3077,133,958,1322,1598,1771,1797,3096,3103,3318,376,1763,3101]),
  ([3423,8115,8156,8138,1239,4940,8158], [226,421,1280,1556,1756,1891,1892,1899,1900,1975,1983,3105,3394,454,1993,1998,2009,3108,3109,3323]),
  ([8156,657,8116,1239,2037,8158], [133,226,319,958,1280,1322,1555,1556,1583,1584,1597,1598,1755,1756,1783,1784,1797,1798,1891,1892,1920,1933,1934,1975,2003,2004,2017,2018,2047,2062,2077,3098,3103,3107,3110,3113,3322,3416,3419,3101,3318,3102,429,430,1787,1912,1926,2009,3097,3109,3308,3323,1771,3096,376,1764,1899,1900,1983,3105,3108,471,1991]),
  ([657,8116,1239,2037,8158], [133,225,318,319,957,958,1249,1250,1253,1254,1265,1305,1306,1309,1322,1583,1584,1597,1598,1783,1784,1797,1798,1920,1933,1934,2003,2004,2017,2018,2047,2062,2077,2329,3084,3085,3098,3103,3107,3110,3113,3249,3420,1210,1213,1214,1225,3111,486,2040,2051,3021,3025,3097,3102,3109,3252,3304,3314,3317,3321,1967,1968,3082,213,1197,1843,1879,3081,3400,199,397,398,1188,1463,1464,1663,1681,1682,1689,1690,1701,1825,3094,3099,393,1669]),
  ([8118,8116,1239,2037,8158], [225,318,319,913,914,917,918,929,1249,1250,1253,1254,1265,1305,1306,1309,1583,1584,1783,1784,1920,2003,2004,2047,2682,3075,3084,3394,3421,881,882,889,890,901,942,945,3076,3077,3193,3197,3111,3417,486,2040,2051,3021,3025,3097,3102,3109,3110,3196,3321,1967,1968,3074,106,875,876,1240,1516,1716,1851,3082,3252,3085,241,1322,1597,1598,1797,3098,3103,3307,3317,3347,412,1856,1859,1871,3104]),
  ([8116,1239,2037,8158], [225,318,319,913,914,917,918,929,1249,1250,1253,1254,1265,1305,1306,1309,1584,1784,1920,2003,2004,2047,2682,3075,3084,3394,3421,3422,881,882,889,890,901,942,945,3076,3077,3107,3197,463,2017,3044,3085,3110,3111,486,2051,3109,3196,3252,3074,3082,213,873]),
  ([1239,2037,8158], [225,318,319,913,914,917,918,929,1306,1584,1784,1919,1920,2004,2047,2682,3075,3394,3423,942,945,3076,3106,3418,460,2010,2053,3098,3111,3197,3035,3077]),
  ([4221,2037,8158], [318,319,459,460,1305,1306,1309,1566,1583,1584,1783,1784,1920,1923,1996,2004,2010,2047,2053,2054,2073,2682,3001,3019,3076,3084,3097,3102,3111,3113,3424,1285,1286,1293,1907,1908,3083,3253,921,922,929,1771,3085,240,241,955,1322,1597,1598,1797,3077,3098,3103,3197,3308,3318,3075,118,916,1280,1555,1556,1755,3096,3101,420,1761]),
  ([3423,4868,4142,8115,8138,8156,4940,8158], [421,1899,1900,1983,3105,3394,454,1993,1998,2009,3108,3109,3323]),
  ([8156,2037,8158], [318,319,1305,1306,1309,1566,1583,1584,1783,1784,1919,1920,2003,2004,2047,2682,3084,3394,3424,3425,942,945,1285,1286,1293,3076,3083,3106,3253,921,922,929,3085,240,241,955,1322,1597,1598,1797,1798,1933,1934,2017,3077,3098,3103,3107,3110,3197,3322,3075,118,916,1280,1555,1556,1755,1756,1891,1892,1975,3416,3426,3101,3318,3102,429,430,1787,1912,1926,2009,3097,3109,3308,3323,3389,1771,3096,3108,376,471,1764,1899,1991,3105]),
  ([657,1106,2564,1832,3290,2558,3284,8091,8114,8118,8054,2037,8158], [133,318,319,957,958,1321,1566,1584,1784,1920,2004,2047,2537,3085,3092,3283,3424,3427,1285,1286,1293,1538,3083,3111,3248,486,1498,1501,2040,3399,1217,1218,1225,1968,3081,199,1187,1188,1464,1663,1843,3088,3099,393,1469,1670]),
  ([8098,8134,8114,8138,8118,513,2037,8158], [117,118,318,319,885,886,889,890,901,916,1279,1306,1565,1566,1569,1583,1584,1783,1784,1919,1920,2003,2004,2047,2308,2537,2682,3090,3320,3394,3396,3425,846,849,850,861,942,945,1538,3076,3106,3111,486,1498,1501,2040,2051,3021,3025,3097,3102,3109,3314,3317,1967,1968,1843,1879,3400,397,398,1681,1682,1689,1690,1701,1825,1481,1482,1205,3428,3077,3193,3196,3074,105,833,3073,91,824,1187,1188,1463,1464,1663,3099,393,1669,2269,3088,3094,3304,3406,3098]),
  ([8134,8114,8138,8118,513,2037,8158], [117,118,318,319,885,886,889,890,901,915,916,1279,1306,1565,1566,1569,1584,1784,1919,1920,2003,2004,2047,2539,2682,3090,3394,3396,3429,942,945,1285,1286,1293,1538,1541,3076,3083,3103,3111,486,1257,1258,1265,2051,3036,3043,3049,3077,3085,3092,3109,3196,3251,3286,3074,106,875,876,1239,3082,3089,300,1245]),
  ([441,8135,8073,8033,2636,4880,1184,1178], [106,875,876,1240,1515,3082,217,1248,1523,1524,1724,1860,1947,3095,3108,468,1733,1870,1958]),
  ([447,8033,1246], [109,872,875,883,1261,1262,1265,3082]),
  ([2637,3350,3344,8136,8138], [370,1732,1736,1739,1740,1746,1749,1750,1751,1767,1777,1778,1793,1794,1798,1872,1882,1934,1960,1970,2018,2031,2041,2042,2061,2073,3096,3097,3098,3111,3112,3113,3308]),
  ([2836,8077,1898,1892,8136,8138], [1595,1791,3092,3097,3394,381,1581,1582,1585,1766,3091,3287,1738,1533,1534,1541,3089]),
  ([2044,8056,8053,8058,8158,8077,1173,1892], [217,1247,1252,1279,1575,1576,3394,1547,3089,304,1536,1539,1540,1568,1583,1736,1872,1960,2031,3090,3097,3288,385,1790,1926,2010,2053,3111]),
  ([2046,8077], [1580,1583,1589,3097]),
  ([8058,8056,8077,1173,1892,8136,8138], [217,1247,3394,3434,3436,323,389,1798,1934,2018,2061,3112,3287,3435]),
  ([2763,8038,8158,8118,2690,4868,4076,1238,8078,8072,4070,8136,8138], [381,382,1582,1765,1766,1769,1784,1919,1920,2004,2047,2689,3096,3306,3394,1306,1309,1562,3084,1285,1286,1293,3083,3253,3111,486,2039,3028,3106,3108,3321,468,1957,1958,1961,3104]),
  ([2769,8158,8118,4142,8098,3416,4868,8138], [385,1780,1783,1784,1789,1790,1919,1920,1925,1926,2003,2004,2010,2047,2053,2054,2073,3102,3106,3111,3113,3318,3322,3416,3426,3101]),
  ([1173,8078,8072,441,8136,8138], [106,217,876,1239,1240,1247,1248,1251,1252,1280,1516,1524,1555,1556,1716,1724,1755,1756,1851,1859,1860,1891,1947,3394,3307,3434,3436,322,389,1797,1798,1933,1934,2018,2061,3103,3107,3112,3439,3097,3438,381,1581,3085,3091,3437,241,1321,3092]),
  ([441,8078,8072,8136,3354,4868,8118,1178,1904,2702,1970,8056,8036,5666,4214,2696,8158,1172,2044,8138], [106,875,876,1239,1240,1516,1575,1576,1716,1851,1859,3394,1547,1548,1267,3082,3252,3085,241,1321,3092,3287,3089,301,1527,1528,1555,3090,3096,3288,3306,3111,486,2039,3028,3106,3108,3321,468,1957,1958,1961,3104]),
  ([1383,440,8136,452,1904,8056,8016,2044,8138], [240,241,955,1321,1322,1576,1598,1798,1934,2018,2062,2077,3077,3092,3113,3196,3287,1547,1548,1268,903,3074,109,872,876,884,1239,1247,3089]),
  ([8078,8072,8136,3354,4868,8118,452,1904,1246,2702,1970,8056,8036,8016,5666,4214,2696,8158,1172,2044,8138], [1261,1262,1265,1575,1576,1848,1851,1859,3394,3441,3442,894,901,1547,3085,3252,3432,3074,3082,3196,214,1239,3077,133,958,1321,3092,3287,3089,301,1527,1528,1555,3090,3096,3288,3306,3111,486,2039,3028,3106,3108,3321,468,1957,1958,1961,3104]),
  ([2835,8136,452,1246,8036,8016,1172,1318,8138], [388,1261,1262,1265,1798,1934,2018,2062,2077,3035,3042,3077,3085,3113,3196,3252,3432,894,901,3074,3082,213,873]),
  ([2044,8033,441,8078,8136,1172,8138], [106,875,876,1239,1240,1515,1516,1576,1715,3394,1548,1267,3082,220,1244,1247,1248,1252,1260,1264,1280,1292,1308,1523,1524,1535,1556,1583,1723,1724,1755,1756,1860,1891,1947,3433,3095,3307,3434,389,1797,1798,1933,1934,2018,2061,3097,3103,3107,3112,3439]),
  ([1179,8053,8073,441], [106,220,876,1239,1240,1244,1247,1248,1259,1260,1515,1523,1535,3089,3095,369,1543]),
  ([8033,441,8078,8136,1172,8138], [106,875,876,1239,3394,3445,321,323,1579,1580,1583,1589,1593,3091,3092,3097,3287,3307,3446,3082,223,1256,1259,1260,1269,1519,3089]),
  ([1905,8073,441,8136,8138], [106,304,876,1240,1515,1516,1520,1523,1524,1535,1715,1723,3095,3433]),
  ([1911,8073,2618], [307,1532,1535,1536,1545,1719,3095]),
  ([2772,8094,5666,3488], [1789,1790,1794,1797,1798,1926,1934,2010,2018,2053,2054,2061,2073,3102,3103,3111,3112,3113,3318]),
  ([2628,8093,8136,5739], [489,1712,1715,1716,1723,1724,1728,1756,1851,1859,1860,1891,1947,2067,2068,2993,2995,2040,2052,1967,1968,2007,1879,3100,412,1871,1872,1876,1899,1904,1919,1959,1960,2031,3104,3105,3106,3108,3111,3319]),
  ([3360,4878,8156,5739], [489,1856,1859,1860,1864,1871,1872,1876,1891,1899,1904,1919,1920,1935,1947,1959,2003,2068,2993,2995,3105,3108,2040,2051,2052,3109,1967,2007,3104,3106,3319]),
  ([441,8093,3356,8136,5739], [106,489,490,876,1239,1240,1515,2059,2060,2077,3057,3098,3110,3113,3451,364,365,1521,1729,1730,1741,2016,3095,3307,3434,1796,1932]),
  ([8096,8116,3361,8136,5739], [412,413,489,490,1877,2059,2060,2068,2077,3039,3046,3052,3061,3064,3077,3085,3092,3103,3107,3110,3113,3314,3317,3321,3348,3350,3453,365,1522,2016,2040,2052,1246,1932,1967,2008,3400,397,398,882,889,890,901,1796,1924,3074,3196,1596,1788,1587,1588,1311,1312,947,3076,127,943,944,1307,3084,3091,3249,3284,3403]),
  ([3489,3358,8136,5739], [426,489,490,1733,1734,1741,1781,1782,1785,2059,2077,2690,2695,3046,3052,3057,3085,3092,3097,3098,3110,3113,3307,1533,1534,1541,1582,1585,3091,3287,3336,1257,1258,1265,1306,1309,3084,3095,3252,363,1521,2422,3082,3089,297,1237]),
  ([3361,8136,5739], [412,413,489,490,1734,1877,2059,2060,2068,2077,3039,3061,3077,3103,3110,3113,3455,1534,2016,2052,1258,1932,2007,2008,893,894,901,1796,1923,3102,3317,3348,3453,3454,1596,3074,3106,3196,1320,2685,3076,951,956]),
  ([3360,5739], [489,1872,1960,2031,2067,3111,3452]),
  ([2626,5739], [489,490,1685,1686,1689,2068,2077,3039,3046,3052,3057,3064,3077,3085,3092,3098,3107,3113,3457,413,1481,1482,1489,1490,1501,1830,1838,2051,2052,3456,1205,1206,1213,1214,1225,2007,2008,3109,474,841,842,849,850,861,1924,2001,2686,2692,2697,2701,3106,1787,1788,3097,3304,1587,1588,3091,3284,3399,1311,1312,3084,3249,3360,947,3076,3081,3193,198,822,825,3073]),
  ([1095,2558,5739], [198,489,490,821,822,825,826,837,838,849,850,861,2060,2068,2077,3039,3064,3073,3077,3107,3113,3457,2016,2051,2052,3456,1932,2007,3109,474,1796,2001,2686,3106,3193,1596,3076,951,956,1320]),
  ([2558,5739], [489,490,2059,2068,2077,3039,3046,3052,3057,3064,3077,3085,3092,3098,3107,3110,3113,3457,3458,3459,363,365,413,1711,1712,1716,1724,1733,1734,1741,1830,1838,1851,1859,2040,2051,2052,3095,3456,1693,1694,1967,2007,2008,3109,474,1493,1494,1501,1924,2001,2651,2686,2692,2697,3104,3106,3301,1217,1218,1225,1788,853,854,861,1587,1588,3091,3284,3398,1311,1312,3084,3249,3360,947,3076,3081,3193,201,829,830,837,3073]),
  ([5739], [489,2059,2068,3061,3064,3103,3107,3110,3457,3458,3460,352,365,412,413,1668,1671,1672,1676,1683,1684,1715,1723,1799,1811,1823,1829,1830,1837,1877,2040,2051,3099,3100,3311,3456,1967,3104,3109,474,1953,1986,2002]),
  ([8159], [3112,3461]),
  ([3297,2559], [352,403,1668,1676,1684,1688,1715,1723,1728,1755,1824,1828,1831,1832,1836,1841,1842,1846,1875,1876,1885,1886,1903,1904,1913,1914,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3100,3101,3102,3108,3109,3111,3315]),
  ([5013,524,590,1316,2042,2768,3291,968,8010,1034,1827,1028,962,896,986,920,1052,980,914,1046,908,1040,4142,974], [400,480,481,1832,1876,1899,1903,1904,1919,2015,2056,2061,2062,2077,2221,3038,3045,3051,3056,3060,3077,3085,3092,3098,3103,3107,3112,3113,2007,2008,2036,3106,3193,1923,1991,3076,3102,3105,3192,126,127,925,943,944,1307,1308,1583,3075,3084,3091,3097,3218,3233,3243,3080,180,1057,2104,3079,3324,159,965,3078]),
  ([5673,8114,8118,8138,4874,4082,2559], [352,486,487,1668,1672,1684,1811,1823,1824,1947,2039,2040,2069,3108,3112,3320,1967,3104]),
  ([8076,8078,8136,8156,8138,2636,2702,2559], [352,1668,1675,1687,3394,3462,3307,3308,3344,367,3095]),
  ([3561,8136,8156,8114,8118,8138,524,2636,2702,2768,8010,2559], [352,432,433,1668,1672,1675,1684,1687,1688,1727,1795,1811,1823,1824,1934,1947,2018,2061,3036,3043,3077,3085,3098,3112,3192,3351,3466,3097,3438,2567,3095]),
  ([8114,8118,8138,8094,5666,4940,4874,4214,4082,3488,8010,2559], [352,1684,1824,1947,3394,3450,3462,3465,385,386,1775,1776,3111,3322,3396,1747,3106,3108,459,460,1923,2009,2966,3102,3109,3318,3467,3103]),
  ([8118,8138,8094,5666,4940,4874,4214,4148,4082,3488,8010,2559], [352,1668,1672,1684,1688,1728,1756,1811,1823,1891,3394,3468,3105,453,454,1963,1997,1998,2009,3104,3106,3109,3321]),
  ([3291,968,8010,1034,1827,1028,962,896,2559], [285,286,352,400,1422,1476,1516,1684,1688,1715,1723,1728,1755,1756,1824,1831,1832,1835,1836,1875,1876,1891,1899,1903,1904,1919,1920,1947,1959,1960,2003,2031,2360,2578,3394,3416,3462,1142,1149,1150,1162,1173,1354,3101,3450,385,386,1006,1009,1010,1021,1022,1033,1078,1086,1097,1098,1109,1587,1588,1776,1311,1312,1572,947,1296,931,3464,3110,3469,3107,462,1931,2012,3103,1923,1996,3102,3318,1964,3111,486,1879,2039,3100,3108,3316]),
  ([8094,8096,8116,8114,4874,4287,4940,5666,8138,8090,4868,2618,2628,2690,2624], [462,463,1712,1715,1723,1931,2012,2018,2061,2062,2077,3055,3098,3103,3112,3113,3312,1924,1996,3111,486,1787,1964,2039,2051,2985,3108,3109,3316,3433,1879,3100,411,1733,3095,3306,3307,3096,3097,381,1765]),
  ([8096,8116,8114,4874,4287,4940,3428,5666,8138,8090,4868,3416,2618,2628,2690,2624], [462,463,1712,1715,1723,1931,2018,2061,2062,2077,3055,3098,3103,3112,3113,3471,3101,3357,367,368,420,1741,1761,1762,1769,1873,1874,1877,3095,3096,3100,3306,3317,3108,3109,477,2035]),
  ([4086,4287,4940,5666,8138,8090,4868,3416,2618,2628,4142,2690,2624], [462,463,1712,1715,1723,1931,1955,1956,1959,1987,2011,2012,2018,2061,2062,2077,2923,3055,3098,3103,3105,3106,3112,3113,3416,3472,1923,3102,426,1781,1782,1785,1901,1902,2595,3097,3101,1761,1762,1769,1874,1877,3096,3100,3308,3316,3108,3111,486,2039]),
  ([3489,4874,8072,8092,2768,8098,8078,4940,3428,8138,3288], [426,1781,1820,1824,1863,1901,1947,3097,3101,3394,3462,3307,3316,3108,3109,477,2035]),
  ([8134,8072,8092,2702,8098,8078,3428,8138,2559], [352,1688,1727,1728,1755,3462,3306,3316,3096,3101,420,1761]),
  ([4874,8135,8072,8092,2768,3494,8098,8078,4940,3428,8138,3288], [1824,1947,3108,3394,3474,472,2037,3102,3109,3317]),
  ([8096,8094,8092,8098,4940,5666,8138], [3394,3462,3317,3318,3109,3111,486,2051]),
  ([4287,4940,5666,8138,8090,2559], [352,462,463,1668,1675,1676,1684,1687,1688,1715,1723,1727,1728,1755,1756,1824,1891,1931,1947,2012,2018,2061,2062,2077,3055,3098,3103,3112,3113,3416,3473,443,1869,1870,1877,1923,1924,1996,3100,1733,1734,1741,1787,1908,3095,1771,3475,3476,2673,2676,3096,3101,3477,3102,426,1781,3097,3307,3308,3109,3111,486,2051]),
  ([4947,8135,8113,2559], [352,477,1668,1672,1684,1811,1823,1824,1947,2035,2956,3104,3108,468,1957]),
  ([3489,8113,8092,2768,8098,4940,3428,8138,1892,2559], [352,426,1668,1675,1687,1688,1728,1755,1781,1782,1901,1902,2684,2690,2695,3097,3101,3394,3462,1582,1585,1762,1874,3091,3316,3479,1306,1309,1310,1562,1733,1734,1741,3084,3095,3109,3307,942,945,1286,1533,1534,1541,3076,3098,387,1258,1595,3092,3287,893,3089,3444,300,1245]),
  ([1971,8115,8135,2559], [313,352,1552,1556,1564,1684,1756,1764,1824,1891,1899,1900,1947,1983,3105,3108,471,1991]),
  ([2835,1970,1250,8056,8116,1976,8156,1316,590,8118,8010], [387,388,1595,1798,1934,2018,2061,2062,2077,3035,3042,3077,3085,3092,3112,3113,3193,3288,3076,3090,127,309,943,1277,1278,1281,3083,3084,3253]),
  ([8136,3488,8092,8098,8118,5666,8138,8010,1892,2559], [352,1668,1672,1675,1676,1684,1687,1688,1715,1723,1724,1727,1728,1755,1756,1811,1823,1824,1891,1947,3394,3433,3462,3317,3439,3102,429,430,1788,1912,1916,1919,1925,1926,2010,2053,3000,3007,3013,3106,3111,3322,3323,3427,3481,1588,1771,1772,3091,1571,1572,1295,3482,3098,3466,3097,381,1765,1766,2567,2683,2689,3076,3084,3095,3193,1562,1738,3077,133,957,958,1286,1321,1533,3085,3092,3287,3435,3438,3443,112,880,888,915]),
  ([8092,8098,4940,5666,8138,8090,8010,1892,2559], [352,1668,1672,1684,1688,1728,1755,1756,1811,1823,1824,1891,1947,3394,3416,3462,3478,3107,3311,3439,3480,3483,3109,477,2007,2956,3024,3102,3104,3314,442,1956,1987,3106]),
  ([4214,8117,8093,8118,4940,5666,8138,8010,2559], [352,1668,1676,1688,1715,1723,1728,1755,1756,1891,3106,3416,459,1995,1996,1964,1879,3100,412,1871,1872,1875,1876,1899,1903,1959,3101,3105,3468]),
  ([4215,8098,8118,3428,8090,3416,4142], [456,1985,1986,1989,3105,3462,1897,3101,3313]),
  ([4155,8116,8093,8118,4940,8138,3288], [454,1824,1947,1980,1983,1984,1993,1994,1998,2009,2014,2018,2031,2041,2042,2061,2073,3108,3109,3111,3112,3113,3323]),
  ([8114,8116,8098,8118,3428,5666,8090,3416], [3394,3462,3313,3314,3322,3101,3111,421,1903,3025,3102]),
  ([8098,4940,5666,8138,8090,8010,1892,2559], [352,1668,1676,1684,1688,1715,1723,1728,1755,1756,1891,3416,3478,3484,3107,3486,3485,3487,3488,3105,450,1954,1869,1870,1877,3100]),
  ([4149,8076,8116,2702,8078,8118,4940,5666,8138,2559], [352,450,1668,1672,1684,1688,1727,1811,1823,1953,1954,1961,2672,3096,3104,3394,3462,3308,3321,3109,3111,486,2051]),
  ([4150,4082,4148,8096,8116,8118,4940,5666,8138,8090,3416,4070,4142,4076], [1897,1898,1905,1954,1961,1989,3101,3104,3105,3312,3394,3111,3321,486,2051,3109]),
  ([8095,8076,2636,2702,8078,4940,5666,8138,2559], [352,1668,1675,1684,1687,1688,1727,1728,1755,1756,1824,1891,1947,3394,3416,3462,3101,3357,367,420,421,1761,1900,1983,3095,3096,3306,3307,3108,3109,477,2035]),
  ([4082,8094,4148,8096,4214,3488,8116,4940,5666,8138,8090,8010,2559], [352,1668,1672,1684,1688,1728,1755,1756,1811,1823,1891,3478,3107,3469,3491,468,1982]),
  ([8116,590,2636,2702,2768,8078,8018,3494,4940,5666,8138,8090,8010,2559], [352,1668,1675,1687,1688,1728,1756,1891,3394,3478,3107,3193,3076,127,944,1308,1583,1584,1783,1784,1919,3097,3102,3490,3492,3493,2644,3095,3307,3109,477,478,2036,2053,3111,3312,1991,3105]),
  ([4221,4148,3561,8118,4940,5666,8138,8010,2559], [352,432,459,460,1668,1676,1688,1715,1723,1728,1756,1796,1891,1995,1996,2009,2010,2053,3019,3105,3109,3111,3433,1596,1908,1320,1771,3467,935,952,956]),
  ([4215,2636,2702,2768,8078,4940,5666,8138,2559], [352,456,1668,1675,1687,1688,1727,1986,2700,3097,3394,3462,1898,1954,1761,1870,3096,3308,1733,3095,3111,3307,486,2051,3109]),
  ([4940,5666,8138,8090,8010,1892,2559], [352,1688,1727,3394,3462,3478,3489,3103,3107,432,1795,1796,1927,1928,3036,3049,3077,3092,3098,1787,1788,1912,1587,1588,1771,1772,1884,1312,1571,1743,3496,947,3494,3106,3425,3495,460,2009,2010,2053,2668,2672,3091,3096,3109,3111,3288,3308,3434,301,1527,3090]),
  ([5666,8138,8090,8010,1892,2559], [352,1668,1672,1676,1684,1688,1715,1723,1728,1755,1756,1811,1823,1824,1891,1947,3416,3497,474,2025,2026,2033,2649,2651,3108,1958,1961,1981,1982,1989,3104,3105,1870,1877,1897,3100,3101,3309]),
  ([5667,8090,4868,3416,4070,2628,4142,4076], [483,1712,1715,1723,2029,2030,2033,2679,3108,3409,1957,1958,1961,1982,1989,3104,3105,3309,1869,1870,1877,3100]),
  ([2559,1106,8031,8051], [351,352,1481,1482,1489,1490,1501,1668,1671,1672,1683,1684,1688,1728,1755,1756,1799,1811,1823,1824,1891,1947,2396,3394,3399,3463,1206,1213,1214,1225,3081,198,199,821,822,825,826,838,849,850,861,1133,1134,1137,1187,2140,2142,3073,3088,286,1070,1073,1475,3470,3099,3499,3416,3498,3110,480,2015,2016,2056,3038,3060,3077,3103,3107,3486,1932,2007,2008,3106,3193,3314,1796,1923,3102,1596,2684,3076,951,956,1320]),
  ([8116,8090,8010,5013], [480,481,2015,2016,2056,2062,2077,3038,3060,3077,3103,3107,3113,3193,3314,1932,2008,1796,1923,3102,1596,2684,3076,951,956,1320]),
  ([4142,8090,8010,5013], [480,481,2015,2056,2061,2062,2077,3038,3056,3060,3077,3098,3103,3107,3112,3113,3501,2007,3106,456,457,1918,1985,1986,1989,2004,2047,2700,3105,3192,3416,3486,417,1753,1754,1755,1757,1758,1769,1782,1785,2439,3096,3097,3308,1556,3111,1280,2967,3075,121,912,916]),
  ([8090,8010,5013,2564,1106,8071,8031,8051], [480,2056,3500,3501,3502,447,1942,2007,2408,3106,1822,2609,2614,1682,1690,1701,1482,1490,1501,3399,1206,1214,1225,3081,199,1187,1188,1463,3094,3364]),
  ([4143,8091,2110,8031,8051], [447,1942,2413,3403,1822]),
  ([3284,3290,8091,3272,3296,2110,8031,8051], [3099,3403,398,1803]),
  ([3285,3298,2564,1106,8071,8031,8051], [396,1681,1682,1690,1701,2406,1482,1489,1490,1501,3399,1206,1213,1214,1225,3081,199,1187,1188,1463,3094,3364]),
  ([1101,2570,2564,2558,8071], [202,1184,1188,1196,1463,1471,3094]),
  ([1113,1844,8051], [208,1204,1207,1208,1213,1219,1467,3088,282,1186,1190,1202]),
  ([5013,2564,1106,8071,8031,8051], [480,2016,2056,3500,1932,2036,1796,1968,1596,1843,1844,3506,1703,1704,3330,3507,1503,1504,3508,1227,3081,3360,3397,3505,198,822,825,826,837,838,849,850,861,3073,3503]),
  ([1842,2546,8138,2564,2558,8071], [1480,1484,1488,1496,1500,1512,1515,1523,1528,1535,1540,1555,1563,1568,1583,1584,1667,1684,1696,1784,1824,1836,1920,1947,1959,1960,2003,2031,3094,358,1706,1709,1710,1749,1750,1777,1778,1790,1846,1926,1969,1970,2009,2041,3095,3096,3097,3108,3109,3111,3305]),
  ([2575,2564,1106,8071,8031,8051], [358,359,1503,1504,3500,3507,3508,3509,1227,3081,3110,199,1187,1188,1463,3094,3364,3510,292]),
  ([2574], [1692,1696,1700,1706,1710,1720,1727,1739,1740,1749,1750,1767,1777,1778,1793,1794,1798,1836,1846,1934,1960,1970,2018,2031,2041,2042,2061,2073,3096,3097,3098,3111,3112,3113,3308]),
  ([2571], [358,1692,1696,1700,1706,1710,1720,1727,1739,1740,1749,1750,1767,1777,1778,1793,1794,1798,1836,1846,1934,1960,1970,2018,2031,2041,2042,2061,2073,3096,3097,3098,3111,3112,3113,3308]),
  ([1845], [295,1492,1496,1500,1506,1510,1520,1527,1539,1540,1549,1550,1567,1577,1578,1593,1594,1598,1696,1706,1798,1836,1846,1934,1960,1970,2018,2031,2041,2042,2061,2073,3090,3091,3092,3111,3112,3113,3288]),
  ([2505], [343,1640,1644,1648,1654,1658,1680,1684,1687,1688,1699,1700,1709,1710,1711,1727,1739,1740,1749,1750,1767,1768,1777,1778,1784,1790,1824,1836,1846,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3095,3096,3097,3108,3109,3111,3305]),
  ([1119], [211,1216,1220,1224,1230,1234,1244,1251,1263,1264,1273,1274,1291,1301,1302,1317,1318,1322,1496,1506,1598,1696,1706,1798,1836,1846,1934,1960,1970,2018,2031,2041,2042,2061,2073,3083,3084,3085,3111,3112,3113,3253]),
  ([1779], [280,1440,1444,1448,1454,1458,1480,1487,1488,1499,1500,1509,1510,1511,1527,1539,1540,1549,1550,1567,1568,1577,1578,1584,1590,1628,1636,1648,1658,1784,1790,1824,1836,1846,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3089,3090,3091,3108,3109,3111,3285]),
  ([393], [103,852,856,860,866,870,880,887,899,900,909,910,927,937,938,953,954,958,1220,1230,1322,1496,1506,1598,1696,1706,1798,1836,1846,1934,1960,1970,2018,2031,2041,2042,2061,2073,3075,3076,3077,3111,3112,3113,3197]),
  ([1053], [196,1164,1168,1172,1178,1182,1204,1211,1212,1223,1224,1233,1234,1235,1251,1263,1264,1273,1274,1291,1292,1301,1302,1308,1314,1428,1432,1444,1454,1584,1590,1636,1648,1658,1784,1790,1824,1836,1846,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3082,3083,3084,3108,3109,3111,3250]),
  ([327], [88,800,804,808,814,818,840,847,848,859,860,869,870,871,887,899,900,909,910,927,928,937,938,944,950,1152,1156,1168,1178,1308,1314,1432,1444,1454,1584,1590,1636,1648,1658,1784,1790,1824,1836,1846,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3074,3075,3076,3108,3109,3111,3194]),
  ([195], [49,660,664,668,674,678,724,728,732,744,754,776,783,784,795,796,807,808,817,818,819,835,847,848,859,860,869,870,887,888,899,900,909,910,916,924,934,1012,1020,1032,1042,1076,1080,1280,1288,1298,1360,1372,1384,1394,1556,1564,1574,1624,1636,1648,1658,1756,1764,1774,1811,1823,1824,1835,1836,1845,1846,1891,1899,1909,1947,1959,1969,3073,3074,3075,3104,3105,3108,3188]),
  ([261], [70,736,740,744,750,754,788,796,808,818,828,835,847,848,859,860,869,870,887,899,900,909,910,927,928,937,938,944,950,1088,1092,1104,1114,1308,1314,1372,1384,1394,1584,1590,1636,1648,1658,1784,1790,1824,1836,1846,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3074,3075,3076,3108,3109,3111,3194]),
  ([3300,8138,2568], [1680,1684,1688,1696,1700,1712,1715,1723,1728,1735,1740,1755,1763,1768,1783,1784,1824,1836,1841,1842,1846,1885,1886,1913,1914,1920,1926,1947,1959,1960,1969,1970,2003,2009,2031,2041,3100,3101,3102,3108,3109,3111,3315]),
  ([3366,8138,2565], [355,1680,1688,1696,1700,1728,1740,1755,1763,1768,1783,1836,1882,1885,1886,1913,1914,1929,1930,1934,1960,1970,2018,2031,2041,2042,2061,2073,3101,3102,3103,3111,3112,3113,3318]),
  ([8134,8138,2565], [355,1680,1687,1688,1696,1699,1700,1711,1712,1715,1723,1727,1728,1735,1739,1740,1755,1756,1763,1768,1783,1836,1891,1960,2031,3416,3462,3524,415,416,1743,3095,3100,3101,3316,3450,386,1775,3096,3103,3306,432,1795,3098]),
  ([8138,2565], [355,1680,1683,1684,1687,1688,1695,1696,1699,1700,1711,1712,1715,1723,1727,1728,1735,1740,1755,1756,1763,1767,1768,1783,1784,1803,1804,1811,1823,1824,1835,1836,1891,1920,1947,1959,1960,2003,2031,3394,3416,3523,3524,3525,403,415,416,1743,1799,3095,3099,3100,3101,3108,3450,3473,385,471,472,1967,2037,3097,3104,3107,3109,3307,3311,3098,3103,432,1795]),
  ([2565], [355,1680,1683,1684,1688,1695,1696,1700,1712,1715,1723,1728,1735,1740,1755,1756,1763,1764,1803,1804,1811,1823,1824,1835,1836,1891,1899,1947,1959,1960,2031,3416,3526,1799,3101,3110,480,2056,2954,2957,2959,3100,3104,3108,2036,1968,1991,3105,3309,1843,3099]),
  ([8071,8031,8051], [3512,3513,3527,3511,205,1192,1196,1208,1460,1463,1471,1483,3094]),
  ([5013,8072,8076,4940,4070,4214,4082,4076,8070], [480,2055,2056,2957,3104,3109,3300,2007,3106]),
  ([8058,8138,8052,8054,8056,5666,4940], [3394,3462,3287,3288,3109,3111,486,2051]),
  ([1107,8070,8051], [205,1192,1195,1196,1200,1207,1208,1212,1239,1240,1247,1248,1252,1279,1280,1459,1460,1464,1472,1484,1515,1523,1524,1555,1556,1663,1671,1672,1683,1684,1755,1756,1811,1823,1824,1891,1947,3462,3514,3088,292,1496,1499,1500,1535,1539,1540,1563,1564,1567,1568,1583,1584,1695,1696,1763,1764,1783,1784,1835,1836,1899,1919,1920,1960,2003,2031,3416,3101,3450,385,386,1587,1775,1776,3091,3096,3097,1571,1747,1748,3090,3095,3529,1543,3089,3110,3523,3530,403,3092,3099,3473,325,1597,3098,3107,3301,3303,3104,3105,453,1963]),
  ([4071,8031,8051], [435,1810,2267,2270,3514,3516,3528,3531,1670,3508,1470,1477,1478,1489,3081,3088,282,1185]),
  ([8116,8090,2109,4947,8070], [325,478,1597,1598,1797,1798,1933,2054,2073,3020,3024,3098,3103,3107,3113,3304,3314,3097,3102,426,1781]),
  ([4215,2109,4947], [325,456,457,478,1597,1598,1797,1798,1917,1918,1921,1934,1986,2004,2018,2047,2053,2054,2061,2073,2700,3020,3097,3098,3102,3103,3111,3112,3113,3308,3318,1897,1898,1905,3101,417,1753,1754,1757,1758,1769,3096]),
  ([2109,4947,8031,8051], [324,325,477,478,1319,1592,1597,1598,1798,1933,1934,2007,2018,2036,2044,2047,2053,2054,2061,2073,3002,3009,3020,3034,3077,3085,3098,3107,3111,3112,3113,3528,3534,1576,1991,3106,3304,3322,3533,1295,1296,3097,3504,931,2683,2689,3076,3084,3105,3197,3253,3351,2663,3083]),
  ([585,8116,8034,4947,8070], [127,478,943,944,1308,1583,1584,1784,1920,2004,2047,2053,2054,2058,2061,2073,3009,3020,3084,3097,3111,3112,3113,3253,3085,241,1322,1597,1598,1798,1933,3098,3107,3304]),
  ([8116,8010,8014,8034,4142,3416,4868,4947,4940,8138,8070], [478,2044,2047,2053,2054,2058,2061,2073,3002,3009,3020,3111,3112,3113,3536,3076,3197,3077,133,957,958,1322,1597,1598,1798,1933,3085,3098,3107,3253,3304,3084,3097,381,1305,1582]),
  ([1965,4868,4947,4940,8138,8031,8051], [309,310,477,478,1277,1278,1281,1282,1293,1526,1556,1755,1756,1891,2007,2044,2047,2053,2054,2058,2061,2073,2350,2437,3002,3009,3083,3111,3112,3113,3514,3516,3518,3528,3531,914,917,918,929,1486,1489,3075,3399,3508,3081,198,821,822,825,826,837,838,849,3073,3537,3106,2685,2691,3076,3084,3197,3253,3077,3085,240,955]),
  ([1964,8055,1976,2702,8156,3428,3494,2768], [3090,3394,3415,3462,313,1552,1555,1556,1563,1568,1583,1584,1755,1783,3096,3097,3101,3102,3308,3318,3098,3103,432,1795]),
  ([4947,4940,8138,8031,8051], [477,478,2036,2044,2047,2053,2054,2058,2061,2073,3015,3020,3024,3111,3112,3113,3427,3535,1992,3091,3092,3288,1907,1908,1771,1772,1571,3539,310,1556,1756,1892,1975,3538]),
  ([2043,8070], [322,1580,1583,1584,1589,1590,1594,1597,1598,1784,1790,1798,1919,1925,1926,1933,2010,2054,2073,3097,3098,3106,3107,3113,3304]),
  ([1965,8156,8136,8138,8031,8051], [309,1277,1278,1281,1282,1293,1525,1526,1529,1530,1541,2350,2437,3083,3394,3462,3514,3516,3528,3531,3541,914,917,918,929,1486,1489,3075,3399,3427,3508,3081,3091,199,1187,3088,286,1475,3089,3287,3092,324,1319,1592,3034,3077,3085,3197,3253,1311,3084,234,941,942,945,3076]),
  ([1311,2109,8156,8136,8138,8070], [234,235,325,941,942,945,1290,1308,1583,1584,1597,1598,1783,1784,1797,1798,1919,1920,1933,1934,2004,2018,2047,2061,2062,2077,3034,3076,3077,3098,3103,3107,3112,3113,3196,3197,921,922,929,3075,117,118,885,886,889,890,901,916,1280,1556,1755,1756,1891,1892,1975,3074,3416,3439,3097,3304,3307,3106,459,1923,1996,3102,3317,3318,1964,3101,3347,420,1873]),
  ([513,8035,1250,8118,8078,8135,8070], [118,915,916,1280,1556,1756,1891,1892,1975,3083,3462,229,1288,1564,1764,1899,1900,1983,3108,3395,471,1991,3105]),
  ([1245,4142,4868,2109,8135,8070], [229,325,1288,1564,1598,1764,1798,1899,1900,1933,1934,1983,2018,2061,3107,3108,3112,3395,471,1991,3105]),
  ([4142,4868,8035,8033,2109,8135,8156,4940,8138,1106,8070,8031,1112], [324,325,1592,1597,1598,1797,1798,1933,1934,2018,2061,2062,2077,3034,3077,3098,3103,3107,3112,3113,3516,3518,3545,1312,1576,947,1295,3083,3361,3414,3416,3544,225,226,914,917,918,929,1249,1250,1253,1254,1265,1280,1556,1755,3075,3082,3197,3439,213,1197,3076,3081,127,198,821,822,826,837,838,849,944,1308,1583,1584,1783,1784,1919,3073,3097,3192,3304,3419,3101,3106,3318,459,1923,3102]),
  ([4143,8035,1250], [1891,2445,3083,229,1276,1280,1556,1756]),
  ([2109,8156,8136,4940,8138,1106,8070,8031,1112], [324,325,1319,1592,1597,1598,1798,1933,1934,2018,2061,2062,2077,3085,3098,3107,3112,3113,3323,3543,1311,1576,3084,3252,3253,1295,3547,3546,465,1974,1977,1978,1989,2446,3083,3105,3401]),
  ([1966,8055,1964], [1557,1558,1569,3090]),
  ([1977,4868,8135], [316,1560,1564,1574,1764,1774,1900,1910,1983,1993,3108]),
  ([8156,4940,8138,8031,8051], [3394,3462,3514,3528,3531,3540,3541,3109,3323,3427,3508,3542,3548,3091,3092,3288,3415,3549,311,1555,1556,1755,1756,1891,1892,1975,3550,3090,313,1563,1564,1568,1583,1584,1764,1783,1784,1899,1900,1919,1983,1984,2031,3108,3416,471,1991,2984,3096,3101,3105,3450,385,3097,3302,3539,430,1925,3106]),
  ([4881,8157], [472,2024,2031,2041,3111]),
  ([2835,8096,8116,8114,8094,4875,8136,8138,8031,8051], [387,388,468,1596,1797,1798,1933,1934,1957,1958,1961,2018,2061,2062,2077,2648,3103,3107,3112,3113,3313,3317,3321,3334,3403,398,1804,1807,1819,1870,1877,3100]),
  ([8096,8116,8076,1968,2618,4875,4940,8138,8031,8051], [468,469,1555,1556,1755,1756,1891,1958,1981,1982,1989,2031,2645,2648,2673,2676,3105,3394,3416,3462,3528,3540,1870,1877,1898,3101,3109,3553,1734,1741,1762,1769,3096,3098,3303,3307,3095,3107,3337,3477,462,1931,3103]),
  ([8078,8016,8076,8114,8074,8053,4875,8136,8138,8070], [468,1958,2630,2641,2645,3394,3462,1870,3303,3307,1734,1741,3107,1534,1541,3037,3077,3196,3336,1258,3095,363,894,901,1521,2417,3074,3089,297,873,1238]),
  ([8116,8076,1968,8053,4875,4940,8138,8031,8051], [468,469,1555,1556,1755,1756,1891,1957,1958,1961,1981,1982,1989,2031,2641,2673,2676,3105,3394,3416,3462,3528,3540,3551,1833,1834,1837,1870,1898,3101,3109,3111,1734,1762,1769,3003,3025,3096,1534,1541,3336,3554,3102,2684,3076,3555,3098,387,388,1596,1797,1798,1933,3103,3107,3313,3321,3334,3403,3505,398,1799,1804]),
  ([1173,8053,4875], [217,1236,1239,1247,1959,2641,3089,307,1532,1536,1736,1872]),
  ([1311,1968,8053,4875,4940,8138,8031,8051], [235,469,1308,1556,1583,1584,1755,1756,1783,1784,1891,1919,2031,2676,3416,3551,3101,3111,3450,385,3028,3097,3106,3556]),
  ([8016,8036,8114,8074,1172,1318,458,1246,452,8136,8138,8070], [3394,3444,3462,3098,3303,3107,3037,3044,3077,3085,3196,3252,3432,3447,3074]),
  ([1968,8053,4875,4940,8138,8031,8051], [468,469,1555,1556,1756,1891,1958,1981,1982,1989,2031,2630,2641,2673,3105,3528,3540,3551,3557,3558,1870,1898,3109,3111,486,1734,1762,1769,2052,3003,3010,3021,3025,3028,3084,3096,1534,1541,1562,2008,3336,1258,1286,1924,894,901,1788,1588,1312,3559,3076,127,944,1308,1583,1584,1783,1784,1919,3097,3102,3106,3554]),
  ([8053,4875,4940,8138,8031,8051], [2641,3514,3516,3528,3531,3560,311,1525,1526,1530,1541,3089,3508,297,1473,1474,1477,1478,1489,3088,3399,282,1185,3081]),
  ([1240,8116,8076,8036,8016,1318,458,1246,452,8136,8138,8070], [1249,1250,3394,3444,881,3098,3304,3107,3037,3044,3077,3085,3196,3252,3447,3074]),
  ([2037,4875,4940,8138,8031,8051], [318,319,468,469,1305,1306,1309,1310,1566,1583,1584,1783,1784,1919,1981,1982,1989,2031,2630,2673,2682,3084,3462,3528,3540,3551,942,945,1286,1538,1898,3076,3109,3111,3425,1258,1762,1769,3021,3025,3097,3102,3106,894,901,3562,227,1280,1555,1556,1756,1891,3096,3105,3554,3559,217,1236,1240,1515]),
  ([441,8033,8078,1184,2636,1178,8135,4880,8136,8138], [106,875,3082,3431,3440]),
  ([585,8118,8078,4220,2768,8070], [127,944,1308,1583,1584,1784,1919,3097,3106,3304,3394]),
  ([8033,8013,8078,458,1184,1246,2636,1178,452,8135,4880,8136,8138], [3432,3564,3074]),
  ([8135,4868,4940,8138,8031,8051], [3394,3528,3540,3541,3551,3552,3108,3109,3561,3563,468,469,1958,1982,2031,2630,2636,3091,3111,3287,1870,1898,3003,3010,3021,3028,3092,324,325,1319,1597,1598,1734,1741,1762,1798,1933,3034,3077,3085,3098,3107,3565,1534,1562,3076,3196,1258,1265,1286,894,901,3566,3252,3084,235,1308,1583,1584,1784,1919,3097,3106,3304]),
  ([1311,8118,4220,2768,8078,8070], [235,1308,1583,1584,1784,1919,3097,3106,3304,3394]),
  ([441,1178,8038,5673,8118,8036,8078,8136,8138,8070], [106,487,876,1240,1515,1516,1715,2069,2073,2985,2992,3112,3113,3252,3447,217,1248,1252,1280,1523,1524,1555,1556,1723,1756,1891,3433,3440,3095,367,1739,1740,1764,1899,3096,3105,3303]),
  ([1178,8038,8013,452,5673,8118,8036,8078,8136,8138,8070], [486,487,2040,2073,3113,3252,3569,1968,1880,1744,1544,1267,1268,903,3074,109,872,875,883,3082]),
  ([1179,5673,8078,8134,8138], [220,486,487,1244,1248,1252,1260,1264,1280,1288,1292,1308,1512,1515,1516,1523,1524,1535,1555,1563,1584,1715,1723,1784,1920,2003,2051,2069,2985,3096,3109,3112,3306,3433,3095]),
  ([8038,8013,452,4874,5673,8118,8036,8078,4880,8136,8138,8070], [3570,3571,220,1244,1248,1524,1724,1860,1947,3108]),
  ([152,158,188,8005,164,170,176,182], [3070,3521]),
  ([224,230,254,8007,236,242,248], [3071,3522]),
  ([296,302,308,320,314,8009], [3072,3520]),
  ([8011,368,374,380,386], [3073,3518]),
  ([1022,1028,1040,1046,8029,1034], [3080,3519]),
  ([1094,1100,8031,1112,1106], [3081,3516]),
  ([1754,1748,1772,8049,1766,1760], [3087,3517]),
  ([1826,1820,1838,1832,8051], [3088,3514]),
  ([2480,2486,2498,8069,2474,2492], [3093,3515]),
  ([2552,2546,8071,2558], [3513,3527,3094]),
  ([8004,8056,8018,8058,8016], [3162,3394]),
  ([8006,8076,8016,8078,8018], [3177,3394]),
  ([8008,8096,8098,8016,8018], [3187,3394]),
  ([8010,8116,8118,8018,8016], [3193,3394]),
  ([8012,8014,8134,8018,8138], [3195,3462]),
  ([8012,8018,8138,8136,8016], [3196,3394]),
  ([8014,8018,8156,8016], [3394,3462,3197]),
  ([8028,8094,8034,8038,8098], [3242,3462]),
  ([8028,8096,8038,8098,8036], [3243,3394]),
  ([8030,8114,8038,8034,8118], [3248,3462]),
  ([8030,8036,8116,8118,8038], [3249,3394]),
  ([8032,8034,8134,8038,8138], [3251,3462]),
  ([8032,8038,8136,8036,8138], [3252,3394]),
  ([8036,8038,8156,8034], [3394,3462,3253]),
  ([8048,8094,8054,8098,8058], [3277,3462]),
  ([8048,8096,8056,8098,8058], [3278,3394]),
  ([8050,8054,8114,8058,8118], [3283,3462]),
  ([8050,8056,8118,8058,8116], [3284,3394]),
  ([8054,8052,8058,8134,8138], [3286,3462]),
  ([8056,8052,8138,8136,8058], [3287,3394]),
  ([8058,8054,8156,8056], [3394,3462,3288]),
  ([8068,8094,8074,8078,8098], [3297,3462]),
  ([8068,8096,8078,8098,8076], [3298,3394]),
  ([8074,8114,8070,8118,8078], [3303,3462]),
  ([8116,8076,8078,8118,8070], [3304,3394]),
  ([8072,8074,8078,8134,8138], [3306,3462]),
  ([8072,8076,8138,8136,8078], [3307,3394]),
  ([8078,8076,8156,8074], [3394,3462,3308]),
  ([8090,8094,8114,8118,8098], [3313,3462]),
  ([8090,8096,8098,8116,8118], [3314,3394]),
  ([8092,8094,8138,8098,8134], [3316,3462]),
  ([8092,8096,8136,8098,8138], [3317,3394]),
  ([8096,8098,8094,8156], [3394,3462,3318]),
  ([8112,8114,8138,8118,8134], [3320,3462]),
  ([8112,8116,8136,8118,8138], [3321,3394]),
  ([8116,8118,8114,8156], [3394,3462,3322]),
  ([8156,8134,8138,8136], [3394,3462,3323]),
  ([3273,2558,8071], [390,1662,1666,1678,1689,1690,1701,3330]),
  ([1245,8114,8031,8070,8118], [3402,3462]),
  ([2835,1965,8134,1244], [388,1798,1934,2018,2061,3112,3405]),
  ([8050,8134,1964,4214,2835,8114,8118], [388,1798,1934,2018,2061,3112,3406]),
  ([1244,8114,8091,8134,8051,8118,3284,3286,2835], [388,1798,1934,2018,2061,3112,3407]),
  ([2835,5672,8014,4941], [388,1798,1934,2018,2061,3112,3408]),
  ([3423,8115,4142,4868,8138,8156,4940], [3426,3462]),
  ([8156,2037], [3427,3462]),
  ([513,2037,8138,8118,8114,8134], [3430,3462]),
  ([2769,8098,4868,8118,4142,3416,8138], [385,1794,1798,1934,2018,2061,3112,3439]),
  ([8072,3354,1172,2702,2696,8078,8136,1904,4868,1246,452,8056,8118,8036,8016,5666,4214,1970,2044,8138], [3443,3462]),
  ([1113,8051], [3508,3514]),
  ([8156,2835,8116,4940,8118,2042,8138], [387,1595,1791,1792,2851,3035,3042,3077,3085,3092,3618,3627,1588,1776,3091,3600,3603,1311,1312,1571,1572,3551,3593,947,1296,3084,234,235,931,941,1290,1308,1584,1784,1920,2004,2047,3076,3589,921,3075,3391,118,916,1279,1280,1556,1756,1891,3090,3416,3539,313,430,1564,1764,1899,1900,1926,1983,2009,3105,3109,3619,454,1993,3108]),
  ([2835,8116,4940,5672,8118,2042,8138], [387,388,1595,1596,1792,1797,3042,3085,3092,3103,3632,1588,3111,483,1311,2030,2046,2049,2693,2698,2705,3084,3091,3109,3593,3600,3617,1957,1958,1961,2002,3334,3532,1918,1921,3102,3104,3612,438,1822,3403]),
  ([5667,8077], [2047,2702,3097,385,1780,1784,1920,2004]),
  ([4151,8135,8115], [450,452,1971,1972,1975,1983,3105,3108,471,1991]),
  ([2109,8034,8014,8156], [324,1319,1592,3034,3077,3085,3589,3596,1311,3084,234,941,942,945,3076]),
  ([3417,8054,3424,8156], [417,1753,1754,1757,1758,1769,2439,2444,3096,3627,1554,1278,1281,1282,1293,3083,914,917,918,929,3075,3636,3092,3603,3091,322,1580,1583,1589,1594,1597,3097,3098,3610]),
  ([2043,8094,8156], [322,1580,1584,1590,1783,1784,1920,2004,2047,3450]),
  ([2772,8094,8156], [1780,1783,1784,1920,2004,2047,3450]),
  ([2691,2698,8094,8156], [372,1553,1554,1557,1558,1569,2438,2443,3090,3627,3638,1278,1281,1282,1293,3083,3091,3603,914,917,918,929,3075,3092,3636]),
  ([2109,8036,8016,1244,1318,8156], [324,1299,1300,1319,3034,3077,3085,3589,3596,931,3083,3351]),
  ([3498,8094,8156], [1915,1916,1919,1920,1925,1926,1929,1930,1933,1934,2003,2004,2009,2017,2047,3103,3106,3107,3109,3110,3450,3615,3618,3619,3627,3635,3638,385,386,1588,1775,1776,1898,1954,3091,3102,3632,1311,1312,1571,1748,1761,1762,1870,3000,3098,3640,1543,1561,1562,1734,3096,3610,1285,1533,1534,3097,1258,2683,2689,3076,3084,3641,893,3092,3600,3602,3603,3090,3542,3593,309,1525,3085,3089,3442,297,873,1238]),
  ([3561,8094,8156], [432,1927,2887,3036,3043,3049,3077,3085,3092,3627,3638,3639,385,386,1588,1775,1776,3091,3603,1311,1312,1571,3539,309,947,1277,1278,1281,1282,1293,2437,3083,3596,914,917,918,929,3075,3084,3589,234,941,3076]),
  ([8094,8156], [3639,3642,3643,385,386,430,1588,1775,1776,3103,3615,1311,1312,1572,3102,426,947,1295,1296,1781,1902,2684,2690,3076,3084,3097,931,1761,1762,3640,1562,3096,3610,1285,3098,3035,3042,3077,3085,3589,3596,3083,3351]),
  ([1965,3428,8016,8036,1244,8156], [309,1277,1278,1282,1293,2437,3083,3596,914,917,918,929,3075,3085,3589,240,955,3077]),
  ([3429,8095], [424,1896,1900,1971,1984,2031,3416]),
  ([8054,8058,8156], [3603,3627,3644,3646,3091,322,1580,1584,1590,1594,1598,1784,1790,1798,1919,1920,1925,1926,1933,1934,2003,2009,2017,3106,3107,3109,3110,3618,3619,3635,1897,1898,3101,3637]),
  ([3417,8055], [417,1754,2448,3549,1554]),
  ([8036,1244,8055,8156], [3644,3646,3648,3101,3415,3645,309,310,420,1277,1278,1282,1293,1555,1556,1756,1761,1762,1769,1891,1892,1975,3083,3096,3596,3085,240,241,1316,1322,1597,1598,1797,1798,1933,1934,2017,3098,3103,3107,3110,3610,3629,947,3076,3097,381,941,1306,1582]),
  ([4221,8017,8037], [3001,3008,3076,3084,234,941]),
  ([8115,8055,8156], [3644,3646,3648,3101,3415,310,421,1556,1756,1891,1892,1899,1904,1920,1975,2003,3105,3626,454,1998,2014,2017,3110]),
  ([4287,8037,8074,8156], [462,2012,3055,3098,3610,1924,3436,323,1311,1787,3084,3097,381,1305,1582]),
  ([8037,8055,8156], [3644,3646,3648,3651,3101,3415,309,310,420,421,1278,1555,1761,1762,1769,1904,1919,2437,2656,3096,3652,914,918,929,3075,3107,3618,3106,3650,3008,3019,3084,3589,235,1308,1583,3077,3097,3610,133,958,1322,1597,3098]),
  ([8055,8156], [3644,3646,3648,3653,3101,3415,3649,229,1276,1279]),
  ([8036,1244,8156], [3644,3646,3654,3647,3092,324,325,1319,1592,1597,1598,1797,1798,1933,1934,2017,3085,3098,3103,3107,3110,3596,1312,1576,3641,947,1295,3076,3083,3547,127,226,944,1280,1308,1555,1556,1583,1755,1756,1892,1975,3101,3629,420,1761,1762,1769,3096,3097,3610]),
  ([1311,8156], [234,235,941,942,945,1290,1308,1583,3076,3644,3646,3654,921,922,929,3647,3092,325,1597,1598,1797,1798,1933,1934,2017,3034,3077,3098,3103,3107,3110,3589,3075,118,916,1280,1555,1556,1755,1756,1891,1892,1975,3101,3629,420,1761,1762,1769,3096,3097,3610]),
  ([8156], [3644,3646,3654,3656,3647,3092,324,1592,1311,3084,3655,229,1276,1280,1288,1556,1564,1755,1763,3101]),
  ([4881], [472,2024,2031,2041,3111,3657]),
  ([8136,8018,8078,8076,8138,8016,2692], [1725,1726,1729,1730,1741,3588,3609,1522,3095,3349,1246,2276,881,882,890,901,3074]),
  ([4947], [478,2044,2047,2053,3111,3657]),
  ([8018,8078,8076,8138,8016,3417], [417,418,1753,1754,1757,1758,1769,1862,1892,1975,2439,3096,3658,3659,3660,1554,1721,1722,1729,1730,1741,3109,474,1278,1522,2025,2631,3108,3608,914,917,918,929,1246,3075,3095,3587,881,882,890,901,2276,3074]),
  ([8134,8058,8078,8138,3417], [417,1753,1754,1757,1758,1769,1862,3096,3608,3648,1721,1722,1729,1730,1741,3095,3601,360,1513,1514,1517,1518,1529,1530,1541,3089]),
  ([8078,8076,8138,8016,3417,8036], [417,418,1753,1754,1757,1758,1769,1891,1892,1975,2444,3096,3648,3658,3661,1554,3077,133,957,958,1278,1281,1282,1293,1321,1322,1598,1798,1933,3083,3085,3092,3107,3662,3108,468,1981,1982,1989,3105,3592,3599,3606,3528]),
  ([2835,8138,8016,3417,8036], [387,388,417,418,1595,1754,1792,1797,1798,1862,1891,1892,1933,1975,2392,2439,3092,3103,3107,3658,3660,1554,1587,1588,1722,1818,1278,1281,1282,1312,1522,914,917,918,929,1245,1246,3075,882,889,3444,3109,3625,474,2001,2002,2005,2025,2026,2697,2704,2992,3025,3091,3102,3106,3108,3600,3612,3624,1981,3105]),
  ([8134,8136,8078,8138,8016,3417], [417,1753,1754,1757,1758,1769,1862,2444,3096,3608,3662,1554,1721,1722,1729,1730,1741,3092,3095,324,360,1278,1281,1282,1293,1319,1514,2280,3083,3085,3594,1238,1241,1242,1253,1254,1265,3082]),
  ([2109,8135,8136,8078,8138,8016,2692,8036], [324,1319,1554,1726,3034,3077,3085,3588,3595,1278,1282,1522,3432,1245,1246,1253,1254,1265,3082,3447,213,874,878,889,890,901,3074]),
  ([8138,8016,2768,8118,3417,8036], [417,418,1754,1862,1891,1892,1975,2444,3648,3657,3658,3660,3664,1554,1722,3098,3663,1278,1281,1282,1293,1521,1522,1529,1530,1541,3083,3097,3436,3634,322,323,381,382,1246,1581,1784,1919,1920,2003,3091,3109,3111,3665,3666,882,889,2992,3028,3092,3106,3108,3530,3600,468,1981,3089,3105,3561,3592,2275,3085,3442]),
  ([8114,5013,8118,3417], [417,1753,1754,1757,1758,1769,2444,3045,3051,3056,3085,3092,3096,3098,3606,3648,1554,3599,1278,1281,1282,1293,3083,3528,3592]),
  ([8051,8031,8116,2110,3494,8098,8078,2768,8118,3417], [417,1862,2392,3528,3607,1818,3097,3403,3612,382,1783,3102]),
  ([5013,2768,8118,3417,8036], [417,418,480,1862,1891,2016,2056,3038,3045,3051,3056,3060,3077,3085,3092,3098,3103,3657,3668,1818,1932,2007,2008,2036,1682,1796,1923,1924,1991,3105,451,1482,1596,1788,1984,1987,2031,2602,2608,3106,3111,3593,3669,1205,1206,1587,3003,3600,841,3091,3326,3578,198,821,822,825,2682,3076,3576,3586]),
  ([8072,8078,8017,8138,2768,3417], [417,418,1753,1754,1757,1758,1769,1892,1975,3096,3608,3657,3658,3660,3108,469,2027,2031,3109,3111,3609,3003,3076,3097,381,941,1306,1582]),
  ([8038,8032,8138,3417,8036], [417,418,1754,1892,1975,2444,3595,3658,3660,1554,3109,474,1278,1281,1282,1293,2025,3083,3108,3594]),
  ([2619,8017,8138,3417,8036], [360,417,418,1513,1514,1517,1518,1529,1530,1541,1754,1892,1975,2276,2280,2439,3089,3648,3657,3658,1238,1241,1242,1253,1254,1265,1554,3082,3672,874,877,878,889,890,901,1278,3074,3085,240,241,914,917,918,929,955,1316,1321,3075,3077,3092,3587,947,3076,3108,127,469,944,1307,1308,1584,1784,1920,2003,2031,3111,3530,3016,3091]),
  ([2768,8118,3417,8036], [417,418,1754,1862,1892,1975,2439,3648,3658,3670,1554,1721,1722,1729,1730,1741,3110,3667,3673,1278,1521,1522,1529,1530,1541,3095,3671,914,917,918,929,1245,1246,1253,1254,1265,3075,3098,387,881,882,889,890,901,1595,1792,3035,3042,3077,3085,3092,3672,1587,1588,3082,213,214,873,1239,1312,3074,3089,3587,947,3076,3108,127,469,944,1307,1308,1584,1784,1920,2003,2031,3091,3530]),
  ([2769], [385,1780,1784,1790,1920,1926,2004,2010,2047,2053,3111,3657]),
  ([3417,8036], [417,418,1862,1892,1975,3658,3660,3675,1721,1722,1729,1730,1741,3674,1521,1522,3107,462,463,1245,1246,1253,1254,1265,1932,2017,3044,3050,3055,3085,3092,3098,3110,3662,3672,1796,3082,3108,214,469,1239,1240,1515,2027,3095,3109,3434,3609]),
  ([2631,8093,3362], [367,1720,1723,1724,1735,1847,3100]),
  ([4287,1167,4940,8138,3422,3416], [213,214,462,873,874,877,878,889,890,901,1239,1240,1515,1931,2012,3037,3050,3055,3074,3077,3092,3098,3103,3660,3675,1923,1924,1996,3109,3588,1788,1907,1964,3101,1587,1588,1879,1880,1312,1743,1744,947,1543,3076,127,944,1307,1308,1583,1584,1783,1784,1920,2004,2047,3091,3097,3102,3477,3602,3609,3677,3095,363,1521,1522,1529,3089]),
  ([3357,5673,2625,8118,4070,8138], [364,412,486,1724,1728,1756,1859,1860,1871,1872,1876,1891,1899,1947,1959,2039,2040,2992,3105,3108,3616,1967,3104]),
  ([8098,8092,4088,8094,4220,3494,2625,8118,4070,8136,8138], [364,1724,1859,1860,1947,3613,3614,3658,3102,3108,427,468,1919,1957,3104,3106,3617]),
  ([5666,8052,2625,8118,8012,4070,3344,8136,8138,3422,3416], [364,1723,1728,1756,1891,3416,3657,3101,3111,3679,486,2040,3003,3016,3025,3028,1967,1968,1879,3100,3680,3103,3036,3049,3077,3092,3588,3602,3076,3091,318,941,1306]),
  ([2625,1910,8118,8012,4070,3344,1892,8136,8138,3422,3416], [363,364,1521,1522,1529,1724,1728,1756,1859,1860,1891,1947,3089,3658,3681,483,2029,2030,2679,3108,1957,1958,1961,1982,1989,3104,3105,3616]),
  ([2631,8118,4070,8138], [367,1720,1724,1728,1736,1740,1756,1764,1859,1860,1871,1872,1891,1899,1947,1959,1960,2031,3657,3658,3108,3111,486,2040,2992,3105,3616,1967,3104]),
  ([4077,8134,3362,8094,8072,1167,8136,8138], [214,438,1239,1240,1516,1715,1857,1858,1865,2428,3100,3613,3103,432,1795,1796,3098,3434,3609]),
  ([8112,8134,4142,5673,8118,8136,8138], [2992,3028,3616,3617,3105,3106,456,1985]),
  ([8078,8070,3354,4868,4083,5666,8072,8118,452,1172,8136,8138,8036], [442,1956,1959,1987,2640,3541,3609,3657,3658,3675,3097,3108,3111,3436,3608,323,381,1581,1765,1766,1769,2683,3003,3076,3091,3096,372,1554,1555,1557,3630,230,1276,1280]),
  ([8098,4868,3272,2546,1820,8031,8114,4083,8134,8094,5666,8072,8118,452,3344,1172,8136,8138,8036], [441,442,1833,1834,1837,1869,1870,1877,1956,1961,1987,2612,3611,3613,3616,3100,3400,397,398,409,1681,1682,3099,393,1481,1669,2269,3580,3582,3621,3686,3098,3622,3623]),
  ([3561,590,8072,8012,8136,8138], [432,1795,3036,3077,3098,3588,3609,3675,3076,3097,381,941,1306,1582]),
  ([8134,4142,8094,5666,4088,8072,8118,1167,1172,8038,8136,8138,8036], [213,214,873,874,877,878,889,890,901,1197,1198,1201,1202,1213,1240,1516,1715,1716,1851,3074,3619,3111,3685,486,2040,2992,3003,3028,3688,1968,3103,1879,3684,3104,442,1940,1947,1955,1956,1987,3105,3106,3593,3578,199,1187,1188,1463,1464,1663,3687]),
  ([4083,8135], [442,1940,1947,1959,3108,3552,3657]),
  ([4869,4082,8098,3362,4220,3494,4088,8118,4070,3344,8136,8138], [465,1945,1946,2434,3104,3617,1858,1865,3100,3106,3614,456,1917,3102]),
  ([4215,1246,5673,8072,452,1172,8136,8138,8036], [1919,2685,2700,3003,3021,3076,3097,3609,1784,3098,3444,239,1304,1308,1584]),
  ([8135,8098,5673,4088,8072,8118,452,4070,3344,1172,8136,8138,8036], [486,487,2039,2040,2052,2063,2989,3003,3021,3025,3028,3676,3690,1968,2008,1879,1924,3691,1788,3108,468,469,1588,1982,2027,2648,2676,3101,1312,1898,1762,1562,1286,3692,3106,3617,3104,438,1857,3100,3477,3102,426,1781,2684,3076,3097,3444,3609,3098]),
  ([5666,4088,8072,8118,1167,1172,8038,8136,8138,3422,8036], [213,214,873,874,877,878,889,890,901,1240,1516,1715,1716,1851,3074,3657,3676,3111,486,2040,2989,3003,3101,3688,1968,3103,3693,1879,3613,3689,447,1942,1857,1858,1865,3100]),
  ([5667,8072,8118,4940,8138], [483,2046,2049,2065,2707,3109,3634,2002,2005,3106,3609,3098,3633,387,1591,1596]),
  ([8072,1167,1172,8038,4940,8138,3422,8036], [3657,3660,3676,3678,3107,3109,3695,3111,3694,486,1967,2040]),
  ([1172,1184,1178,8038,4940,8138,3422,8036], [3660,3676,3109,3595,3082,3678,3696,213,214,873,874,877,878,889,890,901,1239,1240,1515,1516,1715,1716,1851,3074,3107,3449,3682,3683,3095,3433,408,1722,1730,1741]),
  ([2631,4940,8138], [367,1720,1724,1728,1736,1740,1755,1756,1763,1768,1783,1848,1851,1872,1891,1960,2031,3416,3657,3683,3101,3107,3111,462,1931,2012,3025,3102,3103,3477,3677,1883,1912,1924]),
  ([2631,8138], [367,1740,1768,1784,1920,2003,3698]),
  ([2637,8138], [370,1732,1736,1740,1746,1750,1752,1756,1764,1768,1774,1778,1784,1790,1856,1859,1860,1871,1872,1881,1882,1891,1899,1909,1919,1920,1925,1926,1935,1947,1959,1960,1969,1970,2003,2009,2031,2041,3104,3105,3106,3108,3109,3111,3319]),
  ([1095,8029,8009,1168], [198,1133,1134,1137,1138,1149,1150,1161,3577,180,757,758,761,762,773,774,785,786,797,3575]),
  ([297,8069,8029,2619], [73,360,759,760,1124,1399,1674,2242,1618,1625,1626,1637,3581,330,1406,2169,1130,1137,1138,1149,1150,1161,3577]),
  ([4287,8092,4941,8012,2619,8138], [360,462,474,1514,1674,1931,2002,2280,2637,2701,2704,3037,3044,3055,3077,3085,3098,3103,3184,3675,1238,1241,1242,1254,1265,1618,1918,1921,3082,3097,3102,3240,3605,3702,1418,1141,1142,1149,1150,1161,777,778,785,786,797,3575,76,756,759,767,3577]),
  ([8038,8098,8118,8092,4941,8012,8032,2558,1168,2552,8138], [474,475,1197,1198,1201,1202,1213,2001,2002,2005,2047,2692,2701,3106,3240,3657,3675,3097,3111,3010,3084,3593,3578,3701,199,1188,1463,3184,3582,3607,3077,3098,387,955,1320,1596]),
  ([8098,8118,8092,4941,8012,8032,2558,1168,4070,2552,8138], [474,475,1198,2001,2002,2005,2047,2686,2701,3106,3657,3675,3704,829,830,837,838,849,3085,3097,3111,240,241,955,1322,1597,3003,3076,3077,3098,3586,3607,3576,3582,345,821,1186,1462]),
  ([8092,4941,8012,2619,8138], [360,361,474,475,1514,1673,1674,1677,1716,1851,2001,2002,2005,2047,2280,2637,2692,2697,2701,3106,3657,3675,3703,1238,1241,1242,1254,1265,3082,3097,3107,3111,3705,3010,3016,3084,3091,3103,432,1795,3043,3049,3085,3092,3098,3593,3600,3607,3528]),
  ([4941,8012,2619,8138], [360,361,474,475,1514,1715,1716,1851,2025,2026,2033,2047,2280,2637,2649,2651,3657,3706,1238,1241,1242,1254,1265,1958,1961,1981,1982,1989,3082,3111,1870,1877,1898,2967,2974,3100,409,1762,1859,1860,1864,1891,1947,3104,3105,3108,3616,1562,3107,1285,3037,3044,3077,3085,3587,3594,3083,3351]),
  ([4287,8037,8136,8052,8138], [462,2012,3050,3092,3602,1924,1788,1587,3091,318,1305,1306,1309,3084]),
  ([2110,8057,8037], [1591,3091,318,1305,1306,1309,3084]),
  ([2037,8037], [318,1305,1306,1309,3084]),
  ([2043,8037], [322,1580,1584,1590,1593,1784,1790,1920,1926,2004,2010,2047,2053,3092,3111,3647,3654]),
  ([8037,8136,8012,8052,8138], [3710,3711,3091,3602,3092,324,1592,3034,3077,3588,1311,3084,234,941,942,945,3076]),
  ([2624,8073,8138], [3657,3660,3699,3700,3095,3349,360,1513,1514,1517,1518,1529,1530,1541,2276,2280,3089,1238,1241,1242,1253,1254,1265,3082,874,877,878,890,901,3074,3707,3109,3712,3595,3085,240,241,955,1316,1321,3077,3092,3588,3602,947,3076,127,944,1307,1308,1584,1784,1920,2004,2047,3091,3111,486,1587,1788,1924,2008,2052]),
  ([2043], [322,1580,1584,1590,1593,1784,1790,1920,1926,2004,2010,2047,2053,3092,3111,3647,3654]),
  ([2037,1383,8138], [240,241,318,319,955,1306,1322,1566,1583,1584,1597,1598,1783,1784,1797,1798,1920,1933,2003,2004,2047,2682,3077,3098,3103,3107,3627,3660,3675,942,945,1538,3076,3097,3109,3111,3588,3609,3713,364,486,1258,1712,1716,1851,2040,2417,3025,3102,3614,3679,893,894,901,1968,3074,3347]),
  ([8073,1910,441,8053,8136,8138], [106,876,1239,3448,3713,363,1521,3089]),
  ([5673,441,452,8136,8036,1383,8138], [106,241,486,876,1239,1240,1321,1322,1516,1597,1598,1715,1716,1797,1798,1851,1933,2040,2985,3016,3021,3092,3098,3103,3107,3715,1967,1968,3091,3602,1880,1744,1543,3716,3440,3609,3693,3097,3608,381,1765,3096,3344,368,372,1533,1726,3089,1521]),
  ([441,452,4940,8136,8036,1383,8138], [241,1321,1322,1598,1798,1933,3092,3107,3657,3714,3715,3717,3091,3111,3602,3695,3713,3716,363,1522,1530,1541]),
  ([452,8013,4940,8136,8036,1383,8138], [240,241,1316,1322,1597,3098,3675,3699,3700,3714,3715,3718,947,1300,3091,1272,903,3074,109,872,876,884,1240,1248,1515,1523,3095,3609,3097,3436,323,381,1766,2683,3076,3442,1537,1562]),
  ([453,8053,8136,8078,8138], [112,880,884,896,900,928,944,1236,1239,1240,1247,1259,1308,1515,1583,3089,3449,3609,3675,3097]),
  ([585,8136,1383,8138], [127,241,944,1308,1322,1583,1584,1597,1598,1783,1784,1797,1798,1919,1920,1933,2004,2047,3098,3103,3107,3657,3675,3097,3111,3609,3713,364,486,1712,1715,1716,1723,1724,1851,1859,2040,3025,3028,3102,3106,3614,3617,3679,1967,3100,3104,415,1868,1871]),
  ([8136,8036,1383,8138], [240,241,955,1316,1321,1322,1597,3077,3092,3098,3657,3675,3714,3715,3721,947,1300,3076,3091,3588,3602,3720,1272,3719,475,903,2047,2701,3097,3111,3609,3713,3717,2417,3074]),
  ([2625,3362,8094,4874,3356,8098,8138], [364,1712,1715,1723,1724,1860,1947,3100,3613,3658,3108]),
  ([4869,386,8091,3296,8011,8071,3290,4148,5673,4874,4082,8118,8138], [465,1946,1973,1974,1978,1989,3105,3465,3620,1821,3099,393,1669,2262,3582,1463,2176,3576,97,828,832,1184,1188]),
  ([8036,1383,8138], [240,241,955,1316,1322,1597,1598,1797,1798,1933,3077,3098,3103,3107,3657,3658,3660,3675,3676,3722,947,1300,3109,474,475,931,1272,2001,2002,2005,2025,2026,2034,2047,2631,2649,2651,2686,2701,2704,3076,3097,3106,3111,3586,3607,903,1918,1921,1958,1981,1982,1989,2985,2989,3102,3612,1833,1834,1837,1870,1877,1897,1898,3101,3723,1694,1761,1762,3713,1494,1562,1218,1286,853,921,3724,3108,3608,3613,3096,3348,373,1756,1891,2438,3075,3105,3587,3616,3074,3363,97,828,835]),
  ([1383,8138], [240,241,955,1315,1316,1321,1322,1597,3077,3092,3098,3660,3675,3714,3715,3725,947,1300,3084,3091,234,235,941,1272,1308,1583,1584,1784,1920,2003,3076,3097,3109,3588,3602,3609,3713,3720,363,903,1522,1530,1541,2417,3074,3716]),
  ([441,1172,8073,8078,8136,8138], [106,876,1240,1515,1516,1716,1851,3447,3449,3657,3713,3714,3716,3726,3085,3595,3708,3710,3091,3107,3602,3092,324,325,1592,1598,1797,3103,1311,3084,235,1308,1584,1783,1784,1920,2004,2047,3111,3679,486,2040,3025,3102,3614,1968,3347]),
  ([1311,657,2625,8136,8138], [133,235,364,958,1308,1322,1584,1598,1712,1715,1716,1723,1724,1783,1784,1797,1798,1851,1859,1919,1920,1933,2004,2047,3103,3107,3656,3111,3679,486,2040,3025,3028,3102,3106,3614,3617,1967,3100,3104,415,1868,1871]),
  ([1317], [238,1304,1307,1308,1313,1314,1318,1321,1584,1590,1784,1790,1920,1926,2004,2010,2047,2053,3091,3092,3111,3603,3654]),
  ([8037,1172,8073,8136,8138], [3710,3711,3713,3729,363,1522,1530,1541,2417,3084,3091,3728,234,941,942,945,1246,3076,3077,3588,882,889,890,901,3074,3716,3727,3098,3602,387,1595,3092]),
  ([8073,4940,8138], [3657,3658,3660,3713,3714,3726,363,364,1521,1522,1529,1530,1541,1712,1715,1723,1724,1728,1756,1860,1891,1947,2417,2422,3085,3109,3730,1246,1253,1254,1265,3595,3697,420,421,882,889,890,901,1873,1874,1877,1899,1900,1903,1983,1984,2031,2656,3082,3100,3108,3111,213,214,873,1239,2967,2992,3025,3074,3089,3102,3105,3614,3103,433,1933,3036,3049,3077,3092,3107,3587,3602,3075,3091,3628]),
  ([3356,1910,8093,8053,8013,3362,458,452], [3342,3348,3350,365,1522,1529,3074,3089,297,873,1238]),
  ([8037,4940,8138], [3657,3660,3675,3710,3711,3729,3731,3084,3091,3109,234,235,941,942,945,1290,1308,1583,1584,1783,1784,1919,1920,2004,2047,3076,3097,3111,3609,486,1262,2040,3025,3028,3098,3102,3106,387,388,893,894,901,1595,1797,1798,1933,1967,1968,3035,3077,3092,3103,3107,3588,3602,3614,3617,1879,1880,1744,1543,3732,412,1856,1859,1860,1871,1935,3104]),
  ([3357,4940,8138], [411,412,1734,1856,1859,1860,1864,1871,1872,1875,1876,1891,1899,1935,1947,1959,1960,2031,2634,3657,3658,3660,3726,3731,3733,1534,3085,3108,3109,3111,486,1258,1265,2040,2992,3105,3697,217,1236,1239,1247,1967,3104,3616,3107,462,1932,3055,3098,3609,1796,3434]),
  ([8078,1246,4214,4868,3354,2696,1970,1892,452,1904,1172,1898,5666,4940,8138], [1261,1262,1265,3657,3660,3675,3714,3726,3731,3733,3085,3109,3111,3609,3697,420,1762,1769,3003,3097,3434,3436,323,381,389,1581,1798,1933,2683,3076,3091,3107,3630]),
  ([5666,8093,4940,8138], [3657,3658,3660,3726,3731,3733,3734,3085,3109,3111,3595,486,2040,2980,1968,1879,3342,3350,365,1522,1529,1530,1541,1245,1246,1253,1254,1265,3082,3696,213,214,420,421,874,878,889,1239,1240,1516,1715,1761,1762,1888,1892,1900,1904,1919,1975,1983,2662,2667,3089,3100,3108,409,1562,1286,3735,3098,3622,387,1595,3090,3092,3601]),
  ([5667,4940,8138], [483,2046,2049,3109,3634,3731,3609,3695,3098,3107,462,1795,1932]),
  ([8098,4940,8138], [3657,3660,3675,3714,3726,3731,3733,3737,3085,3109,3111,3595,3676,3736,486,2040,2989,3025,3028,3614,1967,1968,3102,426,427,1781,1879,1880,1901,1902,1919,2695,3091,3097,3101,3106,3609,3613,3690,1744,1874,3098,387,388,1544,1595,1734,1798,1933,3092,3107,3593,3600,1267,1534,3532,3567,3691,1257,2281,2425,3082]),
  ([4940,8138], [3657,3658,3660,3675,3714,3726,3731,3733,3737,3738,3085,3103,3109,3111,432,433,1795,1933,3003,3028,3049,3092,3098,3107,3609,3688,3097,381,382,1581,1784,1919,3091,3106,3593,3600,3602,3720,3528,3561,3572]),
  ([4078,8031,8091,8051,2110], [1821,1822,3403]),
  ([2835,8138], [387,388,1595,1596,1797,1798,1933,3042,3085,3092,3103,3107,3658,3714,3729,3739,474,2001,2002,2005,2025,2026,2651,2692,2697,2704,3084,3091,3106,3593,3600,1918,1921,1958,1961,1981,1982,1989,3102,3532,3612,3740,438,440,1943,1947,3104,3105,3108,3616]),
  ([8118,8058,8138], [3675,3714,3726,3729,3739,3741,474,2001,2002,2005,2692,2697,2701,3084,3085,3091,3097,3098,3106,3593,3600,3607,3528]),
  ([8134,8058,8098,8138], [3657,3739,3741,3742,474,475,2025,2026,2047,2631,2649,3098,3107,3111,3662,1958,1982,2967,2980,2985,2989,3037,3077,1870,1877,1897,1898,3101,3613,3723,1761,1762,3350,3713,365,1522,1530,1541,1561,1562,3608,1246,1286,3096,372,882,890,901,921,1553,2438,3075,3090,3587,3601,3732]),
  ([1029,1766,2492,8049,8069,3292], [184,1120,1123,1124,1131,1132,1399,1407,1645,3581,333,1417,1418,1426,1437,3579]),
  ([1023,314,8009,320], [180,757,758,761,762,773,3575]),
  ([8058,8098,8138], [3657,3658,3675,3714,3726,3729,3739,3741,3742,3743,474,475,2002,2025,2047,2686,2692,2697,2701,2704,3084,3085,3091,3097,3098,3107,3108,3111,465,1918,1921,1946,3003,3037,3076,3077,3102,3585,3591,3598,3605,1822,1826,1633,1634,1429,1430,1437,3744,1153,1154,1161,789,790,797,3745,3577,187,1128,1131,1132,1143,1395,3579]),
  ([8098,8138], [3657,3658,3675,3729,3739,3741,3746,474,475,2001,2002,2005,2025,2026,2034,2047,2631,2649,2651,2686,2692,2701,2704,3084,3092,3097,3098,3106,3111,3676,324,325,1592,1598,1798,1918,1921,1933,1958,1981,1982,1989,2967,2985,2989,3003,3034,3076,3077,3102,3107,3586,3607,3612,1576,1833,1834,1837,1870,1877,1897,1898,3101,3723,1548,1694,1761,1762,3713,1268,1494,1562,903,1218,1286,853,921,3724,3108,3608,3613,3096,3348,373,1756,1891,2438,3075,3105,3587,3616,3074,3363,97,828,835]),
  ([8138], [3747,3103,433,1933,3049,3092,3107,3742]),
  ([5012], [3110,3748]),
  ([3363], [415,1868,1872,1875,1876,1882,1885,1886,1887,1903,1913,1914,1929,1960,1970,2031,2041,3101,3102,3103,3111,3615]),
  ([4089], [445,1952,1955,1956,1960,1965,1966,1970,1971,1987,1997,1998,2013,2031,2041,3105,3106,3107,3111,3618]),
  ([657], [133,958,1321,1322,1598,1798,1933,1934,2017,3092,3107,3110,3742]),
  ([1383], [241,1322,1598,1798,1934,2017,3110,3726]),
  ([2109], [325,1598,1797,1798,1934,2017,3103,3110,3747]),
  ([2835], [388,1798,1934,2017,3110,3741]),
  ([3561], [433,1933,1934,2017,3049,3092,3107,3110,3742]),
  ([4287], [462,463,1931,2017,3103,3110,3747]),
  ([8019], [3077,3752]),
  ([8039], [3085,3753]),
  ([8059], [3092,3754]),
  ([8079], [3098,3755]),
  ([8099], [3103,3756]),
  ([8119], [3107,3757]),
  ([4221], [460,2000,2004,2010,2047,2053,3111,3657]),
  ([3495], [430,1916,1920,1926,2004,2010,2047,2053,3111,3657]),
  ([4155], [454,1980,1983,1984,1988,1993,1994,1998,2003,2009,2014,2017,2019,2031,2041,3108,3109,3110,3111,3619]),
  ([2111], [324,326,1598,1798,1933,1934,2017,3092,3107,3110,3742]),
  ([3429], [424,1896,1900,1971,1984,2031,3416]),
  ([3297], [403,1828,1832,1835,1836,1842,1845,1846,1856,1859,1860,1864,1876,1886,1891,1899,1904,1909,1914,1919,1920,1925,1926,1935,1947,1959,1960,1969,1970,2003,2009,2031,2041,3104,3105,3106,3108,3109,3111,3319]),
  ([2703], [379,1760,1763,1764,1768,1773,1778,1783,1887,1900,1984,2031,3101,3450]),
  ([1977], [316,1560,1564,1568,1574,1578,1584,1590,1752,1755,1763,1764,1773,1783,1900,1984,2031,3101,3450]),
  ([591], [130,940,944,950,954,958,1307,1308,1313,1314,1321,1584,1590,1784,1790,1920,1926,2004,2010,2047,2053,3091,3092,3111,3603,3654]),
  ([1251], [232,1284,1288,1292,1298,1302,1308,1314,1552,1556,1564,1574,1584,1590,1755,1763,1764,1773,1783,1900,1984,2031,3101,3450]),
  ([4143,8095], [447,1889,1890,1893,1894,1905,3101]),
  ([8071,380,2558,3284,8011,8091,4084], [1833,1834,1837,3620,1694,3099,393,1494,1669,2262,3582,1218,2176,3576,853]),
  ([8095,8115,4084,8076,8016,8096], [3646,3758,3761,3762,3763,3764,3766,3774,3105,450,451,1897,1987,3101,3106,3586,3607,3612,417,1754,1862,2392,1554,1818,1278,1681,3775,845,886,914]),
  ([2493,3416,3290,8076], [337,1616,1619,1620,1623,1631,1632,1635,1659,1660,1663,1688,1728,1756,1891,3582,3761,3762,3763,3764,3768,3769,3099,3486,3607,3106]),
  ([1023,320,8009], [180,757,758,761,762,773,774,785,3575]),
  ([1041,8049,1772], [190,1140,1143,1144,1149,1155,1403,3579,264,1122,1126,1138]),
  ([2493,3290,8076], [337,1632,1688,1728,1755,3777]),
  ([2481,8049,2500,8009], [330,1405,1406,1413,1414,1425,1426,1437,2166,3579,264,1122,2119,758,762,773,774,785,786,797,3575]),
  ([2475,8049,1772], [327,1397,1398,1401,1402,1413,1414,1425,3579]),
  ([8049,2492,3292,3290,8069,8009,8096], [1645,1646,1837,3675,3729,3759,3760,3761,3762,3763,3764,3767,3781,1441,1442,3779,3782,1165,1166,3581,333,334,801,1418,1425,1604,1607,1611,1619,1623,2250,3744,3778,3577,3591,3709,3084,3568,3582,235,352,1308,1584,1683,1784,1919,2401,3099,3106,3237,3500,3600]),
  ([1240,1100,8031,8029,1112,1774,8009], [1165,1166,1250,801,1209,3578,3778,198,1133,1134,1137,1138,1149,3577]),
  ([4084,8076,8016,8096], [1833,1834,3657,3714,3749,3758,3759,3760,3761,3762,3763,3764,3767,3771,3780,1646,1694,3585,3605,3783,1442,1494,3598,3709,1217,3091,3591,318,319,1565,1584,1784,1919,1920,2004,2047,3106,3111,3326,3593,3607,3784,227,1279,3090,3528,3597,3599,3776]),
  ([8031,8029,1774,8071,5673,8116,8114,8009], [2980,3016,3528,3749,3760,3763,3599,3600,3091,3326,318,1565,3090,309,1278,1527,3784,208,1204,1212,1248]),
  ([3292,2492,2474,2480,1040,8049,8029,1022,1046,8069], [1645,3581,333,1418,1425,2250,3577,3744]),
  ([3293,8091], [399,401,1815,1816,3769,1803,1804,3099,1799]),
  ([2493,8071], [337,1616,1619,1620,1631,1659,3582]),
  ([8029,2500,8071,5673,8116,8114,8069,8009,8096], [1441,1442,3759,3760,3762,3763,3767,3786,3789,1165,1166,3593,3612,3709,3788,801,3598,3778,3779,3781,3782,3787]),
  ([1755,1832,314,248,182,176,1239,308,242,3291,8051,8005,1311,320,254,188,1838,8007,8009], [268,1411,2146,2165,3575,3580,72,693,694,697,2098,3574,51,605,3328,3573]),
  ([2500,8076,8016,8096], [1382,1441,1442,3657,3729,3749,3758,3759,3760,3761,3762,3763,3764,3766,3767,3768,3773,3785,443,1030,1102,1166,1940,1943,1955,1956,1960,1987,2031,3105,3106,3111,3584,3585,3605,3607,3612,3668,3788,3789,3790,661,737,801,1645,1694,3591,3709,1493,3084,3583,3598,3600,3781,3782,3783,234,400,1289,1832,1875,3101,3581,3590,333,334,1358,1417,1418,1425,1604,1607,1619,2231,2246,3083,3582,351,1006,1142,1481,2355,637,638,645,778,785,3791,3579,1123,2119,3575,76,756,760]),
  ([8076,8016,8096], [3658,3750,3751,3766,3768,3769,3785,3792,341,441,443,1628,1632,1635,1636,1644,1647,1668,1671,1672,1676,1688,1700,1715,1723,1728,1735,1740,1755,1756,1763,1764,1799,1811,1823,1824,1891,1899,1947,1959,3099,3100,3101,3104,3105,3108,3309]),
  ([1966,1774,1838,8051,8031,8029,8009], [1278,1526,3631,3784,202,1184,1187,1195,1485,3580]),
  ([8016,8096], [3675,3714,3729,3758,3759,3760,3761,3762,3763,3764,3765,3766,3767,3768,3769,3770,3793,3097,3585,381,382,1581,1765,1784,1919,2689,3084,3091,3106,3591,3593,3598,3600,3612,3669,3740,3788,440,1646,1694,1943,3528,1442,1493,3794,311,1555,3096,3606,3105,450,1897,2620,3101,3604,3783,337,1616,1620,1623,1635,1660,1663,3099]),
  ([585], [127,943,944,1307,1308,1584,1784,1919,3675,3714,3729,3759,3760,3761,3763,3764,3084,3091,3106,3565,3593,3600,3528]),
  ([8017], [3772,3796,3076]),
  ([8096], [3795,3797]),
  ([3488], [3765,3798,3102]),
  ([1311], [235,1308,1584,1783,3799]),
  ([2037], [319,1584,1783,3799]),
  ([2763], [382,1783,3799]),
  ([4215], [456,1917,1918,1921,3102,3795,3797]),
  ([8037], [3729,3800,3084]),
  ([8057], [3714,3801,3091]),
  ([8077], [3675,3802,3097]),
  ([8117], [3764,3803,3106]),
  ([8030], [3759,3763,3804,3807,3593]),
  ([8050], [3760,3763,3805,3807,3600]),
  ([8070], [3761,3763,3806,3807,3607]),
  ([], [3808,3809,3810,3528])
]

def proofTree : ClauseTree :=
  buildClauseTree (baseCNF11 ++ coreClauses5 ++ rupSteps.map Prod.fst)

theorem check_triClauses : genTriClauses.all isValidTriClause = true := by decide
theorem check_monoClauses : genMonoClauses.all isValidMonoClause = true := by decide
theorem check_uniqClauses : genUniqClauses.all isValidUniqClause = true := by decide
theorem check_edgeClauses : genEdgeClauses.all isValidEdgeClause = true := by decide
theorem check_no4Clauses : genNo4Clauses.all isValidNo4Clause = true := by decide
theorem check_cores5 : cores5.all verifyFarkasSpec = true := by decide
theorem check_prefix_all : checkPrefixIndices proofTree 0 (baseCNF11 ++ coreClauses5) = true := by decide
theorem check_steps_all : checkProofSteps proofTree (baseCNF11 ++ coreClauses5).length rupSteps = true := by decide
theorem check_final_empty : proofTree.get? ((baseCNF11 ++ coreClauses5).length + rupSteps.length - 1) = some [] := by decide

theorem base_and_cores_true (x : Nat → Int)
    (hPos0 : 0 < x 0)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b)
    (hEdge4 : ∀ s0 s1 s2 s3, s0 < s1 → s1 < s2 → s2 < s3 → s3 < mVal - 1 →
      evalVarSpec x (.edge s0 s1) = true ∨ evalVarSpec x (.edge s0 s2) = true ∨
      evalVarSpec x (.edge s0 s3) = true ∨ evalVarSpec x (.edge s1 s2) = true ∨
      evalVarSpec x (.edge s1 s3) = true ∨ evalVarSpec x (.edge s2 s3) = true) :
    ∀ c ∈ baseCNF11 ++ coreClauses5, evalClause (mkValuation x) c = true := by
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hBase | hCore
  · unfold baseCNF11 at hBase
    simp only [List.mem_append] at hBase
    rcases hBase with (((hTri | hMono) | hUniq) | hEdge) | hNo4
    · exact isValidTriClause_sound x c ((List.all_eq_true.1 check_triClauses) c hTri)
    · exact isValidMonoClause_sound x hInc c ((List.all_eq_true.1 check_monoClauses) c hMono)
    · exact isValidUniqClause_sound x hInc c ((List.all_eq_true.1 check_uniqClauses) c hUniq)
    · exact isValidEdgeClause_sound x c ((List.all_eq_true.1 check_edgeClauses) c hEdge)
    · exact isValidNo4Clause_sound x hEdge4 c ((List.all_eq_true.1 check_no4Clauses) c hNo4)
  · unfold coreClauses5 at hCore
    rw [List.mem_map] at hCore
    rcases hCore with ⟨spec, hSpecMem, rfl⟩
    exact farkasSpec_sound x hPos0 hInc spec ((List.all_eq_true.1 check_cores5) spec hSpecMem)

theorem m11_no_avoid_5_contradiction (x : Nat → Int)
    (hPos0 : 0 < x 0)
    (hInc : ∀ a b, a < b → b < mVal → x a < x b)
    (hEdge4 : ∀ s0 s1 s2 s3, s0 < s1 → s1 < s2 → s2 < s3 → s3 < mVal - 1 →
      evalVarSpec x (.edge s0 s1) = true ∨ evalVarSpec x (.edge s0 s2) = true ∨
      evalVarSpec x (.edge s0 s3) = true ∨ evalVarSpec x (.edge s1 s2) = true ∨
      evalVarSpec x (.edge s1 s3) = true ∨ evalVarSpec x (.edge s2 s3) = true) :
    False := by
  let v := mkValuation x
  let init := baseCNF11 ++ coreClauses5
  have hInitTrue := base_and_cores_true x hPos0 hInc hEdge4
  have hInv0 : ∀ hid hc, hid < init.length → proofTree.get? hid = some hc → evalClause v hc = true := by
    intro hid hc hLt hGet
    have hMem : hc ∈ init := checkPrefixIndices_sound proofTree init 0 hid hc check_prefix_all (Nat.zero_le hid) (by omega) hGet
    exact hInitTrue hc hMem
  have hAll := checkProofSteps_sound v proofTree rupSteps init.length hInv0 check_steps_all
  have hLenPos : 0 < rupSteps.length := by decide
  have hEmpty := hAll (init.length + rupSteps.length - 1) [] (by omega) check_final_empty
  rw [evalClause_nil] at hEmpty
  cases hEmpty


/-! ==================================================================== -/
/-! ### Section 6: Strict Descending Positives Reduction (`n_max_4`)    -/
/-! ==================================================================== -/

private theorem strictlySorted_getElem :
    ∀ (L : List Int), IsStrictlySorted L →
      ∀ (i j : Nat) (hi : i < L.length) (hj : j < L.length), i < j → L[i] < L[j]
  | [], _, _, _, hi, _, _ => by simp at hi
  | x :: xs, hSort, 0, j + 1, _, hj, _ => by
    rw [IsStrictlySorted, List.pairwise_cons] at hSort
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    have hjxs : j < xs.length := by simp at hj; exact hj
    exact hSort.1 xs[j] (List.getElem_mem hjxs)
  | x :: xs, hSort, i + 1, j + 1, hi, hj, hij => by
    rw [IsStrictlySorted, List.pairwise_cons] at hSort
    simp only [List.getElem_cons_succ]
    exact strictlySorted_getElem xs hSort.2 i j (by simp at hi; omega) (by simp at hj; omega) (by omega)
  | _, _, _, 0, _, _, hij => by omega

private theorem strictlyDesc_11_props
    {x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 : Int} {tail : List Int}
    (hDesc : IsStrictlyDesc (x10 :: x9 :: x8 :: x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: tail)) :
    IsStrictlySorted [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ∧
    (∀ z ∈ x10 :: x9 :: x8 :: x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: tail, z ≤ x10) ∧
    (∀ z ∈ tail, z < x0) := by
  have h1 := hDesc; rw [IsStrictlyDesc, List.pairwise_cons] at h1
  have h2 := h1.2; rw [List.pairwise_cons] at h2
  have h3 := h2.2; rw [List.pairwise_cons] at h3
  have h4 := h3.2; rw [List.pairwise_cons] at h4
  have h5 := h4.2; rw [List.pairwise_cons] at h5
  have h6 := h5.2; rw [List.pairwise_cons] at h6
  have h7 := h6.2; rw [List.pairwise_cons] at h7
  have h8 := h7.2; rw [List.pairwise_cons] at h8
  have h9 := h8.2; rw [List.pairwise_cons] at h9
  have h10 := h9.2; rw [List.pairwise_cons] at h10
  have h11 := h10.2; rw [List.pairwise_cons] at h11
  have ho : x0 < x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧
            x5 < x6 ∧ x6 < x7 ∧ x7 < x8 ∧ x8 < x9 ∧ x9 < x10 :=
    ⟨h10.1 x0 (by simp), h9.1 x1 (by simp), h8.1 x2 (by simp), h7.1 x3 (by simp),
     h6.1 x4 (by simp), h5.1 x5 (by simp), h4.1 x6 (by simp), h3.1 x7 (by simp),
     h2.1 x8 (by simp), h1.1 x9 (by simp)⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold IsStrictlySorted
    repeat' (first | exact List.Pairwise.nil | (rw [List.pairwise_cons]; constructor))
    all_goals (first | exact List.Pairwise.nil | (intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; repeat (first | (rcases hz with rfl | hz) | subst hz); omega))
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hrest
    · omega
    · have := h1.1 z hrest; omega
  · intro z hz
    have := h11.1 z hz; omega

private theorem not_isSumAvoiding_pent {D : List Int} {a b c d e : Int}
    (h : ¬ IsSumAvoiding D [a, b, c, d, e]) :
    (a + b) ∈ D ∨ (a + c) ∈ D ∨ (a + d) ∈ D ∨ (a + e) ∈ D ∨
    (b + c) ∈ D ∨ (b + d) ∈ D ∨ (b + e) ∈ D ∨
    (c + d) ∈ D ∨ (c + e) ∈ D ∨ (d + e) ∈ D := by
  by_cases h1 : (a+b)∈D; exact Or.inl h1
  by_cases h2 : (a+c)∈D; exact Or.inr (Or.inl h2)
  by_cases h3 : (a+d)∈D; exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : (a+e)∈D; exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : (b+c)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  by_cases h6 : (b+d)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  by_cases h7 : (b+e)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  by_cases h8 : (c+d)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
  by_cases h9 : (c+e)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
  by_cases h10 : (d+e)∈D; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h10))))))))
  exfalso; apply h
  intro u hu v hv hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl|rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl|rfl
  · exact absurd rfl hne
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · rw [Int.add_comm]; exact h1
  · exact absurd rfl hne
  · exact h5
  · exact h6
  · exact h7
  · rw [Int.add_comm]; exact h2
  · rw [Int.add_comm]; exact h5
  · exact absurd rfl hne
  · exact h8
  · exact h9
  · rw [Int.add_comm]; exact h3
  · rw [Int.add_comm]; exact h6
  · rw [Int.add_comm]; exact h8
  · exact absurd rfl hne
  · exact h10
  · rw [Int.add_comm]; exact h4
  · rw [Int.add_comm]; exact h7
  · rw [Int.add_comm]; exact h9
  · rw [Int.add_comm]; exact h10
  · exact absurd rfl hne

private theorem pos_desc_no_all_5_avoid :
    ∀ (D : List Int), IsStrictlyDesc D → (∀ x ∈ D, x > 0) → D.length ≥ 11 →
      (∀ B : List Int, (∀ x ∈ B, x ∈ D) → B.Nodup → B.length = 5 → ¬ IsSumAvoiding D B) →
      False
  | [], _, _, hLen, _ => by simp at hLen
  | [_], _, _, hLen, _ => by simp at hLen
  | [_, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | [_, _, _, _, _, _, _, _, _, _], _, _, hLen, _ => by simp at hLen
  | x10 :: x9 :: x8 :: x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: tail, hDesc, hPos, _, hNo5 => by
    let D := x10 :: x9 :: x8 :: x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: tail
    let T := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10]
    have hProps := strictlyDesc_11_props hDesc
    have hTSort := hProps.1
    have hDMax := hProps.2.1
    have hTailLt := hProps.2.2
    let x : Nat → Int := fun idx => T[idx]?.getD 0
    have hx_mem_T : ∀ idx, idx < 11 → x idx ∈ T := fun idx hi => by
      have hLenT : T.length = 11 := rfl
      have : T[idx]? = some T[idx] := List.getElem?_eq_getElem (by omega)
      simp [x, this]
    have hT_sub_D : ∀ z ∈ T, z ∈ D := fun z hz => by
      simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [D]
    have hD_split : ∀ z ∈ D, z ∈ T ∨ z < x0 := fun z hz => by
      simp only [D, List.mem_cons] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|ht
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inl (by simp [T])
      · exact Or.inr (hTailLt z ht)
    have hx0Eq : x 0 = x0 := rfl
    have hx10Eq : x 10 = x10 := rfl
    have hx0Pos : 0 < x 0 := by rw [hx0Eq]; exact hPos x0 (by simp)
    have hInc : ∀ a b, a < b → b < mVal → x a < x b := fun a b hab hb => by
      have ha : a < T.length := by change a < 11; unfold mVal at hb; omega
      have hbT : b < T.length := by change b < 11; unfold mVal at hb; omega
      have h1 : T[a]? = some T[a] := List.getElem?_eq_getElem ha
      have h2 : T[b]? = some T[b] := List.getElem?_eq_getElem hbT
      simp only [x, h1, h2, Option.getD_some]
      exact strictlySorted_getElem T hTSort a b ha hbT hab
    have hPosIdx : ∀ idx, idx < 11 → 0 < x idx := fun idx hi => hPos _ (hT_sub_D _ (hx_mem_T idx hi))
    have hEdgePair : ∀ p q, p < q → q < 10 → (x p + x q) ∈ D → evalVarSpec x (.edge p q) = true := by
      intro p q hpq hq hSumD
      have hpPos := hPosIdx p (by omega)
      have hqPos := hPosIdx q (by omega)
      have hGe0 : x 0 ≤ x q := mono_le_of_strict x hInc 0 q (by omega) (by unfold mVal; omega)
      rcases hD_split (x p + x q) hSumD with hInT | hLt0
      · obtain ⟨l, hlLt, hlEq⟩ := List.mem_iff_getElem.1 hInT
        have hxl : x l = T[l] := by simp [x, List.getElem?_eq_getElem hlLt]
        have hSumEq : x p + x q = x l := hxl.symm ▸ hlEq.symm
        have hql : q < l := by
          by_cases hqlt : q < l
          · exact hqlt
          · exfalso
            have hle := mono_le_of_strict x hInc l q (by omega) (by unfold mVal; omega)
            omega
        unfold evalVarSpec
        rw [List.any_eq_true]
        refine ⟨l, List.mem_range.2 (by unfold mVal; omega), decide_eq_true ⟨hql, hSumEq⟩⟩
      · omega
    have hEdge4 : ∀ s0 s1 s2 s3, s0 < s1 → s1 < s2 → s2 < s3 → s3 < mVal - 1 →
        evalVarSpec x (.edge s0 s1) = true ∨ evalVarSpec x (.edge s0 s2) = true ∨
        evalVarSpec x (.edge s0 s3) = true ∨ evalVarSpec x (.edge s1 s2) = true ∨
        evalVarSpec x (.edge s1 s3) = true ∨ evalVarSpec x (.edge s2 s3) = true := by
      intro s0 s1 s2 s3 h01 h12 h23 h3
      unfold mVal at h3
      have h01' := hInc s0 s1 h01 (by unfold mVal; omega)
      have h12' := hInc s1 s2 h12 (by unfold mVal; omega)
      have h23' := hInc s2 s3 h23 (by unfold mVal; omega)
      have h310 := hInc s3 10 (by omega) (by unfold mVal; omega)
      let B := [x s0, x s1, x s2, x s3, x 10]
      have hBSub : ∀ z ∈ B, z ∈ D := fun z hz => by
        simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl|rfl|rfl|rfl|rfl
        · exact hT_sub_D _ (hx_mem_T s0 (by omega))
        · exact hT_sub_D _ (hx_mem_T s1 (by omega))
        · exact hT_sub_D _ (hx_mem_T s2 (by omega))
        · exact hT_sub_D _ (hx_mem_T s3 (by omega))
        · exact hT_sub_D _ (hx_mem_T 10 (by omega))
      have hBNodup : B.Nodup := by
        simp only [B, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_false_eq_true, List.nodup_nil, and_true]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
      have hNot := hNo5 B hBSub hBNodup rfl
      have hNoTop : ∀ u, u ∈ [s0, s1, s2, s3] → (x u + x 10) ∉ D := fun u hu hmem => by
        have hlt10 : u < 10 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl|rfl|rfl|rfl <;> omega
        have huPos := hPosIdx u (by omega)
        have hle10 := hDMax (x u + x 10) hmem
        rw [hx10Eq] at hle10
        omega
      rcases not_isSumAvoiding_pent hNot with h|h|h|h|h|h|h|h|h|h
      · exact Or.inl (hEdgePair s0 s1 h01 (by omega) h)
      · exact Or.inr (Or.inl (hEdgePair s0 s2 (by omega) (by omega) h))
      · exact Or.inr (Or.inr (Or.inl (hEdgePair s0 s3 (by omega) (by omega) h)))
      · exact absurd h (hNoTop s0 (by simp))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hEdgePair s1 s2 h12 (by omega) h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hEdgePair s1 s3 (by omega) (by omega) h)))))
      · exact absurd h (hNoTop s1 (by simp))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hEdgePair s2 s3 h23 (by omega) h)))))
      · exact absurd h (hNoTop s2 (by simp))
      · exact absurd h (hNoTop s3 (by simp))
    exact m11_no_avoid_5_contradiction x hx0Pos hInc hEdge4

theorem pos_le_10_of_no_5 (P : List Int)
    (hSort : IsStrictlySorted P) (hPos : ∀ x ∈ P, x > 0) (hLen : P.length ≥ 11) :
    ∃ B : List Int, B.Sublist P ∧ B.Nodup ∧ B.length = 5 ∧ IsSumAvoiding P B := by
  by_cases hYes5 : ∃ B : List Int, B.Sublist P ∧ B.Nodup ∧ B.length = 5 ∧ IsSumAvoiding P B
  · exact hYes5
  · exfalso
    have hNo5' : ∀ B : List Int, (∀ x ∈ B, x ∈ P) → B.Nodup → B.length = 5 → ¬ IsSumAvoiding P B := by
      intro B hSub hNd hBLen hAvoid
      obtain ⟨B', hB'sub, hB'nd, hB'len, hIff⟩ := exists_sublist_of_subset P B hNd hSub
      exact hYes5 ⟨B', hB'sub, hB'nd, hB'len.trans hBLen, (isSumAvoiding_congr_mem hIff).2 hAvoid⟩
    let D := P.reverse
    have hDesc : IsStrictlyDesc D := isStrictlyDesc_reverse hSort
    have hDPos : ∀ x ∈ D, x > 0 := fun x hx => hPos x (List.mem_reverse.1 hx)
    have hDLen : D.length ≥ 11 := by simpa [D] using hLen
    have hDNo5 : ∀ B : List Int, (∀ x ∈ B, x ∈ D) → B.Nodup → B.length = 5 → ¬ IsSumAvoiding D B := by
      intro B hSub hNd hBLen hAvoid
      have hSubP : ∀ x ∈ B, x ∈ P := fun x hx => List.mem_reverse.1 (hSub x hx)
      have hAvoidP : IsSumAvoiding P B := fun b1 hb1 b2 hb2 hne hsum =>
        hAvoid b1 hb1 b2 hb2 hne (List.mem_reverse.2 hsum)
      exact hNo5' B hSubP hNd hBLen hAvoidP
    exact pos_desc_no_all_5_avoid D hDesc hDPos hDLen hDNo5


/-! ==================================================================== -/
/-! ### Section 7: Upper Bound `n_max(4) ≤ 21` & Exact `n_max(4) = 21`  -/
/-! ==================================================================== -/

theorem n_max_4_upper (A : List Int) (hNodup : A.Nodup) (hLen : A.length ≥ 22) :
    ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 5 ∧ IsSumAvoiding A B := by
  have hPart := length_pos_neg_zero A
  have hZero := zero_filter_length_le_one A hNodup
  have hSplit : (posPart A).length ≥ 11 ∨ (negPart A).length ≥ 11 := by omega
  rcases hSplit with hPosLen | hNegLen
  · let P := sortAsc (posPart A)
    have hP_sort : IsStrictlySorted P := sortAsc_strictlySorted (posPart A) (posPart_nodup A hNodup)
    have hP_mem : ∀ x, x ∈ P ↔ x ∈ posPart A := sortAsc_mem (posPart A)
    have hP_pos : ∀ x ∈ P, x > 0 := fun x hx => ((posPart_mem_iff A x).1 ((hP_mem x).1 hx)).2
    have hP_len : P.length ≥ 11 := by simpa [P, sortAsc_length] using hPosLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_10_of_no_5 P hP_sort hP_pos hP_len
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
    have hP_len : P.length ≥ 11 := by simpa [P, sortAsc_length] using hNegLen
    obtain ⟨B, hB_subP, hB_nodup, hB_len, hB_avoidP⟩ := pos_le_10_of_no_5 P hP_sort hP_pos hP_len
    have hB_subNeg : ∀ x ∈ B, x ∈ negPart A := fun x hx => (hP_mem x).1 (hB_subP.mem hx)
    have hB_avoidNeg : IsSumAvoiding (negPart A) B := by
      intro b1 hb1 b2 hb2 hne hsum
      exact hB_avoidP b1 hb1 b2 hb2 hne ((hP_mem (b1 + b2)).2 hsum)
    let Bneg := B.map (- ·)
    have hBneg_avoidA : IsSumAvoiding A Bneg := neg_sum_avoiding_lift A B hB_subNeg hB_avoidNeg
    have hBneg_nodup : Bneg.Nodup := hB_nodup.map (- ·) (fun _ _ hne hneg => hne (by omega))
    have hBneg_len : Bneg.length = 5 := by simp [Bneg, hB_len]
    have hBneg_subA : ∀ x ∈ Bneg, x ∈ A := by
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨b, hb, rfl⟩
      exact ((negPart_mem_iff A b).1 (hB_subNeg b hb)).1
    obtain ⟨B', hB'_sub, hB'_nodup, hB'_len, hIff⟩ := exists_sublist_of_subset A Bneg hBneg_nodup hBneg_subA
    exact ⟨B', hB'_sub, hB'_nodup, hB'_len.trans hBneg_len, (isSumAvoiding_congr_mem hIff).2 hBneg_avoidA⟩

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

def A21 : List Int :=
  [-15, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15]

def Cs21 : List (List Int) :=
  [ [-15, 0, 15],
    [-5, -4, -3, -2, -1, 6, 9],
    [-9, -6, 1, 7, 8],
    [-8, -7, 2, 3, 4, 5] ]

theorem A21_card : A21.length = 21 := rfl
theorem A21_nodup : A21.Nodup := by decide
theorem Cs21_valid : isCliqueCoverBool A21 A21 Cs21 = true := by decide

theorem A21_no_sum_avoiding_5 :
    ∀ B : List Int, (∀ x ∈ B, x ∈ A21) → B.Nodup → B.length = 5 → ¬ IsSumAvoiding A21 B := by
  intro B hSub hNd hLen hAvoid
  have h := isCliqueCoverBool_sound A21 A21 Cs21 Cs21_valid
  have hLe := clique_cover_indep_le A21 Cs21 B h.1 (fun x hx => h.2 x (hSub x hx)) hNd hAvoid
  have hCsLen : Cs21.length = 4 := rfl
  omega

/-- Complete exact characterization `n_max(4) = 21` in Pure Lean 4. -/
theorem n_max_4_exact :
    (A21.Nodup ∧ A21.length = 21 ∧
      ∀ B : List Int, (∀ x ∈ B, x ∈ A21) → B.Nodup → B.length = 5 → ¬ IsSumAvoiding A21 B) ∧
    (∀ A : List Int, A.Nodup → A.length ≥ 22 →
      ∃ B : List Int, B.Sublist A ∧ B.Nodup ∧ B.length = 5 ∧ IsSumAvoiding A B) :=
  ⟨⟨A21_nodup, A21_card, A21_no_sum_avoiding_5⟩, n_max_4_upper⟩

end Erdos787Threshold4
