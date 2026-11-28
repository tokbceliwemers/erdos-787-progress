import Init

namespace Erdos787MixedRadixCounterexample

abbrev Vec3 := Int × Int × Int

def normSq (v : Vec3) : Int :=
  v.1 * v.1 + v.2.1 * v.2.1 + v.2.2 * v.2.2

def scalar (v : Vec3) : Int := v.1 + 2 * v.2.1 + 8 * v.2.2

def digits : List Int := [-1, 0, 1]

def cube : List Vec3 :=
  digits.flatMap fun x =>
    digits.flatMap fun y =>
      digits.map fun z => (x, y, z)

def ball (r : Int) : List Vec3 :=
  cube.filter fun v => decide (normSq v ≤ r)

/-- The three layers for `K = 1`, `L = 4`: squared radii `2, 1, 0`. -/
def host : List Int :=
  (ball 2).map scalar ++
    (ball 1).map (fun v => 2 * scalar v) ++
    (ball 0).map (fun v => 4 * scalar v)

def x : Vec3 := (0, 0, 1)
def y : Vec3 := (0, 1, 1)
def kernelCorrection : Vec3 := (2, -1, 0)

def parity (v : Vec3) : Vec3 := (v.1 % 2, v.2.1 % 2, v.2.2 % 2)

theorem pair_and_kernel_checks :
    normSq x ≤ 2 ∧ normSq y ≤ 2 ∧
    scalar x = 8 ∧ scalar y = 10 ∧
    scalar kernelCorrection = 0 ∧ normSq kernelCorrection = 5 := by
  decide

theorem kernel_correction_matches_parity :
    parity (y.1 - x.1, y.2.1 - x.2.1, y.2.2 - x.2.2) = parity kernelCorrection := by
  decide

theorem corrected_midpoint_norms :
    normSq (1, 0, 1) = 2 ∧ normSq (-1, 1, 1) = 3 := by
  decide

theorem host_sum_absent : 18 ∉ host := by
  decide

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases ha : 0 ≤ a
  · exact Int.mul_nonneg ha ha
  · have hna : 0 ≤ -a := by omega
    have heq : a * a = (-a) * (-a) := (Int.neg_mul_neg a a).symm
    rw [heq]
    exact Int.mul_nonneg hna hna

theorem int_eq_neg_one_zero_one_of_sq_le_two (a : Int) (h : a * a ≤ 2) :
    a = -1 ∨ a = 0 ∨ a = 1 := by
  have hlo : -1 ≤ a := by
    by_cases h' : -1 ≤ a
    · exact h'
    · have hneg : a ≤ -2 := by omega
      have hnonneg : 0 ≤ -a := by omega
      have hsquare : 2 * 2 ≤ (-a) * (-a) :=
        Int.mul_self_le_mul_self (by omega) (by omega)
      have heq : a * a = (-a) * (-a) := (Int.neg_mul_neg a a).symm
      omega
  have hhi : a ≤ 1 := by
    by_cases h' : a ≤ 1
    · exact h'
    · have hpos : 2 ≤ a := by omega
      have hsquare : 2 * 2 ≤ a * a :=
        Int.mul_self_le_mul_self (by omega) hpos
      omega
  omega

theorem cube_complete_for_radius_two (v : Vec3) (h : normSq v ≤ 2) : v ∈ cube := by
  rcases v with ⟨a, b, c⟩
  simp only [normSq] at h
  have hbnn : 0 ≤ b * b := int_sq_nonneg b
  have hcnn : 0 ≤ c * c := int_sq_nonneg c
  have hann : 0 ≤ a * a := int_sq_nonneg a
  have ha : a * a ≤ 2 := by omega
  have hb : b * b ≤ 2 := by omega
  have hc : c * c ≤ 2 := by omega
  rcases int_eq_neg_one_zero_one_of_sq_le_two a ha with rfl | rfl | rfl <;>
    rcases int_eq_neg_one_zero_one_of_sq_le_two b hb with rfl | rfl | rfl <;>
    rcases int_eq_neg_one_zero_one_of_sq_le_two c hc with rfl | rfl | rfl <;>
    simp [cube, digits]

theorem mem_ball_of_normSq_le_two (v : Vec3) (r : Int)
    (hr : normSq v ≤ r) (hr2 : r ≤ 2) : v ∈ ball r := by
  apply List.mem_filter.mpr
  exact ⟨cube_complete_for_radius_two v (by omega), by simp [hr]⟩

theorem layer_zero_value_mem_host (v : Vec3) (h : normSq v ≤ 2) : scalar v ∈ host := by
  have hv : v ∈ ball 2 := mem_ball_of_normSq_le_two v 2 h (by omega)
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨v, hv, rfl⟩

theorem layer_one_value_mem_host (v : Vec3) (h : normSq v ≤ 1) :
    2 * scalar v ∈ host := by
  have hv : v ∈ ball 1 := mem_ball_of_normSq_le_two v 1 h (by omega)
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨v, hv, rfl⟩

theorem layer_two_value_mem_host (v : Vec3) (h : normSq v ≤ 0) :
    4 * scalar v ∈ host := by
  have hv : v ∈ ball 0 := mem_ball_of_normSq_le_two v 0 h (by omega)
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨v, hv, rfl⟩

theorem pair_values_are_distinct_and_in_host :
    scalar x ≠ scalar y ∧ scalar x ∈ host ∧ scalar y ∈ host := by
  refine ⟨by decide, ⟨?_, ?_⟩⟩
  · exact layer_zero_value_mem_host x (by decide)
  · exact layer_zero_value_mem_host y (by decide)

theorem no_layer_zero_witness (v : Vec3) (hnorm : normSq v ≤ 2)
    (hvalue : scalar v = 18) : False := by
  have hmem := layer_zero_value_mem_host v hnorm
  rw [hvalue] at hmem
  exact host_sum_absent hmem

theorem no_layer_one_witness (v : Vec3) (hnorm : normSq v ≤ 1)
    (hvalue : 2 * scalar v = 18) : False := by
  have hmem := layer_one_value_mem_host v hnorm
  rw [hvalue] at hmem
  exact host_sum_absent hmem

theorem no_layer_two_witness (v : Vec3) (hnorm : normSq v ≤ 0)
    (hvalue : 4 * scalar v = 18) : False := by
  have hmem := layer_two_value_mem_host v hnorm
  rw [hvalue] at hmem
  exact host_sum_absent hmem

theorem pair_sum_is_not_in_any_layer :
    ∀ (v : Vec3), normSq v ≤ 2 → scalar v ≠ 18 ∧
      (normSq v ≤ 1 → 2 * scalar v ≠ 18) ∧
      (normSq v ≤ 0 → 4 * scalar v ≠ 18) := by
  intro v h2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact no_layer_zero_witness v h2 h
  · intro h1 h
    exact no_layer_one_witness v h1 h
  · intro h0 h
    exact no_layer_two_witness v h0 h

end Erdos787MixedRadixCounterexample
