import CarrySelfAdjointOperator.NativeCauchyLaguerreIsometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CarryVerticalSynthesis
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- A telescoping majorant for the unchanged Cauchy kernel. -/
theorem cauchy_weight_step (i j : ℕ) :
    (((i + j + 2 : ℕ) : ℝ) * Real.sqrt (j + 1))⁻¹ ≤
      4 * ((Real.sqrt (i + 1) + Real.sqrt j)⁻¹ -
        (Real.sqrt (i + 1) + Real.sqrt (j + 1))⁻¹) := by
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have ha := Real.sqrt_pos.2 hi
  have hb := Real.sqrt_pos.2 hj
  have hc := Real.sqrt_nonneg (j : ℝ)
  have hab : 0 < Real.sqrt ((i : ℝ) + 1) + Real.sqrt ((j : ℝ) + 1) := by positivity
  have hac : 0 < Real.sqrt ((i : ℝ) + 1) + Real.sqrt (j : ℝ) := by positivity
  have ha2 := Real.sq_sqrt hi.le
  have hb2 := Real.sq_sqrt hj.le
  have hc2 := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hcb : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have h1 : 1 ≤ 2 * Real.sqrt ((j : ℝ) + 1) *
      (Real.sqrt ((j : ℝ) + 1) - Real.sqrt (j : ℝ)) := by nlinarith
  have h2 : (Real.sqrt ((i : ℝ) + 1) + Real.sqrt (j : ℝ)) *
      (Real.sqrt ((i : ℝ) + 1) + Real.sqrt ((j : ℝ) + 1)) ≤
      2 * ((i : ℝ) + (j : ℝ) + 2) := by
    nlinarith [sq_nonneg (Real.sqrt ((i : ℝ) + 1) - Real.sqrt ((j : ℝ) + 1))]
  have hk : (0 : ℝ) < (i : ℝ) + (j : ℝ) + 2 := by positivity
  push_cast
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right h1 (le_of_lt hk),
    mul_le_mul_of_nonneg_right h2
      (mul_nonneg hb.le (sub_nonneg.mpr hcb))]

theorem cauchy_weight_row_range (i n : ℕ) :
    (∑ j ∈ Finset.range n,
      (((i + j + 2 : ℕ) : ℝ) * Real.sqrt (j + 1))⁻¹) ≤
      4 * (Real.sqrt (i + 1))⁻¹ := by
  have ht : (∑ j ∈ Finset.range n,
      ((Real.sqrt (i + 1) + Real.sqrt j)⁻¹ -
        (Real.sqrt (i + 1) + Real.sqrt (j + 1))⁻¹)) =
      (Real.sqrt (i + 1))⁻¹ -
        (Real.sqrt (i + 1) + Real.sqrt n)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        4 * ((Real.sqrt (i + 1) + Real.sqrt j)⁻¹ -
          (Real.sqrt (i + 1) + Real.sqrt (j + 1))⁻¹) :=
      Finset.sum_le_sum fun j _ => cauchy_weight_step i j
    _ = 4 * ((Real.sqrt (i + 1))⁻¹ -
        (Real.sqrt (i + 1) + Real.sqrt n)⁻¹) := by rw [← Finset.mul_sum, ht]
    _ ≤ _ := by
      have h : 0 ≤ (Real.sqrt (i + 1) + Real.sqrt n)⁻¹ := by positivity
      linarith

theorem cauchy_weight_row (i : ℕ) (s : Finset ℕ) :
    (∑ j ∈ s, (((i + j + 2 : ℕ) : ℝ) * Real.sqrt (j + 1))⁻¹) ≤
      4 * (Real.sqrt (i + 1))⁻¹ := by
  obtain ⟨n, hn⟩ := s.exists_nat_subset_range
  exact (Finset.sum_le_sum_of_subset_of_nonneg hn (fun j _ _ => by positivity)).trans
    (cauchy_weight_row_range i n)

private theorem weighted_young (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * a * b ≤ a ^ 2 / u * v + b ^ 2 / v * u := by
  apply (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp
  field_simp
  nlinarith [sq_nonneg (a * v - b * u)]

theorem cauchy_quadratic_bound (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * (((i + j + 2 : ℕ) : ℝ))⁻¹) ≤
      4 * ∑ i ∈ s, (a i) ^ 2 := by
  let w : ℕ → ℝ := fun i => (Real.sqrt (i + 1))⁻¹
  have hw (i : ℕ) : 0 < w i := by dsimp [w]; positivity
  have hrow (i : ℕ) :
      (∑ j ∈ s, (((i + j + 2 : ℕ) : ℝ))⁻¹ * w j) ≤ 4 * w i := by
    simpa only [w, mul_inv] using cauchy_weight_row i s
  have hsym : (∑ i ∈ s, ∑ j ∈ s,
      ((a j) ^ 2 / w j * w i) * (((i + j + 2 : ℕ) : ℝ))⁻¹) =
      ∑ i ∈ s, ∑ j ∈ s,
        ((a i) ^ 2 / w i * w j) * (((i + j + 2 : ℕ) : ℝ))⁻¹ := by
    rw [Finset.sum_comm]
    congr 1; ext i
    congr 1; ext j
    rw [Nat.add_comm j i]
  have hbound : (∑ i ∈ s, ∑ j ∈ s,
      ((a i) ^ 2 / w i * w j) * (((i + j + 2 : ℕ) : ℝ))⁻¹) ≤
      4 * ∑ i ∈ s, (a i) ^ 2 := by
    calc
      _ = ∑ i ∈ s, (a i) ^ 2 / w i *
          (∑ j ∈ s, (((i + j + 2 : ℕ) : ℝ))⁻¹ * w j) := by
        simp only [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; ring
      _ ≤ ∑ i ∈ s, (a i) ^ 2 / w i * (4 * w i) := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_left (hrow i) (by positivity)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        field_simp [(hw i).ne']
  have hy := Finset.sum_le_sum (s := s) fun i _ =>
    Finset.sum_le_sum (s := s) fun j _ =>
      mul_le_mul_of_nonneg_right (weighted_young (a i) (a j) (w i) (w j) (hw i) (hw j))
        (by positivity : 0 ≤ (((i + j + 2 : ℕ) : ℝ))⁻¹)
  simp only [add_mul, Finset.sum_add_distrib] at hy
  rw [hsym] at hy
  have hdouble : (∑ i ∈ s, ∑ j ∈ s,
      2 * a i * a j * (((i + j + 2 : ℕ) : ℝ))⁻¹) =
      2 * ∑ i ∈ s, ∑ j ∈ s, a i * a j * (((i + j + 2 : ℕ) : ℝ))⁻¹ := by
    simp only [Finset.mul_sum]; congr 1; ext i; congr 1; ext j; ring
  rw [hdouble] at hy
  linarith

end
end CarryVerticalSynthesis
