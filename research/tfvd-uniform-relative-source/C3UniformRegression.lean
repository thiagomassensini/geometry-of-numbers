import RepartitionBudget
import NativeRepartition64

namespace CarryUniformSource
open CarrySourceBezout CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem c3_repartition_head : repHead 64 (originalBoundaryJet 64) = regroupedHead64 := rfl

theorem c3_repartition_tail : repTail 64 (originalBoundaryJet 64) = regroupedTail64 := rfl

theorem c3_normalized_error_upper :
    repNormalizedError 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 2 ≤ (1/10^13:ℝ) := by
  have h := native_regrouped64_error_upper 1 (by norm_num)
  have hvec : twoMonic 1 = (fun _ : Fin 2 => (1:ℝ)) := by
    funext i
    fin_cases i <;> norm_num [twoMonic]
  rw [hvec] at h
  simpa [repNormalizedError,repError,splitErrorBudget,c3_repartition_head,c3_repartition_tail] using h

theorem c3_critical_mass_bound : coordMass (monicSourceDirection nativeC nativeH 0 1) ≤ 2 := by
  rw [native_monic_two_direction native_even_one_isUnit_from_source]
  simp [coordMass,Fin.sum_univ_two,twoMonic]
  have hb := native_monic_two_coordinate_bound
  simp only [neg_mul] at hb
  linarith

theorem c3_uniform_head_bound (x : Fin 2 → ℝ) (hx : x (Fin.last 1) = 1)
    (hmass : coordMass x ≤ 2) :
    repNormalizedError 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 2 * (2:ℝ)^2 <
      (coefficientPair (repHead 64 (originalBoundaryJet 64))
        (repHead 64 (originalBoundaryJet 64)) false 2 x x).re := by
  have hx1 : x 1 = 1 := hx
  have hx0 : |x 0| ≤ 1 := by
    simp [coordMass,Fin.sum_univ_two,hx1] at hmass
    linarith
  have hxvec : x = twoMonic (x 0) := by
    funext i
    fin_cases i <;> simp [twoMonic,hx1]
  have hh := native_regrouped64_head_lower (x 0) hx0
  rw [← hxvec] at hh
  simp only [c3_repartition_head]
  have he := c3_normalized_error_upper
  norm_num at he ⊢
  linarith

theorem c3_second_pivot_pos_via_uniform_budget : 0 < sourceMomentSchur nativeH 0 1 := by
  apply critical_positive_of_repartition_head 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 1 2
    native_even_one_isUnit_from_source c3_critical_mass_bound
  exact c3_uniform_head_bound

/-- Quantitative regression using only the previously certified original C3
head and tail, with the looser uniform coefficient budget. -/
theorem c3_second_scaled_margin_via_uniform_budget :
    (1/10^8-4/10^13:ℝ) < (nativeC 0)^2 * sourceMomentSchur nativeH 0 1 := by
  let z := monicSourceDirection nativeC nativeH 0 1
  have hz : coordMass z ≤ 2 := c3_critical_mass_bound
  have hzpos : 0 ≤ coordMass z := coordMass_nonneg z
  have hzsq : (coordMass z)^2 ≤ (4:ℝ) := by nlinarith
  have he := c3_normalized_error_upper
  have heprod : repNormalizedError 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 2 *
      (coordMass z)^2 ≤ (1/10^13:ℝ)*4 := by
    exact mul_le_mul he hzsq (sq_nonneg _) (by norm_num)
  have hb := (abs_le.mp (repartition_critical_error_bound 64 64 (originalBoundaryJet 64)
    (originalBoundaryJet 64) false 1 native_even_one_isUnit_from_source)).1
  simp only [c3_repartition_head] at hb
  change -(repNormalizedError 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 2 *
      (coordMass z)^2) ≤ (nativeC 0)^2 * sourceMomentSchur nativeH 0 1 -
      (coefficientPair regroupedHead64 regroupedHead64 false 2 z z).re at hb
  have hh := native_regrouped64_head_lower (-(2:ℝ)*nativeC 2/nativeC 1) native_monic_two_coordinate_bound
  rw [← native_monic_two_direction native_even_one_isUnit_from_source] at hh
  change (1/10^8:ℝ) < (coefficientPair regroupedHead64 regroupedHead64 false 2 z z).re at hh
  norm_num at heprod hh ⊢
  linarith

#print axioms c3_second_scaled_margin_via_uniform_budget

#print axioms c3_second_pivot_pos_via_uniform_budget
end
end CarryUniformSource
