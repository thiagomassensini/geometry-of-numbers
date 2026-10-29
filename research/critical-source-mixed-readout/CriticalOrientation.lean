import SecondEvenLimit
import IntegralOrientation
import MixedCritical

namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative Filter Topology
open scoped BigOperators Matrix InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def secondCriticalParameter : ℝ := -h 1/h 0

theorem sourceCoefficient_eq_canonical (j : ℕ) : sourceCoefficient j = 2*h j := by
  change nativeSourceOddBoundaryCoefficient j = 2*h j
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]

theorem second_old_posDef : (sourceMomentMatrix h 0 1).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian _ _ _)
  intro x hx
  have hx0 : x 0 ≠ 0 := by
    intro hz
    apply hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi,hz]
  change 0 < x ⬝ᵥ (sourceMomentMatrix h 0 1 *ᵥ x)
  simp only [dotProduct, Matrix.mulVec, sourceMomentMatrix, Fin.sum_univ_one,
    Fin.val_zero, Nat.add_zero]
  nlinarith [canonicalCompletedNativeLogDerivativeMoment_zero_pos, sq_pos_of_ne_zero hx0]

theorem second_old_solve :
    ((sourceMomentMatrix h 0 1)⁻¹ *ᵥ sourceMomentCoupling h 0 1) 0 = h 1/h 0 := by
  let u := (sourceMomentMatrix h 0 1)⁻¹ *ᵥ sourceMomentCoupling h 0 1
  letI := second_old_posDef.isUnit.invertible
  have hu : sourceMomentMatrix h 0 1 *ᵥ u = sourceMomentCoupling h 0 1 := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hu0 := congrFun hu 0
  simp only [Matrix.mulVec, dotProduct, sourceMomentMatrix, sourceMomentCoupling,
    Fin.sum_univ_one, Fin.val_zero, Nat.zero_add, Nat.add_zero] at hu0
  apply (eq_div_iff canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne').mpr
  change u 0*h 0 = h 1
  linarith

theorem second_critical_coordinates : criticalCoordinates 0 1 = secondEvenJet secondCriticalParameter := by
  funext i
  fin_cases i
  all_goals
    norm_num [criticalCoordinates, parityCoordinates, criticalCoefficients,
      nativeSourceBoundaryFromParity, secondEvenJet, secondCriticalParameter, Fin.snoc,
      Matrix.mulVec, Matrix.diagonal, sourceMomentMatrix, sourceMomentCoupling, dotProduct,
      Fin.sum_univ_one]
  all_goals push_cast
  all_goals ring

theorem second_critical_balance_exact (k : ℕ) :
    criticalBalance 0 1 k = secondBalance secondCriticalParameter k := by
  rw [criticalBalance_eq_storage]
  simp only [criticalInput, second_critical_coordinates, secondBalance]

theorem second_pivot_formula : sourceMomentSchur h 0 1 = h 2-(h 1)^2/h 0 := by
  unfold sourceMomentSchur
  simp only [Nat.mul_one, Nat.add_zero, dotProduct, Fin.sum_univ_one,
    sourceMomentCoupling, Fin.val_zero, Nat.zero_add, Nat.add_zero, second_old_solve]
  ring

theorem second_constant_eq_pivot :
    balanceConstant secondCriticalParameter = 2*sourceMomentSchur h 0 1 := by
  rw [second_pivot_formula]
  unfold balanceConstant secondCriticalParameter
  simp_rw [sourceCoefficient_eq_canonical]
  field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  ring

theorem second_correction_formula :
    balanceCorrection secondCriticalParameter =
      -(2*(h 1)^3-80*h 0*h 1*h 2+28*(h 0)^2*h 3)/(h 0)^2 := by
  unfold balanceCorrection secondCriticalParameter
  simp_rw [sourceCoefficient_eq_canonical]
  field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  ring

theorem second_correction_neg : balanceCorrection secondCriticalParameter < 0 := by
  rw [second_correction_formula]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos source_correction_numerator_pos)
    (sq_pos_of_pos canonicalCompletedNativeLogDerivativeMoment_zero_pos)

/-- A stronger source inequality than positivity of the second Hankel pivot. -/
theorem second_pivot_source_pos : 0 < sourceMomentSchur h 0 1 := by
  rw [second_pivot_formula]
  apply (sub_pos.mpr ((div_lt_iff₀ canonicalCompletedNativeLogDerivativeMoment_zero_pos).mpr ?_))
  nlinarith [source_nonlinear_margin_pos, sq_nonneg (h 1)]

/-- Actual incident-return balance, with its complete source remainder. -/
theorem second_critical_correction_tendsto :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance 0 1 k-2*sourceMomentSchur h 0 1))
      atTop (nhds (balanceCorrection secondCriticalParameter)) := by
  simpa only [second_critical_balance_exact, second_constant_eq_pivot] using
    second_balance_correction_tendsto secondCriticalParameter

/-- Positive balance approaching its limiting pivot from below. This does
not assert monotonicity, a numerical cutoff, or an all-order sign. -/
theorem second_critical_between_zero_and_limit :
    ∀ᶠ k : ℕ in atTop, 0 < criticalBalance 0 1 k ∧
      criticalBalance 0 1 k < 2*sourceMomentSchur h 0 1 := by
  have hp := (tendsto_order.mp (critical_balance_tendsto_of_isUnit 0 1
    second_old_posDef.isUnit)).1 0 (by nlinarith [second_pivot_source_pos] : 0 < 2*sourceMomentSchur h 0 1)
  have hn := (tendsto_order.mp second_critical_correction_tendsto).2 0 second_correction_neg
  filter_upwards [hp,hn] with k hk0 hk1
  refine ⟨hk0,?_⟩
  have hK : 0 < ((k:ℝ)+1)^2 := by positivity
  have hd : criticalBalance 0 1 k-2*sourceMomentSchur h 0 1 < 0 := by
    by_contra hz
    have hp := mul_nonneg hK.le (le_of_not_gt hz)
    linarith
  linarith

end
end CarryCriticalMixed
