import EightHead
import SchurLogic

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open NativeMomentOrthogonalization Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

def eightOldMatrix := sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 3
def eightCoupling := sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 3
def eightCriticalVector : Fin 3 → ℝ := ![critical0,critical1,critical2]

theorem eight_old_matrix_det : eightOldMatrix.det = oldDet := by
  rw [Matrix.det_fin_three]
  simp [eightOldMatrix,sourceMomentMatrix,oldDet,det3]
  ring

theorem eight_old_matrix_isUnit : IsUnit eightOldMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [eight_old_matrix_det]
  exact isUnit_iff_ne_zero.mpr old_det_positive.ne'

theorem eight_critical_vector_equation : eightOldMatrix *ᵥ eightCriticalVector = -eightCoupling := by
  obtain ⟨h0,h1,h2⟩ := eight_critical_old_rows
  ext i
  fin_cases i <;>
    simp [eightOldMatrix,eightCriticalVector,eightCoupling,sourceMomentMatrix,sourceMomentCoupling,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> linarith

theorem eight_critical_vector_eq_inverse :
    eightCriticalVector = -(eightOldMatrix⁻¹ *ᵥ eightCoupling) := by
  letI := eight_old_matrix_isUnit.invertible
  have he := congrArg (fun x => eightOldMatrix⁻¹ *ᵥ x) eight_critical_vector_equation
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec, Matrix.mulVec_neg] at he
  exact he

theorem eight_form_eq_source_quadratic :
    oddCanonicalForm eightOrders eightCoefficients =
      sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 4 (Fin.snoc eightCriticalVector 1) := by
  simp [oddCanonicalForm,eightOrders,eightCoefficients,sourceMomentQuadratic,sourceMomentMatrix,
    eightCriticalVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Finset.sum_range_succ,
    Fin.snoc]
  ring

/-- Exact use of the #41 Schur sewing: no positive pivot is assumed. -/
theorem eight_form_eq_original_schur : oddCanonicalForm eightOrders eightCoefficients =
    sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 3 := by
  rw [eight_form_eq_source_quadratic,eight_critical_vector_eq_inverse]
  exact sourceMomentSchur_critical_direction_of_isUnit _ _ _ eight_old_matrix_isUnit

end
end CarryCriticalRadialMargin
