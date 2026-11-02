import CanonicalBalance
import IntegralOrientation
import CarrySelfAdjointOperator.CompletedNativeGeometricLowOrderClosure

namespace CarryCriticalEuler
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryCriticalMixed Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Reuse of the original source inequality from PR43, not a Hankel positivity
premise or a sign assumption on the present curvature. -/
theorem source_second_even_numerator_positive :
    0 < 3*(canonicalCompletedNativeLogDerivativeMoment 1)^3 -
      20*canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 1*
        canonicalCompletedNativeLogDerivativeMoment 2 +
      21*(canonicalCompletedNativeLogDerivativeMoment 0)^2*canonicalCompletedNativeLogDerivativeMoment 3 := by
  let h := canonicalCompletedNativeLogDerivativeMoment
  change 0 < 3*(h 1)^3-20*h 0*h 1*h 2+21*(h 0)^2*h 3
  have h0 : 0<h 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have h1 : 0<h 1 :=
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).2
  have hm := source_nonlinear_margin_pos
  change 0<h 0*h 2-2*(h 1)^2 at hm
  have h2 : 0<h 2 := by nlinarith [sq_nonneg (h 1)]
  have hn := source_correction_numerator_pos
  change 0<2*(h 1)^3-80*h 0*h 1*h 2+28*(h 0)^2*h 3 at hn
  nlinarith [mul_pos (mul_pos h0 h1) h2,pow_pos h1 3]

theorem first_even_prefix_unit :
    IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 1) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simpa [sourceMomentMatrix] using
    (isUnit_iff_ne_zero.mpr (ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos))

theorem second_even_critical_vector :
    canonicalCriticalVector 0 1 =
      ![-canonicalCompletedNativeLogDerivativeMoment 1 / canonicalCompletedNativeLogDerivativeMoment 0,1] := by
  let v := canonicalCriticalVector 0 1
  have hv1 : v 1 = 1 := rfl
  have hr := congrFun (canonical_critical_relation 0 1 first_even_prefix_unit) (0:Fin 2)
  change (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 2 *ᵥ v) 0 = 0 at hr
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,sourceMomentMatrix] at hr
  have h0 := ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hv0 : v 0 = -canonicalCompletedNativeLogDerivativeMoment 1 / canonicalCompletedNativeLogDerivativeMoment 0 := by
    apply (eq_div_iff h0).mpr
    rw [hv1] at hr
    norm_num at hr
    nlinarith
  ext i
  fin_cases i
  · exact hv0
  · exact hv1

theorem second_even_weighted_positive :
    0 < weightedForm canonicalCompletedNativeLogDerivativeMoment 0 (canonicalCriticalVector 0 1) := by
  let h := canonicalCompletedNativeLogDerivativeMoment
  have h0 : h 0 ≠ 0 := ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have he : (h 0)^2*weightedForm h 0 (canonicalCriticalVector 0 1) =
      3*(h 1)^3-20*h 0*h 1*h 2+21*(h 0)^2*h 3 := by
    rw [second_even_critical_vector]
    unfold weightedForm
    simp only [Fin.sum_univ_castSucc]
    norm_num [Fin.last]
    dsimp [h] at h0 ⊢
    field_simp [h0]
    ring
  have hn := source_second_even_numerator_positive
  change 0 < 3*(h 1)^3-20*h 0*h 1*h 2+21*(h 0)^2*h 3 at hn
  have hp := sq_pos_of_ne_zero h0
  change 0 < weightedForm h 0 (canonicalCriticalVector 0 1)
  nlinarith

/-- A finite original-source sign regression for the newly transported sigma
curvature. It is distinct from the radial correction of PR43. -/
theorem second_even_sigma_curvature_negative :
    iteratedDeriv 2 (fun d => sigmaSchur d 0 1) 0 < 0 := by
  rw [canonical_curvature_eq_weighted 0 1 first_even_prefix_unit]
  have h := second_even_weighted_positive
  linarith

end
end CarryCriticalEuler
