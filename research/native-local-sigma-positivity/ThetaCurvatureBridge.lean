import NativeBoundaryBalance
import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import SourceSignRegression

namespace CarryTiltAudit
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryCriticalEuler Matrix
open scoped BigOperators Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The existing theta readouts of all three exact native boundary terms.
This is a polynomial readout after synthesis, not a replacement source. -/
def thetaCurvaturePolynomial (s n : ℕ) : ℝ[X] :=
  ((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3)) •
    nativeThetaQuadraticPolynomial (s+1) (n+2) (canonicalCriticalVector s (n+1)) -
  ((16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*canonicalCriticalVector s (n+1) (Fin.last n).castSucc) •
    nativeThetaQuadraticPolynomial s (n+2) (canonicalCriticalVector s (n+1)) +
  (4:ℝ) • nativeThetaQuadraticPolynomial (s+1) (n+1)
    (eulerResidual n (canonicalCriticalVector s (n+1)))

theorem thetaCurvaturePolynomial_integral (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1))) :
    nativeXiPolynomialIntegral (thetaCurvaturePolynomial s n) =
      weightedForm canonicalCompletedNativeLogDerivativeMoment s (canonicalCriticalVector s (n+1)) := by
  simp only [thetaCurvaturePolynomial,map_add,map_sub,map_smul,smul_eq_mul,
    nativeThetaQuadraticPolynomial_integral]
  have hQ : sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s (n+2)
      (canonicalCriticalVector s (n+1)) =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s (n+1) :=
    NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit _ _ _ hA
  rw [hQ]
  exact (canonical_weighted_reduction s n hA).symm

theorem sigmaCurvature_eq_thetaIntegral (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1))) :
    iteratedDeriv 2 (fun d => sigmaSchur d s (n+1)) 0 =
      -2*nativeXiPolynomialIntegral (thetaCurvaturePolynomial s n) := by
  rw [thetaCurvaturePolynomial_integral s n hA,canonical_curvature_eq_weighted s (n+1) hA]

theorem sigmaCurvature_negative_iff_thetaDominance (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1))) :
    iteratedDeriv 2 (fun d => sigmaSchur d s (n+1)) 0 < 0 ↔
      nativeThetaNegativeMass (thetaCurvaturePolynomial s n) <
        nativeThetaPositiveMass (thetaCurvaturePolynomial s n) := by
  rw [sigmaCurvature_eq_thetaIntegral s n hA,nativeXiPolynomialIntegral_eq_masses]
  constructor <;> intro h <;> linarith

/-- This algebraic expression is the fourth centered cumulant once the
normalized symmetric theta probability measure and its moments are supplied. -/
def normalizedThetaFourthExpression : ℝ :=
  completedNativeXiCosineMoment 2 / completedNativeXiCosineMoment 0 -
    3*(completedNativeXiCosineMoment 1 / completedNativeXiCosineMoment 0)^2

theorem normalizedThetaFourthExpression_eq_h1 :
    normalizedThetaFourthExpression = -12*canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment]
  unfold normalizedThetaFourthExpression
  have h0 : completedNativeXiCosineMoment 0 ≠ 0 :=
    ne_of_gt (completedNativeXiCosineMoment_pos 0)
  field_simp [h0]
  ring

theorem normalizedThetaFourthExpression_negative : normalizedThetaFourthExpression < 0 := by
  rw [normalizedThetaFourthExpression_eq_h1]
  have h1 := (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).2
  linarith

#print axioms normalizedThetaFourthExpression_eq_h1
#print axioms normalizedThetaFourthExpression_negative

#print axioms thetaCurvaturePolynomial_integral
#print axioms sigmaCurvature_eq_thetaIntegral
#print axioms sigmaCurvature_negative_iff_thetaDominance
end
end CarryTiltAudit
