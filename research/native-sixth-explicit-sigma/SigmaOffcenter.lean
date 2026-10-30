import SigmaGreenCurvature
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Derivative of the actual log modulus squared along a horizontal height
variation, with no restriction on the phase of the completed source. -/
theorem log_density_hasDerivAt (d t : ℝ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d t))
    (hne : completedSigmaResponse d t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (completedSigmaDensity d x))
      (2*(deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
        completedSigmaResponse d t).re) t := by
  have hs : HasDerivAt (fun z : ℂ => z - Complex.I*(d:ℂ)) 1 (t:ℂ) := by
    simpa using (hasDerivAt_id (t:ℂ)).sub_const (Complex.I*(d:ℂ))
  have hc := ha.differentiableAt.hasDerivAt.comp (t:ℂ) hs
  have hr : HasDerivAt (fun x : ℝ => completedSigmaResponse d x)
      (deriv completedNativeOperatorCharacteristic (displacedHeight d t)) t := by
    simpa [completedSigmaResponse,displacedHeight] using hc.comp_ofReal
  have hnorm : completedSigmaDensity d t ≠ 0 := by
    unfold completedSigmaDensity
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hd := hr.norm_sq.log hnorm
  have he : (2 * inner ℝ (completedSigmaResponse d t)
        (deriv completedNativeOperatorCharacteristic (displacedHeight d t))) /
      completedSigmaDensity d t =
      2*(deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
        completedSigmaResponse d t).re := by
    rw [Complex.inner,Complex.div_re]
    unfold completedSigmaDensity
    rw [Complex.sq_norm]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  rw [← he]
  exact hd

end
end CarrySigmaSource
