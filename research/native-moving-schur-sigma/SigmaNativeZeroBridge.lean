import SigmaNativeContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Minimal zero bridge for the original completed characteristic

This file extracts the strip-local factor argument used by
`SigmaRHHeightBridge`. It does not import the height-50 zero count or the
Padé isolation chain. The continuation is identified with the original native
characteristic only in the genuine critical strip.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false

lemma sigmaNativeCompletionFactor_ne_zero_of_strip {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    nativeXiCompletionFactor z ≠ 0 := by
  let s := operatorHeightParameter z
  have hsre : 0 < s.re := by simpa [s] using hs.1
  have hsrlt : s.re < 1 := by simpa [s] using hs.2
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith [hsre]
  have hs1 : s ≠ 1 := by
    intro h
    have hr : s.re = 1 := by simpa using congrArg Complex.re h
    linarith [hsrlt]
  have hg : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [Complex.div_re]
    norm_num
    linarith [hsre]
  have he : Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  unfold nativeXiCompletionFactor
  change (1 / 2 : ℂ) * s * (s - 1) *
    Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) * Complex.Gamma (s / 2) ≠ 0
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact hs0
      · exact sub_ne_zero.mpr hs1
    · exact he
  · exact hg

/-- In the genuine critical strip, the continuation has exactly the zeros of
Mathlib's zeta. This is the strip-local bridge from the original Carry source;
no global equality outside its proven domain is used. -/
theorem completedNativeCharacteristicContinuation_zero_iff_zeta
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeCharacteristicContinuation z = 0 ↔
      riemannZeta (operatorHeightParameter z) = 0 := by
  rw [completedNativeCharacteristicContinuation_eq_native hs,
    completedNativeOperatorCharacteristic_eq_completedRiemannZeta hs]
  simp [sigmaNativeCompletionFactor_ne_zero_of_strip hs]

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.completedNativeCharacteristicContinuation_eq_native
#print axioms CarrySigmaObstruction.completedNativeCharacteristicContinuation_zero_iff_zeta
