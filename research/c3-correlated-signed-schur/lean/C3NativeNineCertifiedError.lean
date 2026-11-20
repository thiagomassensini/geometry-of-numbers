import C3QuadraticRational384

/-!
At order n=9, the true completed native response uses 10×10 and 11×11
source blocks. Both are covered by the SAME 23 original C3/384 tail jets.
These are finite-source error theorems, NOT positivity assertions.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 900000

theorem native_even_nine_c3_signed_error
    (v : Fin 10 → ℝ) (alpha betaA : ℝ) :
    |alpha * matrixPair (sourceMomentMatrix nativeH 1 10) v v -
      betaA * matrixPair (sourceMomentMatrix nativeH 0 10) v v -
      (signedSourcePair alpha betaA true false 10 10
        (mixedSourceLift 10 v) (mixedSourceLift 10 v)
        originalC3Head384Nat originalC3Head384Nat).re| ≤
      (∑ j : Fin 23,
        ‖signedImpulseCoefficient 23 alpha betaA true false 10 10
            (mixedSourceLift 10 v) (mixedSourceLift 10 v)
            originalC3Head384Nat j‖ * originalC3Box384 j) +
      signedQuadraticRational384 alpha betaA true false 10 10
        (mixedSourceLift 10 v) (mixedSourceLift 10 v) := by
  have hb := original_c3_joint_source_budget384_rational
    alpha betaA true false 10 10 (mixedSourceLift 10 v) (mixedSourceLift 10 v)
    (by norm_num) (by norm_num)
  have ht := signed_source_native_even 9 v alpha betaA
  rw [← ht] at hb
  have hr := Complex.abs_re_le_norm
    (((alpha * matrixPair (sourceMomentMatrix nativeH 1 10) v v -
       betaA * matrixPair (sourceMomentMatrix nativeH 0 10) v v : ℝ):ℂ) -
      signedSourcePair alpha betaA true false 10 10
        (mixedSourceLift 10 v) (mixedSourceLift 10 v)
        originalC3Head384Nat originalC3Head384Nat)
  simpa only [Complex.sub_re, Complex.ofReal_re] using hr.trans hb

theorem native_odd_nine_c3_signed_error
    (v : Fin 10 → ℝ) (alpha betaA : ℝ) :
    |alpha * matrixPair (sourceMomentMatrix nativeH 2 10) v v -
      betaA * matrixPair (sourceMomentMatrix nativeH 1 10) v v -
      (signedSourcePair alpha betaA false true 11 10
        (mixedSourceLift 11 (Fin.cons 0 v)) (mixedSourceLift 10 v)
        originalC3Head384Nat originalC3Head384Nat).re| ≤
      (∑ j : Fin 23,
        ‖signedImpulseCoefficient 23 alpha betaA false true 11 10
            (mixedSourceLift 11 (Fin.cons 0 v)) (mixedSourceLift 10 v)
            originalC3Head384Nat j‖ * originalC3Box384 j) +
      signedQuadraticRational384 alpha betaA false true 11 10
        (mixedSourceLift 11 (Fin.cons 0 v)) (mixedSourceLift 10 v) := by
  have hb := original_c3_joint_source_budget384_rational
    alpha betaA false true 11 10
    (mixedSourceLift 11 (Fin.cons 0 v)) (mixedSourceLift 10 v)
    (by norm_num) (by norm_num)
  have ht := signed_source_native_odd 9 v alpha betaA
  rw [← ht] at hb
  have hr := Complex.abs_re_le_norm
    (((alpha * matrixPair (sourceMomentMatrix nativeH 2 10) v v -
       betaA * matrixPair (sourceMomentMatrix nativeH 1 10) v v : ℝ):ℂ) -
      signedSourcePair alpha betaA false true 11 10
        (mixedSourceLift 11 (Fin.cons 0 v)) (mixedSourceLift 10 v)
        originalC3Head384Nat originalC3Head384Nat)
  simpa only [Complex.sub_re, Complex.ofReal_re] using hr.trans hb

end
end CarrySourceBezout
