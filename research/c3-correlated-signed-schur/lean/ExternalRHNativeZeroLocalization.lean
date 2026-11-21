import CarrySelfAdjointOperator.ConditionalCriticalLineConfinement

/-!
## External RH theorem -> original completed-native zero localization

The external 2026 Lean formalization by Levent Alpöge + Claude,
separately independently verified by Sutherland's MIT checks, proves
Mathlib's own RiemannHypothesis. This module DOES NOT IMPORT the
17-million-line proof (which is on Lean v4.33.1 while CSA uses 4.32).
Instead it proves the exact INTERFACE for injecting that theorem,
with RH as a transparent hypothesis and the REAL original
native completion N, F=A*N.

It proves zero localization of native F, not PSD of its canonical
moment Hankels or positivity of a particular TFVD Green state.
No new axioms are declared.
-/

namespace CarryWheelNativeSignedGate

open CarrySelfAdjointOperator CPFormal.Analytic.Cp
noncomputable section

/-- Mathlib's RH, together with the existing Genuine/native identification,
forces every original COMPLETED native zero in the critical strip
to lie on the real height axis. -/
theorem completedNative_zero_height_real_of_RiemannHypothesis
    (hRH : RiemannHypothesis)
    {z : ℂ}
    (hstrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  have hfactor : nativeXiCompletionFactor z ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hstrip
  have hzeta : riemannZeta (operatorHeightParameter z) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta hstrip] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hfactor
  have hnontrivial :
      ¬∃ n : ℕ, operatorHeightParameter z = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre : (operatorHeightParameter z).re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp [Complex.mul_re, Complex.add_re, Complex.neg_re]
    have hp := hstrip.1
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hone : operatorHeightParameter z ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    exact not_lt_of_ge hre.ge hstrip.2
  have hrh := hRH (operatorHeightParameter z) hzeta hnontrivial hone
  have heq : (operatorHeightParameter z).re = 1/2 - z.im := by
    simp [operatorHeightParameter, Complex.mul_re]
    ring
  linarith

end
end CarryWheelNativeSignedGate
