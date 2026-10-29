import GreenSynthesis
import NativeScaleSeam
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

/-! Compatibility with the exact PR38 laws. Scaling a physical vector and
scaling a completed response have different homogeneities. The theorem below
excludes a universal unnormalized linear Gram rule; it does not change the
prescribed native source or refute a fixed-source/projective construction. -/
namespace CarryGlobalScaleCompatibility
open CarryGlobalGreenSynthesis CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis.FiniteClockHeightLedger
open GeometryOfNumbers.Analysis.CarryScale GreenFrame.Concrete
open scoped InnerProductSpace
noncomputable section

/-- Direct reuse of the ORIGINAL PR38 theorem, from its frozen commit. -/
theorem native_log_amplitude_invariant (beta : ℝ) (hb : beta ≠ 0) :
    finiteLogMoment (fun n => beta*completedNativeRealEvenCharacteristicCoefficient n) =
      canonicalCompletedNativeLogDerivativeMoment :=
  CarryNativeScaleSeam.native_log_moments_constant_amplitude beta hb

/-- No linear synthesis in the unchanged physical metric can equate its
unnormalized energy with log moments under EVERY constant source amplitude. -/
theorem no_universal_unnormalized_linear_gram (z : ConcreteAnalysisSpace) :
    ¬ ∀ beta : ℝ, beta ≠ 0 →
      ‖sourceSynthesis (beta • z)‖^2 =
        finiteLogMoment (fun n => beta*completedNativeRealEvenCharacteristicCoefficient n) 0 := by
  intro h
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  rw [native_log_amplitude_invariant 1 (by norm_num)] at h1
  rw [native_log_amplitude_invariant 2 (by norm_num),synthesis_homogeneous_energy] at h2
  simp only [one_smul] at h1
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  norm_num only [pow_two,show (2 : ℝ)*2 = 4 by norm_num] at h2
  nlinarith

/-- Jacobi's insensitivity to these two mass actions does not identify the moments. -/
theorem jacobi_blindness_not_source_equality (q : ℝ) (hq : 0 < q) (hne : q ≠ 1)
    {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) :
    GeometryOfNumbers.Analysis.finiteJacobiTransport (scaledInverseFactor q⁻¹ q B)
      (GeometryOfNumbers.Analysis.shiftedHankel
        (massScaledMoment q⁻¹ q canonicalCompletedNativeLogDerivativeMoment) N) =
    GeometryOfNumbers.Analysis.finiteJacobiTransport (scaledInverseFactor q q B)
      (GeometryOfNumbers.Analysis.shiftedHankel
        (massScaledMoment q q canonicalCompletedNativeLogDerivativeMoment) N) ∧
    massScaledMoment q⁻¹ q canonicalCompletedNativeLogDerivativeMoment ≠
      massScaledMoment q q canonicalCompletedNativeLogDerivativeMoment := by
  exact ⟨CarryNativeScaleSeam.native_two_mass_actions_same_jacobi q hq B,
    CarryNativeScaleSeam.native_geometric_mass_not_response_dilation q hq hne⟩

end
end CarryGlobalScaleCompatibility
