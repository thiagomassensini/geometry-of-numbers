import GeometryOfNumbers.Analysis.LogDerivativeScale
import GeometryOfNumbers.Analysis.MomentScaleHeight
import CarrySelfAdjointOperator.FiniteClockHeightLedger
import CarrySelfAdjointOperator.CompletedNativeCameraUniversality
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate

/-! Native provenance checks for the same scale convention. Camera
universality is not a moment dilation, and mass cannot be inferred from J. -/
namespace CarryNativeScaleSeam
open GeometryOfNumbers.Analysis.CarryScale CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem scaledMoment_native_eq (q : ℝ) (h : ℕ → ℝ) :
    GeometryOfNumbers.Analysis.FiniteClockHeightLedger.scaledMoment q h =
      CarrySelfAdjointOperator.FiniteClockHeightLedger.scaledMoment q h := rfl

/-- Literal covariance for the ORIGINAL native transport symbols. -/
theorem native_jacobi_scale {N : ℕ} (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (h : ℕ → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    CarrySelfAdjointOperator.finiteJacobiTransport (scaledInverseFactor a q B)
        (CarrySelfAdjointOperator.shiftedHankel (massScaledMoment a q h) N) =
      q • CarrySelfAdjointOperator.finiteJacobiTransport B
        (CarrySelfAdjointOperator.shiftedHankel h N) :=
  jacobi_scale a q ha hq h B

/-- The functional-calculus theorem applies to the native operator itself. -/
theorem native_finite_height_scale {N : ℕ} {J : Matrix (Fin N) (Fin N) ℝ}
    (hJ : J.PosDef) (q : ℝ) (hq : 0 < q) :
    CarrySelfAdjointOperator.finiteHeightOperator (hJ.smul hq) =
      (Real.sqrt q)⁻¹ • CarrySelfAdjointOperator.finiteHeightOperator hJ :=
  finite_height_scale hJ q hq

private theorem native_low_nonzero :
    canonicalCompletedNativeLogDerivativeMoment 0 ≠ 0 ∧
      canonicalCompletedNativeLogDerivativeMoment 1 ≠ 0 := by
  have h := canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  exact ⟨h.1.ne', h.2.ne'⟩

/-- The native source recurrence, before any matrix or positivity argument. -/
theorem native_log_moments_dilate (beta q : ℝ) (hb : beta ≠ 0) :
    GeometryOfNumbers.Analysis.FiniteClockHeightLedger.finiteLogMoment
        (fun n => beta*q^n*completedNativeRealEvenCharacteristicCoefficient n) =
      massScaledMoment q q canonicalCompletedNativeLogDerivativeMoment := by
  rw [response_dilation_mass _ beta q hb completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  have he : GeometryOfNumbers.Analysis.FiniteClockHeightLedger.finiteLogMoment
      completedNativeRealEvenCharacteristicCoefficient = canonicalCompletedNativeLogDerivativeMoment := by
    apply GeometryOfNumbers.Analysis.FiniteClockHeightLedger.finiteLogMoment_eq_existing
      completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
    intro n
    simpa only [neg_mul] using canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
  rw [he]

theorem native_log_moments_constant_amplitude (beta : ℝ) (hb : beta ≠ 0) :
    GeometryOfNumbers.Analysis.FiniteClockHeightLedger.finiteLogMoment
        (fun n => beta*completedNativeRealEvenCharacteristicCoefficient n) =
      canonicalCompletedNativeLogDerivativeMoment := by
  funext n
  have he := congrFun (native_log_moments_dilate beta 1 hb) n
  simpa [massScaledMoment, GeometryOfNumbers.Analysis.FiniteClockHeightLedger.scaledMoment] using he

theorem native_camera_scale_rigid {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (M N : ℕ) (a q : ℝ)
    (he : massScaledMoment a q (completedNativeCameraLogDerivativeMoment b M) =
      completedNativeCameraLogDerivativeMoment c N) : a = 1 ∧ q = 1 := by
  rw [completedNativeCameraLogDerivativeMoment_eq_canonical hb,
    completedNativeCameraLogDerivativeMoment_eq_canonical hc] at he
  exact fixed_moment_scale_rigid _ a q native_low_nonzero.1 native_low_nonzero.2 he

theorem native_geometric_mass_not_response_dilation (q : ℝ) (hq : 0 < q) (hne : q ≠ 1) :
    massScaledMoment q⁻¹ q canonicalCompletedNativeLogDerivativeMoment ≠
      massScaledMoment q q canonicalCompletedNativeLogDerivativeMoment :=
  geometric_mass_not_response_dilation _ q hq hne native_low_nonzero.1

/-- The mass distinction is invisible to the matched Jacobi sections. -/
theorem native_two_mass_actions_same_jacobi {N : ℕ} (q : ℝ) (hq : 0 < q)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    GeometryOfNumbers.Analysis.finiteJacobiTransport (scaledInverseFactor q⁻¹ q B)
        (GeometryOfNumbers.Analysis.shiftedHankel
          (massScaledMoment q⁻¹ q canonicalCompletedNativeLogDerivativeMoment) N) =
      GeometryOfNumbers.Analysis.finiteJacobiTransport (scaledInverseFactor q q B)
        (GeometryOfNumbers.Analysis.shiftedHankel
          (massScaledMoment q q canonicalCompletedNativeLogDerivativeMoment) N) :=
  jacobi_mass_blind q⁻¹ q q (inv_pos.mpr hq) hq hq _ B

end
end CarryNativeScaleSeam
