import CriticalRelative
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEulerBoundary

/-! Exact cancellation of source normalizations AFTER the original complete
synthesis. The stencil below is the original finite-difference coefficient
map, not a substitute source or a new metric. -/
namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalRelative Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def jetStencil (n k : ℕ) (x : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  fun r => ∑ a : Fin (2*n), nativeSourceJetOrderPhase a *
    (((a.val.factorial : ℂ) * step k ^ a.val)⁻¹) *
      completedGreenForwardWeight a r * x a

theorem nativeInput_factor (n k : ℕ) (x : Fin (2*n) → ℂ) (r : Fin (2*n)) :
    nativeSourceChiralJetInput n k x r =
      amp (canonicalCompletedC3RadialTiltPoint k r) * jetStencil n k x r := by
  simp only [nativeSourceChiralJetInput, jetStencil, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.mul_sum, nativeSourceChiralJetInputMatrix]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem amplitude_value_cancel {z : ℂ}
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    amp z * completedNativeOperatorCharacteristic z /
      completedNativePositiveHermiteBiehlerCoordinate z = (Real.sqrt 2 : ℂ)⁻¹ := by
  unfold amp completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
  field_simp

/-- Same complete source, with all F and E+ factors cancelled exactly. -/
theorem valueCoefficients_eq_stencil (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    radialCompletedValueCoefficients k (nativeSourceChiralJetInput n k x) =
      (Real.sqrt 2 : ℂ)⁻¹ • jetStencil n k x := by
  funext r
  simp only [radialCompletedValueCoefficients, nativeInput_factor, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (amp (canonicalCompletedC3RadialTiltPoint k r) *
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k r) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k r)) *
        jetStencil n k x r := by ring
    _ = _ := by rw [amplitude_value_cancel (hF r) (hP r)]

theorem sourceValue_eq_stencil (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    sourceValue k (nativeSourceChiralJetInput n k x) 1 =
      (Real.sqrt 2 : ℂ)⁻¹ • radialIncidentSynthesis k (2*n) (jetStencil n k x) := by
  rw [sourceValue_eq_completedCoefficients, valueCoefficients_eq_stencil n k x hF hP,
    map_smul]

theorem sourceCompanion_eq_stencil (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    sourceCompanion k (nativeSourceChiralJetInput n k x) 1 =
      (Complex.I * (Real.sqrt 2 : ℂ)⁻¹) • radialIncidentSynthesis k (2*n)
        (fun r => jetStencil n k x r * radialCompletedSlope k r) := by
  rw [sourceCompanion_eq_completedSlope k (2*n) _ hF,
    valueCoefficients_eq_stencil n k x hF hP]
  have he : (fun r : Fin (2*n) => ((Real.sqrt 2 : ℂ)⁻¹ • jetStencil n k x) r *
      radialCompletedSlope k r) =
      (Real.sqrt 2 : ℂ)⁻¹ • (fun r => jetStencil n k x r * radialCompletedSlope k r) := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [he, map_smul, smul_smul]

/-- Exact mixed readout of the full original storage. -/
theorem storage_eq_stencil_slope (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    (storage k (nativeSourceChiralJetInput n k x) 1).re =
      2 * (inner ℂ (radialIncidentSynthesis k (2*n) (jetStencil n k x))
        (radialIncidentSynthesis k (2*n)
          (fun r => jetStencil n k x r * radialCompletedSlope k r))).re := by
  rw [storage_re_eq_source_cross k _ 1 hP, sourceValue_eq_stencil n k x hF hP,
    sourceCompanion_eq_stencil n k x hF hP, inner_smul_left, inner_smul_right]
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [map_inv₀, Complex.conj_ofReal]
  have he (z : ℂ) :
      ((Real.sqrt 2 : ℂ)⁻¹ * (Complex.I * (Real.sqrt 2 : ℂ)⁻¹ * z)) =
      Complex.I / 2 * z := by
    calc
      _ = Complex.I * (((Real.sqrt 2 : ℂ)^2)⁻¹) * z := by
        rw [pow_two, mul_inv_rev]
        ring
      _ = _ := by rw [hs]; ring
  rw [he]
  simp [Complex.mul_im]
  ring

end
end CarryCriticalMixed
