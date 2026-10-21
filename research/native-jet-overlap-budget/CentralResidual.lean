import DampedCamera
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort
import CarrySelfAdjointOperator.CompletedNativeAmbientRadialIntertwiningNoGo

/-! A literal one-source test of the variable residual, using the already
proved ambient central excess. Finite sign inputs are isolated in this file. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- A cofinal subsequence of the ORIGINAL grid; no point or weight is changed. -/
def centralIndex (k : ℕ) : ℕ := 4*k+3

theorem centralIndex_tendsto : Tendsto centralIndex atTop atTop := by
  apply tendsto_atTop_mono (f := fun k : ℕ => k) _ tendsto_id
  intro k
  dsimp [centralIndex]
  omega

theorem central_point_eq (k : ℕ) :
    radialPoint (centralIndex k) 0=canonicalCompletedC3AmbientRadialTiltPoint k 1 0 := by
  apply Complex.ext
  · simp [radialPoint,canonicalCompletedC3RadialTiltPoint,canonicalCompletedC3RadialTiltStep,
      canonicalGreenJetStep,
      canonicalCompletedC3AmbientRadialTiltPoint,canonicalCompletedC3AmbientRadialTiltStep]
  · rw [canonicalCompletedC3RadialTiltPoint_im,canonicalCompletedC3AmbientRadialTiltPoint_im]
    simp only [Nat.cast_zero,zero_add,one_mul,Fin.val_zero]
    unfold canonicalCompletedC3AmbientRadialTiltScale centralIndex
    push_cast
    field_simp
    ring

theorem centralStrip (k : ℕ) : strip (centralIndex k) 1 := by
  intro i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  change operatorHeightParameter (radialPoint (centralIndex k) 0) ∈ genuineCriticalStrip
  rw [central_point_eq]
  constructor
  · exact canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 1 0
  · have h := canonicalCompletedC3AmbientRadialTiltPoint_im_pos k 1 (0 : Fin 1)
    norm_num [operatorHeightParameter,Complex.mul_re] at *
    linarith

def centralCoefficients (k : ℕ) : Fin 1 → ℂ :=
  radialDifferenceSourceCoefficients (centralIndex k) 1 0

def centralResidual (k : ℕ) : ℂ := variableDefect (centralIndex k)
  (centralCoefficients k) (centralCoefficients k) (centralStrip k)

private theorem central_sourceWeight (k : ℕ)
    (hp : completedNativePositiveHermiteBiehlerCoordinate (radialPoint (centralIndex k) 0) ≠ 0) :
    sourceWeight (centralIndex k) (centralCoefficients k) 0=
      canonicalCompletedC3FullWronskianChiralNormalization (radialPoint (centralIndex k) 0) := by
  have hc : centralCoefficients k 0=
      completedNativeNormalizedPositiveChiralAmplitude (radialPoint (centralIndex k) 0) := by
    unfold centralCoefficients radialDifferenceSourceCoefficients
    norm_num [completedGreenForwardWeight]
  rw [sourceWeight,hc,completedNativeNormalizedPositiveChiralAmplitude]
  simp only [Fin.val_zero]
  exact mul_div_cancel_right₀ _ hp

private theorem normalized_ambient_diagonal (z : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) :
    conj (canonicalCompletedC3FullWronskianChiralNormalization z)*
      canonicalCompletedC3FullWronskianChiralNormalization z*
      canonicalCompletedC3AmbientResponseKernel z z hz hz=
      canonicalCompletedC3NormalizedAmbientResponseKernel z z hz hz := by
  rw [canonicalCompletedC3NormalizedAmbientResponseKernel_eq_inner]
  change conj (canonicalCompletedC3FullWronskianChiralNormalization z)*
    canonicalCompletedC3FullWronskianChiralNormalization z*
    inner ℂ (canonicalCompletedC3AmbientResponseState z hz)
      (canonicalCompletedC3AmbientResponseState z hz)=
    inner ℂ (canonicalCompletedC3FullWronskianChiralNormalization z •
      canonicalCompletedC3AmbientResponseState z hz)
      (canonicalCompletedC3FullWronskianChiralNormalization z •
      canonicalCompletedC3AmbientResponseState z hz)
  rw [inner_smul_left,inner_smul_right]
  ring

private theorem central_damped (k : ℕ)
    (hp : completedNativePositiveHermiteBiehlerCoordinate (radialPoint (centralIndex k) 0) ≠ 0) :
    dampedCameraBalance (centralIndex k) (centralCoefficients k) (centralCoefficients k)
      (centralStrip k)=canonicalCompletedC3NormalizedAmbientResponseKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 1 0) := by
  unfold dampedCameraBalance dampedCameraMatrix overlapMatrix
  simp only [Fin.sum_univ_one,Matrix.hadamard_apply,radialOverlap_diagonal,one_mul]
  rw [central_sourceWeight k hp,ambientMatrix_eq_kernel]
  simp only [Fin.val_zero]
  rw [normalized_ambient_diagonal]
  simp only [central_point_eq]

/-- On the one-source canonical sample, the new residual is precisely the
NEGATIVE of the existing regularized ambient/kernel mismatch. -/
theorem centralResidual_eventually_eq_negative_old_defect :
    ∀ᶠ k : ℕ in atTop, centralResidual k=
      -canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k 1 0 0 := by
  have hreg := centralIndex_tendsto.eventually
    (canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 1)
  filter_upwards [hreg] with k hk
  have hp := (hk (0 : Fin 1)).2.2
  have hpair := radialDifferenceSource_pair (centralIndex k) 1 0 (by omega)
  have hb := radialReturnTransfer_polarized_balance (centralIndex k) 1
    (centralCoefficients k) (centralCoefficients k) (fun i => by
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact hp)
  simp only [radialReturnTransfer_exact] at hb
  have hform : canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet (centralIndex k) 0)
      (projectiveChiralDifferenceJet (centralIndex k) 0)=
      (2 : ℂ)⁻¹*polarizedSourceBalance (centralIndex k)
        (centralCoefficients k) (centralCoefficients k) 1 1 := by
    rw [← hpair]
    unfold canonicalCompletedNativeProjectiveChiralForm
    exact congrArg (fun z : ℂ => (2 : ℂ)⁻¹*z) hb
  rw [source_balance_budget _ _ _ (centralStrip k)] at hform
  have hcam := camera_sub_overlap_eq_damped (centralIndex k)
    (centralCoefficients k) (centralCoefficients k) (centralStrip k)
  have he : canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet (centralIndex k) 0)
      (projectiveChiralDifferenceJet (centralIndex k) 0)=
      dampedCameraBalance (centralIndex k) (centralCoefficients k) (centralCoefficients k)
        (centralStrip k)+centralResidual k := by
    unfold centralResidual
    linear_combination hform + hcam
  have hs := canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope
    (centralIndex k) 1 hk (0 : Fin 1) (0 : Fin 1)
  simp only [Fin.val_zero] at hs
  have hzero : projectiveChiralDifferenceJet (centralIndex k) 0=
      canonicalCompletedNativeRadialProjectiveChiralState (centralIndex k) 0 := by
    simp [projectiveChiralDifferenceJet,completedGreenForwardWeight]
  rw [hzero,hs,central_damped k hp] at he
  dsimp only [canonicalCompletedNativeRadialDslopeSampleMatrix,Matrix.of_apply] at he
  simp only [Fin.val_zero] at he
  have hpoint : canonicalCompletedC3RadialTiltPoint (centralIndex k) 0=
      canonicalCompletedC3AmbientRadialTiltPoint k 1 0 := central_point_eq k
  rw [hpoint] at he
  rw [canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub]
  linear_combination -he

/-- The original-source residual has a strictly NEGATIVE central limit. -/
theorem centralResidual_tendsto_negative_excess :
    Tendsto centralResidual atTop
      (nhds (-(canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ))) := by
  apply (canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess
    1 (0 : Fin 1) (0 : Fin 1)).neg.congr'
  filter_upwards [centralResidual_eventually_eq_negative_old_defect] with k hk
  exact hk.symm

theorem centralResidual_eventually_negative :
    ∀ᶠ k : ℕ in atTop, (centralResidual k).re < 0 := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    centralResidual_tendsto_negative_excess
  have hneg : (-(canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ)).re < 0 := by
    simp only [Complex.neg_re,Complex.ofReal_re]
    exact neg_neg_of_pos canonicalCompletedC3NormalizedAmbientCentralExcess_pos
  exact (tendsto_order.mp h).2 0 hneg

end
end CarryJetOverlap
