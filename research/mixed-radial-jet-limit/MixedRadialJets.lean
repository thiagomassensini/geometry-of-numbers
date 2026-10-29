import CrossRadialGeometry
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

/-! The existing completed jet and the existing signed form, with TWO radial
indices. Neither states nor metric are defined from moments. -/
namespace CarryMixedRadial
open CarrySelfAdjointOperator CarryCompletedTrace
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev zeroJet (k : ℕ) := projectiveChiralDifferenceJet k 0

def zeroPairing (k l : ℕ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm (zeroJet k) (zeroJet l)

def differencePairing (k l : ℕ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm (zeroJet k-zeroJet l) (zeroJet k-zeroJet l)

theorem zero_jet_original (k : ℕ) :
    zeroJet k = canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
  simp [zeroJet,projectiveChiralDifferenceJet,completedGreenForwardWeight]

/-- This is precisely the first even input of the existing FULL boundary
synthesis, including its prescribed amplitude and both channels. -/
theorem zero_jet_boundary (k : ℕ) :
    nativeSourceProjectiveBoundaryJetSynthesis 1 k ![1,0] = zeroJet k := by
  change (∑ i : Fin 1 ⊕ Fin 1,
    Sum.elim (nativeSourceEvenBoundaryPhase 1 ![1,0])
      (nativeSourceOddBoundaryPhase 1 ![1,0]) i •
      projectiveChiralDifferenceJet k
        (Sum.elim (fun i : Fin 1 => 2*i.val) (fun i : Fin 1 => 2*i.val+1) i)) = _
  simp [Fintype.sum_sum_type,nativeSourceEvenBoundaryPhase,
    nativeSourceOddBoundaryPhase,nativeSourceEvenBoundaryIndex,nativeSourceOddBoundaryIndex,zeroJet]

/-- Conversion to the unhalved incidence-minus-return convention used in
previous reports. No factor is fitted to a moment. -/
theorem original_zero_balance_eq_twice_pairing (k l : ℕ) :
    inner ℂ (zeroJet k).1 (zeroJet l).1 - inner ℂ (zeroJet k).2 (zeroJet l).2 =
      2*zeroPairing k l := by
  unfold zeroPairing canonicalCompletedNativeProjectiveChiralForm
  ring

theorem zero_pairing_original (k l : ℕ) :
    zeroPairing k l = (2 : ℂ)⁻¹ *
      conj (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0)) *
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint l 0) *
      crossRadialDefect k l 0 0 := by
  rw [zeroPairing,zero_jet_original,zero_jet_original]
  unfold canonicalCompletedNativeProjectiveChiralForm
    canonicalCompletedNativeRadialProjectiveChiralState
    canonicalCompletedNativeRadialChiralDefectState
  simp only [Prod.smul_fst,Prod.smul_snd,inner_smul_left,inner_smul_right]
  rw [cross_defect_is_original_pairing]
  ring

/-- Exact mixed-radial comparison of the SAME completed source. -/
theorem zero_pairing_factor_kernel (k l : ℕ)
    (hz : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k 0) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hwF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l 0) ≠ 0)
    (hzP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hwP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l 0) ≠ 0) :
    zeroPairing k l = (crossRadialFactor k l 0 0 : ℂ) *
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint l 0) := by
  rw [zero_pairing_original]
  rw [← completedNativeNormalizedPositiveChiralTraceKernel_eq_amplitude]
  exact native_kernel_cross_factor k l 0 0 hz hzF hwF hzP hwP

theorem zero_pairing_conj (k l : ℕ) : conj (zeroPairing k l) = zeroPairing l k := by
  simp [zeroPairing,canonicalCompletedNativeProjectiveChiralForm,inner_conj_symm]
  left
  change conj ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
  exact Complex.conj_ofReal 2

/-- All four crosses are kept; this is a signed balance, not a Hilbert norm. -/
theorem difference_pairing_four_crosses (k l : ℕ) :
    differencePairing k l = zeroPairing k k + zeroPairing l l -
      zeroPairing k l - zeroPairing l k := by
  simp only [differencePairing,zeroPairing,canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_sub,Prod.snd_sub,inner_sub_left,inner_sub_right]
  ring

theorem doubled_zero_factor (k : ℕ) :
    crossRadialFactor k (2*k+1) 0 0 = 3*Real.sqrt 2/4 := by
  unfold crossRadialFactor
  rw [doubled_radial_sqrt_product,doubled_radial_mass]
  have hk : radialMass k ≠ 0 := by unfold radialMass; positivity
  norm_num
  field_simp
  ring

theorem doubled_zero_factor_gt_one : 1 < 3*Real.sqrt 2/4 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h' := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

end
end CarryMixedRadial
