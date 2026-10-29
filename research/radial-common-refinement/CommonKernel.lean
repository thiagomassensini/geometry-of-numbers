import RadialRefinement

namespace CarryRadialRefinement
open CarryPhysicalTrace CarryCompletedTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Original single-grid formula, obtained from amplitude/return, not moments. -/
theorem sample_form_factor (k l i j : ℕ) :
    canonicalCompletedNativeProjectiveChiralForm
      (canonicalCompletedNativeRadialProjectiveChiralState k i)
      (canonicalCompletedNativeRadialProjectiveChiralState l j) =
    completedNativeNormalizedPositiveChiralTraceKernel
      (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) *
      crossRadialDefect k l i j := by
  rw [completedNativeNormalizedPositiveChiralTraceKernel_eq_amplitude,
    cross_defect_is_original_pairing]
  unfold canonicalCompletedNativeProjectiveChiralForm
    canonicalCompletedNativeRadialProjectiveChiralState
    canonicalCompletedNativeRadialChiralDefectState
  simp only [Prod.smul_fst,Prod.smul_snd,
    _root_.inner_smul_left (𝕜 := ℂ) (E := CanonicalCompletedNativeChiralCauchyCarrier),
    _root_.inner_smul_right (𝕜 := ℂ) (E := CanonicalCompletedNativeChiralCauchyCarrier)]
  ring

/-- The repaired crossing comes from native isometries and unchanged columns,
not from dividing a scalar kernel by the discrepancy factor. -/
theorem common_radial_gram (k l i j : ℕ) :
    inner ℂ (powerIsometry l (radialVector k i)) (powerIsometry k (radialVector l j)) =
      Complex.I / (canonicalCompletedC3RadialTiltPoint l j-
        conj (canonicalCompletedC3RadialTiltPoint k i)) := by
  rw [power_isometry_radial,power_isometry_radial]
  have hg : refinedAddress k l = refinedAddress l k := common_grade_comm l k
  rw [hg]
  change radialCrossGram (refinedAddress l k) (refinedAddress l k)
    (refinedAddress l i) (refinedAddress k j) = _
  rw [radial_cross_gram_eq_factor,cross_factor_same_radial]
  rw [refined_point]
  have hw : canonicalCompletedC3RadialTiltPoint (refinedAddress l k) (refinedAddress k j) =
      canonicalCompletedC3RadialTiltPoint l j := by rw [← hg,refined_point]
  rw [hw]
  simp

/-- Full exact canonical kernel at TWO independent original nodes. The source
is first transported vectorially, with both channels and completion retained. -/
theorem common_pairing_kernel (k l i j : ℕ)
    (hz : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l j) ≠ 0)
    (hzP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l j) ≠ 0) :
    commonPairing k l i j = canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  have hz' : canonicalCompletedC3RadialTiltPoint (commonGrade k l) (refinedAddress l i) =
      canonicalCompletedC3RadialTiltPoint k i := refined_point l k i
  have hw' : canonicalCompletedC3RadialTiltPoint (commonGrade k l) (refinedAddress k j) =
      canonicalCompletedC3RadialTiltPoint l j := by rw [common_grade_comm]; exact refined_point k l j
  rw [common_pairing_same_grade,sample_form_factor]
  have h := native_kernel_cross_factor (commonGrade k l) (commonGrade k l)
    (refinedAddress l i) (refinedAddress k j)
    (by simpa only [hz'] using hz) (by simpa only [hz'] using hzF)
    (by simpa only [hw'] using hwF) (by simpa only [hz'] using hzP)
    (by simpa only [hw'] using hwP)
  simpa only [cross_factor_same_radial,Complex.ofReal_one,one_mul,hz',hw'] using h

end
end CarryRadialRefinement
