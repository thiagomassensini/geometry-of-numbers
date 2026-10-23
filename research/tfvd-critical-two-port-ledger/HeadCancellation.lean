import CriticalLedger

namespace CarryTfvdCritical
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open CarryConservativeIntertwiner
open Filter Topology
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Existing finite head response, evaluated on the canonical enriched TFVD state. -/
def canonicalHeadResponse (M : ℕ) (z : ℂ) : ℂ :=
  tfvdStateHeadResponse z (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z))

theorem first_even_material (k : ℕ) :
    fixedMaterial 1 k firstEvenBoundary = ![1,0] := by
  have he : physicalEndpointJetInput 2 k (![1,0] : Fin 2 → ℂ) = firstEvenBoundary := by
    ext a
    fin_cases a <;> simp [physicalEndpointJetInput_finite,Fin.sum_univ_two,
      endpointGauge,firstEvenBoundary,nativeSourceJetOrderPhase]
  unfold fixedMaterial
  rw [← he,decodedEndpointCoefficients_encode]

theorem first_even_head_formula (M k : ℕ) :
    headFlux M 1 k firstEvenBoundary =
      (((k : ℝ)+1)/2) * (canonicalHeadResponse M (canonicalCompletedC3RadialTiltPoint k 0)).im := by
  unfold headFlux portFlux
  rw [first_even_material]
  unfold headSecond
  rw [first_even_material]
  simp [matrixPairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,cauchyMatrix,cauchyEntry,
    canonicalHeadResponse,canonicalStates]
  ring

theorem first_even_head_normalized (M k : ℕ) :
    headFlux M 1 k firstEvenBoundary / ((k : ℝ)+1) =
      (canonicalHeadResponse M (canonicalCompletedC3RadialTiltPoint k 0)).im / 2 := by
  rw [first_even_head_formula]
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- Conditional only on continuity of this finite physical head, with no sign premise. -/
theorem first_even_head_scaled_tendsto (M : ℕ) (hc : ContinuousAt (canonicalHeadResponse M) 0) :
    Tendsto (fun k => headFlux M 1 k firstEvenBoundary / ((k : ℝ)+1)) atTop
      (nhds ((canonicalHeadResponse M 0).im / 2)) := by
  simp_rw [first_even_head_normalized]
  exact ((Complex.continuous_im.continuousAt.tendsto.comp
    (hc.tendsto.comp (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0))).div_const 2)

/-- A convergent absolute balance vanishes after division by k+1. -/
theorem convergent_div_radial_scale {a : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (nhds L)) :
    Tendsto (fun k => a k / ((k : ℝ)+1)) atTop (nhds 0) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [div_eq_mul_inv,mul_zero] using ha.mul hi

/-- The head's linear-in-k term is cancelled by the exact TFVD correction. -/
theorem first_even_correction_scaled_tendsto (M : ℕ)
    (hc : ContinuousAt (canonicalHeadResponse M) 0) :
    Tendsto (fun k => correctionFlux M 1 k firstEvenBoundary / ((k : ℝ)+1)) atTop
      (nhds (-((canonicalHeadResponse M 0).im / 2))) := by
  have ht := convergent_div_radial_scale (total_flux_tendsto 1 firstEvenBoundary (fun _ => M))
  have hh := first_even_head_scaled_tendsto M hc
  have hs := ht.sub hh
  simpa only [Pi.sub_apply,add_div,add_sub_cancel_left,zero_sub] using hs

/-- A fixed head with a nonzero imaginary central response cannot have a finite balance limit. -/
theorem fixed_head_no_finite_limit (M : ℕ) (hc : ContinuousAt (canonicalHeadResponse M) 0)
    (hne : (canonicalHeadResponse M 0).im ≠ 0) :
    ¬ ∃ L : ℝ, Tendsto (fun k => headFlux M 1 k firstEvenBoundary) atTop (nhds L) := by
  rintro ⟨L,hL⟩
  have hz := convergent_div_radial_scale hL
  have he := tendsto_nhds_unique (first_even_head_scaled_tendsto M hc) hz
  apply hne
  linarith

/-- Consequently its correction cannot be separately replaced by a finite tail margin. -/
theorem fixed_correction_no_finite_limit (M : ℕ) (hc : ContinuousAt (canonicalHeadResponse M) 0)
    (hne : (canonicalHeadResponse M 0).im ≠ 0) :
    ¬ ∃ L : ℝ, Tendsto (fun k => correctionFlux M 1 k firstEvenBoundary) atTop (nhds L) := by
  rintro ⟨L,hL⟩
  apply fixed_head_no_finite_limit M hc hne
  refine ⟨nativeSourceFiniteBoundaryEnergy 2 firstEvenBoundary/4-L,?_⟩
  have ht := (total_flux_tendsto 1 firstEvenBoundary (fun _ => M)).sub hL
  simpa only [Pi.sub_apply,add_sub_cancel_right] using ht

end
end CarryTfvdCritical
