import CanonicalExtraction

namespace CarryBinomialGreen
open CarryPolarizedFour CarryGreenFinitePart CarryFirstOddGreen CarryRadialGreen CarryRadialRefinement
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def evenScale (k i : ℕ) : ℝ :=
  (-1:ℝ)^i*((k:ℝ)+1)^(2*i)/((2*i).factorial:ℝ)

theorem even_scale_original (k i : ℕ) :
    (((2*i).factorial:ℂ)*canonicalCompletedC3RadialSecondStep k^(2*i))⁻¹=
      (evenScale k i:ℂ) := by
  unfold evenScale canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  push_cast
  simp only [mul_pow, pow_mul, Complex.I_sq, mul_inv_rev, inv_pow, inv_inv]
  have hm : (-1:ℂ)⁻¹=(-1:ℂ) := by norm_num [Complex.inv_def]
  rw [← inv_pow,hm]
  ring

theorem forward_weight_real (n r : ℕ) :
    completedGreenForwardWeight n r=(realWeight n r:ℂ) := by
  simp only [completedGreenForwardWeight,realWeight]
  norm_cast

theorem even_jet_input_real (k i : ℕ) :
    jetInput k (2*i)=∑ r ∈ Finset.range (2*i+1),
      ((evenScale k i*realWeight (2*i) r:ℝ):ℂ) • basisInput r := by
  unfold jetInput
  rw [even_scale_original, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul,forward_weight_real,Complex.ofReal_mul]

theorem raw_ray_real (p q : ℕ) (t : ℝ) : (rawRay p q (t:ℂ)).re=
    ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
      realWeight p r*realWeight q s*
        ((imaginaryReadout (((r:ℂ)+1)*(t:ℂ))).re+
          (imaginaryReadout (((s:ℂ)+1)*(t:ℂ))).re)/((r:ℝ)+(s:ℝ)+2) := by
  unfold rawRay
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  unfold nodeRay
  have hd : ((r:ℂ)+(s:ℂ)+2)⁻¹=((((r:ℝ)+(s:ℝ)+2)⁻¹:ℝ):ℂ) := by
    push_cast
    rfl
  rw [hd]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    sub_zero,Complex.add_re]
  ring

/-- Exact sampling identity for the ORIGINAL physical jets. All source
regularity hypotheses concern the actual nodes and are eventually available. -/
theorem even_physical_ray (i j k : ℕ)
    (hr : ∀ a : Fin (2*i+2*j+1),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k a)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k a)≠0) :
    (physicalForm (physicalJet k (2*i)) (physicalJet k (2*j))).re=
      evenScale k i*evenScale k j*((k:ℝ)+1)*(rawRay (2*i) (2*j) (radialStep k:ℂ)).re := by
  rw [← jet_input_source, ← jet_input_source,even_jet_input_real,even_jet_input_real]
  simp only [map_sum,map_smul]
  rw [physical_form_sum]
  simp only [Complex.re_sum]
  rw [raw_ray_real]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hri
  apply Finset.sum_congr rfl
  intro s hsj
  have hri' : r<2*i+2*j+1 := by have := Finset.mem_range.mp hri; omega
  have hsj' : s<2*i+2*j+1 := by have := Finset.mem_range.mp hsj; omega
  rw [real_weighted_form,source_basis_real k r s
    (hr ⟨r,hri'⟩).1 (hr ⟨r,hri'⟩).2 (hr ⟨s,hsj'⟩).1 (hr ⟨s,hsj'⟩).2,
    radial_node_readout,radial_node_readout]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

end
end CarryBinomialGreen
