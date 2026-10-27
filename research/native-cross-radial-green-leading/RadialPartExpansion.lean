import PartVectors
import DoubledMixedExpansion
import MixedRayLeading

namespace CarryGreenLeading
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl
open CarryEnergyCorrection CarryMixedParity CarryCrossRadial NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- The fixed constant and linear ADDRESS profiles of each original TFVD part. -/
abbrev constantPart (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) (a : Fin 3) :=
  partField eta h0 h1 (fun _ => 1) c a
abbrev linearPart (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) (a : Fin 3) :=
  partField eta h0 h1 (monomialWeight 1) c a

theorem native_part_coordinates (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, ∀ a : Fin 3, completedSourceParts eta h0 h1 k c a=
      ((Real.sqrt ((k:ℝ)+1):ℂ) •
        ((Complex.I/(Real.sqrt 2:ℂ)) • constantPart eta h0 h1 c a+
          chiralDifference • partField eta h0 h1 (responseSamples (radialStep k)) c a),
       (Real.sqrt ((k:ℝ)+1):ℂ) •
        ((-Complex.I/(Real.sqrt 2:ℂ)) • constantPart eta h0 h1 c a+
          chiralDifference • partField eta h0 h1 (responseSamples (radialStep k)) c a)) := by
  obtain ⟨N,hN⟩ := part_field_finite_locality eta h0 h1 c
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hA (j : Fin N) : incidentWeight k j=
      (Complex.I/(Real.sqrt 2:ℂ))*1+chiralDifference*responseSamples (radialStep k) j := by
    have hh := incident_amplitude_response _ (hk j).2.1
    change incidentWeight k j=(2*responseWeight k j+Complex.I)/(Real.sqrt 2:ℂ) at hh
    rw [response_radial_readout] at hh
    rw [hh]
    unfold chiralDifference responseSamples
    ring
  have hB (j : Fin N) : returnedWeight k j=
      (-Complex.I/(Real.sqrt 2:ℂ))*1+chiralDifference*responseSamples (radialStep k) j := by
    have hd := radial_weight_difference k j (hk j).2.1 (hk j).2.2
    rw [hA j] at hd
    unfold chiralDifference at hd ⊢
    linear_combination -hd
  intro a
  rw [completed_part_as_fields,
    hN (incidentWeight k) (fun j : ℕ => (Complex.I/(Real.sqrt 2:ℂ))*1+
      chiralDifference*responseSamples (radialStep k) j) hA a,
    hN (returnedWeight k) (fun j : ℕ => (-Complex.I/(Real.sqrt 2:ℂ))*1+
      chiralDifference*responseSamples (radialStep k) j) hB a]
  simp only [part_field_add_weight,part_field_scale_weight]

/-- Mean and contrast of EACH original part as whole vectors. -/
theorem native_part_contrast_mean (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, ∀ a : Fin 3,
      (completedSourceParts eta h0 h1 k c a).1-(completedSourceParts eta h0 h1 k c a).2=
        ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) • constantPart eta h0 h1 c a ∧
      (2:ℂ)⁻¹ • ((completedSourceParts eta h0 h1 k c a).1+(completedSourceParts eta h0 h1 k c a).2)=
        ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) •
          partField eta h0 h1 (responseSamples (radialStep k)) c a := by
  filter_upwards [native_part_coordinates eta h0 h1 c] with k hk
  intro a
  rw [hk a]
  unfold chiralDifference
  constructor <;> module

/-- Uniform finite-source vector Taylor extraction for each physical part.
The original native remainder is retained BEFORE any pairing. -/
theorem part_response_expansion (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) :
    ∀ᶠ z : ℂ in nhds 0, ∀ a : Fin 3,
      partField eta h0 h1 (responseSamples z) c a=
        ((h 0:ℂ)*z) • linearPart eta h0 h1 c a+
        (-(h 1:ℂ)*z^3) • partField eta h0 h1 (monomialWeight 3) c a+
        z^5 • partField eta h0 h1 (remainderSamples 2 z) c a := by
  obtain ⟨N,hN⟩ := part_field_finite_locality eta h0 h1 c
  filter_upwards [response_samples_prefix 2 N] with z hz
  intro a
  rw [hN (responseSamples z) (fun j : ℕ => taylorSamples 2 z j+z^(2*2+1)*remainderSamples 2 z j) hz a]
  have ht : taylorSamples 2 z=(fun j => ((h 0:ℂ)*z)*monomialWeight 1 j+
      (-(h 1:ℂ)*z^3)*monomialWeight 3 j) := by
    funext j
    norm_num [taylorSamples,Finset.sum_range_succ]
  norm_num only [show 2*2+1=5 by decide]
  rw [ht,part_field_add_weight,part_field_add_weight,
    part_field_scale_weight,part_field_scale_weight,part_field_scale_weight]

theorem part_field_continuous (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℂ → ℕ → ℂ) (c : ℕ →₀ ℂ)
    (hw : ∀ j, ContinuousAt (fun z => w z j) 0) (a : Fin 3) :
    ContinuousAt (fun z : ℂ => partField eta h0 h1 (w z) c a) 0 := by
  have hfull := weighted_synthesis_continuous w c hw
  have hbulk := weighted_synthesis_continuous w (finiteTfvdBulk eta c) hw
  have hb : ContinuousAt (fun z : ℂ => partField eta h0 h1 (w z) c 0) 0 := by
    simp only [partField,ite_true]
    exact (physicalGreenOperator eta h0.le h1).continuous.continuousAt.comp hbulk
  have ht : ContinuousAt (fun z : ℂ => partField eta h0 h1 (w z) c 1) 0 := by
    simp only [partField,show (1:Fin 3)≠0 by decide,ite_false,ite_true]
    have hw0 := hw 0
    have hw1 := hw 1
    apply ((physicalGreenResolvent eta h0.le h1)^2).continuous.continuousAt.comp
    fun_prop
  fin_cases a
  · exact hb
  · exact ht
  · have he : (fun z : ℂ => partField eta h0 h1 (w z) c 2)=
        (fun z : ℂ => physicalCauchySynthesis (coefficientWeight (w z) c)-
          partField eta h0 h1 (w z) c 0-partField eta h0 h1 (w z) c 1) := by
      funext z
      have hs := part_field_reconstruction eta h0 h1 (w z) c
      simp only [Fin.sum_univ_three] at hs
      rw [← hs]
      abel
    have hc : ContinuousAt (fun z : ℂ => physicalCauchySynthesis (coefficientWeight (w z) c)-
        partField eta h0 h1 (w z) c 0-partField eta h0 h1 (w z) c 1) 0 := (hfull.sub hb).sub ht
    rw [← he] at hc
    exact hc

theorem part_remainder_continuous (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) :
    ContinuousAt (fun z : ℂ => partField eta h0 h1 (remainderSamples 2 z) c a) 0 :=
  part_field_continuous eta h0 h1 (fun z => remainderSamples 2 z) c
    (CarryMixedImaginary.remainder_samples_continuous 2) a

/-- Normalized observation of the same part field, not a source redefinition. -/
def normalizedPart (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) (k : ℕ) :=
  ((k:ℂ)+1) • partField eta h0 h1 (responseSamples (radialStep k)) c a

theorem normalized_part_expansion (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) :
    ∀ᶠ k : ℕ in atTop, normalizedPart eta h0 h1 c a k=
      (h 0:ℂ) • linearPart eta h0 h1 c a+
      (-(h 1:ℂ)*(radialStep k:ℂ)^2) • partField eta h0 h1 (monomialWeight 3) c a+
      (radialStep k:ℂ)^4 • partField eta h0 h1 (remainderSamples 2 (radialStep k)) c a := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  filter_upwards [ht.eventually (part_response_expansion eta h0 h1 c)] with k hk
  unfold normalizedPart
  rw [hk a]
  simp only [smul_add,smul_smul]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hA : ((k:ℂ)+1)*((h 0:ℂ)*(radialStep k:ℂ))=(h 0:ℂ) := by
    linear_combination (h 0:ℂ)*hi
  have hB : ((k:ℂ)+1)*(-(h 1:ℂ)*(radialStep k:ℂ)^3)=
      -(h 1:ℂ)*(radialStep k:ℂ)^2 := by linear_combination -(h 1:ℂ)*(radialStep k:ℂ)^2*hi
  have hR : ((k:ℂ)+1)*(radialStep k:ℂ)^5=(radialStep k:ℂ)^4 := by
    linear_combination (radialStep k:ℂ)^4*hi
  rw [hA,hB,hR]

theorem normalized_part_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (a : Fin 3) :
    Tendsto (normalizedPart eta h0 h1 c a) atTop
      (nhds ((h 0:ℂ) • linearPart eta h0 h1 c a)) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (part_remainder_continuous eta h0 h1 c a).tendsto.comp ht
  have hB := ((tendsto_const_nhds (x:=-(h 1:ℂ))).mul (ht.pow 2)).smul
    (tendsto_const_nhds (x:=partField eta h0 h1 (monomialWeight 3) c a))
  have hl := ((tendsto_const_nhds (x:=(h 0:ℂ) • linearPart eta h0 h1 c a)).add hB).add
    ((ht.pow 4).smul hR)
  simp only [zero_pow (by decide : 2≠0),zero_pow (by decide : 4≠0),mul_zero,zero_smul,add_zero] at hl
  apply hl.congr'
  filter_upwards [normalized_part_expansion eta h0 h1 c a] with k hk
  exact hk.symm

end
end CarryGreenLeading
