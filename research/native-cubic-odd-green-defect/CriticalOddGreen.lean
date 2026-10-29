import CubicOddVectors

namespace CarryCubicOdd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Additivity of the three ORIGINAL vector fields in the physical input. -/
theorem part_field_add_input (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) (a : Fin 3) :
    partField eta h0 h1 w (c+d) a=
      partField eta h0 h1 w c a+partField eta h0 h1 w d a := by
  have hb (f g : ℕ →₀ ℂ) : finiteTfvdBulk eta (f+g)=finiteTfvdBulk eta f+finiteTfvdBulk eta g := by
    ext j
    cases j with
    | zero => simp [finiteTfvdBulk_zero]
    | succ j => simp only [Finsupp.add_apply,finiteTfvdBulk_succ]; ring
  have hw (f g : ℕ →₀ ℂ) : coefficientWeight w (f+g)=coefficientWeight w f+coefficientWeight w g := by
    ext j
    simp only [coefficient_weight_apply,Finsupp.add_apply,mul_add]
  have hc : completionCommutator eta w (c+d)=completionCommutator eta w c+completionCommutator eta w d := by
    unfold completionCommutator
    rw [hw,hb,hb,hw]
    abel
  fin_cases a
  all_goals dsimp [partField]
  · rw [hb,hw,map_add,map_add]
  · rw [← map_add]
    congr 1
    module
  · rw [hc,map_add,map_add]

/-- BOTH chiral legs of each part, before any readout. -/
theorem completed_part_add_input (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k : ℕ) (c d : ℕ →₀ ℂ) (a : Fin 3) :
    completedSourceParts eta h0 h1 k (c+d) a=
      completedSourceParts eta h0 h1 k c a+completedSourceParts eta h0 h1 k d a := by
  rw [completed_part_as_fields,completed_part_as_fields,completed_part_as_fields]
  simp only [part_field_add_input,smul_add,Prod.mk_add_mk]

/-- A freely chosen trial direction in the ORIGINAL odd jets. No moments enter. -/
def criticalOddSource (a : ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  radialJetCoefficients k 3+(-a:ℂ) • radialJetCoefficients k 1

abbrev trialCoeff (a : ℝ) (r : ℕ) : ℝ := if r=0 then -a else 1

theorem critical_source_as_finite (a : ℝ) (k : ℕ) :
    finiteOddJetSource {0,1} (trialCoeff a) k=criticalOddSource a k := by
  simp [finiteOddJetSource,trialCoeff,criticalOddSource,add_comm]

theorem critical_source_profiles (a : ℝ) (k : ℕ) :
    criticalOddSource a k=((k:ℂ)+1)^3 • nativeOddProfile 1+
      ((-a:ℂ)*((k:ℂ)+1)) • nativeOddProfile 0 := by
  unfold criticalOddSource
  rw [show 3=2*1+1 by decide,radial_odd_calibration,odd_profile_radial_jet,smul_smul]

/-- The cubic/lower-jet mixing is derived for every field and arbitrary weight. -/
theorem critical_field_vectors (a : ℝ) (k : ℕ) (w : ℕ → ℂ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (j : Fin 3) :
    partField eta h0 h1 w (criticalOddSource a k) j=
      ((k:ℂ)+1)^3 • partField eta h0 h1 w (nativeOddProfile 1) j+
      ((-a:ℂ)*((k:ℂ)+1)) • partField eta h0 h1 w (nativeOddProfile 0) j := by
  rw [critical_source_profiles,part_field_add_input,part_field_scale_input,part_field_scale_input]

/-- The SAME identity in all three TWO-leg physical source parts. -/
theorem critical_completed_parts (a : ℝ) (k : ℕ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (j : Fin 3) :
    completedSourceParts eta h0 h1 k (criticalOddSource a k) j=
      ((k:ℂ)+1)^3 • completedSourceParts eta h0 h1 k (nativeOddProfile 1) j+
      ((-a:ℂ)*((k:ℂ)+1)) • completedSourceParts eta h0 h1 k (nativeOddProfile 0) j := by
  rw [critical_source_profiles,completed_part_add_input,completed_part_scale_input,completed_part_scale_input]

/-- Independent trial coefficients in BOTH inputs of the canonical odd form. -/
theorem critical_bilinear (a b : ℝ) :
    oddBilinear {0,1} {0,1} (trialCoeff a) (trialCoeff b)=
      h 3-(a+b)*h 2+a*b*h 1 := by
  simp [oddBilinear,trialCoeff]
  ring

/-- Full nine-cross physical transport; the trial coefficients are still free. -/
theorem critical_green_tendsto (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (criticalOddSource a k) (criticalOddSource b k)) atTop
      (nhds ((h 3-(a+b)*h 2+a*b*h 1:ℝ):ℂ)) := by
  have he := odd_green_pairing_tendsto eta h0 h1 {0,1} {0,1} (trialCoeff a) (trialCoeff b)
  simpa only [critical_source_as_finite,critical_bilinear] using he

theorem critical_signed_tendsto (a b : ℝ) :
    Tendsto (fun k : ℕ => signedPair k (criticalOddSource a k) (criticalOddSource b k)) atTop
      (nhds ((h 3-(a+b)*h 2+a*b*h 1:ℝ):ℂ)) := by
  have he := odd_pairing_tendsto {0,1} {0,1} (trialCoeff a) (trialCoeff b)
  change Tendsto (fun k : ℕ => signedPair k
    (finiteOddJetSource {0,1} (trialCoeff a) k)
    (finiteOddJetSource {0,1} (trialCoeff b) k)) atTop _ at he
  simpa only [critical_source_as_finite,critical_bilinear] using he

/-- Algebraic orthogonality to the old jet needs nonzero h1, not its sign. -/
theorem critical_old_cross_tendsto (a : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (criticalOddSource a k) (radialJetCoefficients k 1)) atTop
      (nhds ((h 2-a*h 1:ℝ):ℂ)) := by
  have he := odd_green_pairing_tendsto eta h0 h1 {0,1} {0} (trialCoeff a) (fun _ => 1)
  have hs (k : ℕ) : finiteOddJetSource {0} (fun _ => 1) k=radialJetCoefficients k 1 := by
    simp [finiteOddJetSource]
  have hv : oddBilinear {0,1} {0} (trialCoeff a) (fun _ => 1)=h 2-a*h 1 := by
    simp [oddBilinear,trialCoeff]
    ring
  simpa only [critical_source_as_finite,hs,hv] using he

theorem critical_old_cross_zero (hh : h 1≠0) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (criticalOddSource (h 2/h 1) k) (radialJetCoefficients k 1)) atTop (nhds 0) := by
  have he := critical_old_cross_tendsto (h 2/h 1) eta h0 h1
  simpa only [div_mul_cancel₀ _ hh,sub_self,Complex.ofReal_zero] using he

/-- The original physical Schur direction, without assuming its positivity. -/
theorem critical_schur_tendsto (hh : h 1≠0) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (criticalOddSource (h 2/h 1) k) (criticalOddSource (h 2/h 1) k)) atTop
      (nhds ((h 3-h 2^2/h 1:ℝ):ℂ)) := by
  have he := critical_green_tendsto (h 2/h 1) (h 2/h 1) eta h0 h1
  convert he using 1
  congr 2
  field_simp
  ring

end
end CarryCubicOdd
