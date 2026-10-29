import OddKernelFilters

namespace CarryOddCauchy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Each ORIGINAL two-leg completed source part is calibrated before pairing. -/
theorem completed_odd_part_calibration (r k : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a : Fin 3) :
    completedSourceParts eta h0 h1 k (radialJetCoefficients k (2*r+1)) a=
      ((k:ℂ)+1)^(2*r+1) • completedSourceParts eta h0 h1 k (nativeOddProfile r) a := by
  rw [radial_odd_calibration,completed_part_scale_input]

/-- Complete synthesis, including BOTH native chiral legs, has the same scale. -/
theorem completed_odd_source_calibration (r k : ℕ) :
    projectiveChiralDifferenceJet k (2*r+1)=
      ((k:ℂ)+1)^(2*r+1) • physicalCompletedFiniteSource k (nativeOddProfile r) := by
  rw [← radial_jet_original_source,radial_odd_calibration]
  simp only [physicalCompletedFiniteSource_original,map_smul]

/-- Both independent weighted fields are reconstructed before any pairing. -/
theorem native_odd_nine_field_reconstruction (r s : ℕ) (u v : ℕ → ℂ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      inner ℂ (partField eta h0 h1 u (nativeOddProfile r) a)
        (partField eta h0 h1 v (nativeOddProfile s) b))=
      inner ℂ (physicalCauchySynthesis (coefficientWeight u (nativeOddProfile r)))
        (physicalCauchySynthesis (coefficientWeight v (nativeOddProfile s))) := by
  have he : inner ℂ (∑ a : Fin 3, partField eta h0 h1 u (nativeOddProfile r) a)
      (∑ b : Fin 3, partField eta h0 h1 v (nativeOddProfile s) b)=
      ∑ a : Fin 3, ∑ b : Fin 3,
        inner ℂ (partField eta h0 h1 u (nativeOddProfile r) a)
          (partField eta h0 h1 v (nativeOddProfile s) b) := by
    simp only [sum_inner,inner_sum]
    rw [Finset.sum_comm]
  rw [← he,part_field_reconstruction,part_field_reconstruction]

/-- The all-order filter is a readout of those reconstructed fields. -/
theorem native_odd_nine_fields_filter (r s : ℕ) (w : ℕ → ℂ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      inner ℂ (partField eta h0 h1 (fun _ => 1) (nativeOddProfile r) a)
        (partField eta h0 h1 w (nativeOddProfile s) b))=oddFilter r s w := by
  rw [native_odd_nine_field_reconstruction]
  have hw : coefficientWeight (fun _ => 1) (nativeOddProfile r)=nativeOddProfile r := by
    ext j
    simp [coefficient_weight_apply]
  rw [hw]
  exact native_odd_kernel_filter r s w

/-- Entire ORIGINAL response: no Taylor replacement, and BOTH ordered filters. -/
theorem normalized_odd_filter_exact (r s k : ℕ) :
    normalizedOddPair r s k=((k:ℂ)+1)^(2*(r+s+1)+1)*
      (oddFilter r s (responseSamples (radialStep k))+
       oddFilter s r (responseSamples (radialStep k))) := by
  unfold normalizedOddPair
  rw [native_odd_ordered_filters]

/-- Two independent original radial jets in the COMPLETE signed source form. -/
theorem radial_odd_signed_filter_exact (r s : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      signedPair k (radialJetCoefficients k (2*r+1)) (radialJetCoefficients k (2*s+1))=
        ((k:ℂ)+1)^(2*(r+s+1)+1)*
          (oddFilter r s (responseSamples (radialStep k))+
           oddFilter s r (responseSamples (radialStep k))) := by
  filter_upwards [odd_pairing_exact {r} {s} (fun _ => 1) (fun _ => 1)] with k hk
  have he : signedPair k (radialJetCoefficients k (2*r+1))
      (radialJetCoefficients k (2*s+1))=normalizedOddPair r s k := by
    simpa [oddPairing,finiteOddJetSource] using hk
  exact he.trans (normalized_odd_filter_exact r s k)

/-- ALL NINE Green/boundary/commutator crosses of the two completed jets. -/
theorem completed_odd_green_filter_exact (r s : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k
        (radialJetCoefficients k (2*r+1)) (radialJetCoefficients k (2*s+1))=
        ((k:ℂ)+1)^(2*(r+s+1)+1)*
          (oddFilter r s (responseSamples (radialStep k))+
           oddFilter s r (responseSamples (radialStep k))) := by
  filter_upwards [radial_odd_signed_filter_exact r s] with k hk
  rw [cross_green_eq_original]
  exact hk

/-- Arbitrary finite mixtures, TWO independent supports and coefficients.
The radial power is retained separately for EVERY ordered profile pair. -/
theorem finite_odd_signed_filters_exact (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop,
      signedPair k (finiteOddJetSource S c k) (finiteOddJetSource T d k)=
        ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*
          (((k:ℂ)+1)^(2*(r+s+1)+1)*
            (oddFilter r s (responseSamples (radialStep k))+
             oddFilter s r (responseSamples (radialStep k)))) := by
  filter_upwards [odd_pairing_exact S T c d] with k hk
  simpa only [oddPairing,normalized_odd_filter_exact] using hk

/-- The SAME arbitrary finite mixtures in all nine completed Green crosses. -/
theorem finite_odd_green_filters_exact (S T : Finset ℕ) (c d : ℕ → ℝ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (finiteOddJetSource S c k) (finiteOddJetSource T d k)=
        ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*
          (((k:ℂ)+1)^(2*(r+s+1)+1)*
            (oddFilter r s (responseSamples (radialStep k))+
             oddFilter s r (responseSamples (radialStep k)))) := by
  filter_upwards [finite_odd_signed_filters_exact S T c d] with k hk
  rw [cross_green_eq_original]
  exact hk

/-- Compatibility with the SAME canonical moments; no canonical sign is used. -/
theorem completed_odd_filter_tendsto (r s : ℕ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^(2*(r+s+1)+1)*
      (oddFilter r s (responseSamples (radialStep k))+
       oddFilter s r (responseSamples (radialStep k)))) atTop (nhds (h (r+s+1):ℂ)) := by
  apply (normalized_odd_pair_tendsto r s).congr'
  filter_upwards [] with k
  exact normalized_odd_filter_exact r s k

/-- The explicit all-order filter reproduces the previously proved Green limit. -/
theorem completed_odd_green_filter_tendsto (r s : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (radialJetCoefficients k (2*r+1)) (radialJetCoefficients k (2*s+1))) atTop
      (nhds (h (r+s+1):ℂ)) := by
  apply (completed_odd_filter_tendsto r s).congr'
  filter_upwards [completed_odd_green_filter_exact r s eta h0 h1] with k hk
  exact hk.symm

/-- Checks of phase and factorial at the two original lowest profiles. -/
theorem native_odd_row_regressions :
    inner ℂ (completedNativeChiralCauchyFeature 0) (physicalCauchySynthesis (nativeOddProfile 0))=Complex.I/6 ∧
    inner ℂ (completedNativeChiralCauchyFeature 0) (physicalCauchySynthesis (nativeOddProfile 1))= -Complex.I/120 := by
  rw [native_odd_cauchy_row,native_odd_cauchy_row]
  norm_num

theorem odd_filter_regressions :
    oddFilterCoefficient 0 0 0=1/6 ∧ oddFilterCoefficient 0 0 1= -1/12 ∧
    oddFilterCoefficient 1 1 0=1/720 ∧ oddFilterCoefficient 1 1 3= -1/10080 := by
  norm_num [oddFilterCoefficient,nativeOddBeta]

end
end CarryOddCauchy
