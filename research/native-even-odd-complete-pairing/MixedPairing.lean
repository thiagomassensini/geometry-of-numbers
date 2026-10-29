import ResponseReality

namespace CarryMixedParity
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

abbrev signedPair (k : ℕ) (c d : ℕ →₀ ℂ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (physicalCompletedFiniteSource k c) (physicalCompletedFiniteSource k d)

/-- Exact two-state algebra in the ORIGINAL signed form. -/
theorem signed_mean_contrast (p q : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm p q=(2:ℂ)⁻¹*
      (inner ℂ (p.1-p.2) ((2:ℂ)⁻¹ • (q.1+q.2))+
        inner ℂ ((2:ℂ)⁻¹ • (p.1+p.2)) (q.1-q.2)) := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_inv₀, map_ofNat]
  norm_num
  ring

/-- Both complete vector observables are transported before their pairing. -/
theorem source_mean_and_contrast {N : ℕ} (k : ℕ) (c : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hd : ∀ j : ℕ, j<N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    (physicalCompletedFiniteSource k c).1-(physicalCompletedFiniteSource k c).2=
      ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) • physicalCauchySynthesis c ∧
    (2:ℂ)⁻¹ • ((physicalCompletedFiniteSource k c).1+(physicalCompletedFiniteSource k c).2)=
      ((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ))) •
        physicalCauchySynthesis (coefficientWeight (responseWeight k) c) :=
  ⟨completed_source_contrast k c hc hd, source_mean_response k c hc hF hd⟩

/-- Product forced by the ORIGINAL source scales; no metric is rescaled. -/
theorem contrast_mean_scale (k : ℕ) :
    conj ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)*
      ((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))= -2*Complex.I*((k:ℝ)+1:ℂ) := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hk : (Real.sqrt ((k:ℝ)+1):ℂ)^2=((k:ℝ)+1:ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : conj chiralDifference*(2/(Real.sqrt 2:ℂ))= -2*Complex.I := by
    simp only [chiralDifference, map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    field_simp [hn]
    linear_combination hs
  calc
    _ = (conj chiralDifference*(2/(Real.sqrt 2:ℂ)))*(Real.sqrt ((k:ℝ)+1):ℂ)^2 := by
      simp only [map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by rw [ha,hk]

/-- Exact COMPLEX flux for two independent complete sources, with both
ordered terms present. This is not inferred from a diagonal norm. -/
theorem complete_complex_pair {N : ℕ} (k : ℕ) (c d : ℕ →₀ ℂ)
    (hc : c.support ⊆ Finset.range N) (hdc : d.support ⊆ Finset.range N)
    (hF : ∀ j : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hd : ∀ j : ℕ, j<N → incidentWeight k j-returnedWeight k j=chiralDifference) :
    signedPair k c d=((k:ℂ)+1)*
      (kernel (responseSamples (radialStep k)) c d+
        conj (kernel (responseSamples (radialStep k)) d c)) := by
  obtain ⟨hcd,hcm⟩ := source_mean_and_contrast k c hc hF hd
  obtain ⟨hdd,hdm⟩ := source_mean_and_contrast k d hdc hF hd
  have he := signed_mean_contrast (physicalCompletedFiniteSource k c) (physicalCompletedFiniteSource k d)
  rw [hcd, hdm, hcm, hdd] at he
  simp only [inner_smul_left, inner_smul_right] at he
  have hi : inner ℂ (physicalCauchySynthesis (coefficientWeight (responseWeight k) c))
      (physicalCauchySynthesis d)=conj (kernel (responseWeight k) d c) := by
    change inner ℂ _ _=conj (inner ℂ _ _)
    rw [inner_conj_symm]
    rfl
  rw [hi] at he
  have hkernel : inner ℂ (physicalCauchySynthesis c)
      (physicalCauchySynthesis (coefficientWeight (responseWeight k) d))=kernel (responseWeight k) c d := rfl
  rw [hkernel] at he
  have hs := contrast_mean_scale k
  have ht : conj ((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))*
      ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)=2*Complex.I*((k:ℝ)+1:ℂ) := by
    have hh := congrArg conj hs
    norm_num [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal] at hh ⊢
    linear_combination hh
  have hpair : signedPair k c d= -Complex.I*((k:ℝ)+1:ℂ)*kernel (responseWeight k) c d+
      Complex.I*((k:ℝ)+1:ℂ)*conj (kernel (responseWeight k) d c) := by
    change signedPair k c d=_ at he
    linear_combination he+(1/2:ℂ)*kernel (responseWeight k) c d*hs+
      (1/2:ℂ)*conj (kernel (responseWeight k) d c)*ht
  have hw : responseWeight k=(fun j => Complex.I*responseSamples (radialStep k) j) := by
    funext j; exact response_radial_readout k j
  rw [hpair, hw, kernel_scale, kernel_scale]
  simp only [map_mul, Complex.conj_I]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

/-- The SAME native completed state in each of the two independent inputs. -/
def mixedPair (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) : ℂ :=
  signedPair k (finiteJetSource S c k) (finiteOddJetSource T d k)

theorem mixed_pair_exact (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, mixedPair S T c d k=((k:ℂ)+1)*
      (kernel (responseSamples (radialStep k)) (finiteJetSource S c k) (finiteOddJetSource T d k)-
       kernel (responseSamples (radialStep k)) (finiteOddJetSource T d k) (finiteJetSource S c k)) := by
  let N := (2*S.sup id+1)+(2*T.sup id+2)
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hc : (finiteJetSource S c k).support ⊆ Finset.range N :=
    (finite_source_support S c k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hdc : (finiteOddJetSource T d k).support ⊆ Finset.range N :=
    (finite_odd_source_support T d k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hF (j : Fin N) := (hk j).2.1
  have hd (j : ℕ) (hj : j<N) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := complete_complex_pair k _ _ hc hdc hF hd
  rw [kernel_imaginary_real _ _ _ (response_samples_real (radialStep k))
    (odd_coefficients_imaginary T d k) (even_coefficients_real S c k)] at he
  exact he

theorem mixed_pair_conjugate (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, conj (mixedPair S T c d k)= -mixedPair S T c d k := by
  filter_upwards [mixed_pair_exact S T c d] with k hk
  rw [hk]
  simp only [map_mul, map_sub, map_add, map_natCast, map_one]
  rw [kernel_real_imaginary _ _ _ (response_samples_real (radialStep k))
    (even_coefficients_real S c k) (odd_coefficients_imaginary T d k),
    kernel_imaginary_real _ _ _ (response_samples_real (radialStep k))
    (odd_coefficients_imaginary T d k) (even_coefficients_real S c k)]
  ring

/-- Real orthogonality is a conclusion AFTER the complete complex pairing. -/
theorem mixed_pair_real_zero (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, (mixedPair S T c d k).re=0 := by
  filter_upwards [mixed_pair_conjugate S T c d] with k hk
  have he := congrArg Complex.re hk
  simp only [Complex.conj_re, Complex.neg_re] at he
  linarith

/-- Complex TFVD recomposition of the mixed source; both ordered correction
terms survive in the identity before its final real readout. -/
theorem mixed_pair_green_recomposition (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, mixedPair S T c d k=
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k (finiteJetSource S c k) 0+
          completedSourceParts eta h0 h1 k (finiteJetSource S c k) 1)
        (completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 0+
          completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 1)+
      (canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k (finiteJetSource S c k) 2)
        (physicalCompletedFiniteSource k (finiteOddJetSource T d k))+
       canonicalCompletedNativeProjectiveChiralForm
        (physicalCompletedFiniteSource k (finiteJetSource S c k))
        (completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 2)) := by
  let N := (2*S.sup id+1)+(2*T.sup id+2)
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  have hc : (finiteJetSource S c k).support ⊆ Finset.range N :=
    (finite_source_support S c k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hdc : (finiteOddJetSource T d k).support ⊆ Finset.range N :=
    (finite_odd_source_support T d k).trans (Finset.range_mono (by dsimp [N]; omega))
  have hd (j : ℕ) (hj : j<N+1) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := completed_kernel_mixed_reduction eta h0 h1 k _ _ hc hdc hd
  rw [← completed_commutator_mixed_pairing eta h0 h1 k _ _ hc hdc hd] at he
  exact he

end
end CarryMixedParity
