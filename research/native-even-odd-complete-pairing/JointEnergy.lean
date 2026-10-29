import MixedPairing

namespace CarryMixedParity
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem native_source_add (k : ℕ) (c d : ℕ →₀ ℂ) :
    physicalCompletedFiniteSource k (c+d)=
      physicalCompletedFiniteSource k c+physicalCompletedFiniteSource k d := by
  simp only [physicalCompletedFiniteSource_original, map_add]

/-- Polarization in the ORIGINAL signed form, not in a replacement norm. -/
theorem signed_form_add (p q : CanonicalCompletedNativeProjectiveChiralCarrier) :
    (canonicalCompletedNativeProjectiveChiralForm (p+q) (p+q)).re=
      (canonicalCompletedNativeProjectiveChiralForm p p).re+
        (canonicalCompletedNativeProjectiveChiralForm q q).re+
          2*(canonicalCompletedNativeProjectiveChiralForm p q).re := by
  have h1 : (inner ℂ p.1 q.1).re=(inner ℂ q.1 p.1).re := inner_re_symm (𝕜:=ℂ) _ _
  have h2 : (inner ℂ p.2 q.2).re=(inner ℂ q.2 p.2).re := inner_re_symm (𝕜:=ℂ) _ _
  unfold canonicalCompletedNativeProjectiveChiralForm
  simp only [Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re, h1, h2]
  ring

theorem full_energy_add (k : ℕ) (c d : ℕ →₀ ℂ) :
    fullEnergy k (c+d)=fullEnergy k c+fullEnergy k d+2*(signedPair k c d).re := by
  unfold fullEnergy
  rw [native_source_add]
  exact signed_form_add _ _

/-- Literal sum of the two existing finite inputs; both quadratures remain. -/
def jointJetSource (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  finiteJetSource S c k+finiteOddJetSource T d k

theorem joint_source_original (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (jointJetSource S T c d k)=
      (∑ r ∈ S, (c r:ℂ) • projectiveChiralDifferenceJet k (2*r))+
        ∑ s ∈ T, (d s:ℂ) • projectiveChiralDifferenceJet k (2*s+1) := by
  rw [jointJetSource, native_source_add, finite_source_original, finite_odd_source_original]

/-- The interference term vanishes only AFTER the complete complex
cross-pairing and its conjugation identity have been proved. -/
theorem joint_energy_add (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (jointJetSource S T c d k)=
      fullEnergy k (finiteJetSource S c k)+fullEnergy k (finiteOddJetSource T d k) := by
  filter_upwards [mixed_pair_real_zero S T c d] with k hk
  rw [jointJetSource, full_energy_add, show (signedPair k (finiteJetSource S c k)
    (finiteOddJetSource T d k)).re=0 from hk]
  ring

/-- The joint correction, for arbitrary independent finite inputs in the
same original TWO-channel carrier. No sign of either canonical form is used. -/
theorem joint_energy_correction_tendsto (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (jointJetSource S T c d k)-(canonicalForm S c+oddCanonicalForm T d)))
      atTop (nhds (canonicalCorrection S c+oddCanonicalCorrection T d)) := by
  have ht := (finite_energy_correction_tendsto S c).add
    (finite_odd_energy_correction_tendsto T d)
  apply ht.congr'
  filter_upwards [joint_energy_add S T c d] with k hk
  rw [hk]
  ring

theorem joint_source_support (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) :
    (jointJetSource S T c d k).support ⊆ Finset.range ((2*S.sup id+1)+(2*T.sup id+2)) := by
  intro j hj
  have hs : (finiteJetSource S c k+finiteOddJetSource T d k).support ⊆
      (finiteJetSource S c k).support ∪ (finiteOddJetSource T d k).support := Finsupp.support_add
  rcases Finset.mem_union.mp (hs hj) with he | ho
  · have h := Finset.mem_range.mp (finite_source_support S c k he)
    exact Finset.mem_range.mpr (by omega)
  · have h := Finset.mem_range.mp (finite_odd_source_support T d k ho)
    exact Finset.mem_range.mpr (by omega)

/-- Full joint TFVD recomposition with the halo address retained. -/
theorem joint_green_recomposition (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (jointJetSource S T c d k)=
      bulkBoundaryEnergy eta h0 h1 k (jointJetSource S T c d k)+
        mixedEnergy eta h0 h1 k (jointJetSource S T c d k) := by
  let N := (2*S.sup id+1)+(2*T.sup id+2)
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  have hd (j : ℕ) (hj : j<N+1) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  exact full_split eta h0 h1 k _ (joint_source_support S T c d k) hd

theorem joint_green_correction_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (bulkBoundaryEnergy eta h0 h1 k (jointJetSource S T c d k)+
        mixedEnergy eta h0 h1 k (jointJetSource S T c d k)-
          (canonicalForm S c+oddCanonicalForm T d)))
      atTop (nhds (canonicalCorrection S c+oddCanonicalCorrection T d)) := by
  apply (joint_energy_correction_tendsto S T c d).congr'
  filter_upwards [joint_green_recomposition eta h0 h1 S T c d] with k hk
  rw [hk]

theorem joint_norm_difference_correction (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (‖(physicalCompletedFiniteSource k (jointJetSource S T c d k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (jointJetSource S T c d k)).2‖^2-
          2*(canonicalForm S c+oddCanonicalForm T d)))
      atTop (nhds (2*(canonicalCorrection S c+oddCanonicalCorrection T d))) := by
  have ht := (tendsto_const_nhds (x := (2:ℝ))).mul (joint_energy_correction_tendsto S T c d)
  apply ht.congr'
  filter_upwards [] with k
  rw [← original_norm_difference]
  ring

end
end CarryMixedParity
