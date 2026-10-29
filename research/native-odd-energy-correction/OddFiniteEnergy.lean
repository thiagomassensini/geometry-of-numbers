import OddPairExpansion

namespace CarryOddEnergy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Literal finite sum of the existing original radial jets. -/
def finiteOddJetSource (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  ∑ r ∈ S, (c r:ℂ) • radialJetCoefficients k (2*r+1)

theorem finite_odd_source_profile (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    finiteOddJetSource S c k=∑ r ∈ S,
      ((c r:ℂ)*((k:ℂ)+1)^(2*r+1)) • nativeOddProfile r := by
  simp only [finiteOddJetSource, radial_odd_calibration, smul_smul]

/-- Whole TWO-channel source identity, before any signed pairing. -/
theorem finite_odd_source_original (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (finiteOddJetSource S c k)=
      ∑ r ∈ S, (c r:ℂ) • projectiveChiralDifferenceJet k (2*r+1) := by
  simp only [finiteOddJetSource, physicalCompletedFiniteSource_original, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [← physicalCompletedFiniteSource_original, radial_jet_original_source]

/-- A finite support bound is derived from the actual original stencils. -/
theorem finite_odd_source_support (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    (finiteOddJetSource S c k).support ⊆ Finset.range (2*S.sup id+2) := by
  classical
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  have hz : finiteOddJetSource S c k j=0 := by
    rw [finite_odd_source_profile]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro r hr
    have hm : r ≤ S.sup id := Finset.le_sup (f:=id) hr
    have hjr : j ∉ (nativeOddProfile r).support := by
      intro he
      have := Finset.mem_range.mp (odd_profile_support r he)
      omega
    rw [Finsupp.notMem_support_iff.mp hjr, mul_zero]
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- Symmetrization retains BOTH ordered complex crosses of the original source. -/
theorem finite_odd_source_pairing (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    ((k:ℂ)+1)*2*kernel (responseSamples (radialStep k))
      (finiteOddJetSource S c k) (finiteOddJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, (c r:ℂ)*(c s:ℂ)*normalizedOddPair r s k := by
  rw [finite_odd_source_profile, kernel_sum_inputs]
  simp_rw [kernel_scale_inputs]
  simp only [map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  rw [mul_assoc, double_sum_symmetrize]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  unfold normalizedOddPair oddPairKernel
  rw [show 2*(r+s+1)+1=(2*r+1)+(2*s+1)+1 by omega, pow_succ, pow_add]
  ring

/-- The previous identity reaches the SAME native signed energy, with
regularity discharged on the actual finite prefix. -/
theorem finite_odd_energy_pairing (S : Finset ℕ) (c : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (finiteOddJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, c r*c s*(normalizedOddPair r s k).re := by
  let N := 2*S.sup id+2
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hc := finite_odd_source_support S c k
  have hF (j : Fin N) := (hk j).2.1
  have hd (j : ℕ) (hj : j<N) :=
    radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := full_response_flux k (finiteOddJetSource S c k) hc hF hd
  have hw : responseWeight k=(fun j => Complex.I*responseSamples (radialStep k) j) := by
    funext j
    exact response_radial_readout k j
  rw [hw] at he
  change fullEnergy k (finiteOddJetSource S c k)=
    2*((k:ℝ)+1)*(kernel (fun j => Complex.I*responseSamples (radialStep k) j)
      (finiteOddJetSource S c k) (finiteOddJetSource S c k)).im at he
  rw [kernel_scale] at he
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at he
  have hp := congrArg Complex.re (finite_odd_source_pairing S c k)
  simp [Complex.mul_re, Complex.mul_im] at hp
  rw [he]
  linear_combination hp

/-- Complete TFVD split, including the outgoing halo address, with no sector
removed. The same source remains on all three sides. -/
theorem finite_odd_green_recomposition (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (finiteOddJetSource S c k)=
      bulkBoundaryEnergy eta h0 h1 k (finiteOddJetSource S c k)+
        mixedEnergy eta h0 h1 k (finiteOddJetSource S c k) := by
  let N := 2*S.sup id+2
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  have hd (j : ℕ) (hj : j<N+1) :=
    radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  exact full_split eta h0 h1 k _ (finite_odd_source_support S c k) hd

/-- Original canonical quadratic form; no whitening or sign is supplied. -/
def oddCanonicalForm (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, c r*c s*h (r+s+1)

/-- Explicit first correction, using the proved spatial coefficients. -/
def oddCanonicalCorrection (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, -(c r*c s)*(spatialCorrection (2*r+1) (2*s+1)).re*h (r+s+2)

/-- The first correction of the SAME full completed energy, in arbitrary
finite order. No PosDef, IsUnit, pivot sign or fitted Gram is assumed. -/
theorem finite_odd_energy_correction_tendsto (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (finiteOddJetSource S c k)-oddCanonicalForm S c))
      atTop (nhds (oddCanonicalCorrection S c)) := by
  have hr (r s : ℕ) : Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      ((normalizedOddPair r s k).re-h (r+s+1))) atTop
      (nhds (-(spatialCorrection (2*r+1) (2*s+1)).re*h (r+s+2))) := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (normalized_odd_pair_correction_tendsto r s)
    simpa [Function.comp_def, pow_two, Complex.mul_re, Complex.mul_im] using hh
  have hlim := tendsto_finsetSum S (fun r _ => tendsto_finsetSum S (fun s _ =>
    (tendsto_const_nhds (x := c r*c s)).mul (hr r s)))
  have he : (∑ r ∈ S, ∑ s ∈ S, c r*c s*(-(spatialCorrection (2*r+1) (2*s+1)).re*h (r+s+2)))=
      oddCanonicalCorrection S c := by
    unfold oddCanonicalCorrection
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [finite_odd_energy_pairing S c] with k hk
  rw [hk]
  unfold oddCanonicalForm
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring
/-- The correction of the recomposed Green/bulk/boundary balance is the same
one; positivity or a vanishing mixed sector is not presumed. -/
theorem finite_odd_green_correction_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (bulkBoundaryEnergy eta h0 h1 k (finiteOddJetSource S c k)+
        mixedEnergy eta h0 h1 k (finiteOddJetSource S c k)-oddCanonicalForm S c))
      atTop (nhds (oddCanonicalCorrection S c)) := by
  apply (finite_odd_energy_correction_tendsto S c).congr'
  filter_upwards [finite_odd_green_recomposition eta h0 h1 S c] with k hk
  rw [hk]


end
end CarryOddEnergy
