import PairExpansion

namespace CarryEnergyCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Literal finite sum of the existing original radial jets. -/
def finiteJetSource (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  ∑ r ∈ S, (c r:ℂ) • radialJetCoefficients k (2*r)

theorem finite_source_profile (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    finiteJetSource S c k=∑ r ∈ S,
      ((c r:ℂ)*((k:ℂ)+1)^(2*r)) • nativeEvenProfile r := by
  simp only [finiteJetSource, radial_even_calibration, smul_smul]

/-- Whole TWO-channel source identity, before any signed pairing. -/
theorem finite_source_original (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (finiteJetSource S c k)=
      ∑ r ∈ S, (c r:ℂ) • projectiveChiralDifferenceJet k (2*r) := by
  simp only [finiteJetSource, physicalCompletedFiniteSource_original, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [← physicalCompletedFiniteSource_original, radial_jet_original_source]

/-- A finite support bound is derived from the actual original stencils. -/
theorem finite_source_support (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    (finiteJetSource S c k).support ⊆ Finset.range (2*S.sup id+1) := by
  classical
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  have hz : finiteJetSource S c k j=0 := by
    rw [finite_source_profile]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro r hr
    have hm : r ≤ S.sup id := Finset.le_sup (f:=id) hr
    have hjr : j ∉ (nativeEvenProfile r).support := by
      intro he
      have := Finset.mem_range.mp (native_profile_support r he)
      omega
    rw [Finsupp.notMem_support_iff.mp hjr, mul_zero]
  exact (Finsupp.mem_support_iff.mp hj) hz

theorem weight_sum_input (w : ℕ → ℂ) (S : Finset ℕ) (f : ℕ → ℕ →₀ ℂ) :
    coefficientWeight w (∑ r ∈ S, f r)=∑ r ∈ S, coefficientWeight w (f r) := by
  classical
  ext j
  simp only [coefficient_weight_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finset.mul_sum]

theorem kernel_sum_inputs (w : ℕ → ℂ) (S U : Finset ℕ) (f g : ℕ → ℕ →₀ ℂ) :
    kernel w (∑ r ∈ S, f r) (∑ s ∈ U, g s)=
      ∑ r ∈ S, ∑ s ∈ U, kernel w (f r) (g s) := by
  change inner ℂ (physicalCauchySynthesis (∑ r ∈ S, f r))
    (physicalCauchySynthesis (coefficientWeight w (∑ s ∈ U, g s)))=_
  simp only [weight_sum_input, map_sum, inner_sum, sum_inner]
  rw [Finset.sum_comm]
  rfl

theorem kernel_scale_inputs (w : ℕ → ℂ) (a b : ℂ) (f g : ℕ →₀ ℂ) :
    kernel w (a • f) (b • g)=conj a*b*kernel w f g := by
  simp only [kernel, sectorKernel, map_smul, field_scale_input, inner_smul_left, inner_smul_right]
  ring

theorem double_sum_symmetrize (S : Finset ℕ) (a : ℕ → ℂ) (K : ℕ → ℕ → ℂ) :
    2*(∑ r ∈ S, ∑ s ∈ S, a r*a s*K r s)=
      ∑ r ∈ S, ∑ s ∈ S, a r*a s*(K r s+K s r) := by
  have he : (∑ r ∈ S, ∑ s ∈ S, a r*a s*K s r)=
      ∑ r ∈ S, ∑ s ∈ S, a r*a s*K r s := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [he]
  ring

/-- Symmetrization retains BOTH ordered complex crosses of the original source. -/
theorem finite_source_pairing (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    ((k:ℂ)+1)*2*kernel (responseSamples (radialStep k))
      (finiteJetSource S c k) (finiteJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, (c r:ℂ)*(c s:ℂ)*normalizedPair r s k := by
  rw [finite_source_profile, kernel_sum_inputs]
  simp_rw [kernel_scale_inputs]
  simp only [map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  rw [mul_assoc, double_sum_symmetrize]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  unfold normalizedPair pairKernel
  rw [show 2*(r+s)+1=2*r+2*s+1 by omega, pow_succ, pow_add]
  ring

/-- The previous identity reaches the SAME native signed energy, with
regularity discharged on the actual finite prefix. -/
theorem finite_energy_pairing (S : Finset ℕ) (c : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (finiteJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, c r*c s*(normalizedPair r s k).re := by
  let N := 2*S.sup id+1
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hc := finite_source_support S c k
  have hF (j : Fin N) := (hk j).2.1
  have hd (j : ℕ) (hj : j<N) :=
    radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := full_response_flux k (finiteJetSource S c k) hc hF hd
  have hw : responseWeight k=(fun j => Complex.I*responseSamples (radialStep k) j) := by
    funext j
    exact response_radial_readout k j
  rw [hw] at he
  change fullEnergy k (finiteJetSource S c k)=
    2*((k:ℝ)+1)*(kernel (fun j => Complex.I*responseSamples (radialStep k) j)
      (finiteJetSource S c k) (finiteJetSource S c k)).im at he
  rw [kernel_scale] at he
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at he
  have hp := congrArg Complex.re (finite_source_pairing S c k)
  simp [Complex.mul_re, Complex.mul_im] at hp
  rw [he]
  linear_combination hp

/-- Complete TFVD split, including the outgoing halo address, with no sector
removed. The same source remains on all three sides. -/
theorem finite_source_green_recomposition (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (finiteJetSource S c k)=
      bulkBoundaryEnergy eta h0 h1 k (finiteJetSource S c k)+
        mixedEnergy eta h0 h1 k (finiteJetSource S c k) := by
  let N := 2*S.sup id+1
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  have hd (j : ℕ) (hj : j<N+1) :=
    radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  exact full_split eta h0 h1 k _ (finite_source_support S c k) hd

/-- Original canonical quadratic form; no whitening or sign is supplied. -/
def canonicalForm (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, c r*c s*h (r+s)

/-- Explicit first correction, using the proved spatial coefficients. -/
def canonicalCorrection (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, -(c r*c s)*(spatialCorrection (2*r) (2*s)).re*h (r+s+1)

/-- The first correction of the SAME full completed energy, in arbitrary
finite order. No PosDef, IsUnit, pivot sign or fitted Gram is assumed. -/
theorem finite_energy_correction_tendsto (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (finiteJetSource S c k)-canonicalForm S c))
      atTop (nhds (canonicalCorrection S c)) := by
  have hr (r s : ℕ) : Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      ((normalizedPair r s k).re-h (r+s))) atTop
      (nhds (-(spatialCorrection (2*r) (2*s)).re*h (r+s+1))) := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (normalized_pair_correction_tendsto r s)
    simpa [Function.comp_def, pow_two, Complex.mul_re, Complex.mul_im] using hh
  have hlim := tendsto_finsetSum S (fun r _ => tendsto_finsetSum S (fun s _ =>
    (tendsto_const_nhds (x := c r*c s)).mul (hr r s)))
  have he : (∑ r ∈ S, ∑ s ∈ S, c r*c s*(-(spatialCorrection (2*r) (2*s)).re*h (r+s+1)))=
      canonicalCorrection S c := by
    unfold canonicalCorrection
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [finite_energy_pairing S c] with k hk
  rw [hk]
  unfold canonicalForm
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring
/-- The correction of the recomposed Green/bulk/boundary balance is the same
one; positivity or a vanishing mixed sector is not presumed. -/
theorem finite_green_correction_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (bulkBoundaryEnergy eta h0 h1 k (finiteJetSource S c k)+
        mixedEnergy eta h0 h1 k (finiteJetSource S c k)-canonicalForm S c))
      atTop (nhds (canonicalCorrection S c)) := by
  apply (finite_energy_correction_tendsto S c).congr'
  filter_upwards [finite_source_green_recomposition eta h0 h1 S c] with k hk
  rw [hk]


end
end CarryEnergyCorrection
