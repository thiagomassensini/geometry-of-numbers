import FourSourcePathLimit
namespace CarryCriticalComplete
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- The regularity threshold depends on the finite prefix, not the input. -/
theorem regular_imaginary_pair_exact (k N : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) (hy : y.support ⊆ Finset.range N)
    (hxi : ∀ j, conj (x j)= -x j) (hyi : ∀ j, conj (y j)= -y j)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    signedPair k x y=((k:ℂ)+1)*symKernel (responseSamples (radialStep k)) x y := by
  have hd (j : ℕ) (hj : j<N) := radial_weight_difference k j (hF ⟨j,hj⟩) (hP ⟨j,hj⟩)
  have he := complete_complex_pair k x y hx hy hF hd
  rw [kernel_imaginary_imaginary _ _ _ (response_samples_real (radialStep k)) hyi hxi] at he
  exact he

theorem critical_input_imaginary (a : ℝ) (k j : ℕ) :
    conj (criticalOddSource a k j)= -criticalOddSource a k j := by
  rw [critical_input_split]
  simp only [Finsupp.sub_apply,map_sub,principal_imaginary,defect_imaginary]
  ring

/-- All nine field crossings are synthesized first. One common radial
threshold works for TWO independent parameters in the exact full split. -/
theorem critical_split_uniform (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : ℝ,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)+
        crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  intro a b
  have hF (i : Fin 4) := (hk i).2.1
  have hP (i : Fin 4) := (hk i).2.2
  have hc := regular_imaginary_pair_exact k 4 _ _ (critical_four_support a k) (critical_four_support b k)
    (critical_input_imaginary a k) (critical_input_imaginary b k) hF hP
  have hp := regular_imaginary_pair_exact k 4 _ _ (principal_support a k) (principal_support b k)
    (principal_imaginary a k) (principal_imaginary b k) hF hP
  have hd := regular_imaginary_pair_exact k 4 _ _ (defect_support a k) (defect_support b k)
    (defect_imaginary a k) (defect_imaginary b k) hF hP
  simp only [cross_green_eq_original]
  change signedPair k _ _=signedPair k _ _+signedPair k _ _
  rw [hc,hp,hd,critical_kernel_split,mul_add]

/-- The correction is linear in its actual real parameter, at source level. -/
theorem defect_input_scale (a : ℝ) (k : ℕ) :
    defectInput a k=(a:ℂ) • defectInput 1 k := by
  ext j
  simp only [defectInput,Finsupp.smul_apply,smul_eq_mul]
  push_cast
  ring

/-- Exact COMPLEX polarized factor, retaining both quadratures before Re. -/
theorem defect_pair_factor (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (k : ℕ) (a b : ℝ) :
    crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)=
      (a:ℂ)*(b:ℂ)*crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k) := by
  simp only [cross_green_eq_original]
  rw [defect_input_scale a k,defect_input_scale b k]
  simp only [physicalCompletedFiniteSource_original,
    map_smul,canonicalCompletedNativeProjectiveChiralForm,Prod.smul_fst,Prod.smul_snd,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  ring

/-- Vanishing defect energy follows from the complete native boundary VECTOR
limit and the exact source remainder. No canonical moment is used. -/
theorem defect_energy_tendsto_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => (crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re)
      atTop (nhds 0) := by
  have ht := four_source_path_energy_tendsto (defectInput 1) 0 (defect_support 1)
    (defect_boundary_tendsto_zero 1)
  have hz : nativeSourceFourBoundaryEnergy 0/2=0 := by
    simp [nativeSourceFourBoundaryEnergy,nativeSourceEvenBoundaryEnergy,nativeSourceOddBoundaryEnergy]
  rw [hz] at ht
  simpa only [cross_green_eq_original] using ht

/-- Real readout only AFTER the exact two-argument complex factorization. -/
theorem defect_pair_re_factor (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (k : ℕ) (a b : ℝ) :
    (crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)).re=
      a*b*(crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re := by
  rw [defect_pair_factor]
  simp [mul_assoc]

def defectRateTemplate (t : ℝ) : Fin 4 → ℂ :=
  fun i => Complex.I*((![0,0,7,70*t] i/Real.sqrt 2:ℝ):ℂ)

/-- Scaled correction is used only to extract its actual quadratic rate.
No replacement is made in the physical source being certified. -/
theorem defect_scaled_boundary_tendsto :
    Tendsto (fun k : ℕ => sourceBoundary k ((((k:ℝ)+1):ℂ) • defectInput 1 k)) atTop
      (nhds (defectRateTemplate 0)) := by
  have hc : Continuous defectRateTemplate := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [defectRateTemplate] <;> fun_prop
  have ht := hc.continuousAt.tendsto.comp radialFourSourceStep_tendsto_zero
  apply ht.congr'
  filter_upwards [boundary_eventually_exact] with k hk
  have hκ : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  rw [source_boundary_smul]
  change defectRateTemplate (radialFourSourceStep k)=(((k:ℝ)+1):ℂ) • defectBoundary 1 k
  rw [(hk 1).2]
  funext i
  fin_cases i <;> norm_num [defectRateTemplate,defectTemplate,radialFourSourceStep,Pi.smul_apply,smul_eq_mul] <;>
    field_simp [hκ]

/-- The leading rate comes from the exact source analytic remainder theorem,
not from canonical moments or a sign supplied for the coefficient. -/
theorem defect_scaled_energy_limit (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re) atTop
      (nhds (nativeSourceFourBoundaryEnergy (defectRateTemplate 0)/2)) := by
  have hx (k : ℕ) : ((((k:ℝ)+1):ℂ) • defectInput 1 k).support ⊆ Finset.range 4 :=
    Finsupp.support_smul.trans (defect_support 1 k)
  have ht := four_source_path_energy_tendsto
    (fun k : ℕ => (((k:ℝ)+1):ℂ) • defectInput 1 k) (defectRateTemplate 0) hx defect_scaled_boundary_tendsto
  apply ht.congr'
  filter_upwards [] with k
  have he := defect_pair_factor eta h0 h1 k ((k:ℝ)+1) ((k:ℝ)+1)
  simp only [cross_green_eq_original,defect_input_scale ((k:ℝ)+1) k] at he
  have hr := congrArg Complex.re he
  simpa [cross_green_eq_original,crossSignedPair,pow_two,mul_assoc] using hr

/-- Uniform O(kappa^-2) control for TWO independent, unbounded parameters.
The constant bounds the actual native rate; its sign is not presumed. -/
theorem defect_uniform_quadratic_rate (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k : ℕ in atTop, ∀ a b : ℝ,
      |(crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)).re|≤
        M*|a*b|/((k:ℝ)+1)^2 := by
  let L := nativeSourceFourBoundaryEnergy (defectRateTemplate 0)/2
  have ht := (defect_scaled_energy_limit eta h0 h1).abs
  have hs := ht.eventually (gt_mem_nhds (by linarith : |L| < |L| + 1))
  refine ⟨|L|+1,by positivity,?_⟩
  filter_upwards [hs] with k hk
  intro a b
  have hκ : (0:ℝ)<((k:ℝ)+1)^2 := by positivity
  have hq : |(crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re|≤
      (|L|+1)/((k:ℝ)+1)^2 := by
    apply (le_div_iff₀ hκ).mpr
    rw [abs_mul,abs_of_nonneg hκ.le] at hk
    nlinarith
  rw [defect_pair_re_factor,abs_mul]
  calc
    _ ≤ |a*b| *((|L|+1)/((k:ℝ)+1)^2) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    _ = _ := by ring

/-- Relative smallness is uniform in BOTH a,b after a single threshold.
It is not absolute smallness of unbounded-parameter source energies. -/
theorem defect_uniform_relative_small (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : ℝ,
      |(crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)).re|≤ε*|a*b| := by
  have ht : Tendsto (fun k : ℕ => |(crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re|)
      atTop (nhds 0) := by
    simpa using (defect_energy_tendsto_zero eta h0 h1).abs
  have hs := ht.eventually (gt_mem_nhds he)
  filter_upwards [hs] with k hk
  intro a b
  have hr : (crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)).re=
      a*b*(crossGreenPair eta h0 h1 k k (defectInput 1 k) (defectInput 1 k)).re := by
    rw [defect_pair_factor]
    simp [mul_assoc]
  rw [hr,abs_mul]
  calc
    _ ≤ |a*b| *ε := mul_le_mul_of_nonneg_left hk.le (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- Uniform signed correction to the COMPLETE critical Green form, obtained
only after its full complex polarized decomposition has been established. -/
theorem critical_principal_uniform_close (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : ℝ,
      |(crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)-
        crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)).re|≤ε*|a*b| := by
  filter_upwards [critical_split_uniform eta h0 h1,defect_uniform_relative_small eta h0 h1 ε he] with k hs hd
  intro a b
  rw [hs a b,add_sub_cancel_left]
  exact hd a b

end
end CarryCriticalComplete
