import CriticalAddressSplit
namespace CarryAddressSplit
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- Generic original completed-source transport, preserving the full complex form. -/
theorem imaginary_families_exact (N : ℕ) (c d : ℕ → ℕ →₀ ℂ)
    (hc : ∀ k, (c k).support ⊆ Finset.range N)
    (hd : ∀ k, (d k).support ⊆ Finset.range N)
    (hci : ∀ k j, conj (c k j)= -c k j) (hdi : ∀ k j, conj (d k j)= -d k j) :
    ∀ᶠ k : ℕ in atTop, signedPair k (c k) (d k)=
      ((k:ℂ)+1)*symKernel (responseSamples (radialStep k)) (c k) (d k) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  have hF (j : Fin N) := (hk j).2.1
  have hdiff (j : ℕ) (hj : j<N) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have he := complete_complex_pair k (c k) (d k) (hc k) (hd k) hF hdiff
  rw [kernel_imaginary_imaginary _ _ _ (response_samples_real (radialStep k)) (hdi k) (hci k)] at he
  exact he

/-- All NINE Green crossings cancel jointly in the off-diagonal block.
No claim that an individual field crossing vanishes. -/
theorem principal_defect_green_orthogonal (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (principalInput a k) (defectInput b k)=0 := by
  have hp k := (principal_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  have hd k := (defect_support b k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  filter_upwards [imaginary_families_exact 5 (principalInput a) (defectInput b)
    hp hd (principal_imaginary a) (defect_imaginary b)] with k hk
  rw [cross_green_eq_original]
  change signedPair k _ _=0
  rw [hk,principal_defect_kernel_orthogonal,mul_zero]

theorem defect_principal_green_orthogonal (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (defectInput a k) (principalInput b k)=0 := by
  have hp k := (principal_support b k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  have hd k := (defect_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  filter_upwards [imaginary_families_exact 5 (defectInput a) (principalInput b)
    hd hp (defect_imaginary a) (principal_imaginary b)] with k hk
  rw [cross_green_eq_original]
  change signedPair k _ _=0
  rw [hk,defect_principal_kernel_orthogonal,mul_zero]

/-- Exact source-level split with two independent arguments, BEFORE response readout. -/
theorem critical_kernel_split (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    symKernel w (criticalOddSource a k) (criticalOddSource b k)=
      symKernel w (principalInput a k) (principalInput b k)+
      symKernel w (defectInput a k) (defectInput b k) := by
  rw [critical_input_split,critical_input_split,sym_sub_sub,
    principal_defect_kernel_orthogonal,defect_principal_kernel_orthogonal]
  ring

/-- Original cubic filter on the squared grid. No moments enter this identity. -/
theorem cubic_kernel_grid (k : ℕ) (w : ℕ → ℂ) :
    2*((k:ℂ)+1)^7*kernel w (nativeOddProfile 1) (nativeOddProfile 1)=
      -gridThird (squaredScale k) (normalizedFourSamples k w) := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  rw [native_odd_kernel_filter,grid_third_barycentric _ (squared_scale_nonzero k)]
  norm_num [oddFilter,oddFilterCoefficient,nativeOddBeta,Finset.sum_range_succ,
    normalizedFourSamples,squaredScale]
  field_simp
  ring

/-- Exact retained correction from the physical source component, not a scalar fit. -/
theorem defect_kernel_grid (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    ((k:ℂ)+1)*symKernel w (defectInput a k) (defectInput b k)=
      49*(a:ℂ)*(b:ℂ)*squaredScale k*
        gridThird (squaredScale k) (fun j => squaredNode (squaredScale k) j*normalizedFourSamples k w j) := by
  have hz := endpoint_odd_power_zero 1 0 (by omega)
  have hzero : sourceEndpoint (nativeOddProfile 1)=0 := by
    simpa only [address_power_zero] using hz
  have he := kernel_address_green w (nativeOddProfile 1) (addressPower 1 (nativeOddProfile 1))
  rw [hzero,map_zero,zero_mul,address_power_comp] at he
  rw [kernel_address_right 2 w (nativeOddProfile 1) (nativeOddProfile 1)] at he
  have hg := cubic_kernel_grid k (fun j => ((j:ℂ)+1)^2*w j)
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  simp only [symKernel,defectInput,kernel_smul_left,kernel_smul_right,
    Complex.conj_ofReal]
  push_cast
  have heq : gridThird (squaredScale k) (fun j => squaredNode (squaredScale k) j*normalizedFourSamples k w j)=
      squaredScale k*gridThird (squaredScale k)
        (normalizedFourSamples k (fun j => ((j:ℂ)+1)^2*w j)) := by
    unfold gridThird gridSecondRight gridSecond squaredNode normalizedFourSamples
    ring
  rw [heq]
  unfold squaredScale at hg ⊢
  field_simp at hg ⊢
  linear_combination -49*(a:ℂ)*(b:ℂ)*hg+98*(a:ℂ)*(b:ℂ)*((k:ℂ)+1)^7*he

/-- Principal readout from PR116, now assigned to its literal physical component. -/
abbrev principalGrid (a b : ℝ) (k : ℕ) : ℂ :=
  -gridThird (squaredScale k) (fun j =>
    (1+(a:ℂ)*(squaredNode (squaredScale k) j+12*squaredScale k))*
    (1+(b:ℂ)*(squaredNode (squaredScale k) j+12*squaredScale k))*nativeFourSamples k j)

/-- The correction is identified in the COMPLETE two-leg, nine-cross Green form. -/
theorem defect_physical_grid (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)=nativeGridDefect a b k := by
  have hd a k := (defect_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  filter_upwards [imaginary_families_exact 5 (defectInput a) (defectInput b)
    (hd a) (hd b) (defect_imaginary a) (defect_imaginary b)] with k hk
  rw [cross_green_eq_original]
  exact hk.trans (defect_kernel_grid a b k _)

/-- Full original signed Green form decomposes; no independent channel is discarded. -/
theorem critical_physical_split (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)+
        crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k) := by
  have hp a k := (principal_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  have hd a k := (defect_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  filter_upwards [critical_signed_readout_exact a b,
    imaginary_families_exact 5 (principalInput a) (principalInput b)
      (hp a) (hp b) (principal_imaginary a) (principal_imaginary b),
    imaginary_families_exact 5 (defectInput a) (defectInput b)
      (hd a) (hd b) (defect_imaginary a) (defect_imaginary b)] with k hc hx hy
  simp only [cross_green_eq_original,cross_pair_diagonal]
  rw [hc,hx,hy,← critical_kernel_readout,← critical_kernel_readout]
  change ((k:ℂ)+1)*symKernel _ _ _=_
  rw [critical_kernel_split,mul_add]

/-- The missing physical identity for PR116's PRINCIPAL term, in two arguments. -/
theorem principal_physical_grid (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)=principalGrid a b k := by
  filter_upwards [critical_physical_split a b eta h0 h1,
    native_critical_product_defect_exact a b eta h0 h1,
    defect_physical_grid a b eta h0 h1] with k hs hg hd
  change crossGreenPair eta h0 h1 k k _ _=principalGrid a b k+nativeGridDefect a b k at hg
  rw [hd] at hs
  linear_combination hg-hs

/-- This part tends to zero but was NOT erased from any finite identity. -/
theorem defect_physical_tendsto_zero (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k))
      atTop (nhds 0) := by
  apply (native_grid_defect_tendsto_zero a b).congr'
  filter_upwards [defect_physical_grid a b eta h0 h1] with k hk
  exact hk.symm

/-- Its first scaled coefficient is kept, WITHOUT a sign hypothesis. -/
theorem defect_physical_scaled_tendsto (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k (defectInput a k) (defectInput b k)/squaredScale k)
      atTop (nhds (49*(a:ℂ)*(b:ℂ)*(h 2:ℂ))) := by
  apply (native_grid_defect_scaled_tendsto a b).congr'
  filter_upwards [defect_physical_grid a b eta h0 h1] with k hk
  rw [hk]

/-- Compatibility with canonical moments is applied ONLY AFTER complete synthesis. -/
theorem principal_physical_tendsto (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)) atTop
      (nhds ((h 3-(a+b)*h 2+a*b*h 1:ℝ):ℂ)) := by
  have he := (critical_green_tendsto a b eta h0 h1).sub (defect_physical_tendsto_zero a b eta h0 h1)
  simp only [sub_zero] at he
  apply he.congr'
  filter_upwards [critical_physical_split a b eta h0 h1] with k hk
  rw [hk]
  ring

/-- The actual odd Schur specialization needs h1 NONZERO, never its sign here. -/
theorem principal_physical_schur_tendsto (hh : h 1≠0) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (principalInput (h 2/h 1) k) (principalInput (h 2/h 1) k)) atTop
      (nhds ((h 3-h 2^2/h 1:ℝ):ℂ)) := by
  have he := principal_physical_tendsto (h 2/h 1) (h 2/h 1) eta h0 h1
  convert he using 1
  congr 2
  field_simp
  ring

end
end CarryAddressSplit
