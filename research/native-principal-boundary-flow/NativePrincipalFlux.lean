import PrincipalFlux
namespace CarryPrincipalFlow
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- Three response layers, used ONLY to split the original completed response. -/
def responseHead (e v q : ℝ) (k : ℕ) (j : ℕ) : ℂ :=
  (e:ℂ)/((k:ℂ)+1)*monomialWeight 1 j+
    (v:ℂ)/((k:ℂ)+1)^3*monomialWeight 3 j+
    (q:ℂ)/((k:ℂ)+1)^5*monomialWeight 5 j

/-- Exact remaining response. The original input, metric and full response are unchanged. -/
def responseTail (e v q : ℝ) (k : ℕ) (j : ℕ) : ℂ :=
  responseSamples (radialStep k) j-responseHead e v q k j

theorem full_response_head_tail (e v q : ℝ) (k : ℕ) :
    responseSamples (radialStep k)=(fun j => responseHead e v q k j+responseTail e v q k j) := by
  funext j
  unfold responseTail
  ring

/-- Each original Green/boundary/commutator VECTOR keeps its whole tail. -/
theorem original_field_head_tail (e v q : ℝ) (k : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) (i : Fin 3) :
    partField eta h0 h1 (responseSamples (radialStep k)) c i=
      partField eta h0 h1 (responseHead e v q k) c i+
      partField eta h0 h1 (responseTail e v q k) c i := by
  rw [full_response_head_tail e v q k,part_field_add_weight]

/-- Complete response synthesis BEFORE any scalar pairing. -/
theorem original_vector_head_tail (e v q : ℝ) (k : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (c : ℕ →₀ ℂ) :
    physicalCauchySynthesis (coefficientWeight (responseSamples (radialStep k)) c)=
      (∑ i : Fin 3, partField eta h0 h1 (responseHead e v q k) c i)+
      (∑ i : Fin 3, partField eta h0 h1 (responseTail e v q k) c i) := by
  rw [← part_field_reconstruction eta h0 h1,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact original_field_head_tail e v q k eta h0 h1 c i

theorem sym_add_weight (w z : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    symKernel (fun j => w j+z j) c d=symKernel w c d+symKernel z c d := by
  simp only [symKernel,kernel_add]
  ring

theorem sym_scale_weight (A : ℂ) (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    symKernel (fun j => A*w j) c d=A*symKernel w c d := by
  simp only [symKernel,kernel_scale]
  ring

/-- The first three layers, with BOTH independent arguments. Euler vanishes;
cubic and quintic endpoint terms keep their distinct signs. -/
theorem principal_head_flux (e v q a b : ℝ) (k : ℕ) :
    ((k:ℂ)+1)*symKernel (responseHead e v q k) (principalInput a k) (principalInput b k)=
      -(v:ℂ)*(a:ℂ)*(b:ℂ)-(q:ℂ)*((a:ℂ)+(b:ℂ))-
        54*(q:ℂ)*(a:ℂ)*(b:ℂ)/((k:ℂ)+1)^2 := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  unfold responseHead
  rw [sym_add_weight,sym_add_weight,sym_scale_weight,sym_scale_weight,sym_scale_weight,
    principal_monomial_one,principal_monomial_three,principal_monomial_five]
  field_simp
  ring

/-- This remains a signed polarized pairing of the SAME synthesized source response. -/
def principalTailFlux (e v q a b : ℝ) (k : ℕ) : ℂ :=
  ((k:ℂ)+1)*symKernel (responseTail e v q k) (principalInput a k) (principalInput b k)

/-- Reality of each response layer is proved without deleting either quadrature. -/
theorem response_head_real (e v q : ℝ) (k j : ℕ) :
    conj (responseHead e v q k j)=responseHead e v q k j := by
  simp [responseHead,monomialWeight]

theorem response_tail_real (e v q : ℝ) (k j : ℕ) :
    conj (responseTail e v q k j)=responseTail e v q k j := by
  simp only [responseTail,map_sub,response_samples_real (radialStep k),response_head_real]

theorem principal_tail_flux_real (e v q a b : ℝ) (k : ℕ) :
    conj (principalTailFlux e v q a b k)=principalTailFlux e v q a b k := by
  have hc := kernel_imaginary_imaginary (responseTail e v q k) _ _
    (response_tail_real e v q k) (principal_imaginary a k) (principal_imaginary b k)
  have hd := kernel_imaginary_imaginary (responseTail e v q k) _ _
    (response_tail_real e v q k) (principal_imaginary b k) (principal_imaginary a k)
  simp only [principalTailFlux,symKernel,map_mul,map_add,map_natCast,map_one,hc,hd]

theorem principal_native_response (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)=
      ((k:ℂ)+1)*symKernel (responseSamples (radialStep k)) (principalInput a k) (principalInput b k) := by
  have hp a k := (principal_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  filter_upwards [imaginary_families_exact 5 (principalInput a) (principalInput b)
    (hp a) (hp b) (principal_imaginary a) (principal_imaginary b)] with k hk
  rw [cross_green_eq_original]
  exact hk

/-- Exact NINE-cross physical Green flow with its full remainder; no moment is used. -/
theorem principal_physical_flow (e v q a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)=
      -(v:ℂ)*(a:ℂ)*(b:ℂ)-(q:ℂ)*((a:ℂ)+(b:ℂ))-
        54*(q:ℂ)*(a:ℂ)*(b:ℂ)/((k:ℂ)+1)^2+principalTailFlux e v q a b k := by
  filter_upwards [principal_native_response a b eta h0 h1] with k hk
  rw [hk,full_response_head_tail e v q k,sym_add_weight,mul_add,principal_head_flux]
  rfl

/-- Literal common-mean tail of the existing two-leg state. It is a COMPONENT,
not a replacement source or a separate return operator. -/
def tailComponent (e v q a : ℝ) (k : ℕ) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  let z := ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) •
    physicalCauchySynthesis (coefficientWeight (responseTail e v q k) (principalInput a k))
  (z,z)

def headComponent (e v q a : ℝ) (k : ℕ) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  physicalCompletedFiniteSource k (principalInput a k)-tailComponent e v q a k

/-- ALL three original Green fields of the same two-leg remainder. -/
def tailPartComponent (e v q a : ℝ) (k : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (i : Fin 3) : CanonicalCompletedNativeProjectiveChiralCarrier :=
  let z := ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) •
    partField eta h0 h1 (responseTail e v q k) (principalInput a k) i
  (z,z)

theorem tail_parts_reconstruct (e v q a : ℝ) (k : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ i : Fin 3, tailPartComponent e v q a k eta h0 h1 i)=tailComponent e v q a k := by
  unfold tailPartComponent tailComponent
  rw [← part_field_reconstruction eta h0 h1 (responseTail e v q k) (principalInput a k)]
  simp only [Fin.sum_univ_three,smul_add,Prod.mk_add_mk]

theorem complete_state_head_tail (e v q a : ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (principalInput a k)=headComponent e v q a k+tailComponent e v q a k := by
  unfold headComponent
  abel

/-- Isotropic does NOT mean zero state or absent information. -/
theorem tail_pairing_zero (e v q a b : ℝ) (k : ℕ) :
    canonicalCompletedNativeProjectiveChiralForm (tailComponent e v q a k) (tailComponent e v q b k)=0 := by
  simp [canonicalCompletedNativeProjectiveChiralForm,tailComponent]

theorem head_preserves_contrast (e v q a : ℝ) (k : ℕ) :
    (headComponent e v q a k).1-(headComponent e v q a k).2=
      (physicalCompletedFiniteSource k (principalInput a k)).1-
        (physicalCompletedFiniteSource k (principalInput a k)).2 := by
  let u := physicalCompletedFiniteSource k (principalInput a k)
  let z := ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) •
    physicalCauchySynthesis (coefficientWeight (responseTail e v q k) (principalInput a k))
  change (u.1-z)-(u.2-z)=u.1-u.2
  abel

/-- The factor is forced by the original amplitude; no rescaling of B. -/
theorem tail_scale_calibration (k : ℕ) :
    conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*
      (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))=2*((k:ℂ)+1) := by
  have hc : ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)=
      Complex.I*((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ))) := by
    unfold chiralDifference
    ring
  calc
    _ = conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*
        (Complex.I*((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))) :=
      congrArg (fun z => conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*z) hc
    _ = Complex.I*(conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*
        ((Real.sqrt ((k:ℝ)+1):ℂ)*(2/(Real.sqrt 2:ℂ)))) := by ring
    _ = _ := by
      rw [contrast_mean_scale]
      push_cast
      ring_nf
      norm_num [Complex.I_sq]

/-- The retained tail is a MIXED physical flux. Its self-energy is zero,
so a norm square of the tail cannot replace these two ordered crossings. -/
theorem tail_mixed_physical_flux (e v q a b : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedNativeProjectiveChiralForm
        (physicalCompletedFiniteSource k (principalInput a k)) (tailComponent e v q b k)+
      canonicalCompletedNativeProjectiveChiralForm
        (tailComponent e v q a k) (physicalCompletedFiniteSource k (principalInput b k))=
        principalTailFlux e v q a b k := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 5] with k hk
  have hp a := (principal_support a k).trans (Finset.range_mono (by omega : 4 ≤ 5))
  have hd (j : ℕ) (hj : j<5) := radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2
  have hc := completed_source_contrast k (principalInput a k) (hp a) hd
  have he := completed_source_contrast k (principalInput b k) (hp b) hd
  have hl : canonicalCompletedNativeProjectiveChiralForm
      (physicalCompletedFiniteSource k (principalInput a k)) (tailComponent e v q b k)=
        (2:ℂ)⁻¹*inner ℂ
          ((physicalCompletedFiniteSource k (principalInput a k)).1-
            (physicalCompletedFiniteSource k (principalInput a k)).2) (tailComponent e v q b k).1 := by
    unfold canonicalCompletedNativeProjectiveChiralForm tailComponent
    rw [inner_sub_left]
  have hr : canonicalCompletedNativeProjectiveChiralForm
      (tailComponent e v q a k) (physicalCompletedFiniteSource k (principalInput b k))=
        (2:ℂ)⁻¹*inner ℂ (tailComponent e v q a k).1
          ((physicalCompletedFiniteSource k (principalInput b k)).1-
            (physicalCompletedFiniteSource k (principalInput b k)).2) := by
    unfold canonicalCompletedNativeProjectiveChiralForm tailComponent
    rw [inner_sub_right]
  rw [hl,hr,hc,he]
  dsimp only [tailComponent]
  simp only [inner_smul_left,inner_smul_right]
  have hs := tail_scale_calibration k
  have hrev : inner ℂ (physicalCauchySynthesis
      (coefficientWeight (responseTail e v q k) (principalInput a k)))
      (physicalCauchySynthesis (principalInput b k))=
        kernel (responseTail e v q k) (principalInput b k) (principalInput a k) := by
    rw [← inner_conj_symm]
    exact kernel_imaginary_imaginary _ _ _ (response_tail_real e v q k)
      (principal_imaginary b k) (principal_imaginary a k)
  rw [hrev]
  change (2:ℂ)⁻¹*(((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)*
    (conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*
      kernel (responseTail e v q k) (principalInput a k) (principalInput b k)))+
    (2:ℂ)⁻¹*(((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference)*
    (conj (((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference))*
      kernel (responseTail e v q k) (principalInput b k) (principalInput a k)))=_
  unfold principalTailFlux symKernel
  linear_combination (1/2:ℂ)*
    (kernel (responseTail e v q k) (principalInput a k) (principalInput b k)+
      kernel (responseTail e v q k) (principalInput b k) (principalInput a k))*hs

/-- Pure two-leg algebra, retaining both off-diagonal mixed terms. -/
theorem signed_sub_isotropic (u v e f : CanonicalCompletedNativeProjectiveChiralCarrier)
    (he : e.1=e.2) (hf : f.1=f.2) :
    canonicalCompletedNativeProjectiveChiralForm (u-e) (v-f)=
      canonicalCompletedNativeProjectiveChiralForm u v-
        canonicalCompletedNativeProjectiveChiralForm u f-
        canonicalCompletedNativeProjectiveChiralForm e v := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  simp only [Prod.fst_sub,Prod.snd_sub,inner_sub_left,inner_sub_right,he,hf]
  ring

/-- The finite three-layer flux is the signed form of the literal head component.
The original state is still head+tail, and the tail contributes through mixing. -/
theorem head_physical_flow (e v q a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedNativeProjectiveChiralForm (headComponent e v q a k) (headComponent e v q b k)=
        -(v:ℂ)*(a:ℂ)*(b:ℂ)-(q:ℂ)*((a:ℂ)+(b:ℂ))-
          54*(q:ℂ)*(a:ℂ)*(b:ℂ)/((k:ℂ)+1)^2 := by
  filter_upwards [principal_physical_flow e v q a b eta h0 h1,
    tail_mixed_physical_flux e v q a b] with k hb ht
  rw [cross_green_eq_original] at hb
  change canonicalCompletedNativeProjectiveChiralForm
    (physicalCompletedFiniteSource k (principalInput a k))
    (physicalCompletedFiniteSource k (principalInput b k))=_ at hb
  unfold headComponent
  rw [signed_sub_isotropic _ _ _ _ rfl rfl]
  linear_combination hb-ht

/-- Only now specialize the response coefficients to their original canonical values. -/
abbrev nativePrincipalTail (a b : ℝ) (k : ℕ) : ℂ :=
  principalTailFlux (h 0) (-(h 1)) (h 2) a b k

/-- The scalar canonical reading is AFTER all original fields and both arguments. -/
theorem native_principal_flow (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput b k)=
      (a:ℂ)*(b:ℂ)*(h 1:ℂ)-((a:ℂ)+(b:ℂ))*(h 2:ℂ)-
        54*(a:ℂ)*(b:ℂ)*(h 2:ℂ)/((k:ℂ)+1)^2+nativePrincipalTail a b k := by
  filter_upwards [principal_physical_flow (h 0) (-(h 1)) (h 2) a b eta h0 h1] with k hk
  rw [hk]
  unfold nativePrincipalTail
  simp only [Complex.ofReal_neg]
  ring

/-- Exact old/new budget in the actual critical direction. Invertibility only;
this is NOT an independent proof that the retained tail dominates this budget. -/
theorem critical_tail_budget_exact (hh : h 1≠0) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, crossGreenPair eta h0 h1 k k
      (principalInput (h 2/h 1) k) (principalInput (h 2/h 1) k)=
        nativePrincipalTail (h 2/h 1) (h 2/h 1) k-
          ((h 2:ℂ)^2/(h 1:ℂ))-54*squaredScale k*(h 2:ℂ)^3/(h 1:ℂ)^2 := by
  filter_upwards [native_principal_flow (h 2/h 1) (h 2/h 1) eta h0 h1] with k hk
  have hhC : (h 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh
  have hn : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  rw [hk]
  unfold squaredScale
  push_cast
  field_simp
  ring

/-- The tail is exactly the NATIVE analytic remainder at each actual address,
including the outgoing halo. It is not a different response or a fitted source. -/
theorem native_tail_samples (M : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : Fin M,
      responseTail (h 0) (-(h 1)) (h 2) k j=
        (radialStep k:ℂ)^7*remainderSamples 3 (radialStep k) j := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  filter_upwards [ht.eventually (response_samples_prefix 3 M)] with k hk
  intro j
  have hn : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  unfold responseTail
  rw [hk j]
  norm_num [taylorSamples,Finset.sum_range_succ,responseHead,radialStep]
  field_simp
  ring

/-- The analytic tail remains a WHOLE original field, for every fixed finite input. -/
theorem native_tail_field_fixed (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin 3,
      partField eta h0 h1 (responseTail (h 0) (-(h 1)) (h 2) k) c i=
        (radialStep k:ℂ)^7 • partField eta h0 h1 (remainderSamples 3 (radialStep k)) c i := by
  obtain ⟨M,hM⟩ := part_field_finite_locality eta h0 h1 c
  filter_upwards [native_tail_samples M] with k hk
  intro i
  rw [hM _ (fun j => (radialStep k:ℂ)^7*remainderSamples 3 (radialStep k) j) hk i,
    part_field_scale_weight]

/-- The actual k-dependent X also retains ALL three analytic remainder fields.
Its finite support and its outgoing halo are inherited from its literal basis. -/
theorem native_principal_tail_fields (a : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin 3,
      partField eta h0 h1 (responseTail (h 0) (-(h 1)) (h 2) k) (principalInput a k) i=
        (radialStep k:ℂ)^7 • partField eta h0 h1 (remainderSamples 3 (radialStep k)) (principalInput a k) i := by
  filter_upwards [native_tail_field_fixed eta h0 h1 (nativeOddProfile 1),
    native_tail_field_fixed eta h0 h1 (addressPower 2 (nativeOddProfile 1))] with k hO hD
  intro i
  simp only [principalInput,part_field_add_input,part_field_scale_input,hO i,hD i]
  module

/-- The retained tail has its canonical leading term; it is not assumed zero.
No sign of h3 or of the Schur pivot is used. -/
theorem native_principal_tail_tendsto (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (nativePrincipalTail a b) atTop (nhds (h 3:ℂ)) := by
  have hs := squared_scale_tendsto_zero
  have hz : Tendsto (fun k : ℕ => 54*(a:ℂ)*(b:ℂ)*(h 2:ℂ)/((k:ℂ)+1)^2) atTop (nhds 0) := by
    have he := (tendsto_const_nhds (x:=(54*(a:ℂ)*(b:ℂ)*(h 2:ℂ)))).mul hs
    simpa [squaredScale,div_eq_mul_inv,inv_pow] using he
  have he := (((principal_physical_tendsto a b eta h0 h1).sub
    (tendsto_const_nhds (x:=(a:ℂ)*(b:ℂ)*(h 1:ℂ)))).add
      (tendsto_const_nhds (x:=((a:ℂ)+(b:ℂ))*(h 2:ℂ)))).add hz
  convert he.congr' ?_ using 1
  · push_cast
    ring
  · filter_upwards [native_principal_flow a b eta h0 h1] with k hk
    rw [hk]
    ring

end
end CarryPrincipalFlow
