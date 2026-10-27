import RemainderValue
import WeightEleven
import QuarticFlux

namespace CarryQuarticCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open CarryCriticalTfvd CarryCurvatureGreen CarryCubicTfvd CarryStencilBoundary CarryQuarticTaylor
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def quarticCorrection (a b : ℝ) : ℝ :=
  -55*h 5+150*a*h 4-14*a^2*h 3+252*b*h 3-40*a*b*h 2-b^2*h 1

/-- The remainder is fixed at the response stage, before either field or pairing. -/
theorem native_response_field_kernel_prefix (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
      (c d : ℕ →₀ ℂ), d.support ⊆ Finset.range N →
    sectorField mixed eta h0 h1 (responseWeight k) d=
      Complex.I • (sectorField mixed eta h0 h1 (taylorWeight9 (radialStep k)) d+
        (radialStep k : ℂ)^11 • sectorField mixed eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k)) d) ∧
    sectorKernel mixed eta h0 h1 (responseWeight k) c d=
      Complex.I*(sectorKernel mixed eta h0 h1 (taylorWeight9 (radialStep k)) c d+
        (radialStep k : ℂ)^11*sectorKernel mixed eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k)) c d) := by
  filter_upwards [native_response_weight_prefix (N+1)] with k hk
  intro mixed eta h0 h1 c d hd
  have hf : sectorField mixed eta h0 h1 (responseWeight k) d=
      Complex.I • (sectorField mixed eta h0 h1 (taylorWeight9 (radialStep k)) d+
        (radialStep k : ℂ)^11 • sectorField mixed eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k)) d) := by
    rw [field_congr_prefix mixed eta h0 h1 (responseWeight k)
      (fun j => Complex.I*(taylorWeight9 (radialStep k) j+
        (radialStep k : ℂ)^11*remainderWeight11 nativeRemainder11 (radialStep k) j)) d hd hk]
    rw [field_scale_weight,field_add_weight,field_scale_weight]
  refine ⟨hf,?_⟩
  simp only [sectorKernel,hf,inner_smul_right,inner_add_right]

/-- Both original sectors carry precisely the same remainder and its known value. -/
theorem native_sector_expansion (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      sectorFlux mixed eta h0 h1 k (criticalFamily k a b)=
        quarticLeadingFlux mixed eta h0 h1 k a b+
        2*radialStep k^2*(sectorKernel mixed eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k))
          (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re := by
  filter_upwards [native_response_field_kernel_prefix 5] with k hk
  have hw := (hk mixed eta h0 h1 (quarticProfile a b (radialStep k))
    (quarticProfile a b (radialStep k)) (profile_support a b (radialStep k))).2
  unfold sectorFlux quarticLeadingFlux
  simp only [critical_family_profile,kernel_scale_both]
  rw [hw]
  generalize sectorKernel mixed eta h0 h1 (taylorWeight9 (radialStep k))
    (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))=U
  generalize sectorKernel mixed eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k))
    (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))=V
  simp only [Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add,Complex.ofReal_re,Complex.ofReal_im,← Complex.ofReal_pow,add_zero,sub_zero]
  unfold radialStep
  generalize hk : (k : ℝ)+1=K
  have hK : K≠0 := by rw [← hk]; positivity
  field_simp [hK]

/-- All mixed and bulk/boundary terms stay explicit through the complete synthesis. -/
theorem native_complete_expansion (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    ∀ᶠ k : ℕ in atTop,
    mixedEnergy eta h0 h1 k (criticalFamily k a b)=quarticLeadingFlux true eta h0 h1 k a b+
      2*radialStep k^2*(sectorKernel true eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k))
        (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re ∧
    bulkBoundaryEnergy eta h0 h1 k (criticalFamily k a b)=
      canonicalQuarticQuadratic a b-quarticLeadingFlux true eta h0 h1 k a b+
      radialStep k^2*(quarticFullError eta h0 h1 nativeRemainder11 a b (radialStep k)-
        2*(sectorKernel true eta h0 h1 (remainderWeight11 nativeRemainder11 (radialStep k))
          (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re) ∧
    fullEnergy k (criticalFamily k a b)=canonicalQuarticQuadratic a b+
      radialStep k^2*quarticFullError eta h0 h1 nativeRemainder11 a b (radialStep k) := by
  filter_upwards [native_sector_expansion false eta h0 h1 a b,
    native_sector_expansion true eta h0 h1 a b,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hf hm hr
  have hc := critical_family_support k a b
  have hF (j : Fin 6) := (hr j).2.1
  have hd (j : ℕ) (hj : j<6) := radial_weight_difference k j (hr ⟨j,hj⟩).2.1 (hr ⟨j,hj⟩).2.2
  have hfull : fullEnergy k (criticalFamily k a b)=sectorFlux false eta h0 h1 k (criticalFamily k a b) :=
    full_response_flux k _ hc (fun j => hF ⟨j,by omega⟩) (fun j hj => hd j (by omega))
  have hmixed : mixedEnergy eta h0 h1 k (criticalFamily k a b)=sectorFlux true eta h0 h1 k (criticalFamily k a b) :=
    mixed_response_flux eta h0 h1 k _ hc hF hd
  have hfe := quartic_full_flux_exact eta h0 h1 nativeRemainder11 k a b hf
  rw [← hfull] at hfe
  rw [← hmixed] at hm
  refine ⟨hm,?_,hfe⟩
  have hs := full_split eta h0 h1 k _ hc hd
  rw [hfe,hm] at hs
  linear_combination -hs

theorem native_full_error_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    quarticFullError eta h0 h1 nativeRemainder11 a b 0=quarticCorrection a b := by
  unfold quarticFullError
  rw [zero_remainder_kernel,native_remainder_value]
  unfold quarticPolynomialError quarticCorrection
  norm_num [Complex.mul_re]
  ring

/-- The first complete correction, with unrestricted real a,b and no pivot sign. -/
theorem native_scaled_error_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    Tendsto (fun k : ℕ => ((k : ℝ)+1)^2*
      (fullEnergy k (criticalFamily k a b)-canonicalQuarticQuadratic a b))
      atTop (nhds (quarticCorrection a b)) := by
  have ht := (quartic_full_error_continuous eta h0 h1 nativeRemainder11
    native_remainder_analytic a b).tendsto.comp radial_step_tendsto
  rw [native_full_error_zero] at ht
  apply ht.congr'
  filter_upwards [native_complete_expansion eta h0 h1 a b] with k hk
  rw [hk.2.2,add_sub_cancel_left]
  have hd : ((k : ℝ)+1)^2*radialStep k^2=1 := by
    unfold radialStep
    have hK : (k : ℝ)+1≠0 := by positivity
    field_simp [hK]
  rw [← mul_assoc,hd,one_mul]
  rfl

theorem native_scaled_norm_difference_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    Tendsto (fun k : ℕ => ((k : ℝ)+1)^2*
      (‖(physicalCompletedFiniteSource k (criticalFamily k a b)).1‖^2-
        ‖(physicalCompletedFiniteSource k (criticalFamily k a b)).2‖^2-
        2*canonicalQuarticQuadratic a b)) atTop (nhds (2*quarticCorrection a b)) := by
  have ht := (tendsto_const_nhds (x := (2 : ℝ))).mul (native_scaled_error_limit eta h0 h1 a b)
  apply ht.congr'
  filter_upwards [] with k
  rw [← full_energy_norm_difference]
  ring

/-- The direction of approach follows IF this explicit correction is negative.
Its sign is not assumed by the unconditional expansion or limit. -/
theorem native_eventually_below (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ)
    (hc : quarticCorrection a b < 0) :
    ∀ᶠ k : ℕ in atTop, fullEnergy k (criticalFamily k a b)<canonicalQuarticQuadratic a b := by
  have ht := (native_scaled_error_limit eta h0 h1 a b).eventually (gt_mem_nhds hc)
  filter_upwards [ht] with k hk
  by_contra hn
  have hnon : 0 ≤ fullEnergy k (criticalFamily k a b)-canonicalQuarticQuadratic a b := by linarith
  have hh := mul_nonneg (sq_nonneg ((k : ℝ)+1)) hnon
  linarith

theorem native_eventually_above (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ)
    (hc : 0 < quarticCorrection a b) :
    ∀ᶠ k : ℕ in atTop, canonicalQuarticQuadratic a b<fullEnergy k (criticalFamily k a b) := by
  have ht := (native_scaled_error_limit eta h0 h1 a b).eventually (lt_mem_nhds hc)
  filter_upwards [ht] with k hk
  by_contra hn
  have hnon : fullEnergy k (criticalFamily k a b)-canonicalQuarticQuadratic a b ≤ 0 := by linarith
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((k : ℝ)+1)) hnon
  linarith

end
end CarryQuarticCorrection
