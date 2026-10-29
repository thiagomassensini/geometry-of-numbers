import QuarticRemainder
import SectorExpansion

namespace CarryQuarticTaylor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open CarryCriticalTfvd CarryCurvatureGreen CarryCubicTfvd CarryStencilBoundary
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def canonicalQuarticQuadratic (a b : ℝ) : ℝ :=
  quarticQuadratic (h 0) (h 1) (h 2) (h 3) (h 4) a b

def quarticFullError (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (a b t : ℝ) : ℝ :=
  quarticPolynomialError (h 1) (h 2) (h 3) (h 4) a b t+
    2*(sectorKernel false eta h0 h1 (remainderWeight11 R t) (quarticProfile a b t) (quarticProfile a b t)).re

def quarticLeadingFlux (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (a b : ℝ) : ℝ :=
  2*((k : ℝ)+1)^9*(sectorKernel mixed eta h0 h1 (taylorWeight9 (radialStep k))
    (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re

theorem kernel_taylor9_real (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (t : ℝ) (c d : ℕ →₀ ℂ) :
    (sectorKernel mixed eta h0 h1 (taylorWeight9 t) c d).re=
      h 0*t*(sectorKernel mixed eta h0 h1 (monomialWeight 1) c d).re-
      h 1*t^3*(sectorKernel mixed eta h0 h1 (monomialWeight 3) c d).re+
      h 2*t^5*(sectorKernel mixed eta h0 h1 (monomialWeight 5) c d).re-
      h 3*t^7*(sectorKernel mixed eta h0 h1 (monomialWeight 7) c d).re+
      h 4*t^9*(sectorKernel mixed eta h0 h1 (monomialWeight 9) c d).re := by
  have hw : taylorWeight9 t=(fun j =>
      ((h 0 : ℂ)*(t : ℂ))*monomialWeight 1 j+
      (-(h 1 : ℂ)*(t : ℂ)^3)*monomialWeight 3 j+
      ((h 2 : ℂ)*(t : ℂ)^5)*monomialWeight 5 j+
      (-(h 3 : ℂ)*(t : ℂ)^7)*monomialWeight 7 j+
      ((h 4 : ℂ)*(t : ℂ)^9)*monomialWeight 9 j) := by
    funext j
    unfold taylorWeight9
    ring
  rw [hw]
  simp only [kernel_add_weight,kernel_scale_weight]
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
  ring

theorem full_profile_taylor_cancellation (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b t : ℝ) :
    2*(sectorKernel false eta h0 h1 (taylorWeight9 t) (quarticProfile a b t) (quarticProfile a b t)).re=
      t^9*(canonicalQuarticQuadratic a b+t^2*quarticPolynomialError (h 1) (h 2) (h 3) (h 4) a b t) := by
  have hh := congrArg (fun z : ℝ => t*z)
    (full_weight_cancellation eta h0 h1 (h 0) (h 1) (h 2) (h 3) (h 4) a b t)
  rw [kernel_taylor9_real]
  unfold canonicalQuarticQuadratic
  linear_combination hh

/-- One remainder, the same radial family and BOTH unaltered sectors. -/
theorem quartic_sector_taylor_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (mixed : Bool) (eta : ℝ)
      (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ), ∀ᶠ k : ℕ in atTop,
      sectorFlux mixed eta h0 h1 k (criticalFamily k a b)=
        quarticLeadingFlux mixed eta h0 h1 k a b+
        2*radialStep k^2*(sectorKernel mixed eta h0 h1 (remainderWeight11 R (radialStep k))
          (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re := by
  obtain ⟨R,hR,he⟩ := response_field_kernel_taylor11
  refine ⟨R,hR,?_⟩
  intro mixed eta h0 h1 a b
  filter_upwards [he 5] with k hk
  have hw := (hk mixed eta h0 h1 (quarticProfile a b (radialStep k))
    (quarticProfile a b (radialStep k)) (profile_support a b (radialStep k))).2
  unfold sectorFlux quarticLeadingFlux
  simp only [critical_family_profile,kernel_scale_both]
  rw [hw]
  generalize sectorKernel mixed eta h0 h1 (taylorWeight9 (radialStep k))
    (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))=U
  generalize sectorKernel mixed eta h0 h1 (remainderWeight11 R (radialStep k))
    (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))=V
  simp only [Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add,Complex.ofReal_re,Complex.ofReal_im,
    ← Complex.ofReal_pow,add_zero,sub_zero]
  unfold radialStep
  generalize hk : (k : ℝ)+1=K
  have hK : K≠0 := by rw [← hk]; positivity
  field_simp [hK]

theorem quartic_full_flux_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (k : ℕ) (a b : ℝ)
    (he : sectorFlux false eta h0 h1 k (criticalFamily k a b)=
      quarticLeadingFlux false eta h0 h1 k a b+
      2*radialStep k^2*(sectorKernel false eta h0 h1 (remainderWeight11 R (radialStep k))
        (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re) :
    sectorFlux false eta h0 h1 k (criticalFamily k a b)=
      canonicalQuarticQuadratic a b+radialStep k^2*quarticFullError eta h0 h1 R a b (radialStep k) := by
  rw [he]
  have hc := full_profile_taylor_cancellation eta h0 h1 a b (radialStep k)
  have hd : ((k : ℝ)+1)^9*radialStep k^9=1 := by
    unfold radialStep
    have hk : (k : ℝ)+1≠0 := by positivity
    field_simp [hk]
  have hh := congrArg (fun z : ℝ => ((k : ℝ)+1)^9*z) hc
  rw [← mul_assoc (((k : ℝ)+1)^9) (radialStep k^9),hd,one_mul] at hh
  unfold quarticLeadingFlux quarticFullError
  linear_combination hh

theorem quartic_full_error_continuous (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b : ℝ) :
    ContinuousAt (quarticFullError eta h0 h1 R a b) 0 := by
  have hr := remainder_profile_kernel_continuous false eta h0 h1 R hR a b
  unfold quarticFullError quarticPolynomialError
  fun_prop

/-- No leading Green term is erased: the bulk/boundary sector contains
its exact opposite, and both analytic remainders remain in the identity. -/
theorem quartic_complete_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
      (a b : ℝ), ∀ᶠ k : ℕ in atTop,
      mixedEnergy eta h0 h1 k (criticalFamily k a b)=quarticLeadingFlux true eta h0 h1 k a b+
        2*radialStep k^2*(sectorKernel true eta h0 h1 (remainderWeight11 R (radialStep k))
          (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re ∧
      bulkBoundaryEnergy eta h0 h1 k (criticalFamily k a b)=
        canonicalQuarticQuadratic a b-quarticLeadingFlux true eta h0 h1 k a b+
        radialStep k^2*(quarticFullError eta h0 h1 R a b (radialStep k)-
          2*(sectorKernel true eta h0 h1 (remainderWeight11 R (radialStep k))
            (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re) ∧
      fullEnergy k (criticalFamily k a b)=canonicalQuarticQuadratic a b+
        radialStep k^2*quarticFullError eta h0 h1 R a b (radialStep k) := by
  obtain ⟨R,hR,he⟩ := quartic_sector_taylor_expansion
  refine ⟨R,hR,?_⟩
  intro eta h0 h1 a b
  filter_upwards [he false eta h0 h1 a b,he true eta h0 h1 a b,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hf hm hr
  have hc := critical_family_support k a b
  have hF (j : Fin 6) := (hr j).2.1
  have hd (j : ℕ) (hj : j<6) := radial_weight_difference k j (hr ⟨j,hj⟩).2.1 (hr ⟨j,hj⟩).2.2
  have hfull : fullEnergy k (criticalFamily k a b)=sectorFlux false eta h0 h1 k (criticalFamily k a b) :=
    full_response_flux k _ hc (fun j => hF ⟨j,by omega⟩) (fun j hj => hd j (by omega))
  have hmixed : mixedEnergy eta h0 h1 k (criticalFamily k a b)=sectorFlux true eta h0 h1 k (criticalFamily k a b) :=
    mixed_response_flux eta h0 h1 k _ hc hF hd
  have hfe := quartic_full_flux_exact eta h0 h1 R k a b hf
  rw [← hfull] at hfe
  rw [← hmixed] at hm
  refine ⟨hm,?_,hfe⟩
  have hs := full_split eta h0 h1 k _ hc hd
  rw [hfe,hm] at hs
  linear_combination -hs

theorem quartic_full_energy_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    Tendsto (fun k : ℕ => fullEnergy k (criticalFamily k a b))
      atTop (nhds (canonicalQuarticQuadratic a b)) := by
  obtain ⟨R,hR,he⟩ := quartic_complete_expansion
  have hr := (quartic_full_error_continuous eta h0 h1 R hR a b).tendsto.comp radial_step_tendsto
  have ht := (tendsto_const_nhds (x := canonicalQuarticQuadratic a b)).add
    ((radial_step_tendsto.pow 2).mul hr)
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at ht
  apply ht.congr'
  filter_upwards [he eta h0 h1 a b] with k hk
  exact hk.2.2.symm

theorem quartic_full_second_order_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k : ℕ in atTop,
      |fullEnergy k (criticalFamily k a b)-canonicalQuarticQuadratic a b| ≤ M*radialStep k^2 := by
  obtain ⟨R,hR,he⟩ := quartic_complete_expansion
  let M := |quarticFullError eta h0 h1 R a b 0|+1
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  have ht := (quartic_full_error_continuous eta h0 h1 R hR a b).tendsto.comp radial_step_tendsto
  have hb := ht.abs.eventually (gt_mem_nhds (show |quarticFullError eta h0 h1 R a b 0|<M by dsimp [M]; linarith))
  filter_upwards [he eta h0 h1 a b,hb] with k hk hbound
  rw [hk.2.2,add_sub_cancel_left,abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ radialStep k^2*M := mul_le_mul_of_nonneg_left hbound.le (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- The native form has its original factor 1/2; no metric is rescaled. -/
theorem full_energy_norm_difference (k : ℕ) (c : ℕ →₀ ℂ) :
    2*fullEnergy k c=‖(physicalCompletedFiniteSource k c).1‖^2-
      ‖(physicalCompletedFiniteSource k c).2‖^2 := by
  unfold fullEnergy canonicalCompletedNativeProjectiveChiralForm
  simp only [inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re,Complex.sub_re,← Complex.ofReal_pow]
  ring

theorem quartic_norm_difference_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    Tendsto (fun k : ℕ => ‖(physicalCompletedFiniteSource k (criticalFamily k a b)).1‖^2-
      ‖(physicalCompletedFiniteSource k (criticalFamily k a b)).2‖^2)
      atTop (nhds (2*canonicalQuarticQuadratic a b)) := by
  simpa only [full_energy_norm_difference] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul (quartic_full_energy_limit eta h0 h1 a b)

end
end CarryQuarticTaylor
