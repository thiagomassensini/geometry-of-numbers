import Taylor11
import QuarticKernel

namespace CarryQuarticTaylor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open CarryCriticalTfvd CarryCurvatureGreen CarryCubicTfvd CarryStencilBoundary
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem field_congr_prefix {N : ℕ} (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w z : ℕ → ℂ) (c : ℕ →₀ ℂ) (hc : c.support ⊆ Finset.range N)
    (he : ∀ j : Fin (N+1), w j=z j) :
    sectorField mixed eta h0 h1 w c=sectorField mixed eta h0 h1 z c := by
  unfold sectorField
  rw [stencil_congr mixed eta w z c hc he]

/-- Whole complex fields are transported first, for both original sectors.
Only then is the same equality paired with an independent left input. -/
theorem response_field_kernel_taylor11 :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
        (c d : ℕ →₀ ℂ), d.support ⊆ Finset.range N →
      sectorField mixed eta h0 h1 (responseWeight k) d=
        Complex.I • (sectorField mixed eta h0 h1 (taylorWeight9 (radialStep k)) d+
          (radialStep k : ℂ)^11 • sectorField mixed eta h0 h1 (remainderWeight11 R (radialStep k)) d) ∧
      sectorKernel mixed eta h0 h1 (responseWeight k) c d=
        Complex.I*(sectorKernel mixed eta h0 h1 (taylorWeight9 (radialStep k)) c d+
          (radialStep k : ℂ)^11*sectorKernel mixed eta h0 h1 (remainderWeight11 R (radialStep k)) c d) := by
  obtain ⟨R,hR,he⟩ := response_weight_taylor11_prefix
  refine ⟨R,hR,?_⟩
  intro N
  filter_upwards [he (N+1)] with k hk
  intro mixed eta h0 h1 c d hd
  have hf : sectorField mixed eta h0 h1 (responseWeight k) d=
      Complex.I • (sectorField mixed eta h0 h1 (taylorWeight9 (radialStep k)) d+
        (radialStep k : ℂ)^11 • sectorField mixed eta h0 h1 (remainderWeight11 R (radialStep k)) d) := by
    rw [field_congr_prefix mixed eta h0 h1 (responseWeight k)
      (fun j => Complex.I*(taylorWeight9 (radialStep k) j+
        (radialStep k : ℂ)^11*remainderWeight11 R (radialStep k) j)) d hd hk]
    rw [field_scale_weight,field_add_weight,field_scale_weight]
  refine ⟨hf,?_⟩
  simp only [sectorKernel,hf,inner_smul_right,inner_add_right]

/-- The outgoing address 5 is kept in the mixed field, including the remainder. -/
theorem remainder_five_field_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b c d e : ℂ) :
    ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight11 R t) (five a b c d e)) 0 := by
  have hr0 := remainder_weight11_continuous R hR 0
  have hr1 := remainder_weight11_continuous R hR 1
  have hr2 := remainder_weight11_continuous R hR 2
  have hr3 := remainder_weight11_continuous R hR 3
  have hr4 := remainder_weight11_continuous R hR 4
  have hr5 := remainder_weight11_continuous R hR 5
  cases mixed
  · simp only [sectorField,coefficientStencil,Bool.false_eq_true,ite_false]
    simp only [weight_five]
    simp only [five,physicalCauchySynthesis,map_add,Finsupp.linearCombination_single]
    exact (((((hr0.mul continuousAt_const).smul continuousAt_const).add
      ((hr1.mul continuousAt_const).smul continuousAt_const)).add
      ((hr2.mul continuousAt_const).smul continuousAt_const)).add
      ((hr3.mul continuousAt_const).smul continuousAt_const)).add
      ((hr4.mul continuousAt_const).smul continuousAt_const)
  · simp only [sectorField,coefficientStencil,ite_true,commutator_five,
      physicalCauchySynthesis,map_add,Finsupp.linearCombination_single]
    have hc1 := (((continuousAt_const (y := (eta : ℂ)⁻¹)).mul (hr2.sub hr1)).mul (continuousAt_const (y := c))).add
      (((continuousAt_const (y := (eta : ℂ))).mul (hr0.sub hr1)).mul (continuousAt_const (y := a)))
    have hc2 := (((continuousAt_const (y := (eta : ℂ)⁻¹)).mul (hr3.sub hr2)).mul (continuousAt_const (y := d))).add
      (((continuousAt_const (y := (eta : ℂ))).mul (hr1.sub hr2)).mul (continuousAt_const (y := b)))
    have hc3 := (((continuousAt_const (y := (eta : ℂ)⁻¹)).mul (hr4.sub hr3)).mul (continuousAt_const (y := e))).add
      (((continuousAt_const (y := (eta : ℂ))).mul (hr2.sub hr3)).mul (continuousAt_const (y := c)))
    have hc4 := ((continuousAt_const (y := (eta : ℂ))).mul (hr3.sub hr4)).mul (continuousAt_const (y := d))
    have hc5 := ((continuousAt_const (y := (eta : ℂ))).mul (hr4.sub hr5)).mul (continuousAt_const (y := e))
    have hG := (physicalGreenOperator eta h0.le h1).continuous
    exact ((((hG.continuousAt.comp (hc1.smul continuousAt_const)).add
      (hG.continuousAt.comp (hc2.smul continuousAt_const))).add
      (hG.continuousAt.comp (hc3.smul continuousAt_const))).add
      (hG.continuousAt.comp (hc4.smul continuousAt_const))).add
      (hG.continuousAt.comp (hc5.smul continuousAt_const))

theorem remainder_profile_field_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b : ℝ) :
    ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight11 R t) (quarticProfile a b t)) 0 := by
  have h4 : ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight11 R t) fourthShape) 0 := by
    simpa only [five,fourth_shape_explicit] using
      remainder_five_field_continuous mixed eta h0 h1 R hR (1/24) (-(1/6)) (1/4) (-(1/6)) (1/24)
  have h2 : ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight11 R t) curvatureInput) 0 := by
    simpa [five,curvatureInput,triple] using
      remainder_five_field_continuous mixed eta h0 h1 R hR (-(1/2)) 1 (-(1/2)) 0 0
  have hz : ContinuousAt (fun t : ℝ => sectorField mixed eta h0 h1 (remainderWeight11 R t) (Finsupp.single 0 1)) 0 := by
    simpa [five] using remainder_five_field_continuous mixed eta h0 h1 R hR 1 0 0 0 0
  simp only [quarticProfile,sub_eq_add_neg,← neg_smul,field_add_input,field_scale_input]
  have ha : ContinuousAt (fun t : ℝ => -((a*t^2 : ℝ) : ℂ)) 0 := by fun_prop
  have hb : ContinuousAt (fun t : ℝ => -((b*t^4 : ℝ) : ℂ)) 0 := by fun_prop
  exact (h4.add (ha.smul h2)).add (hb.smul hz)

theorem remainder_profile_kernel_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b : ℝ) :
    ContinuousAt (fun t : ℝ =>
      (sectorKernel mixed eta h0 h1 (remainderWeight11 R t) (quarticProfile a b t) (quarticProfile a b t)).re) 0 := by
  have hr := remainder_profile_field_continuous mixed eta h0 h1 R hR a b
  have hl : ContinuousAt (fun t : ℝ => physicalCauchySynthesis (quarticProfile a b t)) 0 := by
    simp only [quarticProfile,map_sub,map_smul]
    fun_prop
  unfold sectorKernel
  exact Complex.continuous_re.continuousAt.comp (hl.inner hr)

theorem remainder_profile_second_order (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a b : ℝ) :
    Tendsto (fun k : ℕ => radialStep k^2*
      (sectorKernel mixed eta h0 h1 (remainderWeight11 R (radialStep k))
        (quarticProfile a b (radialStep k)) (quarticProfile a b (radialStep k))).re)
      atTop (nhds 0) := by
  have hr := (remainder_profile_kernel_continuous mixed eta h0 h1 R hR a b).tendsto.comp radial_step_tendsto
  simpa only [Function.comp_def,zero_pow (by decide : 2≠0),zero_mul] using (radial_step_tendsto.pow 2).mul hr

end
end CarryQuarticTaylor
