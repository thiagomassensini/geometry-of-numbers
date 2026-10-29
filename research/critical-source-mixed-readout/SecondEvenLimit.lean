import SecondEvenReadout

namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- No pivot sign or moment coefficient is used in this regularization limit. -/
theorem realStep_tendsto_zero :
    Tendsto canonicalGreenJetRealStep atTop (nhds 0) := by
  unfold canonicalGreenJetRealStep
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)

theorem normalizedSourceRemainder_continuousAt (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) (a : ℝ) :
    ContinuousAt (normalizedSourceRemainder R a) 0 := by
  have hf (c : ℝ) : ContinuousAt (fun t : ℝ => (R ((c*t : ℝ):ℂ)).re) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ((c*t : ℝ):ℂ)) 0 := by fun_prop
    have hx : Tendsto (fun t : ℝ => ((c*t : ℝ):ℂ)) (nhds 0) (nhds 0) := by
      simpa only [mul_zero, Complex.ofReal_zero] using hc.tendsto
    have hz := (Complex.continuous_re.tendsto (R 0)).comp
      (hR.continuousAt.tendsto.comp hx)
    simpa only [ContinuousAt, mul_zero, Complex.ofReal_zero, Function.comp_def] using hz
  have h1 : ContinuousAt (fun t : ℝ => (R (t:ℂ)).re) 0 := by simpa using hf 1
  unfold normalizedSourceRemainder
  fun_prop

/-- The original balance has a finite source-only limit for every a. -/
theorem second_balance_tendsto (a : ℝ) :
    Tendsto (secondBalance a) atTop (nhds (balanceConstant a)) := by
  obtain ⟨R,hR,he⟩ := second_balance_exact_source_remainder
  have ht := realStep_tendsto_zero
  have hr := (normalizedSourceRemainder_continuousAt R hR a).tendsto.comp ht
  have hu := ((((tendsto_const_nhds (x := balanceConstant a)).add
      ((ht.pow 2).mul_const (balanceCorrection a))).add
      ((ht.pow 4).mul_const (balanceFourth a))).sub
      (((ht.pow 6).mul_const (sourceCoefficient 3)).mul_const (a^2))).add
      ((ht.pow 3).mul hr)
  have hv : Tendsto (fun k => balanceConstant a +
      canonicalGreenJetRealStep k^2*balanceCorrection a +
      canonicalGreenJetRealStep k^4*balanceFourth a -
      canonicalGreenJetRealStep k^6*sourceCoefficient 3*a^2 +
      canonicalGreenJetRealStep k^3*normalizedSourceRemainder R a (canonicalGreenJetRealStep k))
      atTop (nhds (balanceConstant a)) := by simpa using hu
  apply hv.congr'
  filter_upwards [he a] with k hk
  exact hk.symm

/-- First correction to the finite balance; the entire analytic remainder
has been controlled. No condition on the sign of this correction is assumed. -/
theorem second_balance_correction_tendsto (a : ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*(secondBalance a k-balanceConstant a))
      atTop (nhds (balanceCorrection a)) := by
  obtain ⟨R,hR,he⟩ := second_balance_exact_source_remainder
  have ht := realStep_tendsto_zero
  have hr := (normalizedSourceRemainder_continuousAt R hR a).tendsto.comp ht
  have hu := (((tendsto_const_nhds (x := balanceCorrection a)).add
      ((ht.pow 2).mul_const (balanceFourth a))).sub
      (((ht.pow 4).mul_const (sourceCoefficient 3)).mul_const (a^2))).add (ht.mul hr)
  have hv : Tendsto (fun k => balanceCorrection a +
      canonicalGreenJetRealStep k^2*balanceFourth a -
      canonicalGreenJetRealStep k^4*sourceCoefficient 3*a^2 +
      canonicalGreenJetRealStep k*normalizedSourceRemainder R a (canonicalGreenJetRealStep k))
      atTop (nhds (balanceCorrection a)) := by simpa using hu
  apply hv.congr'
  filter_upwards [he a] with k hk
  rw [hk]
  unfold canonicalGreenJetRealStep
  have hn : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

end
end CarryCriticalMixed
