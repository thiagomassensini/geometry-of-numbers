import OddReadout

namespace CarrySourceLaw
open CarrySelfAdjointOperator CarryCriticalMixed Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem oddRemainder_continuousAt (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a : ℝ) :
    ContinuousAt (oddRemainder R a) 0 := by
  have hf (c : ℝ) : ContinuousAt (fun t : ℝ => (R ((c*t:ℝ):ℂ)).re) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ((c*t:ℝ):ℂ)) 0 := by fun_prop
    have hx : Tendsto (fun t : ℝ => ((c*t:ℝ):ℂ)) (nhds 0) (nhds 0) := by
      simpa only [mul_zero, Complex.ofReal_zero] using hc.tendsto
    have hz := (Complex.continuous_re.tendsto (R 0)).comp
      (hR.continuousAt.tendsto.comp hx)
    simpa only [ContinuousAt, mul_zero, Complex.ofReal_zero, Function.comp_def] using hz
  have h1 : ContinuousAt (fun t : ℝ => (R (t:ℂ)).re) 0 := by simpa using hf 1
  unfold oddRemainder
  fun_prop

theorem oddHigher_continuous (a : ℝ) : Continuous (oddHigher a) := by
  unfold oddHigher
  fun_prop

/-- Finite balance limit on this entire family, before choosing a critical
vector and without any sign premise. -/
theorem odd_balance_tendsto (a : ℝ) :
    Tendsto (oddBalance a) atTop (nhds (oddConstant a)) := by
  obtain ⟨R,hR,he⟩ := odd_balance_exact_remainder
  have ht := realStep_tendsto_zero
  have hr := (oddRemainder_continuousAt R hR a).tendsto.comp ht
  have hh := (oddHigher_continuous a).continuousAt.tendsto.comp ht
  have hu := (((tendsto_const_nhds (x := oddConstant a)).add
      ((ht.pow 2).mul_const (oddCorrection a))).add
      ((ht.pow 4).mul hh)).add ((ht.pow 3).mul hr)
  have hv : Tendsto (fun k => oddConstant a +
      canonicalGreenJetRealStep k^2*oddCorrection a +
      canonicalGreenJetRealStep k^4*oddHigher a (canonicalGreenJetRealStep k) +
      canonicalGreenJetRealStep k^3*oddRemainder R a (canonicalGreenJetRealStep k))
      atTop (nhds (oddConstant a)) := by simpa using hu
  apply hv.congr'
  filter_upwards [he a] with k hk
  exact hk.symm

/-- First finite-balance correction of the ORIGINAL source, with its entire
analytic remainder controlled. It may have either sign. -/
theorem odd_balance_correction_tendsto (a : ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*(oddBalance a k-oddConstant a))
      atTop (nhds (oddCorrection a)) := by
  obtain ⟨R,hR,he⟩ := odd_balance_exact_remainder
  have ht := realStep_tendsto_zero
  have hr := (oddRemainder_continuousAt R hR a).tendsto.comp ht
  have hh := (oddHigher_continuous a).continuousAt.tendsto.comp ht
  have hu := ((tendsto_const_nhds (x := oddCorrection a)).add
      ((ht.pow 2).mul hh)).add (ht.mul hr)
  have hv : Tendsto (fun k => oddCorrection a +
      canonicalGreenJetRealStep k^2*oddHigher a (canonicalGreenJetRealStep k) +
      canonicalGreenJetRealStep k*oddRemainder R a (canonicalGreenJetRealStep k))
      atTop (nhds (oddCorrection a)) := by simpa using hu
  apply hv.congr'
  filter_upwards [he a] with k hk
  rw [hk]
  unfold canonicalGreenJetRealStep
  have hn : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

end
end CarrySourceLaw
