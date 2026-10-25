import FiniteExpansion

namespace CarryGreenFinitePart
open CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem error_readout_continuousAt (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a : ℝ) :
    ContinuousAt (errorReadout R a) 0 := by
  have hf (c : ℝ) : ContinuousAt (fun t : ℝ => (R ((c*t : ℝ) : ℂ)).re) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ((c*t : ℝ) : ℂ)) 0 := by fun_prop
    have hx : Tendsto (fun t : ℝ => ((c*t : ℝ) : ℂ)) (nhds 0) (nhds 0) := by
      simpa only [mul_zero,Complex.ofReal_zero] using hc.tendsto
    simpa only [ContinuousAt,mul_zero,Complex.ofReal_zero,Function.comp_def] using
      (Complex.continuous_re.tendsto (R 0)).comp (hR.continuousAt.tendsto.comp hx)
  have h1 : ContinuousAt (fun t : ℝ => (R (t : ℂ)).re) 0 := by simpa using hf 1
  unfold errorReadout remainderReadout
  fun_prop

theorem radial_mass_step (k : ℕ) : ((k : ℝ)+1)*radialStep k=1 := by
  unfold radialStep
  exact mul_inv_cancel₀ (by positivity)

theorem green_finite_term_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (a : ℝ) :
    Tendsto (greenBalance η a) atTop (nhds (finiteTerm a)) := by
  obtain ⟨R,hR,he⟩ := green_balance_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR a).tendsto.comp ht
  have h := (((tendsto_const_nhds (x := finiteTerm a)).add
    ((ht.pow 2).mul_const (correctionTerm a))).add
    ((ht.pow 4).mul_const (fourthPolynomial a))).add ((ht.pow 6).mul hr)
  have hv : Tendsto (fun k => finiteTerm a+radialStep k^2*correctionTerm a+
      radialStep k^4*fourthPolynomial a+radialStep k^6*errorReadout R a (radialStep k))
      atTop (nhds (finiteTerm a)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 a] with k hk
  exact hk.symm

/-- First finite correction of the COMPLETE nine-crossing Green balance. -/
theorem green_correction_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (a : ℝ) :
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^2*(greenBalance η a k-finiteTerm a)) atTop
      (nhds (correctionTerm a)) := by
  obtain ⟨R,hR,he⟩ := green_balance_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR a).tendsto.comp ht
  have h := ((tendsto_const_nhds (x := correctionTerm a)).add
    ((ht.pow 2).mul_const (fourthPolynomial a))).add ((ht.pow 4).mul hr)
  have hv : Tendsto (fun k => correctionTerm a+radialStep k^2*fourthPolynomial a+
      radialStep k^4*errorReadout R a (radialStep k)) atTop (nhds (correctionTerm a)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 a] with k hk
  rw [hk]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

/-- The next correction is explicit as well; its sign is not postulated. -/
theorem green_fourth_correction_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (a : ℝ) :
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^4*(greenBalance η a k-finiteTerm a-
      radialStep k^2*correctionTerm a)) atTop (nhds (fourthPolynomial a)) := by
  obtain ⟨R,hR,he⟩ := green_balance_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR a).tendsto.comp ht
  have h := (tendsto_const_nhds (x := fourthPolynomial a)).add ((ht.pow 2).mul hr)
  have hv : Tendsto (fun k => fourthPolynomial a+radialStep k^2*errorReadout R a (radialStep k))
      atTop (nhds (fourthPolynomial a)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 a] with k hk
  rw [hk]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

/-- A genuine bound on the retained analytic error, after the two finite
corrections. M and the eventual threshold may depend on a and the source;
no uniform-in-order estimate or numerical cutoff is claimed. -/
theorem green_sixth_order_error_bound (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (a : ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k : ℕ in atTop,
      |greenBalance η a k-finiteTerm a-radialStep k^2*correctionTerm a-
        radialStep k^4*fourthPolynomial a|≤M*radialStep k^6 := by
  obtain ⟨R,hR,he⟩ := green_balance_exact_expansion
  let M : ℝ := |errorReadout R a 0|+1
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  have hu := (error_readout_continuousAt R hR a).tendsto.comp radial_step_limit
  have hb := hu.abs.eventually (gt_mem_nhds (show |errorReadout R a 0|<M by dsimp [M]; linarith))
  filter_upwards [he η hη0 hη1 a,hb] with k hk hbound
  rw [hk]
  have hz : finiteTerm a+radialStep k^2*correctionTerm a+
      radialStep k^4*fourthPolynomial a+radialStep k^6*errorReadout R a (radialStep k)-
      finiteTerm a-radialStep k^2*correctionTerm a-radialStep k^4*fourthPolynomial a=
      radialStep k^6*errorReadout R a (radialStep k) := by ring
  rw [hz,abs_mul,abs_of_nonneg (by positivity : 0≤radialStep k^6)]
  calc
    _ ≤ radialStep k^6*M := mul_le_mul_of_nonneg_left hbound.le (by positivity)
    _ = M*radialStep k^6 := mul_comm _ _

end
end CarryGreenFinitePart
