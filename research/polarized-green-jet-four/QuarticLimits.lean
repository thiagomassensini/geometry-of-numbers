import QuarticExpansion

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem error_readout_continuousAt (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (u v : Fin 3 → ℝ) :
    ContinuousAt (errorReadout R u v) 0 := by
  have hf (c : ℝ) : ContinuousAt (fun t : ℝ => (R ((c*t : ℝ) : ℂ)).re) 0 := by
    have hc : ContinuousAt (fun t : ℝ => ((c*t : ℝ) : ℂ)) 0 := by fun_prop
    have hx : Tendsto (fun t : ℝ => ((c*t : ℝ) : ℂ)) (nhds 0) (nhds 0) := by
      simpa only [mul_zero,Complex.ofReal_zero] using hc.tendsto
    simpa only [ContinuousAt,mul_zero,Complex.ofReal_zero,Function.comp_def] using
      (Complex.continuous_re.tendsto (R 0)).comp (hR.continuousAt.tendsto.comp hx)
  have h1 : ContinuousAt (fun t : ℝ => (R (t : ℂ)).re) 0 := by simpa using hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  have h5 := hf 5
  unfold errorReadout higherPolynomial normalizedMass
  norm_num only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,
    Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,add_zero]
  fun_prop

theorem quartic_finite_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (u v : Fin 3 → ℝ) :
    Tendsto (quarticBalance η u v) atTop (nhds (finiteTerm u v)) := by
  obtain ⟨R,hR,he⟩ := quartic_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR u v).tendsto.comp ht
  have h := (((tendsto_const_nhds (x := finiteTerm u v)).add
    ((ht.pow 2).mul_const (correctionTerm u v))).add
    ((ht.pow 4).mul_const (fourthTerm u v))).add ((ht.pow 6).mul hr)
  have hv : Tendsto (fun k => finiteTerm u v+radialStep k^2*correctionTerm u v+
      radialStep k^4*fourthTerm u v+radialStep k^6*errorReadout R u v (radialStep k))
      atTop (nhds (finiteTerm u v)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 u v] with k hk
  exact hk.symm

/-- First finite correction of the COMPLETE 25-crossing Green balance. -/
theorem quartic_correction_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (u v : Fin 3 → ℝ) :
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^2*(quarticBalance η u v k-finiteTerm u v)) atTop
      (nhds (correctionTerm u v)) := by
  obtain ⟨R,hR,he⟩ := quartic_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR u v).tendsto.comp ht
  have h := ((tendsto_const_nhds (x := correctionTerm u v)).add
    ((ht.pow 2).mul_const (fourthTerm u v))).add ((ht.pow 4).mul hr)
  have hv : Tendsto (fun k => correctionTerm u v+radialStep k^2*fourthTerm u v+
      radialStep k^4*errorReadout R u v (radialStep k)) atTop (nhds (correctionTerm u v)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 u v] with k hk
  rw [hk]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

/-- The next correction is explicit as well; its sign is not postulated. -/
theorem quartic_fourth_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (u v : Fin 3 → ℝ) :
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^4*(quarticBalance η u v k-finiteTerm u v-
      radialStep k^2*correctionTerm u v)) atTop (nhds (fourthTerm u v)) := by
  obtain ⟨R,hR,he⟩ := quartic_exact_expansion
  have ht := radial_step_limit
  have hr := (error_readout_continuousAt R hR u v).tendsto.comp ht
  have h := (tendsto_const_nhds (x := fourthTerm u v)).add ((ht.pow 2).mul hr)
  have hv : Tendsto (fun k => fourthTerm u v+radialStep k^2*errorReadout R u v (radialStep k))
      atTop (nhds (fourthTerm u v)) := by simpa using h
  apply hv.congr'
  filter_upwards [he η hη0 hη1 u v] with k hk
  rw [hk]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

/-- A genuine bound on the retained analytic error, after the two finite
corrections. M and the eventual threshold may depend on both coefficient vectors and the source;
no uniform-in-order estimate or numerical cutoff is claimed. -/
theorem quartic_sixth_error_bound (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (u v : Fin 3 → ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k : ℕ in atTop,
      |quarticBalance η u v k-finiteTerm u v-radialStep k^2*correctionTerm u v-
        radialStep k^4*fourthTerm u v|≤M*radialStep k^6 := by
  obtain ⟨R,hR,he⟩ := quartic_exact_expansion
  let M : ℝ := |errorReadout R u v 0|+1
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  have hu := (error_readout_continuousAt R hR u v).tendsto.comp radial_step_limit
  have hb := hu.abs.eventually (gt_mem_nhds (show |errorReadout R u v 0|<M by dsimp [M]; linarith))
  filter_upwards [he η hη0 hη1 u v,hb] with k hk hbound
  rw [hk]
  have hz : finiteTerm u v+radialStep k^2*correctionTerm u v+
      radialStep k^4*fourthTerm u v+radialStep k^6*errorReadout R u v (radialStep k)-
      finiteTerm u v-radialStep k^2*correctionTerm u v-radialStep k^4*fourthTerm u v=
      radialStep k^6*errorReadout R u v (radialStep k) := by ring
  rw [hz,abs_mul,abs_of_nonneg (by positivity : 0≤radialStep k^6)]
  calc
    _ ≤ radialStep k^6*M := mul_le_mul_of_nonneg_left hbound.le (by positivity)
    _ = M*radialStep k^6 := mul_comm _ _

end
end CarryPolarizedFour
