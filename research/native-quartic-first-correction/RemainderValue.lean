import Taylor11

namespace CarryQuarticCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl CarryCriticalTfvd CarryQuarticTaylor
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The value is obtained from the next original Taylor coefficient, not fitted
to an energy or selected after a real readout. -/
theorem response_remainder11_with_value :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0= -(h 5 : ℂ) ∧
      ∀ᶠ z : ℂ in nhds 0,
        responseReadout z=(h 0 : ℂ)*z-(h 1 : ℂ)*z^3+(h 2 : ℂ)*z^5-
          (h 3 : ℂ)*z^7+(h 4 : ℂ)*z^9+z^11*R z := by
  obtain ⟨S,hS,he⟩ := response_readout_analytic.exists_eventuallyEq_sum_add_pow_mul 13
  refine ⟨fun z => -(h 5 : ℂ)+z^2*S z, by fun_prop, by simp, ?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  have hp : (∑ n ∈ Finset.range 13, (z^n/(n.factorial : ℂ)) • iteratedDeriv n responseReadout 0)=
      ∑ n ∈ Finset.range 13, responseCoefficient n*z^n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← response_coefficient_derivative]
    simp only [smul_eq_mul]
    ring
  rw [hp]
  have c0 := response_coefficient_even 0
  have c1 := response_coefficient_odd 0
  have c2 := response_coefficient_even 1
  have c3 := response_coefficient_odd 1
  have c4 := response_coefficient_even 2
  have c5 := response_coefficient_odd 2
  have c6 := response_coefficient_even 3
  have c7 := response_coefficient_odd 3
  have c8 := response_coefficient_even 4
  have c9 := response_coefficient_odd 4
  have c10 := response_coefficient_even 5
  have c11 := response_coefficient_odd 5
  have c12 := response_coefficient_even 6
  norm_num only at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,
    c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,smul_eq_mul]
  ring

/-- A witness for the remainder of the existing response; not a new source. -/
def nativeRemainder11 : ℂ → ℂ := Classical.choose response_remainder11_with_value

theorem native_remainder_analytic : AnalyticAt ℂ nativeRemainder11 0 :=
  (Classical.choose_spec response_remainder11_with_value).1

theorem native_remainder_value : nativeRemainder11 0= -(h 5 : ℂ) :=
  (Classical.choose_spec response_remainder11_with_value).2.1

theorem native_response_taylor11 :
    ∀ᶠ z : ℂ in nhds 0,
      responseReadout z=(h 0 : ℂ)*z-(h 1 : ℂ)*z^3+(h 2 : ℂ)*z^5-
        (h 3 : ℂ)*z^7+(h 4 : ℂ)*z^9+z^11*nativeRemainder11 z :=
  (Classical.choose_spec response_remainder11_with_value).2.2

/-- The SAME named witness is retained for every finite prefix and its halo. -/
theorem native_response_weight_prefix (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      responseWeight k j=Complex.I*(taylorWeight9 (radialStep k) j+
        (radialStep k : ℂ)^11*remainderWeight11 nativeRemainder11 (radialStep k) j) := by
  have ht (j : Fin N) : Tendsto (fun k : ℕ => ((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))
      atTop (nhds 0) := by
    have hv := Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
    simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero] using
      hv.const_mul (((j.val+1 : ℕ) : ℂ))
  have hall : ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      responseReadout (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) =
        (h 0 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))-
        (h 1 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^3+
        (h 2 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^5-
        (h 3 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^7+
        (h 4 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^9+
        (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^11*
          nativeRemainder11 (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
    rw [eventually_all]
    exact fun j => (ht j).eventually native_response_taylor11
  filter_upwards [hall] with k hk
  intro j
  rw [response_radial_readout,hk j]
  unfold taylorWeight9 remainderWeight11 monomialWeight
  ring

/-- Any analytic remainder of this SAME pointwise response identity has the
same center value, independently of the chosen witness off the neighborhood. -/
theorem remainder_value_of_response_identity (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0)
    (he : ∀ᶠ z : ℂ in nhds 0,
      responseReadout z=(h 0 : ℂ)*z-(h 1 : ℂ)*z^3+(h 2 : ℂ)*z^5-
        (h 3 : ℂ)*z^7+(h 4 : ℂ)*z^9+z^11*R z) :
    R 0= -(h 5 : ℂ) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k : ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have heq : ∀ᶠ k : ℕ in atTop,
      R (radialStep k : ℂ)=nativeRemainder11 (radialStep k : ℂ) := by
    filter_upwards [ht.eventually he,ht.eventually native_response_taylor11] with k hk hn
    have hd : (radialStep k : ℂ)^11≠0 := by
      apply pow_ne_zero
      apply Complex.ofReal_ne_zero.mpr
      unfold radialStep
      positivity
    apply mul_left_cancel₀ hd
    linear_combination -hk+hn
  have hleft := hR.continuousAt.tendsto.comp ht
  have hright := native_remainder_analytic.continuousAt.tendsto.comp ht
  rw [native_remainder_value] at hright
  have hsame : ∀ᶠ k : ℕ in atTop,
      nativeRemainder11 (radialStep k : ℂ)=R (radialStep k : ℂ) := by
    filter_upwards [heq] with k hk
    exact hk.symm
  exact tendsto_nhds_unique hleft (hright.congr' hsame)

end
end CarryQuarticCorrection
