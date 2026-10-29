import ResponseTaylor

namespace CarryQuarticTaylor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl CarryCriticalTfvd
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The old completed response, through degree nine; no coefficient sign is used. -/
theorem response_eleventh_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ t : ℂ in nhds 0,
      responseReadout t=(h 0 : ℂ)*t-(h 1 : ℂ)*t^3+(h 2 : ℂ)*t^5-
        (h 3 : ℂ)*t^7+(h 4 : ℂ)*t^9+t^11*R t := by
  obtain ⟨R,hR,he⟩ := response_readout_analytic.exists_eventuallyEq_sum_add_pow_mul 11
  refine ⟨R,hR,?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  have hp : (∑ n ∈ Finset.range 11, (t^n/(n.factorial : ℂ)) • iteratedDeriv n responseReadout 0)=
      ∑ n ∈ Finset.range 11, responseCoefficient n*t^n := by
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
  norm_num only at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,smul_eq_mul]
  ring

def remainderWeight11 (R : ℂ → ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  ((j+1 : ℕ) : ℂ)^11*R (((j+1 : ℕ) : ℂ)*(t : ℂ))

def taylorWeight9 (t : ℝ) (j : ℕ) : ℂ :=
  (h 0 : ℂ)*(t : ℂ)*monomialWeight 1 j-
    (h 1 : ℂ)*(t : ℂ)^3*monomialWeight 3 j+
    (h 2 : ℂ)*(t : ℂ)^5*monomialWeight 5 j-
    (h 3 : ℂ)*(t : ℂ)^7*monomialWeight 7 j+
    (h 4 : ℂ)*(t : ℂ)^9*monomialWeight 9 j

/-- ONE analytic remainder works for every finite prefix, including any halo. -/
theorem response_weight_taylor11_prefix :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ N : ℕ,
      ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
        responseWeight k j=Complex.I*(taylorWeight9 (radialStep k) j+
          (radialStep k : ℂ)^11*remainderWeight11 R (radialStep k) j) := by
  obtain ⟨R,hR,he⟩ := response_eleventh_remainder
  refine ⟨R,hR,?_⟩
  intro N
  have ht (j : Fin N) : Tendsto (fun k : ℕ => ((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))
      atTop (nhds 0) := by
    have hv := Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
    simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero] using
      hv.const_mul (((j.val+1 : ℕ) : ℂ))
  have hall : ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      responseReadout (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) =
        (h 0 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))-
        (h 1 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^3+
        (h 2 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^5-
        (h 3 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^7+
        (h 4 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^9+
        (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^11*
          R (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
    rw [eventually_all]
    exact fun j => (ht j).eventually he
  filter_upwards [hall] with k hk
  intro j
  rw [response_radial_readout, hk j]
  unfold taylorWeight9 remainderWeight11 monomialWeight
  ring

theorem response_weight_taylor11_six :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop, ∀ j : Fin 6,
      responseWeight k j=Complex.I*(taylorWeight9 (radialStep k) j+
        (radialStep k : ℂ)^11*remainderWeight11 R (radialStep k) j) := by
  obtain ⟨R,hR,he⟩ := response_weight_taylor11_prefix
  exact ⟨R,hR,he 6⟩

theorem remainder_weight11_continuous (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (j : ℕ) :
    ContinuousAt (fun t : ℝ => remainderWeight11 R t j) 0 := by
  have ht : Tendsto (fun t : ℝ => ((j+1 : ℕ) : ℂ)*(t : ℂ)) (nhds 0) (nhds 0) := by
    have hh : ContinuousAt (fun t : ℝ => ((j+1 : ℕ) : ℂ)*(t : ℂ)) 0 := by fun_prop
    simpa using hh.tendsto
  have hh : ContinuousAt (fun t : ℝ => R (((j+1 : ℕ) : ℂ)*(t : ℂ))) 0 := by
    simpa only [ContinuousAt,mul_zero,Complex.ofReal_zero,Function.comp_def] using
      hR.continuousAt.tendsto.comp ht
  exact continuousAt_const.mul hh

end
end CarryQuarticTaylor
