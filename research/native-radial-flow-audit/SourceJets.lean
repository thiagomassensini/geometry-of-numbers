import CarrySelfAdjointOperator.CompletedNativeChiralReturnSeventhSourceJet
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceLimit

namespace CarryRadialFlow
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Ordinary Taylor coefficient at the original center. -/
def tc (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0/(n.factorial:ℂ)

theorem tc_mul (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    tc (fun z => f z*g z) n=∑ j ∈ Finset.range (n+1), tc f j*tc g (n-j) := by
  unfold tc
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
  have he : (n.choose j:ℂ)*(j.factorial:ℂ)*((n-j).factorial:ℂ)=(n.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hjf : (j.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnj : ((n-j).factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hn,hjf,hnj]
  linear_combination (iteratedDeriv j f 0)*(iteratedDeriv (n-j) g 0)*he

theorem tc_add (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    tc (fun z => f z+g z) n=tc f n+tc g n := by
  unfold tc
  rw [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt]
  ring

theorem tc_deriv (f : ℂ → ℂ) (n : ℕ) :
    tc (deriv f) n=(n+1:ℂ)*tc f (n+1) := by
  unfold tc
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have hn : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : (n:ℂ)+1≠0 := by exact_mod_cast (by omega : n+1≠0)
  field_simp [hn,hs]

theorem tc_id (n : ℕ) : tc (fun z : ℂ => z) n=if n=1 then 1 else 0 := by
  cases n with
  | zero => simp [tc]
  | succ n =>
    rw [tc,iteratedDeriv_succ']
    cases n <;> simp [iteratedDeriv_const]

/-- The source logarithmic derivative is exactly twice the old normalized
Green response. No moment or zero is supplied as input to the source. -/
theorem source_normalized_response :
    completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion=
        fun z => completedNativeOperatorLogDerivative z/2 := by
  funext z
  simp only [completedGreenNormalizedResponse,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv, completedNativeOperatorLogDerivative,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem source_tc_odd (n : ℕ) :
    tc completedNativeOperatorLogDerivative (2*n+1)=
      2*(canonicalCompletedNativeLogDerivativeMoment n:ℂ) := by
  have h := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n
  unfold completedNativeGreenResponseTaylorCoefficient at h
  rw [source_normalized_response,iteratedDeriv_div_const] at h
  rw [div_right_comm] at h
  change tc completedNativeOperatorLogDerivative (2*n+1)/2=_ at h
  linear_combination 2*h

theorem source_tc_even (n : ℕ) : tc completedNativeOperatorLogDerivative (2*n)=0 := by
  have h := completedNativeGreenResponseTaylorCoefficient_even_eq_zero n
  unfold completedNativeGreenResponseTaylorCoefficient at h
  rw [source_normalized_response,iteratedDeriv_div_const] at h
  rw [div_right_comm] at h
  change tc completedNativeOperatorLogDerivative (2*n)/2=0 at h
  linear_combination 2*h

/-- Diagnostic response of the proposed radial Loewner flow. This does not
replace the original moments or construct a new height operator. -/
def flowResponse (z : ℂ) : ℂ :=
  z*deriv completedNativeOperatorLogDerivative z/
    (1+completedNativeOperatorLogDerivative z^2)

theorem source_zero : completedNativeOperatorLogDerivative 0=0 := by
  simpa [tc] using source_tc_even 0

theorem flow_analytic : AnalyticAt ℂ flowResponse 0 := by
  have hq := nativeSourceLogSlope_analyticAt
  unfold flowResponse
  exact (analyticAt_id.fun_mul hq.deriv).div (analyticAt_const.fun_add (hq.pow 2))
    (by simp [source_zero])

theorem flow_equation : (fun z => flowResponse z+
    completedNativeOperatorLogDerivative z*(completedNativeOperatorLogDerivative z*flowResponse z))
    =ᶠ[nhds 0] (fun z => z*deriv completedNativeOperatorLogDerivative z) := by
  have hc : ContinuousAt (fun z => 1+completedNativeOperatorLogDerivative z^2) 0 := by
    exact (analyticAt_const.fun_add (nativeSourceLogSlope_analyticAt.pow 2)).continuousAt
  have hne : (1+completedNativeOperatorLogDerivative 0^2:ℂ)≠0 := by simp [source_zero]
  filter_upwards [hc.eventually_ne hne] with z hz
  unfold flowResponse
  field_simp [hz]

theorem flow_tc_recurrence (n : ℕ) :
    tc flowResponse n+
      ∑ j ∈ Finset.range (n+1), tc completedNativeOperatorLogDerivative j*
        (∑ l ∈ Finset.range (n-j+1), tc completedNativeOperatorLogDerivative l*
          tc flowResponse (n-j-l))=
      ∑ j ∈ Finset.range (n+1), (if j=1 then (1:ℂ) else 0)*
        ((((n-j:ℕ):ℂ)+1)*tc completedNativeOperatorLogDerivative (n-j+1)) := by
  have he := flow_equation.iteratedDeriv_eq n
  have ht : tc (fun z => flowResponse z+
      completedNativeOperatorLogDerivative z*(completedNativeOperatorLogDerivative z*flowResponse z)) n=
      tc (fun z => z*deriv completedNativeOperatorLogDerivative z) n := by
    unfold tc
    rw [he]
  rw [tc_add _ _ flow_analytic
    (nativeSourceLogSlope_analyticAt.fun_mul (nativeSourceLogSlope_analyticAt.fun_mul flow_analytic))] at ht
  rw [tc_mul _ _ nativeSourceLogSlope_analyticAt
    (nativeSourceLogSlope_analyticAt.fun_mul flow_analytic),
    tc_mul (fun z : ℂ => z) (deriv completedNativeOperatorLogDerivative)
      (by fun_prop) nativeSourceLogSlope_analyticAt.deriv] at ht
  simp_rw [tc_mul _ _ nativeSourceLogSlope_analyticAt flow_analytic,tc_id,tc_deriv] at ht
  exact ht

end
end CarryRadialFlow
