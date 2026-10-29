import VariationBudget
import NormalizedRemainder

namespace CarryJetVariationBudget
open CarryEffectiveRadial CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Derivative of the full omitted analytic tail before any scalarization.
The factor (2M+1) is retained; this does not assume uniformity in M. -/
theorem omitted_response_derivative_bound (M : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1/4) :
    ‖deriv (fun w : ℂ => w^(2*M+1)*sourceRemainder M w) z‖ ≤
      ((2*M+1:ℕ):ℝ)*‖z‖^(2*M) + 4*‖z‖^(2*M+1) := by
  have ha := source_remainder_analytic M z (by linarith)
  have hR := source_remainder_norm_le_one M z (by linarith)
  have hD := source_remainder_deriv_bound M z hz
  have hp := (hasDerivAt_id z).pow (2*M+1)
  have hh := hp.mul ha.differentiableAt.hasDerivAt
  change HasDerivAt (fun w : ℂ => w^(2*M+1)*sourceRemainder M w) _ z at hh
  rw [hh.deriv]
  simp only [id_eq, Pi.pow_apply, Nat.add_sub_cancel, mul_one]
  calc
    _ ≤ ‖((2*M+1:ℕ):ℂ)*z^(2*M)*sourceRemainder M z‖+
      ‖z^(2*M+1)*deriv (sourceRemainder M) z‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul,norm_pow,norm_natCast]
      have h1 := mul_le_mul_of_nonneg_left hR (show 0 ≤ ((2*M+1:ℕ):ℝ)*‖z‖^(2*M) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hD (show 0 ≤ ‖z‖^(2*M+1) by positivity)
      nlinarith


/-- The omitted-response derivative bound is for the original completed
logarithmic response, locally identified with the entire analytic remainder. -/
theorem native_response_derivative_prefix_error (M : ℕ) (z : ℂ)
    (hz : ‖z‖ < 1/4) (hD : z ∈ completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    ‖deriv (fun w : ℂ => completedNativeOperatorLogDerivative w -
      (2*w)*∑ n ∈ Finset.range M, (w^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)) z‖ ≤
      ((2*M+1:ℕ):ℝ)*‖z‖^(2*M) + 4*‖z‖^(2*M+1) := by
  have hfc := (completedNativeOperatorCharacteristic_analyticAt hD).continuousAt
  have hf := hfc.eventually_ne hF
  have hd : ∀ᶠ w : ℂ in nhds z, ‖w‖ < 1/4 := by
    exact (continuous_norm.continuousAt.eventually (gt_mem_nhds hz))
  have he : (fun w : ℂ => completedNativeOperatorLogDerivative w -
      (2*w)*∑ n ∈ Finset.range M, (w^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)) =ᶠ[nhds z]
      (fun w : ℂ => w^(2*M+1)*sourceRemainder M w) := by
    filter_upwards [hf,hd] with w hwF hwd
    rw [native_response_exact_remainder M w hwd hwF]
    ring
  rw [he.deriv_eq]
  exact omitted_response_derivative_bound M z hz.le


def responseTail (M : ℕ) (z : ℂ) : ℂ :=
  completedNativeOperatorLogDerivative z -
    (2*z)*∑ n ∈ Finset.range M, (z^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)

/-- Explicit derivative error at a native radial address, including its
original arithmetic address factor. -/
theorem radial_response_derivative_prefix_error (M i : ℕ) (t : ℝ)
    (hz : ‖CarryMovingRadial.point t i‖ < 1/4)
    (hD : CarryMovingRadial.point t i ∈ completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic (CarryMovingRadial.point t i) ≠ 0) :
    ‖deriv (fun h : ℝ => CarryMovingRadial.rho h i - CarryAllOrderTail.rhoPrefix h i M) t‖ ≤
      (((i:ℝ)+1)/2) *
        (((2*M+1:ℕ):ℝ)*‖CarryMovingRadial.point t i‖^(2*M) +
          4*‖CarryMovingRadial.point t i‖^(2*M+1)) := by
  have he : (fun h : ℝ => CarryMovingRadial.rho h i - CarryAllOrderTail.rhoPrefix h i M) =
      (fun h : ℝ => (-Complex.I/2)*responseTail M (CarryMovingRadial.point h i)) := by
    funext h
    have hq : completedNativeOperatorLogDerivative (CarryMovingRadial.point h i) =
        2*Complex.I*CarryMovingRadial.rho h i := by
      simpa only [CarryMovingRadial.point,CarryMovingRadial.rho,mul_assoc] using
        CarryRadialFlow.original_rotated_response (((i:ℂ)+1)*(h:ℂ))
    unfold CarryAllOrderTail.rhoPrefix responseTail
    rw [hq]
    have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
    linear_combination (CarryMovingRadial.rho h i)*hi
  have hf := completedNativeOperatorCharacteristic_analyticAt hD
  have hq := hf.deriv.neg.div hf hF
  have hg : AnalyticAt ℂ (responseTail M) (CarryMovingRadial.point t i) := by
    unfold responseTail
    apply hq.fun_sub
    fun_prop
  have hp := (hasDerivAt_id (t:ℂ)).const_mul (Complex.I*((i:ℂ)+1))
  have hc := (hg.differentiableAt.hasDerivAt.comp (t:ℂ) hp).comp_ofReal
  have hh := hc.const_mul (-Complex.I/2)
  have hd := native_response_derivative_prefix_error M (CarryMovingRadial.point t i) hz hD hF
  have hnorm : ‖Complex.I*((i:ℂ)+1)‖ = (i:ℝ)+1 := by
    rw [norm_mul,Complex.norm_I,one_mul]
    have hx := Complex.norm_real ((i:ℝ)+1)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hx
    push_cast at hx
    exact hx
  rw [he]
  change HasDerivAt (fun h : ℝ => (-Complex.I/2)*responseTail M (CarryMovingRadial.point h i)) _ t at hh
  rw [hh.deriv]
  simp only [norm_mul,norm_div,norm_neg,Complex.norm_I,Complex.norm_ofNat, mul_one, hnorm]
  change ‖deriv (responseTail M) (CarryMovingRadial.point t i)‖ ≤ _ at hd
  have ht := mul_le_mul_of_nonneg_left hd (show 0 ≤ (i:ℝ)+1 by positivity)
  nlinarith

end
end CarryJetVariationBudget
