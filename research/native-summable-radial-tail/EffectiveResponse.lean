import ExplicitFinitePairing
import NormalizedRemainder
import OddKernelFilters

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The explicit bounded tail of the original native response. -/
def effectiveResponseRemainder (M : ℕ) (z : ℂ) : ℂ :=
  (-Complex.I/2)*Complex.I^(2*M+1)*sourceRemainder M (Complex.I*z)

theorem effective_remainder_norm (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖effectiveResponseRemainder M z‖ ≤ 1/2 := by
  have hr := source_remainder_norm_le_one M (Complex.I*z) (by simpa [norm_mul] using hz)
  unfold effectiveResponseRemainder
  simp only [norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat,
    norm_pow, one_pow]
  nlinarith

theorem effective_remainder_analytic (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (effectiveResponseRemainder M) z := by
  unfold effectiveResponseRemainder
  have hr := source_remainder_analytic M (Complex.I*z) (by simpa [norm_mul] using hz)
  exact analyticAt_const.fun_mul (hr.fun_comp_of_eq (by fun_prop) rfl)

/-- The response decomposition holds on the explicit quarter disc, rather
than merely in an unspecified neighborhood of the origin. -/
theorem effective_response_expansion (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic (Complex.I*z) ≠ 0) :
    responseReadout z=oddTaylor M z+z^(2*M+1)*effectiveResponseRemainder M z := by
  have hnorm : ‖Complex.I*z‖ < 1/4 := by simpa [norm_mul] using hz
  have he := native_response_exact_remainder M (Complex.I*z) hnorm hF
  rw [CarryRadialFlow.original_rotated_response] at he
  have hp : (∑ n ∈ Finset.range M, ((Complex.I*z)^2)^n*(h n:ℂ)) =
      ∑ n ∈ Finset.range M, (-1:ℂ)^n*z^(2*n)*(h n:ℂ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_pow, Complex.I_sq, mul_pow, ← pow_mul]
  rw [hp] at he
  have ht : (2*Complex.I*z)*(∑ n ∈ Finset.range M, (-1:ℂ)^n*z^(2*n)*(h n:ℂ)) =
      2*Complex.I*oddTaylor M z := by
    unfold oddTaylor
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [pow_succ]
    ring
  rw [show 2*(Complex.I*z)=2*Complex.I*z by ring, ht] at he
  unfold effectiveResponseRemainder
  rw [mul_pow] at he
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  linear_combination (-Complex.I/2)*he +
    (responseReadout z-oddTaylor M z)*hi

/-- The effective native tail has an explicit derivative budget on the
same quarter disc, in the original rotated coordinate. -/
theorem effective_remainder_deriv_bound (M : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1/4) :
    ‖deriv (effectiveResponseRemainder M) z‖ ≤ 2 := by
  have hz' : ‖Complex.I*z‖ ≤ 1/4 := by simpa [norm_mul] using hz
  have hs := (source_remainder_analytic M (Complex.I*z) (by
    have := hz'; linarith)).differentiableAt.hasDerivAt
  have hi : HasDerivAt (fun w : ℂ => Complex.I*w) Complex.I z := by
    simpa using (hasDerivAt_id z).const_mul Complex.I
  have hc := hs.comp z hi
  have hd : HasDerivAt (effectiveResponseRemainder M)
      (((-Complex.I/2)*Complex.I^(2*M+1)) *
        (deriv (sourceRemainder M) (Complex.I*z)*Complex.I)) z := by
    exact hc.const_mul _
  rw [hd.deriv, norm_mul, norm_mul, norm_mul, norm_div, norm_neg,
    Complex.norm_I, Complex.norm_ofNat, norm_pow, Complex.norm_I, one_pow]
  have hb := source_remainder_deriv_bound M (Complex.I*z) hz'
  nlinarith

end
end CarrySummableRadial
