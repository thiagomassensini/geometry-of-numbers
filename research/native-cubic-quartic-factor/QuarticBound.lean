import QuarticFactor

namespace CarryCubicQuartic
open CarrySelfAdjointOperator NativeLaguerre CarryCurvatureGreen CarryQuarticBoundary
open CarryCubicTfvd CarryStencilBoundary
open scoped InnerProductSpace unitInterval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- B4≤36 C², from the actual nonnegative symbol x³(120-91x), x=1-u. -/
theorem quartic_backward_upper_positive :
    ((36 : ℂ) • physicalComplement^2-quarticBackward).IsPositive := by
  let c : C(unitInterval, ℂ) := 1-physicalRadialCoefficient
  let symbol : C(unitInterval, ℂ) :=
    (36 : ℂ) • c^2-c^2*((36 : ℂ) • 1-(120 : ℂ) • c+(91 : ℂ) • c^2)
  have hop : (36 : ℂ) • physicalComplement^2-quarticBackward=intervalMultiplier symbol := by
    simp only [symbol, c, intervalMultiplier_sub, intervalMultiplier_smul,
      intervalMultiplier_mul, multiplier_add, intervalMultiplier_one,
      multiplier_pow, quarticBackward, physicalComplement, physicalRadialAdvance]
  rw [hop]
  have he (u : unitInterval) : symbol u=
      (((1-(u : ℝ))^3*(120-91*(1-(u : ℝ))) : ℝ) : ℂ) := by
    simp only [symbol, c, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      ContinuousMap.one_apply, physicalRadialCoefficient, ContinuousMap.coe_mk, smul_eq_mul]
    push_cast
    ring
  apply intervalMultiplier_isPositive
  · intro u
    simp only [he, Complex.ofReal_re]
  · intro u
    rw [he]
    simp only [Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr u.property.2) 3)
      (by nlinarith [u.property.1])

/-- The full signed response exceeds 27I on the same physical space.
No term is discarded: the positive decomposition is a proved symbol equality. -/
theorem quartic_margin_positive (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (quarticForward-(eta : ℂ)^2 • quarticBackward-(27 : ℂ) • 1).IsPositive := by
  let c : C(unitInterval, ℂ) := 1-physicalRadialCoefficient
  let symbol : C(unitInterval, ℂ) :=
    ((27 : ℂ) • 1+(26 : ℂ) • c+(61 : ℂ) • c^2)-
      (eta : ℂ)^2 • (c^2*((36 : ℂ) • 1-(120 : ℂ) • c+(91 : ℂ) • c^2))-(27 : ℂ) • 1
  have hop : quarticForward-(eta : ℂ)^2 • quarticBackward-(27 : ℂ) • 1=intervalMultiplier symbol := by
    simp only [symbol, c, intervalMultiplier_sub, intervalMultiplier_smul,
      intervalMultiplier_mul, multiplier_add, intervalMultiplier_one,
      multiplier_pow, quarticForward, quarticBackward, physicalComplement, physicalRadialAdvance]
  rw [hop]
  have he (u : unitInterval) : symbol u=Complex.ofReal
      (26*(1-(u : ℝ))+(61-36*eta^2)*(1-(u : ℝ))^2+
        eta^2*(1-(u : ℝ))^3*(120-91*(1-(u : ℝ)))) := by
    simp only [symbol, c, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      ContinuousMap.one_apply, physicalRadialCoefficient, ContinuousMap.coe_mk, smul_eq_mul]
    push_cast
    ring
  apply intervalMultiplier_isPositive
  · intro u
    simp only [he, Complex.ofReal_re]
  · intro u
    rw [he]
    simp only [Complex.ofReal_re]
    have hx : 0 ≤ 1-(u : ℝ) := sub_nonneg.mpr u.property.2
    have hc : 0 ≤ 61-36*eta^2 := by nlinarith
    have hd : 0 ≤ 120-91*(1-(u : ℝ)) := by nlinarith [u.property.1]
    positivity

theorem quartic_margin_inner_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    27*‖f‖^2 ≤ (inner ℂ f ((quarticForward-(eta : ℂ)^2 • quarticBackward) f)).re := by
  have hh := (quartic_margin_positive eta h0 h1).re_inner_nonneg_right f
  change 0 ≤ (inner ℂ f ((quarticForward-(eta : ℂ)^2 • quarticBackward-(27 : ℂ) • 1) f)).re at hh
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hh ⊢
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two, Complex.mul_im]
  norm_num [Complex.sub_re, Complex.mul_re, hRe, hIm] at hh ⊢
  linarith

theorem quartic_cubic_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (27/576 : ℝ)*‖quarticGradient eta h0 h1 f‖^2 ≤
      (inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta f))).re := by
  have hh := quartic_margin_inner_lower eta h0 h1 (quarticGradient eta h0 h1 f)
  rw [quartic_cubic_diagonal eta h0 h1]
  linarith

theorem native_quartic_cubic_lower_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (3/17920 : ℝ) ≤ nativeQuarticU3 eta h0 h1 := by
  have hn := mul_le_mul_of_nonneg_left (native_quartic_gradient_lower eta h0 h1)
    (by norm_num : (0 : ℝ)≤27/576)
  have hl := quartic_cubic_lower eta h0 h1 (completedNativeChiralCauchyFeature 0)
  rw [← native_quartic_cubic_identification eta h0 h1] at hl
  have hc : (27/576 : ℝ)*(1/280)=3/17920 := by norm_num
  rw [hc] at hn
  exact hn.trans hl

theorem native_quartic_cubic_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < nativeQuarticU3 eta h0 h1 :=
  lt_of_lt_of_le (by norm_num) (native_quartic_cubic_lower_bound eta h0 h1)

end
end CarryCubicQuartic
