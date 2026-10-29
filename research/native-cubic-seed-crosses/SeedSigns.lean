import SeedFactors

namespace CarryCubicSeed
open CarrySelfAdjointOperator NativeLaguerre CarryCriticalTfvd CarryCurvatureGreen
open CarryQuarticBoundary CarryCubicTfvd CarryCubicQuartic
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem quadratic_gradient_norm_le_base (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    ‖transportedGradient eta h0 h1 f‖^2 ≤ ‖baseGradient eta h0 h1 f‖^2 := by
  have hh := physical_complement_contracts (baseGradient eta h0 h1 f)
  rw [← gradient_as_complement eta h0 h1] at hh
  nlinarith [norm_nonneg (transportedGradient eta h0 h1 f),
    norm_nonneg (baseGradient eta h0 h1 f)]

theorem quartic_gradient_norm_le_base (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    ‖quarticGradient eta h0 h1 f‖^2 ≤ ‖baseGradient eta h0 h1 f‖^2 := by
  have hh := (physical_complement_contracts
    (physicalComplement (baseGradient eta h0 h1 f))).trans
    (physical_complement_contracts (baseGradient eta h0 h1 f))
  rw [← quartic_gradient_as_complement eta h0 h1] at hh
  nlinarith [norm_nonneg (quarticGradient eta h0 h1 f),
    norm_nonneg (baseGradient eta h0 h1 f)]

/-- A coarse bound inherited from the literal native curvature norm. -/
theorem native_base_gradient_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/60 : ℝ) ≤ ‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 :=
  (native_gradient_norm_lower eta h0 h1).trans (quadratic_gradient_norm_le_base eta h0 h1 _)

theorem quadratic_margin_inner_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    12*‖f‖^2 ≤ (inner ℂ f
      (((19 : ℂ) • 1-(eta : ℂ)^2 • cubicQuadraticMultiplier) f)).re := by
  have hh := mul_le_mul_of_nonneg_left (cubic_multiplier_inner_upper f) (sq_nonneg eta)
  have he := mul_le_mul_of_nonneg_right (by nlinarith : eta^2 ≤ 1) (sq_nonneg ‖f‖)
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two, Complex.mul_im]
  norm_num [Complex.mul_re, Complex.sub_re, hRe, hIm]
  nlinarith

theorem native_quadratic_seed_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    7*eta^2/120 ≤ (cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)).re := by
  rw [native_quadratic_seed]
  have hh := mul_le_mul_of_nonneg_left (native_gradient_norm_lower eta h0 h1)
    (by positivity : 0 ≤ 7*eta^2/2)
  nlinarith

theorem native_seed_quadratic_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput).re ≤ -(1/10 : ℝ) := by
  rw [native_seed_quadratic]
  have hh := quadratic_margin_inner_lower eta h0 h1 (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
  have hn := native_base_gradient_lower eta h0 h1
  linarith

theorem native_quartic_seed_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)).re ≤ -eta^2/960 := by
  rw [native_quartic_seed]
  have hh := mul_le_mul_of_nonneg_left (native_quartic_gradient_lower eta h0 h1) (sq_nonneg eta)
  nlinarith

theorem native_seed_quartic_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (3/160 : ℝ) ≤ (cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape).re := by
  rw [native_seed_quartic]
  have hh := quartic_margin_inner_lower eta h0 h1 (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
  have hn := native_base_gradient_lower eta h0 h1
  linarith

theorem native_seed_seed_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) (Finsupp.single 0 1)).re ≤ -7*eta^2/60 := by
  rw [native_seed_seed]
  have hh := mul_le_mul_of_nonneg_left (native_base_gradient_lower eta h0 h1) (sq_nonneg eta)
  nlinarith

/-- The ordered crosses have opposite signs; neither is replaced by its reverse. -/
theorem native_seed_cross_signs (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < (cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)).re ∧
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput).re < 0 ∧
    (cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)).re < 0 ∧
    0 < (cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape).re := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := native_quadratic_seed_lower eta h0 h1
    nlinarith [sq_pos_of_pos h0]
  · exact lt_of_le_of_lt (native_seed_quadratic_upper eta h0 h1) (by norm_num)
  · have hh := native_quartic_seed_upper eta h0 h1
    nlinarith [sq_pos_of_pos h0]
  · exact lt_of_lt_of_le (by norm_num) (native_seed_quartic_lower eta h0 h1)

/-- Both ordered terms are retained, before estimating their sum. -/
theorem native_quadratic_seed_sum_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)+
      cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput).re ≤ -(1/24 : ℝ) := by
  rw [Complex.add_re, native_quadratic_seed, native_seed_quadratic]
  have hh := quadratic_margin_inner_lower eta h0 h1 (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
  have hn := native_base_gradient_lower eta h0 h1
  have hc := mul_le_mul_of_nonneg_left
    (quadratic_gradient_norm_le_base eta h0 h1 (completedNativeChiralCauchyFeature 0)) (sq_nonneg eta)
  have he := mul_le_mul_of_nonneg_right (by nlinarith : eta^2 ≤ 1)
    (sq_nonneg ‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖)
  nlinarith

theorem native_quartic_seed_sum_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/72 : ℝ) ≤ (cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)+
      cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape).re := by
  rw [Complex.add_re, native_quartic_seed, native_seed_quartic]
  have hh := quartic_margin_inner_lower eta h0 h1 (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
  have hn := native_base_gradient_lower eta h0 h1
  have hc := mul_le_mul_of_nonneg_left
    (quartic_gradient_norm_le_base eta h0 h1 (completedNativeChiralCauchyFeature 0)) (sq_nonneg eta)
  have he := mul_le_mul_of_nonneg_right (by nlinarith : eta^2 ≤ 1)
    (sq_nonneg ‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖)
  nlinarith

end
end CarryCubicSeed
