import QuarticBound

namespace CarryCubicQuartic
open CarrySelfAdjointOperator NativeLaguerre CarryNativeTfvd CarryCriticalTfvd
open CarryCurvatureGreen CarryQuarticBoundary CarryCubicTfvd
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def mixedQuarticQuadratic (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  (cubicKernel eta h0 h1 fourthShape curvatureInput).re

def mixedQuadraticQuartic (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  (cubicKernel eta h0 h1 curvatureInput fourthShape).re

theorem quartic_quadratic_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement (quarticGradient eta h0 h1 f)))
      (cubicQuadraticMultiplier (baseGradient eta h0 h1 g))=
      inner ℂ (quarticGradient eta h0 h1 f)
        (cubicQuadraticMultiplier (quarticGradient eta h0 h1 g)) := by
  rw [complement_twice_pairing, ← cubic_multiplier_complement,
    ← cubic_multiplier_complement, ← quartic_gradient_as_complement eta h0 h1]

/-- Ordered 4→2 cross; no identification with the reverse cross is presumed. -/
theorem quartic_quadratic_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (cubicTangent eta g))=
      (-(1/48) : ℂ)*inner ℂ (quarticGradient eta h0 h1 f)
        (((19 : ℂ) • 1-(eta : ℂ)^2 • cubicQuadraticMultiplier) (quarticGradient eta h0 h1 g)) := by
  conv_rhs => simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right]
  rw [green_inner_transport eta h0 h1, quartic_resolvent_advance eta h0 h1,
    cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_smul_right, inner_add_right]
  rw [quartic_base_pairing eta h0 h1, quartic_quadratic_pairing eta h0 h1]
  norm_num only [map_div₀, map_one, map_ofNat]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]
  ring

theorem forward_gradient_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
      (quarticForward (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f) (quarticForward (transportedGradient eta h0 h1 g)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physical_complement_selfAdjoint
  have hh := hs (transportedGradient eta h0 h1 f) (quarticForward (baseGradient eta h0 h1 g))
  change inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
    (quarticForward (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f)
        (physicalComplement (quarticForward (baseGradient eta h0 h1 g))) at hh
  rw [← forward_complement, ← gradient_as_complement eta h0 h1] at hh
  exact hh

theorem backward_gradient_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
      (quarticBackward (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f) (quarticBackward (transportedGradient eta h0 h1 g)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physical_complement_selfAdjoint
  have hh := hs (transportedGradient eta h0 h1 f) (quarticBackward (baseGradient eta h0 h1 g))
  change inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
    (quarticBackward (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f)
        (physicalComplement (quarticBackward (baseGradient eta h0 h1 g))) at hh
  rw [← backward_complement, ← gradient_as_complement eta h0 h1] at hh
  exact hh

/-- The reverse ordered 2→4 cross is calibrated separately. -/
theorem quadratic_quartic_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta g))=
      (-(1/48) : ℂ)*inner ℂ (transportedGradient eta h0 h1 f)
        ((quarticForward-(eta : ℂ)^2 • quarticBackward) (transportedGradient eta h0 h1 g)) := by
  conv_rhs => simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right]
  rw [green_inner_transport eta h0 h1, curvature_resolvent_advance eta h0 h1,
    quartic_cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_smul_right, inner_sub_right]
  rw [forward_gradient_pairing eta h0 h1, backward_gradient_pairing eta h0 h1]
  norm_num only [map_div₀, map_one, map_ofNat, map_neg]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]
  ring

theorem native_quadratic_quartic_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    mixedQuadraticQuartic eta h0 h1 ≤ -(3/320 : ℝ) := by
  unfold mixedQuadraticQuartic
  rw [cubic_kernel_original, ← native_curvature, ← quartic_cubic_tangent_native,
    quadratic_quartic_polarized eta h0 h1]
  have hl := quartic_margin_inner_lower eta h0 h1
    (transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
  have hn := native_gradient_norm_lower eta h0 h1
  simp only [sub_apply, smul_apply] at hl
  norm_num [Complex.mul_re]
  linarith

theorem native_quartic_quadratic_upper (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    mixedQuarticQuadratic eta h0 h1 ≤ -(1/1120 : ℝ) := by
  unfold mixedQuarticQuadratic
  rw [cubic_kernel_original, ← native_quartic_vector, ← cubic_native_tangent,
    quartic_quadratic_polarized eta h0 h1]
  have hb := mul_le_mul_of_nonneg_left
    (cubic_multiplier_inner_upper (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))
    (sq_nonneg eta)
  have he := mul_le_mul_of_nonneg_right (by nlinarith : eta^2 ≤ 1)
    (sq_nonneg ‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖)
  have hn := native_quartic_gradient_lower eta h0 h1
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two, Complex.mul_im]
  norm_num [Complex.mul_re, Complex.sub_re, hRe, hIm]
  nlinarith

theorem native_ordered_crosses_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    mixedQuarticQuadratic eta h0 h1 < 0 ∧ mixedQuadraticQuartic eta h0 h1 < 0 := by
  constructor
  · exact lt_of_le_of_lt (native_quartic_quadratic_upper eta h0 h1) (by norm_num)
  · exact lt_of_le_of_lt (native_quadratic_quartic_upper eta h0 h1) (by norm_num)

/-- All four ordered pairings are retained in the two-jet source. -/
theorem two_jet_expansion (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    (cubicKernel eta h0 h1 (fourthShape-(a : ℂ) • curvatureInput)
      (fourthShape-(a : ℂ) • curvatureInput)).re =
      nativeQuarticU3 eta h0 h1+a^2*nativeU3 eta h0 h1-
        a*(mixedQuarticQuadratic eta h0 h1+mixedQuadraticQuartic eta h0 h1) := by
  have hh := cubic_three_input_expansion eta h0 h1 fourthShape curvatureInput
    (Finsupp.single 0 1) a 0
  simpa only [Complex.ofReal_zero, zero_smul, sub_zero, zero_pow (by decide : 2≠0),
    zero_mul, mul_zero, add_zero, nativeQuarticU3, nativeU3, spatialU,
    mixedQuarticQuadratic, mixedQuadraticQuartic, cubicKernel, Complex.add_re] using hh

/-- A genuine positive cone for the SAME two-jet source, not a Gram claim.
The sign restriction is on the free source coefficient, not on a moment form. -/
theorem two_jet_cone_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) (ha : 0 ≤ a) :
    (3/17920 : ℝ)+a^2/20+23*a/2240 ≤
      (cubicKernel eta h0 h1 (fourthShape-(a : ℂ) • curvatureInput)
        (fourthShape-(a : ℂ) • curvatureInput)).re := by
  have h4 := native_quartic_cubic_lower_bound eta h0 h1
  have h2 := mul_le_mul_of_nonneg_left (native_cubic_uniform_lower eta h0 h1) (sq_nonneg a)
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (native_quartic_quadratic_upper eta h0 h1)
      (native_quadratic_quartic_upper eta h0 h1)) ha
  rw [two_jet_expansion eta h0 h1]
  linarith

theorem two_jet_cone_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) (ha : 0 ≤ a) :
    0 < (cubicKernel eta h0 h1 (fourthShape-(a : ℂ) • curvatureInput)
      (fourthShape-(a : ℂ) • curvatureInput)).re := by
  apply lt_of_lt_of_le _ (two_jet_cone_lower eta h0 h1 a ha)
  nlinarith [sq_nonneg a]

end
end CarryCubicQuartic
