import CriticalFamily

namespace CarryCubicTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen CarryLinearTfvd CarryStencilBoundary
open scoped BigOperators InnerProductSpace ComplexConjugate unitInterval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Forced by the old cubic commutator on the original quadratic stencil. -/
def cubicQuadraticMultiplier : PhysicalSpace →L[ℂ] PhysicalSpace :=
  (7 : ℂ) • 1-(38 : ℂ) • physicalRadialAdvance+(37 : ℂ) • physicalRadialAdvance^2

/-- Algebraic re-expression of that literal commutator; no new source. -/
def cubicTangent (eta : ℝ) (f : PhysicalSpace) : PhysicalSpace :=
  (-19*(eta : ℂ)⁻¹/2) • physicalRadialAdvance f+
    ((eta : ℂ)/2) • physicalRadialAdvance (cubicQuadraticMultiplier f)

def nativeU3 (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  spatialU true eta h0 h1 (monomialWeight 3)

/-- Literal matching at all exterior addresses, before using an inequality. -/
theorem cubic_native_tangent (eta : ℝ) :
    cubicTangent eta (completedNativeChiralCauchyFeature 0)=
      physicalCauchySynthesis (completionCommutator eta (monomialWeight 3) curvatureInput) := by
  rw [curvatureInput, commutator_triple]
  unfold cubicTangent cubicQuadraticMultiplier
  simp only [physicalCauchySynthesis, map_add, map_smul, Finsupp.linearCombination_single,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_two, mul_apply_eq_comp,
    map_sub, physicalRadialAdvance_feature]
  norm_num [monomialWeight]
  module

theorem cubic_multiplier_advance (f : PhysicalSpace) :
    cubicQuadraticMultiplier (physicalRadialAdvance f)=physicalRadialAdvance (cubicQuadraticMultiplier f) := by
  simp only [cubicQuadraticMultiplier, add_apply, sub_apply, smul_apply, one_apply_eq_self,
    pow_two, mul_apply_eq_comp, map_add, map_sub, map_smul]

theorem cubic_multiplier_complement (f : PhysicalSpace) :
    cubicQuadraticMultiplier (physicalComplement f)=physicalComplement (cubicQuadraticMultiplier f) := by
  change cubicQuadraticMultiplier (f-physicalRadialAdvance f)=_
  rw [map_sub, cubic_multiplier_advance]
  rfl

theorem resolvent_cubic_multiplier (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (cubicQuadraticMultiplier f)=
      cubicQuadraticMultiplier (physicalGreenResolvent eta h0.le h1 f) := by
  simp only [cubicQuadraticMultiplier, add_apply, sub_apply, smul_apply, one_apply_eq_self,
    pow_two, mul_apply_eq_comp, map_add, map_sub, map_smul, resolvent_advance eta h0 h1]

theorem cubic_tangent_resolvent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (cubicTangent eta f)=
      (-19*(eta : ℂ)⁻¹/2) • baseGradient eta h0 h1 f+
      ((eta : ℂ)/2) • cubicQuadraticMultiplier (baseGradient eta h0 h1 f) := by
  unfold cubicTangent
  rw [map_add, map_smul, map_smul, ← cubic_multiplier_advance,
    resolvent_cubic_multiplier eta h0 h1]
  rfl

theorem cubic_multiplier_gradient_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
      (cubicQuadraticMultiplier (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f) (cubicQuadraticMultiplier (transportedGradient eta h0 h1 g)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physical_complement_selfAdjoint
  have hh := hs (transportedGradient eta h0 h1 f) (cubicQuadraticMultiplier (baseGradient eta h0 h1 g))
  change inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
    (cubicQuadraticMultiplier (baseGradient eta h0 h1 g))=
      inner ℂ (transportedGradient eta h0 h1 f)
        (physicalComplement (cubicQuadraticMultiplier (baseGradient eta h0 h1 g))) at hh
  rw [← cubic_multiplier_complement, ← gradient_as_complement eta h0 h1] at hh
  exact hh

/-- Two independent inputs, preserving the old Green pairing. -/
theorem cubic_curvature_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (cubicTangent eta g))=
      (1/4 : ℂ)*(19*inner ℂ (transportedGradient eta h0 h1 f) (transportedGradient eta h0 h1 g)-
        (eta : ℂ)^2*inner ℂ (transportedGradient eta h0 h1 f)
          (cubicQuadraticMultiplier (transportedGradient eta h0 h1 g))) := by
  rw [green_inner_transport eta h0 h1, curvature_resolvent_advance eta h0 h1,
    cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_add_right, inner_smul_right]
  rw [gradient_pairing eta h0 h1, cubic_multiplier_gradient_pairing eta h0 h1]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  norm_num only [map_neg, map_div₀, map_one, map_ofNat]
  field_simp [he]
  ring

theorem cubic_curvature_diagonal (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (cubicTangent eta f))).re=
      (1/4 : ℝ)*(19*‖transportedGradient eta h0 h1 f‖^2-
        eta^2*(inner ℂ (transportedGradient eta h0 h1 f)
          (cubicQuadraticMultiplier (transportedGradient eta h0 h1 f))).re) := by
  rw [cubic_curvature_polarized eta h0 h1, inner_self_eq_norm_sq_to_K]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two, Complex.mul_im]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re, Complex.sub_re, hRe, hIm]

/-- B≤7I follows from the actual symbol u(38-37u)≥0 on [0,1]. -/
theorem cubic_multiplier_upper_positive : ((7 : ℂ) • 1-cubicQuadraticMultiplier).IsPositive := by
  let symbol : C(unitInterval, ℂ) :=
    physicalRadialCoefficient*((38 : ℂ) • 1-(37 : ℂ) • physicalRadialCoefficient)
  have hop : (7 : ℂ) • 1-cubicQuadraticMultiplier=intervalMultiplier symbol := by
    simp only [symbol, intervalMultiplier_mul, intervalMultiplier_sub,
      intervalMultiplier_smul, intervalMultiplier_one]
    change _=physicalRadialAdvance*((38 : ℂ) • 1-(37 : ℂ) • physicalRadialAdvance)
    simp only [mul_sub, mul_smul_comm, mul_one, cubicQuadraticMultiplier, pow_two]
    module
  rw [hop]
  have he (u : unitInterval) : symbol u=(((u : ℝ)*(38-37*(u : ℝ)) : ℝ) : ℂ) := by
    simp only [symbol, ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, physicalRadialCoefficient, ContinuousMap.coe_mk, smul_eq_mul]
    push_cast
    ring
  apply intervalMultiplier_isPositive
  · intro u
    simp only [he, Complex.ofReal_re]
  · intro u
    rw [he]
    simp only [Complex.ofReal_re]
    exact mul_nonneg u.property.1 (by nlinarith [u.property.2])

theorem cubic_multiplier_inner_upper (f : PhysicalSpace) :
    (inner ℂ f (cubicQuadraticMultiplier f)).re ≤ 7*‖f‖^2 := by
  have hh := cubic_multiplier_upper_positive.re_inner_nonneg_right f
  change 0 ≤ (inner ℂ f (((7 : ℂ) • 1-cubicQuadraticMultiplier) f)).re at hh
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hh
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  norm_num [Complex.sub_re, Complex.mul_re, hRe] at hh
  linarith

theorem cubic_curvature_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (19-7*eta^2)/4*‖transportedGradient eta h0 h1 f‖^2 ≤
      (inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (cubicTangent eta f))).re := by
  have hh := mul_le_mul_of_nonneg_left (cubic_multiplier_inner_upper (transportedGradient eta h0 h1 f)) (sq_nonneg eta)
  rw [cubic_curvature_diagonal eta h0 h1]
  nlinarith

theorem native_cubic_identification (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeU3 eta h0 h1=(inner ℂ (physicalCurvature (completedNativeChiralCauchyFeature 0))
      (physicalGreenOperator eta h0.le h1 (cubicTangent eta (completedNativeChiralCauchyFeature 0)))).re := by
  simp only [nativeU3, spatialU, sectorKernel, sectorField, coefficientStencil, ite_true]
  rw [native_curvature, cubic_native_tangent]

theorem native_cubic_lower_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (19-7*eta^2)/240 ≤ nativeU3 eta h0 h1 := by
  have hh := mul_le_mul_of_nonneg_left (native_gradient_norm_lower eta h0 h1)
    (by nlinarith : 0 ≤ (19-7*eta^2)/4)
  have hb := cubic_curvature_lower eta h0 h1 (completedNativeChiralCauchyFeature 0)
  rw [← native_cubic_identification eta h0 h1] at hb
  have hc : (19-7*eta^2)/4*(1/60 : ℝ)=(19-7*eta^2)/240 := by ring
  rw [hc] at hh
  exact hh.trans hb

theorem native_cubic_uniform_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/20 : ℝ) ≤ nativeU3 eta h0 h1 := by
  have hh := native_cubic_lower_bound eta h0 h1
  have he : eta^2 ≤ 1 := by nlinarith
  linarith

theorem native_cubic_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : 0 < nativeU3 eta h0 h1 :=
  lt_of_lt_of_le (by norm_num) (native_cubic_uniform_lower eta h0 h1)

end
end CarryCubicTfvd
