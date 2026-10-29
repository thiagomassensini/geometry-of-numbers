import QuarticPolynomials

namespace CarryCubicQuartic
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre CarryNativeTfvd
open CarryCriticalTfvd CarryCurvatureGreen CarryLinearTfvd CarryQuarticBoundary
open CarryCubicTfvd CarryStencilBoundary
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Forced cubic tangent of the OLD fourth difference, including its 4!. -/
def quarticCubicTangent (eta : ℝ) (f : PhysicalSpace) : PhysicalSpace :=
  (1/24 : ℂ) • ((eta : ℂ)⁻¹ • physicalRadialAdvance (quarticForward f)-
    (eta : ℂ) • physicalRadialAdvance (quarticBackward f))

def nativeQuarticU3 (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  (cubicKernel eta h0 h1 fourthShape fourthShape).re

/-- Exact original commutator, including the outgoing coefficient at address 5. -/
theorem quartic_cubic_commutator (eta : ℝ) :
    completionCommutator eta (monomialWeight 3) fourthShape =
      Finsupp.single 1 (19*(eta : ℂ)⁻¹/4-7*(eta : ℂ)/24)+
      Finsupp.single 2 (-37*(eta : ℂ)⁻¹/6+19*(eta : ℂ)/6)+
      Finsupp.single 3 (61*(eta : ℂ)⁻¹/24-37*(eta : ℂ)/4)+
      Finsupp.single 4 (61*(eta : ℂ)/6)+Finsupp.single 5 (-91*(eta : ℂ)/24) := by
  ext j
  rcases j with _ | _ | _ | _ | _ | _ | j
  all_goals simp [completion_commutator_zero, cubic_commutator_succ,
    fourth_shape_explicit, cubicForwardWeight, cubicBackwardWeight] <;> ring

theorem quartic_cubic_halo_nonzero (eta : ℝ) (h0 : 0 < eta) :
    completionCommutator eta (monomialWeight 3) fourthShape 5 ≠ 0 := by
  simp [quartic_cubic_commutator, Complex.ofReal_ne_zero.mpr h0.ne']

/-- Whole-vector matching precedes the Green factorization and any sign. -/
theorem quartic_cubic_tangent_native (eta : ℝ) :
    quarticCubicTangent eta (completedNativeChiralCauchyFeature 0)=
      physicalCauchySynthesis (completionCommutator eta (monomialWeight 3) fourthShape) := by
  rw [quartic_cubic_commutator]
  unfold quarticCubicTangent
  rw [quartic_forward_in_advance, quartic_backward_in_advance]
  simp only [physicalCauchySynthesis, map_add, Finsupp.linearCombination_single,
    add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_succ, pow_zero,
    mul_apply_eq_comp, map_sub, map_smul, physicalRadialAdvance_feature]
  module

theorem quartic_cubic_tangent_resolvent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (quarticCubicTangent eta f)=
      (1/24 : ℂ) • ((eta : ℂ)⁻¹ • quarticForward (baseGradient eta h0 h1 f)-
        (eta : ℂ) • quarticBackward (baseGradient eta h0 h1 f)) := by
  unfold quarticCubicTangent
  rw [map_smul, map_sub, map_smul, map_smul, ← forward_advance, ← backward_advance,
    resolvent_forward eta h0 h1, resolvent_backward eta h0 h1]
  rfl

theorem quartic_forward_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement (quarticGradient eta h0 h1 f)))
      (quarticForward (baseGradient eta h0 h1 g))=
      inner ℂ (quarticGradient eta h0 h1 f) (quarticForward (quarticGradient eta h0 h1 g)) := by
  rw [complement_twice_pairing, ← forward_complement, ← forward_complement,
    ← quartic_gradient_as_complement eta h0 h1]

theorem quartic_backward_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement (quarticGradient eta h0 h1 f)))
      (quarticBackward (baseGradient eta h0 h1 g))=
      inner ℂ (quarticGradient eta h0 h1 f) (quarticBackward (quarticGradient eta h0 h1 g)) := by
  rw [complement_twice_pairing, ← backward_complement, ← backward_complement,
    ← quartic_gradient_as_complement eta h0 h1]

/-- Two independent physical inputs; every signed term stays in the same kernel. -/
theorem quartic_cubic_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta g))=
      (1/576 : ℂ)*inner ℂ (quarticGradient eta h0 h1 f)
        ((quarticForward-(eta : ℂ)^2 • quarticBackward) (quarticGradient eta h0 h1 g)) := by
  conv_rhs => simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right]
  rw [green_inner_transport eta h0 h1, quartic_resolvent_advance eta h0 h1,
    quartic_cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_smul_right, inner_sub_right]
  rw [quartic_forward_pairing eta h0 h1, quartic_backward_pairing eta h0 h1]
  norm_num only [map_div₀, map_one, map_ofNat]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]
  ring

theorem quartic_cubic_diagonal (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta f))).re=
      (inner ℂ (quarticGradient eta h0 h1 f)
        ((quarticForward-(eta : ℂ)^2 • quarticBackward) (quarticGradient eta h0 h1 f))).re/576 := by
  rw [quartic_cubic_polarized eta h0 h1]
  norm_num [Complex.mul_re]
  ring

theorem native_quartic_cubic_identification (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeQuarticU3 eta h0 h1 =
      (inner ℂ (quarticVector (completedNativeChiralCauchyFeature 0))
        (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta (completedNativeChiralCauchyFeature 0)))).re := by
  unfold nativeQuarticU3
  rw [cubic_kernel_original, ← native_quartic_vector, ← quartic_cubic_tangent_native]

theorem native_quartic_cubic_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeQuarticU3 eta h0 h1 =
      (inner ℂ (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        ((quarticForward-(eta : ℂ)^2 • quarticBackward)
          (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))).re/576 := by
  rw [native_quartic_cubic_identification eta h0 h1, quartic_cubic_diagonal eta h0 h1]

end
end CarryCubicQuartic
