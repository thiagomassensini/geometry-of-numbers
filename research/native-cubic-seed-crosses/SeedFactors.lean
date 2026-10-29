import MixedFactors

namespace CarryCubicSeed
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre CarryNativeTfvd
open CarryCriticalTfvd CarryCurvatureGreen CarryQuarticBoundary CarryCubicTfvd
open CarryCubicQuartic CarryStencilBoundary CarryCommutatorControl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Forced by the cubic commutator of the positive original seed e₀. -/
def seedCubicTangent (eta : ℝ) (f : PhysicalSpace) : PhysicalSpace :=
  (-7*(eta : ℂ)) • physicalRadialAdvance f

theorem positive_seed_cubic_commutator (eta : ℝ) :
    completionCommutator eta (monomialWeight 3) (Finsupp.single 0 1)=
      Finsupp.single 1 (-7*(eta : ℂ)) := by
  ext j
  rcases j with _ | _ | j
  all_goals simp [completion_commutator_zero, cubic_commutator_succ,
    cubicForwardWeight, cubicBackwardWeight] <;> ring

/-- Calibration uses e₀, without identifying it with the old negative seedInput. -/
theorem positive_seed_eq_neg_seedInput :
    (Finsupp.single 0 1 : ℕ →₀ ℂ) = -seedInput := by
  ext j
  simp [seedInput, triple]

theorem seed_cubic_tangent_native (eta : ℝ) :
    seedCubicTangent eta (completedNativeChiralCauchyFeature 0)=
      physicalCauchySynthesis
        (completionCommutator eta (monomialWeight 3) (Finsupp.single 0 1)) := by
  rw [positive_seed_cubic_commutator]
  simp only [seedCubicTangent, physicalCauchySynthesis,
    Finsupp.linearCombination_single, physicalRadialAdvance_feature]

theorem seed_cubic_tangent_resolvent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (seedCubicTangent eta f)=
      (-7*(eta : ℂ)) • baseGradient eta h0 h1 f := by
  simp only [seedCubicTangent, map_smul, baseGradient]

/-- Complex 2→0 pairing, with independent physical inputs. -/
theorem quadratic_seed_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalCurvature f)
      (physicalGreenOperator eta h0.le h1 (seedCubicTangent eta g))=
      (7*(eta : ℂ)^2/2)*inner ℂ (transportedGradient eta h0 h1 f)
        (transportedGradient eta h0 h1 g) := by
  rw [green_inner_transport eta h0 h1, curvature_resolvent_advance eta h0 h1,
    seed_cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_smul_right]
  rw [gradient_pairing eta h0 h1]
  norm_num only [map_neg, map_div₀, map_one, map_ofNat]
  ring

/-- Complex 0→2 pairing is proved separately; the kernel is not symmetrized. -/
theorem seed_quadratic_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ f (physicalGreenOperator eta h0.le h1 (cubicTangent eta g))=
      (-(1/2) : ℂ)*inner ℂ (baseGradient eta h0 h1 f)
        (((19 : ℂ) • 1-(eta : ℂ)^2 • cubicQuadraticMultiplier)
          (baseGradient eta h0 h1 g)) := by
  rw [green_inner_transport eta h0 h1, cubic_tangent_resolvent eta h0 h1]
  simp only [sub_apply, smul_apply, one_apply_eq_self,
    inner_add_right, inner_sub_right, inner_smul_right]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]
  simp only [baseGradient]
  ring

/-- Complex 4→0 pairing keeps the original factorial 4!. -/
theorem quartic_seed_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (quarticVector f)
      (physicalGreenOperator eta h0.le h1 (seedCubicTangent eta g))=
      (-7*(eta : ℂ)^2/24)*inner ℂ (quarticGradient eta h0 h1 f)
        (quarticGradient eta h0 h1 g) := by
  rw [green_inner_transport eta h0 h1, quartic_resolvent_advance eta h0 h1,
    seed_cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_left, inner_smul_right]
  rw [quartic_base_pairing eta h0 h1]
  norm_num only [map_div₀, map_one, map_ofNat]
  ring

/-- Complex 0→4 pairing keeps the full signed quartic multiplier. -/
theorem seed_quartic_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ f (physicalGreenOperator eta h0.le h1 (quarticCubicTangent eta g))=
      (1/24 : ℂ)*inner ℂ (baseGradient eta h0 h1 f)
        ((quarticForward-(eta : ℂ)^2 • quarticBackward)
          (baseGradient eta h0 h1 g)) := by
  rw [green_inner_transport eta h0 h1, quartic_cubic_tangent_resolvent eta h0 h1]
  simp only [sub_apply, smul_apply, inner_smul_right, inner_sub_right]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]
  simp only [baseGradient]

theorem seed_seed_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ f (physicalGreenOperator eta h0.le h1 (seedCubicTangent eta g))=
      (-7*(eta : ℂ)^2)*inner ℂ (baseGradient eta h0 h1 f)
        (baseGradient eta h0 h1 g) := by
  rw [green_inner_transport eta h0 h1, seed_cubic_tangent_resolvent eta h0 h1]
  simp only [inner_smul_right, baseGradient]
  ring

theorem native_quadratic_seed_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)=
      (7*(eta : ℂ)^2/2)*inner ℂ
        (transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        (transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)) := by
  rw [cubic_kernel_original, ← native_curvature, ← seed_cubic_tangent_native]
  exact quadratic_seed_polarized eta h0 h1 _ _

theorem native_seed_quadratic_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput=
      (-(1/2) : ℂ)*inner ℂ
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        (((19 : ℂ) • 1-(eta : ℂ)^2 • cubicQuadraticMultiplier)
          (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))) := by
  rw [cubic_kernel_original, ← cubic_native_tangent]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul]
  exact seed_quadratic_polarized eta h0 h1 _ _

theorem native_quartic_seed_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)=
      (-7*(eta : ℂ)^2/24)*inner ℂ
        (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)) := by
  rw [cubic_kernel_original, ← native_quartic_vector, ← seed_cubic_tangent_native]
  exact quartic_seed_polarized eta h0 h1 _ _

theorem native_seed_quartic_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape=
      (1/24 : ℂ)*inner ℂ
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        ((quarticForward-(eta : ℂ)^2 • quarticBackward)
          (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))) := by
  rw [cubic_kernel_original, ← quartic_cubic_tangent_native]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul]
  exact seed_quartic_polarized eta h0 h1 _ _

theorem native_seed_seed_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    cubicKernel eta h0 h1 (Finsupp.single 0 1) (Finsupp.single 0 1)=
      (-7*(eta : ℂ)^2)*inner ℂ
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)) := by
  rw [cubic_kernel_original, ← seed_cubic_tangent_native]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul]
  exact seed_seed_polarized eta h0 h1 _ _

theorem native_quadratic_seed (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)).re=
      7*eta^2/2*‖transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 := by
  rw [native_quadratic_seed_complex, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, Complex.mul_im, pow_two]

theorem native_seed_quadratic (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput).re=
      -(1/2 : ℝ)*(inner ℂ
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        (((19 : ℂ) • 1-(eta : ℂ)^2 • cubicQuadraticMultiplier)
          (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))).re := by
  rw [native_seed_quadratic_complex]
  norm_num [Complex.mul_re]

theorem native_quartic_seed (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)).re=
      -7*eta^2/24*‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 := by
  rw [native_quartic_seed_complex, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, Complex.mul_im, pow_two]

theorem native_seed_quartic (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape).re=
      (1/24 : ℝ)*(inner ℂ
        (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
        ((quarticForward-(eta : ℂ)^2 • quarticBackward)
          (baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))).re := by
  rw [native_seed_quartic_complex]
  norm_num [Complex.mul_re]

theorem native_seed_seed (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) (Finsupp.single 0 1)).re=
      -7*eta^2*‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 := by
  rw [native_seed_seed_complex, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, Complex.mul_im, pow_two]

end
end CarryCubicSeed
