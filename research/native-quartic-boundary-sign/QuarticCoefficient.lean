import BoundaryFactor
import BoundaryPolynomial

namespace CarryQuarticBoundary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen NativeLaguerre
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeBoundaryVector : PhysicalSpace :=
  (5/24 : ℂ) • completedNativeChiralCauchyFeature 1-(1/12 : ℂ) • completedNativeChiralCauchyFeature 2

def nativeBoundaryPair (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  (inner ℂ (physicalCauchySynthesis fourthShape)
    (physicalGreenOperator eta h0.le h1 nativeBoundaryVector)).re

def nativeQuarticCoefficient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  (inner ℂ (physicalCauchySynthesis fourthShape)
    (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) fourthShape)))).re

theorem native_quartic_vector : quarticVector (completedNativeChiralCauchyFeature 0)=
    physicalCauchySynthesis fourthShape := by
  rw [← fourth_native_curvature]
  simp only [quarticVector,physicalCurvature,liftedFourthSeed,map_smul,smul_smul]
  module

theorem native_boundary_vector : boundaryVector (completedNativeChiralCauchyFeature 0)=nativeBoundaryVector := by
  simp only [boundaryVector,nativeBoundaryVector,map_sub,map_smul,physicalRadialAdvance_feature]
  module

theorem native_quartic_gradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)=
      physicalGreenResolvent eta h0.le h1
        (completedNativeChiralCauchyFeature 1-(2 : ℂ) • completedNativeChiralCauchyFeature 2+
          completedNativeChiralCauchyFeature 3) := by
  unfold quarticGradient
  congr 1
  simp only [physicalComplement,sub_apply,one_apply_eq_self,map_sub,physicalRadialAdvance_feature]
  module

theorem fourth_lift_gradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    transportedGradient eta h0 h1 liftedFourthSeed = (-(1/12) : ℂ) •
      physicalComplement (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)) := by
  unfold transportedGradient liftedFourthSeed
  rw [map_smul,map_smul,map_smul,resolvent_advance_complement eta h0 h1]
  rfl

theorem native_boundary_pair_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeBoundaryPair eta h0 h1=eta/576*
      (5*‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2-
        2*(inner ℂ (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
          (physicalRadialAdvance (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))).re) := by
  unfold nativeBoundaryPair
  rw [← native_quartic_vector,← native_boundary_vector]
  exact quartic_boundary_diagonal_factor eta h0 h1 _

theorem native_quartic_seed_norm_square :
    ‖completedNativeChiralCauchyFeature 1-(2 : ℂ) • completedNativeChiralCauchyFeature 2+
      completedNativeChiralCauchyFeature 3‖^2=(1/280 : ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,inner_completedNativeChiralCauchyFeature]
  norm_num

theorem native_quartic_gradient_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/280 : ℝ) ≤ ‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 := by
  rw [native_quartic_gradient eta h0 h1,← native_quartic_seed_norm_square]
  have hn := resolvent_norm_lower eta h0.le h1
    (completedNativeChiralCauchyFeature 1-(2 : ℂ) • completedNativeChiralCauchyFeature 2+
      completedNativeChiralCauchyFeature 3)
  nlinarith [norm_nonneg (completedNativeChiralCauchyFeature 1-(2 : ℂ) • completedNativeChiralCauchyFeature 2+
    completedNativeChiralCauchyFeature 3),norm_nonneg (physicalGreenResolvent eta h0.le h1
      (completedNativeChiralCauchyFeature 1-(2 : ℂ) • completedNativeChiralCauchyFeature 2+
        completedNativeChiralCauchyFeature 3))]

/-- 53760=192*280, from the physical factor and the unchanged Cauchy Gram. -/
theorem native_boundary_pair_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    eta/53760 ≤ nativeBoundaryPair eta h0 h1 := by
  have hb := quartic_boundary_lower eta h0 h1 (completedNativeChiralCauchyFeature 0)
  rw [native_quartic_vector,native_boundary_vector] at hb
  change eta/192*‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 ≤
    nativeBoundaryPair eta h0 h1 at hb
  have hn := mul_le_mul_of_nonneg_left (native_quartic_gradient_lower eta h0 h1)
    (show 0≤eta/192 by positivity)
  nlinarith

theorem native_boundary_pair_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < nativeBoundaryPair eta h0 h1 := by
  have hp : 0 < eta/53760 := by positivity
  exact hp.trans_le (native_boundary_pair_lower eta h0 h1)

/-- The full native coefficient retains the boundary cross from PR96. -/
theorem native_quartic_coefficient_split (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeQuarticCoefficient eta h0 h1=
      (inner ℂ (physicalCurvature liftedFourthSeed)
        (physicalGreenOperator eta h0.le h1 (physicalTangent eta liftedFourthSeed))).re +
      eta⁻¹*nativeBoundaryPair eta h0 h1 := by
  unfold nativeQuarticCoefficient nativeBoundaryPair nativeBoundaryVector
  rw [fourth_tangent_defect,map_add,map_smul,inner_add_right,inner_smul_right]
  simp only [Complex.add_re,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rw [fourth_native_curvature]

/-- The corrected native coefficient, with the boundary kept in the SAME
physical state. The mixed advance pairing is not discarded. -/
theorem native_quartic_coefficient_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeQuarticCoefficient eta h0 h1 = (1/576 : ℝ)*
      (5*‖quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2-
        2*(inner ℂ (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))
          (physicalRadialAdvance (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))).re+
        ‖physicalComplement (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0))‖^2-
        eta^2*‖physicalComplement (physicalComplement
          (quarticGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)))‖^2) := by
  rw [native_quartic_coefficient_split eta h0 h1,
    curvature_green_diagonal_factor eta h0 h1,fourth_lift_gradient eta h0 h1,
    native_boundary_pair_factor eta h0 h1,map_smul]
  norm_num [norm_smul]
  field_simp [h0.ne']
  ring

theorem native_quartic_coefficient_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/53760 : ℝ) ≤ nativeQuarticCoefficient eta h0 h1 := by
  have hq := curvature_green_nonnegative eta h0 h1 liftedFourthSeed
  have hb := mul_le_mul_of_nonneg_left (native_boundary_pair_lower eta h0 h1)
    (show 0≤eta⁻¹ by positivity)
  have he : eta⁻¹*(eta/53760)=(1/53760 : ℝ) := by field_simp [h0.ne']
  rw [he] at hb
  rw [native_quartic_coefficient_split eta h0 h1]
  linarith

theorem native_quartic_coefficient_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < nativeQuarticCoefficient eta h0 h1 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/53760) (native_quartic_coefficient_lower eta h0 h1)

end
end CarryQuarticBoundary
