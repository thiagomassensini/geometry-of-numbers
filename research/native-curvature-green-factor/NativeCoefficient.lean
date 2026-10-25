import CurvatureKernel
import Cancellation

namespace CarryCurvatureGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre CarryCriticalTfvd
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeU1 (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  spatialU true eta h0 h1 (monomialWeight 1)

/-- Identification with the original native three-address stencil, before pairing. -/
theorem native_curvature : physicalCurvature (completedNativeChiralCauchyFeature 0)=
    physicalCauchySynthesis curvatureInput := by
  change (-(1/2) : ℂ) •
    ((completedNativeChiralCauchyFeature 0-physicalRadialAdvance (completedNativeChiralCauchyFeature 0))-
      physicalRadialAdvance (completedNativeChiralCauchyFeature 0-
        physicalRadialAdvance (completedNativeChiralCauchyFeature 0))) = _
  rw [map_sub]
  simp only [physicalRadialAdvance_feature,curvatureInput,synthesis_triple]
  module

/-- The outgoing address and the original boundary contribution both survive. -/
theorem native_tangent (eta : ℝ) :
    physicalTangent eta (completedNativeChiralCauchyFeature 0)=
      physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) curvatureInput) := by
  unfold physicalTangent
  rw [native_curvature]
  have hs : physicalCauchySynthesis curvatureInput =
      (-(1/2) : ℂ) • completedNativeChiralCauchyFeature 0 +
      (1 : ℂ) • completedNativeChiralCauchyFeature 1 +
      (-(1/2) : ℂ) • completedNativeChiralCauchyFeature 2 := synthesis_triple _ _ _
  rw [hs,curvatureInput,commutator_triple]
  simp only [physicalCauchySynthesis,map_add,map_smul,Finsupp.linearCombination_single,
    physicalRadialAdvance_feature]
  norm_num [monomialWeight]
  module

theorem native_transported_gradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)=
      physicalGreenResolvent eta h0.le h1
        (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2) := by
  unfold transportedGradient
  change physicalGreenResolvent eta h0.le h1
    (physicalRadialAdvance (completedNativeChiralCauchyFeature 0-
      physicalRadialAdvance (completedNativeChiralCauchyFeature 0))) = _
  simp only [map_sub,physicalRadialAdvance_feature]

theorem native_u1_identification (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeU1 eta h0 h1 =
      (inner ℂ (physicalCurvature (completedNativeChiralCauchyFeature 0))
        (physicalGreenOperator eta h0.le h1
          (physicalTangent eta (completedNativeChiralCauchyFeature 0)))).re := by
  simp only [nativeU1,spatialU,sectorKernel,sectorField,coefficientStencil,ite_true]
  rw [native_curvature,native_tangent]

/-- The candidate from PR95 is now a theorem about the SAME physical coefficient. -/
theorem native_u1_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    nativeU1 eta h0 h1=(1/4 : ℝ)*
      (‖physicalGreenResolvent eta h0.le h1
          (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2)‖^2-
        eta^2*‖physicalComplement (physicalGreenResolvent eta h0.le h1
          (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2))‖^2) := by
  rw [native_u1_identification eta h0 h1,curvature_green_diagonal_factor eta h0 h1,native_transported_gradient eta h0 h1]

theorem native_difference_norm_square :
    ‖completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2‖^2=(1/60 : ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_sub_left,inner_sub_right,inner_completedNativeChiralCauchyFeature]
  norm_num

theorem native_gradient_norm_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1/60 : ℝ) ≤ ‖transportedGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2 := by
  rw [native_transported_gradient eta h0 h1,← native_difference_norm_square]
  have hn := resolvent_norm_lower eta h0.le h1
    (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2)
  nlinarith [norm_nonneg (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2),
    norm_nonneg (physicalGreenResolvent eta h0.le h1
      (completedNativeChiralCauchyFeature 1-completedNativeChiralCauchyFeature 2))]

/-- The constant 240 is 4*60, from the factorization and the original column Gram. -/
theorem native_u1_lower_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1-eta^2)/240 ≤ nativeU1 eta h0 h1 := by
  have hn := native_gradient_norm_lower eta h0 h1
  have hp : 0 ≤ (1-eta^2)/4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hn hp
  have hb := curvature_green_lower_bound eta h0 h1 (completedNativeChiralCauchyFeature 0)
  rw [← native_u1_identification eta h0 h1] at hb
  have hc : (1-eta^2)/4*(1/60 : ℝ)=(1-eta^2)/240 := by ring
  rw [hc] at hm
  exact hm.trans hb

theorem native_u1_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : 0 < nativeU1 eta h0 h1 := by
  have hp : 0 < (1-eta^2)/240 := by nlinarith
  exact hp.trans_le (native_u1_lower_bound eta h0 h1)

end
end CarryCurvatureGreen
