import ComplementNorm
import GreenSeed

namespace CarryCurvatureGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The native second-difference shape under the ORIGINAL radial advance. -/
def physicalCurvature (f : PhysicalSpace) : PhysicalSpace :=
  (-(1/2) : ℂ) • physicalComplement (physicalComplement f)

/-- The corresponding first response-commutator shape. The boundary term M f
is retained; it is not removed when reconstructing the curvature. -/
def physicalTangent (eta : ℝ) (f : PhysicalSpace) : PhysicalSpace :=
  (-(eta : ℂ)⁻¹/2) • physicalRadialAdvance f -
    (eta : ℂ) • physicalRadialAdvance (physicalCurvature f)

def baseGradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) : PhysicalSpace :=
  physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance f)

def transportedGradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) : PhysicalSpace :=
  physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalComplement f))

theorem advance_complement (f : PhysicalSpace) :
    physicalRadialAdvance (physicalComplement f)=physicalComplement (physicalRadialAdvance f) := by
  change physicalRadialAdvance (f-physicalRadialAdvance f)=_
  exact map_sub physicalRadialAdvance f (physicalRadialAdvance f)

theorem resolvent_advance (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance f)=
      physicalRadialAdvance (physicalGreenResolvent eta h0.le h1 f) :=
  congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace => T f)
    (physical_resolvent_commutes_advance eta h0.le h1).eq

theorem resolvent_complement (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalComplement f)=
      physicalComplement (physicalGreenResolvent eta h0.le h1 f) := by
  change physicalGreenResolvent eta h0.le h1 (f-physicalRadialAdvance f)=_
  rw [map_sub,resolvent_advance eta h0 h1]
  rfl

theorem gradient_as_complement (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    transportedGradient eta h0 h1 f=physicalComplement (baseGradient eta h0 h1 f) := by
  unfold transportedGradient baseGradient
  rw [advance_complement,resolvent_complement eta h0 h1]

theorem curvature_resolvent_advance (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCurvature f))=
      (-(1/2) : ℂ) • physicalComplement (transportedGradient eta h0 h1 f) := by
  unfold physicalCurvature
  rw [map_smul,map_smul,advance_complement,resolvent_complement eta h0 h1]
  rfl

theorem tangent_resolvent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalTangent eta f)=
      (-(eta : ℂ)⁻¹/2) • baseGradient eta h0 h1 f +
      ((eta : ℂ)/2) • physicalComplement (transportedGradient eta h0 h1 f) := by
  unfold physicalTangent
  rw [map_sub,map_smul,map_smul,curvature_resolvent_advance eta h0 h1,smul_smul]
  change _ • baseGradient eta h0 h1 f - _ • _ = _
  module

/-- Transfer through the actual Green and its self-adjoint resolvent. -/
theorem green_inner_transport (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ f (physicalGreenOperator eta h0.le h1 g)=
      (eta : ℂ)*inner ℂ
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance f))
        (physicalGreenResolvent eta h0.le h1 g) := by
  let R := physicalGreenResolvent eta h0.le h1
  have hM := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physicalRadialAdvance_isSelfAdjoint
  have hR := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (physical_resolvent_selfAdjoint eta h0.le h1)
  have hm := hM f ((R^2) g)
  change inner ℂ (physicalRadialAdvance f) ((R^2) g)=
    inner ℂ f (physicalRadialAdvance ((R^2) g)) at hm
  have hr := hR (physicalRadialAdvance f) (R g)
  change inner ℂ (R (physicalRadialAdvance f)) (R g)=
    inner ℂ (physicalRadialAdvance f) (R (R g)) at hr
  unfold physicalGreenOperator
  rw [smul_apply,mul_apply_eq_comp,inner_smul_right]
  congr 1
  calc
    _ = inner ℂ (physicalRadialAdvance f) ((R^2) g) := hm.symm
    _ = _ := hr.symm

theorem gradient_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (transportedGradient eta h0 h1 f)) (baseGradient eta h0 h1 g)=
      inner ℂ (transportedGradient eta h0 h1 f) (transportedGradient eta h0 h1 g) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physical_complement_selfAdjoint
  have hh := hs (transportedGradient eta h0 h1 f) (baseGradient eta h0 h1 g)
  change inner ℂ (physicalComplement (transportedGradient eta h0 h1 f)) (baseGradient eta h0 h1 g)=
    inner ℂ (transportedGradient eta h0 h1 f) (physicalComplement (baseGradient eta h0 h1 g)) at hh
  rw [← gradient_as_complement eta h0 h1 g] at hh
  exact hh

/-- Two INDEPENDENT physical inputs, before any real or diagonal readout. -/
theorem curvature_green_polarized_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (physicalTangent eta g))=
      (1/4 : ℂ)*(inner ℂ (transportedGradient eta h0 h1 f) (transportedGradient eta h0 h1 g)-
        (eta : ℂ)^2*inner ℂ (physicalComplement (transportedGradient eta h0 h1 f))
          (physicalComplement (transportedGradient eta h0 h1 g))) := by
  rw [green_inner_transport eta h0 h1,curvature_resolvent_advance eta h0 h1,tangent_resolvent eta h0 h1]
  simp only [inner_smul_left,inner_add_right,inner_smul_right]
  rw [gradient_pairing eta h0 h1]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  norm_num only [map_neg,map_div₀,map_one,map_ofNat]
  field_simp [he]
  ring

theorem curvature_green_diagonal_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (physicalTangent eta f))).re=
      (1/4 : ℝ)*(‖transportedGradient eta h0 h1 f‖^2-
        eta^2*‖physicalComplement (transportedGradient eta h0 h1 f)‖^2) := by
  rw [curvature_green_polarized_factor eta h0 h1 f f,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two,Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two,Complex.mul_im]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re,Complex.sub_re,hRe,hIm]

theorem curvature_green_lower_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (1-eta^2)/4*‖transportedGradient eta h0 h1 f‖^2 ≤
      (inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (physicalTangent eta f))).re := by
  have hn := physical_complement_contracts (transportedGradient eta h0 h1 f)
  have hs : ‖physicalComplement (transportedGradient eta h0 h1 f)‖^2 ≤
      ‖transportedGradient eta h0 h1 f‖^2 := by nlinarith [norm_nonneg (physicalComplement (transportedGradient eta h0 h1 f)),norm_nonneg (transportedGradient eta h0 h1 f)]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg eta)
  rw [curvature_green_diagonal_factor eta h0 h1]
  linarith

theorem curvature_green_nonnegative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    0 ≤ (inner ℂ (physicalCurvature f) (physicalGreenOperator eta h0.le h1 (physicalTangent eta f))).re := by
  apply (le_trans _ (curvature_green_lower_bound eta h0 h1 f))
  exact mul_nonneg (by nlinarith : 0≤(1-eta^2)/4) (sq_nonneg _)

end
end CarryCurvatureGreen
