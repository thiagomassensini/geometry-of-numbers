import FourthBoundaryDefect

namespace CarryQuarticBoundary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCurvatureGreen NativeLaguerre
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def quarticVector (f : PhysicalSpace) : PhysicalSpace := (1/24 : ℂ) •
  physicalComplement (physicalComplement (physicalComplement (physicalComplement f)))

def boundaryVector (f : PhysicalSpace) : PhysicalSpace := (1/24 : ℂ) •
  physicalRadialAdvance ((5 : ℂ) • f-(2 : ℂ) • physicalRadialAdvance f)

def quarticGradient (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) : PhysicalSpace :=
  physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalComplement (physicalComplement f)))

theorem resolvent_advance_complement (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalComplement f))=
      physicalComplement (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance f)) :=
  gradient_as_complement eta h0 h1 f

theorem quartic_gradient_as_complement (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    quarticGradient eta h0 h1 f=physicalComplement (physicalComplement (baseGradient eta h0 h1 f)) := by
  unfold quarticGradient
  rw [resolvent_advance_complement eta h0 h1,resolvent_advance_complement eta h0 h1]
  rfl

theorem quartic_resolvent_advance (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (quarticVector f))=
      (1/24 : ℂ) • physicalComplement (physicalComplement (quarticGradient eta h0 h1 f)) := by
  unfold quarticVector
  rw [map_smul,map_smul,resolvent_advance_complement eta h0 h1,
    resolvent_advance_complement eta h0 h1]
  rfl

theorem boundary_resolvent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (boundaryVector f)=
      (1/24 : ℂ) • ((5 : ℂ) • baseGradient eta h0 h1 f-
        (2 : ℂ) • physicalRadialAdvance (baseGradient eta h0 h1 f)) := by
  unfold boundaryVector
  rw [map_smul,map_sub,map_smul,map_smul,map_sub,map_smul,map_smul,
    resolvent_advance eta h0 h1 (physicalRadialAdvance f)]
  rfl

theorem complement_twice_pairing (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement f)) g=
      inner ℂ f (physicalComplement (physicalComplement g)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physical_complement_selfAdjoint
  have hh := hs (physicalComplement f) g
  have hi := hs f (physicalComplement g)
  exact hh.trans hi

theorem quartic_base_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement (quarticGradient eta h0 h1 f))) (baseGradient eta h0 h1 g)=
      inner ℂ (quarticGradient eta h0 h1 f) (quarticGradient eta h0 h1 g) := by
  rw [complement_twice_pairing,← quartic_gradient_as_complement eta h0 h1 g]

theorem quartic_advance_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ (physicalComplement (physicalComplement (quarticGradient eta h0 h1 f)))
        (physicalRadialAdvance (baseGradient eta h0 h1 g))=
      inner ℂ (quarticGradient eta h0 h1 f) (physicalRadialAdvance (quarticGradient eta h0 h1 g)) := by
  rw [complement_twice_pairing,← advance_complement,← advance_complement,
    ← quartic_gradient_as_complement eta h0 h1 g]

/-- The SAME boundary is factored in two independent arguments, before Re. -/
theorem quartic_boundary_polarized_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f g : PhysicalSpace) :
    inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (boundaryVector g))=
      (eta : ℂ)*(1/576 : ℂ)*
        (5*inner ℂ (quarticGradient eta h0 h1 f) (quarticGradient eta h0 h1 g)-
          2*inner ℂ (quarticGradient eta h0 h1 f) (physicalRadialAdvance (quarticGradient eta h0 h1 g))) := by
  rw [green_inner_transport eta h0 h1,quartic_resolvent_advance eta h0 h1,
    boundary_resolvent eta h0 h1]
  simp only [inner_smul_left,inner_smul_right,inner_sub_right]
  rw [quartic_base_pairing eta h0 h1,quartic_advance_pairing eta h0 h1]
  norm_num only [map_div₀,map_one,map_ofNat]
  ring

theorem quartic_boundary_diagonal_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    (inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (boundaryVector f))).re=
      eta/576*(5*‖quarticGradient eta h0 h1 f‖^2-
        2*(inner ℂ (quarticGradient eta h0 h1 f) (physicalRadialAdvance (quarticGradient eta h0 h1 f))).re) := by
  rw [quartic_boundary_polarized_factor eta h0 h1 f f,inner_self_eq_norm_sq_to_K]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two,Complex.mul_re]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re,Complex.sub_re,hRe]
  simp [div_eq_mul_inv]

theorem advance_inner_upper (f : PhysicalSpace) :
    (inner ℂ f (physicalRadialAdvance f)).re ≤ ‖f‖^2 := by
  have hn : ‖physicalRadialAdvance f‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖physicalRadialAdvance‖*‖f‖ := physicalRadialAdvance.le_opNorm f
      _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right physicalRadialAdvance_norm_le_one (norm_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ ‖inner ℂ f (physicalRadialAdvance f)‖ := Complex.re_le_norm _
    _ ≤ ‖f‖*‖physicalRadialAdvance f‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖f‖*‖f‖ := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by ring

theorem quartic_boundary_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    eta/192*‖quarticGradient eta h0 h1 f‖^2 ≤
      (inner ℂ (quarticVector f) (physicalGreenOperator eta h0.le h1 (boundaryVector f))).re := by
  have hh := mul_le_mul_of_nonneg_left (advance_inner_upper (quarticGradient eta h0 h1 f)) h0.le
  rw [quartic_boundary_diagonal_factor eta h0 h1]
  nlinarith

end
end CarryQuarticBoundary
