import QuadraticSign
import QuarticCoefficient
import BoundaryOperator

namespace CarryCubicQuartic
open CarrySelfAdjointOperator NativeLaguerre CarryCurvatureGreen
open CarryCubicTfvd CarryQuarticBoundary CarryStencilBoundary
open scoped InnerProductSpace unitInterval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Polynomial forced by the ORIGINAL cubic forward weight on d4. -/
def quarticForward : PhysicalSpace →L[ℂ] PhysicalSpace :=
  (27 : ℂ) • 1+(26 : ℂ) • physicalComplement+(61 : ℂ) • physicalComplement^2

/-- Polynomial forced by the ORIGINAL cubic backward weight on d4. -/
def quarticBackward : PhysicalSpace →L[ℂ] PhysicalSpace :=
  physicalComplement^2*((36 : ℂ) • 1-(120 : ℂ) • physicalComplement+
    (91 : ℂ) • physicalComplement^2)

theorem quartic_forward_in_advance : quarticForward=
    (114 : ℂ) • 1-(148 : ℂ) • physicalRadialAdvance+(61 : ℂ) • physicalRadialAdvance^2 := by
  simp only [quarticForward, physicalComplement, pow_two, mul_sub, sub_mul,
    mul_one, one_mul]
  module

theorem quartic_backward_in_advance : quarticBackward=
    (7 : ℂ) • 1-(76 : ℂ) • physicalRadialAdvance+(222 : ℂ) • physicalRadialAdvance^2-
      (244 : ℂ) • physicalRadialAdvance^3+(91 : ℂ) • physicalRadialAdvance^4 := by
  simp only [quarticBackward, physicalComplement, pow_succ, pow_zero, mul_add,
    mul_sub, sub_mul, mul_smul_comm, mul_one, one_mul, mul_assoc]
  module

theorem forward_advance (f : PhysicalSpace) :
    quarticForward (physicalRadialAdvance f)=physicalRadialAdvance (quarticForward f) := by
  rw [quartic_forward_in_advance]
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_two,
    mul_apply_eq_comp, map_add, map_sub, map_smul]

theorem backward_advance (f : PhysicalSpace) :
    quarticBackward (physicalRadialAdvance f)=physicalRadialAdvance (quarticBackward f) := by
  rw [quartic_backward_in_advance]
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_succ, pow_zero,
    mul_apply_eq_comp, map_add, map_sub, map_smul]

theorem forward_complement (f : PhysicalSpace) :
    quarticForward (physicalComplement f)=physicalComplement (quarticForward f) := by
  change quarticForward (f-physicalRadialAdvance f)=_
  rw [map_sub, forward_advance]
  rfl

theorem backward_complement (f : PhysicalSpace) :
    quarticBackward (physicalComplement f)=physicalComplement (quarticBackward f) := by
  change quarticBackward (f-physicalRadialAdvance f)=_
  rw [map_sub, backward_advance]
  rfl

theorem resolvent_forward (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (quarticForward f)=
      quarticForward (physicalGreenResolvent eta h0.le h1 f) := by
  rw [quartic_forward_in_advance]
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_two,
    mul_apply_eq_comp, map_add, map_sub, map_smul, resolvent_advance eta h0 h1]

theorem resolvent_backward (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (quarticBackward f)=
      quarticBackward (physicalGreenResolvent eta h0.le h1 f) := by
  rw [quartic_backward_in_advance]
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self, pow_succ, pow_zero,
    mul_apply_eq_comp, map_add, map_sub, map_smul, resolvent_advance eta h0 h1]

theorem forward_as_multiplier : quarticForward=intervalMultiplier
    ((27 : ℂ) • 1+(26 : ℂ) • (1-physicalRadialCoefficient)+
      (61 : ℂ) • (1-physicalRadialCoefficient)^2) := by
  simp only [quarticForward, multiplier_add, intervalMultiplier_smul,
    intervalMultiplier_one, multiplier_pow, complement_multiplier]

theorem backward_as_multiplier : quarticBackward=intervalMultiplier
    ((1-physicalRadialCoefficient)^2*((36 : ℂ) • 1-(120 : ℂ) • (1-physicalRadialCoefficient)+
      (91 : ℂ) • (1-physicalRadialCoefficient)^2)) := by
  simp only [quarticBackward, intervalMultiplier_mul, multiplier_add, intervalMultiplier_sub,
    intervalMultiplier_smul, intervalMultiplier_one, multiplier_pow, physicalComplement, physicalRadialAdvance]

end
end CarryCubicQuartic
