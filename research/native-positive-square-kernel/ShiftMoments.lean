import ShiftBoundary

namespace CarryPositiveSquare
open CarrySelfAdjointOperator.NativeLaguerre
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Riesz vector of the old coordinate, not selected from native moments. -/
def boundaryVector : PhysicalCauchySpace := shiftBoundary.adjoint 1
abbrev shiftSquare := (physicalCauchyShift 1).adjoint.comp (physicalCauchyShift 1)

theorem boundary_adjoint_apply (c : ℂ) :
    shiftBoundary.adjoint c = c • boundaryVector := by
  rw [boundaryVector, ← map_smul]
  simp

theorem boundary_readout :
    shiftBoundary boundaryVector = (‖boundaryVector‖^2:ℝ) := by
  have hh := shiftBoundary.adjoint_inner_left boundaryVector (1:ℂ)
  change inner ℂ
    (boundaryVector:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)
    (boundaryVector:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier) =
    inner ℂ (1:ℂ) (shiftBoundary boundaryVector) at hh
  rw [inner_self_eq_norm_sq_to_K] at hh
  simpa [RCLike.inner_apply, ← Complex.ofReal_pow] using hh.symm

theorem shiftSquare_apply (x : PhysicalCauchySpace) :
    shiftSquare x = x-shiftBoundary x • boundaryVector := by
  have hh := congrArg (fun A : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace => A x) physical_shift_square
  simpa [shiftSquare,sub_apply,ContinuousLinearMap.comp_apply,boundary_adjoint_apply] using hh

/-- This candidate positive operator is identity minus rank one, hence has
an algebraic recurrence of order at most two for EVERY source. -/
theorem shiftSquare_twice (x : PhysicalCauchySpace) :
    shiftSquare (shiftSquare x) =
      ((2-‖boundaryVector‖^2:ℝ):ℂ) • shiftSquare x-
      ((1-‖boundaryVector‖^2:ℝ):ℂ) • x := by
  simp only [shiftSquare_apply,map_sub,map_smul,boundary_readout,Complex.ofReal_sub,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  module

def shiftWeightedMoment (v : PhysicalCauchySpace) (n : ℕ) : ℝ :=
  (inner ℂ v ((shiftSquare.toLinearMap^(n+1)) v)).re

theorem shift_moment_recurrence (v : PhysicalCauchySpace) (n : ℕ) :
    shiftWeightedMoment v (n+2) =
      (2-‖boundaryVector‖^2)*shiftWeightedMoment v (n+1)-
      (1-‖boundaryVector‖^2)*shiftWeightedMoment v n := by
  let u := (shiftSquare.toLinearMap^(n+1)) v
  have hp := congrArg (fun y : PhysicalCauchySpace =>
    inner ℂ (v:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)
      (y:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)) (shiftSquare_twice u)
  change inner ℂ (v:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)
    (shiftSquare (shiftSquare u):CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier) =
    inner ℂ (v:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)
      (((2-‖boundaryVector‖^2:ℝ):ℂ) • (shiftSquare u:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)-
      ((1-‖boundaryVector‖^2:ℝ):ℂ) • (u:CarrySelfAdjointOperator.CanonicalCompletedNativeChiralCauchyCarrier)) at hp
  rw [inner_sub_right,inner_smul_right,inner_smul_right] at hp
  have hh := congrArg Complex.re hp
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hh
  simpa [u,shiftWeightedMoment,pow_succ',Module.End.mul_apply,Nat.add_assoc] using hh

end
end CarryPositiveSquare
