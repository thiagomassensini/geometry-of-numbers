import GeometryOfNumbers.Geometry.BalancedCarryOffset
import GeometryOfNumbers.Geometry.CenteredSecondDifference

/-! The one-cell crosswalk uses the same stepping/reset quantity as a leg of
the existing geometry. It does not identify depths, historical observables or
the antipodal even branch. No new defect/reflection operation is defined. -/

namespace GeometryOfNumbers.Geometry

open Foundation

set_option autoImplicit false
universe u v

theorem balancedCarry_spec (b n : Nat) (hodd : IsOddCapacity b) :
    (n : Int) = balancedCarryCenter b n hodd + balancedCarryOffset b n hodd ∧
    (b : Int) ∣ balancedCarryCenter b n hodd ∧
    2 * (balancedCarryOffset b n hodd).natAbs < b :=
  ⟨balancedCarry_reconstruction b n hodd, balancedCarry_center_aligned b n hodd,
    balancedCarry_offset_natAbs_bound b n hodd⟩

theorem balancedCarry_rightLeg (b n : Nat) (hodd : IsOddCapacity b) :
    rightLeg (balancedCarryCenter b n hodd) (balancedCarryOffset b n hodd) =
      (n : Int) :=
  (balancedCarry_reconstruction b n hodd).symm

theorem balancedCarry_reflect_eq_leftLeg (b n : Nat) (hodd : IsOddCapacity b) :
    reflect (balancedCarryCenter b n hodd) (n : Int) =
      leftLeg (balancedCarryCenter b n hodd) (balancedCarryOffset b n hodd) := by
  rw [← balancedCarry_rightLeg b n hodd]
  exact reflect_rightLeg _ _

theorem balancedCarry_reflect_eq_center_sub_offset
    (b n : Nat) (hodd : IsOddCapacity b) :
    reflect (balancedCarryCenter b n hodd) (n : Int) =
      balancedCarryCenter b n hodd - balancedCarryOffset b n hodd :=
  balancedCarry_reflect_eq_leftLeg b n hodd

theorem balancedCarry_centerDefect_zero (b n : Nat) (hodd : IsOddCapacity b) :
    centerDefect
      (reflect (balancedCarryCenter b n hodd) (n : Int))
      (balancedCarryCenter b n hodd) (n : Int) = 0 := by
  rw [balancedCarry_reflect_eq_leftLeg, ← balancedCarry_rightLeg b n hodd]
  exact centerDefect_constructed _ _

theorem balancedCarry_centerDefect_shift
    (b n : Nat) (hodd : IsOddCapacity b) (displacement : Int) :
    centerDefect
      (reflect (balancedCarryCenter b n hodd) (n : Int))
      (balancedCarryCenter b n hodd + displacement) (n : Int) =
      -2 * displacement := by
  rw [balancedCarry_reflect_eq_leftLeg, ← balancedCarry_rightLeg b n hodd]
  exact centerDefect_fixed_legs_shift _ _ displacement

theorem balancedCarry_secondDifference_identity_shift
    (b n : Nat) (hodd : IsOddCapacity b) (displacement : Int) :
    secondDifferenceAt (fun x => x)
      (reflect (balancedCarryCenter b n hodd) (n : Int))
      (balancedCarryCenter b n hodd + displacement) (n : Int) =
      -2 * displacement := by
  rw [secondDifferenceAt_identity]
  exact balancedCarry_centerDefect_shift b n hodd displacement

theorem balancedCarry_zero_residual_reflect (b n : Nat) (hodd : IsOddCapacity b)
    (hzero : cycleResidual b n = 0) :
    reflect (balancedCarryCenter b n hodd) (n : Int) = (n : Int) := by
  rw [(balancedCarry_zero_residual b n hodd hzero).2]
  exact reflect_center _

/-- The same actual first-return capacity supplies the original cycle data and
the balanced geometry. Oddness is a separate regime hypothesis, not derived
from local finitude, first-return minimality or primality. -/
theorem emergentCapacity_balancedCarry_spec
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b : Nat} (hcap : EmergentLocalCapacity trajectory model b)
    (hodd : IsOddCapacity b) (n : Nat) :
    IsCycleDecomposition b n (completedCycleCount b n) (cycleResidual b n) ∧
    (n : Int) = balancedCarryCenter b n hodd + balancedCarryOffset b n hodd ∧
    (b : Int) ∣ balancedCarryCenter b n hodd ∧
    2 * (balancedCarryOffset b n hodd).natAbs < b :=
  ⟨cycleCoordinatesRec_spec b hcap.1.1 n, balancedCarry_spec b n hodd⟩

end GeometryOfNumbers.Geometry
