import GeometryOfNumbers.Geometry
import Lean

/-! Separate audit: integer arithmetic here permits propext and Quot.sound,
but not choice or any other axiom. Foundation still permits none. -/

open Lean Elab Command

elab "#assert_geometry_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  for axiomName in axioms do
    unless axiomName == ``propext || axiomName == ``Quot.sound do
      throwError "Discrete geometry violation: {decl} depends on {axiomName}"

elab "#assert_geometry_definition_no_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  unless axioms.isEmpty do
    throwError "Geometry definition violation: {decl} depends on {axioms}"

namespace GeometryOfNumbers.Geometry

open Foundation

#assert_geometry_definition_no_axioms IsOddCapacity
#assert_geometry_definition_no_axioms IsBalancedOffset
#assert_geometry_definition_no_axioms balancedCarryOffset
#assert_geometry_definition_no_axioms balancedCarryCenter

#assert_geometry_axioms oddCapacity_pos
#assert_geometry_axioms oddCapacity_no_antipodal
#assert_geometry_axioms oddCapacity_residual_side
#assert_geometry_axioms balancedCarry_reconstruction
#assert_geometry_axioms balancedCarry_center_aligned
#assert_geometry_axioms balancedCarry_offset_balanced
#assert_geometry_axioms balancedOffset_iff_natAbs
#assert_geometry_axioms balancedCarry_offset_natAbs_bound
#assert_geometry_axioms balancedCenterOffset_unique
#assert_geometry_axioms balancedCarry_unique
#assert_geometry_axioms balancedCarry_zero_residual
#assert_geometry_axioms balancedCarry_nonzero_residual
#assert_geometry_axioms antipodal_two_no_strict_decomposition
#assert_geometry_axioms antipodal_two_boundary_nonunique
#assert_geometry_axioms balancedCarry_spec
#assert_geometry_axioms balancedCarry_rightLeg
#assert_geometry_axioms balancedCarry_reflect_eq_leftLeg
#assert_geometry_axioms balancedCarry_reflect_eq_center_sub_offset
#assert_geometry_axioms balancedCarry_centerDefect_zero
#assert_geometry_axioms balancedCarry_centerDefect_shift
#assert_geometry_axioms balancedCarry_secondDifference_identity_shift
#assert_geometry_axioms balancedCarry_zero_residual_reflect
#assert_geometry_axioms emergentCapacity_balancedCarry_spec

#print axioms oddCapacity_pos
#print axioms oddCapacity_no_antipodal
#print axioms oddCapacity_residual_side
#print axioms balancedCarry_reconstruction
#print axioms balancedCarry_center_aligned
#print axioms balancedCarry_offset_balanced
#print axioms balancedOffset_iff_natAbs
#print axioms balancedCarry_offset_natAbs_bound
#print axioms balancedCenterOffset_unique
#print axioms balancedCarry_unique
#print axioms balancedCarry_zero_residual
#print axioms balancedCarry_nonzero_residual
#print axioms antipodal_two_no_strict_decomposition
#print axioms antipodal_two_boundary_nonunique
#print axioms balancedCarry_spec
#print axioms balancedCarry_rightLeg
#print axioms balancedCarry_reflect_eq_leftLeg
#print axioms balancedCarry_reflect_eq_center_sub_offset
#print axioms balancedCarry_centerDefect_zero
#print axioms balancedCarry_centerDefect_shift
#print axioms balancedCarry_secondDifference_identity_shift
#print axioms balancedCarry_zero_residual_reflect
#print axioms emergentCapacity_balancedCarry_spec

#assert_geometry_definition_no_axioms leftLeg
#assert_geometry_definition_no_axioms rightLeg
#assert_geometry_definition_no_axioms reflect
#assert_geometry_definition_no_axioms IsCenterOf
#assert_geometry_definition_no_axioms centerDefect
#assert_geometry_definition_no_axioms secondDifferenceAt
#assert_geometry_definition_no_axioms centeredSecondDifference

#assert_geometry_axioms leftLeg_add_rightLeg
#assert_geometry_axioms reflect_center
#assert_geometry_axioms reflect_leftLeg
#assert_geometry_axioms reflect_rightLeg
#assert_geometry_axioms reflect_involutive
#assert_geometry_axioms leftLeg_neg_radius
#assert_geometry_axioms rightLeg_neg_radius
#assert_geometry_axioms isCenterOf_iff_sum
#assert_geometry_axioms constructed_legs_have_center
#assert_geometry_axioms constructed_center_unique
#assert_geometry_axioms centerDefect_eq_zero_iff_isCenterOf
#assert_geometry_axioms centerDefect_constructed
#assert_geometry_axioms centerDefect_fixed_legs_shift
#assert_geometry_axioms centerDefect_fixed_legs_shift_neg
#assert_geometry_axioms centerDefect_recentered
#assert_geometry_axioms secondDifferenceAt_identity
#assert_geometry_axioms centeredSecondDifference_identity
#assert_geometry_axioms secondDifferenceAt_identity_fixed_legs_shift
#assert_geometry_axioms centeredSecondDifference_neg_radius
#assert_geometry_axioms centeredSecondDifference_zero_radius
#assert_geometry_axioms centeredSecondDifference_square

#print axioms leftLeg_add_rightLeg
#print axioms reflect_center
#print axioms reflect_leftLeg
#print axioms reflect_rightLeg
#print axioms reflect_involutive
#print axioms leftLeg_neg_radius
#print axioms rightLeg_neg_radius
#print axioms isCenterOf_iff_sum
#print axioms constructed_legs_have_center
#print axioms constructed_center_unique
#print axioms centerDefect_eq_zero_iff_isCenterOf
#print axioms centerDefect_constructed
#print axioms centerDefect_fixed_legs_shift
#print axioms centerDefect_fixed_legs_shift_neg
#print axioms centerDefect_recentered
#print axioms secondDifferenceAt_identity
#print axioms centeredSecondDifference_identity
#print axioms secondDifferenceAt_identity_fixed_legs_shift
#print axioms centeredSecondDifference_neg_radius
#print axioms centeredSecondDifference_zero_radius
#print axioms centeredSecondDifference_square

-- Closed computations check orientation without any external numerical probe.
example : leftLeg 10 3 = 7 := rfl
example : rightLeg 10 3 = 13 := rfl
example : centerDefect 7 11 13 = -2 := rfl
example : centerDefect 8 11 14 = 0 := rfl
example : reflect 10 7 = 13 := rfl
example : reflect 10 13 = 7 := rfl
example : centeredSecondDifference (fun x => x * x) 10 3 = 18 := rfl
example : 2 * ((3 : Int) * 3) = 18 := rfl
example : centerDefect (leftLeg (-10) (-3)) (-9) (rightLeg (-10) (-3)) = -2 := rfl
example : centeredSecondDifference (fun x => x * x) 0 0 = 0 := rfl
-- Arbitrary integer endpoints need not possess an integer center.
example (candidate : Int) : ¬ IsCenterOf 0 1 candidate := by
  unfold IsCenterOf reflect
  omega

-- Existing cycle coordinates, both balancing branches, and the central case.
example : (completedCycleCount 5 6, cycleResidual 5 6) = (1, 1) := rfl
example : (completedCycleCount 5 7, cycleResidual 5 7) = (1, 2) := rfl
example : (completedCycleCount 5 8, cycleResidual 5 8) = (1, 3) := rfl
example : (completedCycleCount 5 9, cycleResidual 5 9) = (1, 4) := rfl
example : (completedCycleCount 5 10, cycleResidual 5 10) = (2, 0) := rfl
example : (balancedCarryCenter 5 6 ⟨2, rfl⟩, balancedCarryOffset 5 6 ⟨2, rfl⟩) =
    (5, 1) := rfl
example : (balancedCarryCenter 5 7 ⟨2, rfl⟩, balancedCarryOffset 5 7 ⟨2, rfl⟩) =
    (5, 2) := rfl
example : (balancedCarryCenter 5 8 ⟨2, rfl⟩, balancedCarryOffset 5 8 ⟨2, rfl⟩) =
    (10, -2) := rfl
example : (balancedCarryCenter 5 9 ⟨2, rfl⟩, balancedCarryOffset 5 9 ⟨2, rfl⟩) =
    (10, -1) := rfl
example : (balancedCarryCenter 5 10 ⟨2, rfl⟩, balancedCarryOffset 5 10 ⟨2, rfl⟩) =
    (10, 0) := rfl
example : reflect (balancedCarryCenter 5 6 ⟨2, rfl⟩) 6 = 4 := rfl
example : reflect (balancedCarryCenter 5 7 ⟨2, rfl⟩) 7 = 3 := rfl
example : reflect (balancedCarryCenter 5 8 ⟨2, rfl⟩) 8 = 12 := rfl
example : reflect (balancedCarryCenter 5 9 ⟨2, rfl⟩) 9 = 11 := rfl
example : reflect (balancedCarryCenter 5 10 ⟨2, rfl⟩) 10 = 10 :=
  balancedCarry_zero_residual_reflect 5 10 ⟨2, rfl⟩ rfl
example : centerDefect
    (reflect (balancedCarryCenter 5 9 ⟨2, rfl⟩) 9)
    (balancedCarryCenter 5 9 ⟨2, rfl⟩) 9 = 0 :=
  balancedCarry_centerDefect_zero 5 9 ⟨2, rfl⟩
example : centerDefect
    (reflect (balancedCarryCenter 5 9 ⟨2, rfl⟩) 9)
    (balancedCarryCenter 5 9 ⟨2, rfl⟩ + 1) 9 = -2 :=
  balancedCarry_centerDefect_shift 5 9 ⟨2, rfl⟩ 1
-- Composite odd capacity works; primality is not an input.
example : (balancedCarryCenter 9 17 ⟨4, rfl⟩, balancedCarryOffset 9 17 ⟨4, rfl⟩) =
    (18, -1) := rfl
example : (balancedCarryCenter 1 3 ⟨0, rfl⟩, balancedCarryOffset 1 3 ⟨0, rfl⟩) =
    (3, 0) := rfl
example : ¬ IsOddCapacity 0 := fun h => Nat.lt_irrefl 0 (oddCapacity_pos h)
example : ¬ IsOddCapacity 2 := fun h => oddCapacity_no_antipodal h 1 rfl
example : (balancedCarryCenter 5 0 ⟨2, rfl⟩, balancedCarryOffset 5 0 ⟨2, rfl⟩) =
    (0, 0) := rfl
example : (1 : Int) = 0 + 1 := rfl
example : (1 : Int) = 2 + (-1) := rfl

end GeometryOfNumbers.Geometry
