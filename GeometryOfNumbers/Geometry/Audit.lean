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

end GeometryOfNumbers.Geometry
