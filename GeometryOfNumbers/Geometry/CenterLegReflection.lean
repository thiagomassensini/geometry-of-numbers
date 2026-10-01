import Init

/-! Discrete integer geometry, separate from the frozen scale-selection foundation.
The center and signed radius are input data; no midpoint division is used.
Standard Init integer arithmetic is audited separately, not claimed axiom-free. -/

namespace GeometryOfNumbers.Geometry

/-- The two legs are constructed from the same center and signed radius. -/
def leftLeg (center radius : Int) : Int := center - radius

def rightLeg (center radius : Int) : Int := center + radius

/-- Reflection uses doubling, not a division-based definition of midpoint. -/
def reflect (center point : Int) : Int := 2 * center - point

/-- A candidate center exchanges the specified, fixed legs by reflection. -/
def IsCenterOf (left right candidate : Int) : Prop :=
  reflect candidate left = right

/-- This tests a candidate against fixed legs, not an absolute property of it. -/
def centerDefect (left candidate right : Int) : Int :=
  left - 2 * candidate + right

theorem leftLeg_add_rightLeg (center radius : Int) :
    leftLeg center radius + rightLeg center radius = 2 * center := by
  unfold leftLeg rightLeg
  omega

theorem reflect_center (center : Int) : reflect center center = center := by
  unfold reflect
  omega

theorem reflect_leftLeg (center radius : Int) :
    reflect center (leftLeg center radius) = rightLeg center radius := by
  unfold reflect leftLeg rightLeg
  omega

theorem reflect_rightLeg (center radius : Int) :
    reflect center (rightLeg center radius) = leftLeg center radius := by
  unfold reflect leftLeg rightLeg
  omega

theorem reflect_involutive (center point : Int) :
    reflect center (reflect center point) = point := by
  unfold reflect
  omega

theorem leftLeg_neg_radius (center radius : Int) :
    leftLeg center (-radius) = rightLeg center radius := by
  unfold leftLeg rightLeg
  omega

theorem rightLeg_neg_radius (center radius : Int) :
    rightLeg center (-radius) = leftLeg center radius := by
  unfold leftLeg rightLeg
  omega

theorem isCenterOf_iff_sum (left right candidate : Int) :
    IsCenterOf left right candidate ↔ left + right = 2 * candidate := by
  unfold IsCenterOf reflect
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Existence here concerns constructed legs, not arbitrary integer endpoints. -/
theorem constructed_legs_have_center (center radius : Int) :
    IsCenterOf (leftLeg center radius) (rightLeg center radius) center :=
  reflect_leftLeg center radius

theorem constructed_center_unique (center radius candidate : Int)
    (h : IsCenterOf (leftLeg center radius) (rightLeg center radius) candidate) :
    candidate = center := by
  have hsum := (isCenterOf_iff_sum _ _ _).1 h
  rw [leftLeg_add_rightLeg] at hsum
  omega

theorem centerDefect_eq_zero_iff_isCenterOf (left candidate right : Int) :
    centerDefect left candidate right = 0 ↔ IsCenterOf left right candidate := by
  unfold centerDefect IsCenterOf reflect
  constructor
  · intro h
    omega
  · intro h
    omega

theorem centerDefect_constructed (center radius : Int) :
    centerDefect (leftLeg center radius) center (rightLeg center radius) = 0 :=
  (centerDefect_eq_zero_iff_isCenterOf _ _ _).2
    (constructed_legs_have_center center radius)

/-- The original legs stay fixed while only the tested center moves. -/
theorem centerDefect_fixed_legs_shift (center radius displacement : Int) :
    centerDefect (leftLeg center radius) (center + displacement)
      (rightLeg center radius) = -2 * displacement := by
  unfold centerDefect leftLeg rightLeg
  omega

theorem centerDefect_fixed_legs_shift_neg (center radius displacement : Int) :
    centerDefect (leftLeg center radius) (center - displacement)
      (rightLeg center radius) = 2 * displacement := by
  unfold centerDefect leftLeg rightLeg
  omega

/-- Rebuilding both legs at the moved center removes the geometric mismatch. -/
theorem centerDefect_recentered (center radius displacement : Int) :
    centerDefect (leftLeg (center + displacement) radius) (center + displacement)
      (rightLeg (center + displacement) radius) = 0 :=
  centerDefect_constructed (center + displacement) radius

end GeometryOfNumbers.Geometry
