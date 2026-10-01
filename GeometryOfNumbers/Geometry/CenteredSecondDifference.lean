import GeometryOfNumbers.Geometry.CenterLegReflection

/-! Observables are evaluated only after choosing the geometry. Integer-valued
observables suffice for this layer; no analytical or abstract normed carrier is
introduced. Fixed-node and recentered configurations are distinct operations. -/

namespace GeometryOfNumbers.Geometry

/-- The observable response on three specified nodes, possibly miscentered. -/
def secondDifferenceAt (f : Int → Int) (left center right : Int) : Int :=
  f left - 2 * f center + f right

/-- A specialization to the legs already constructed from a center and radius. -/
def centeredSecondDifference (f : Int → Int) (center radius : Int) : Int :=
  secondDifferenceAt f (leftLeg center radius) center (rightLeg center radius)

theorem secondDifferenceAt_identity (left center right : Int) :
    secondDifferenceAt (fun x => x) left center right =
      centerDefect left center right := rfl

theorem centeredSecondDifference_identity (center radius : Int) :
    centeredSecondDifference (fun x => x) center radius = 0 :=
  centerDefect_constructed center radius

theorem secondDifferenceAt_identity_fixed_legs_shift
    (center radius displacement : Int) :
    secondDifferenceAt (fun x => x) (leftLeg center radius) (center + displacement)
      (rightLeg center radius) = -2 * displacement :=
  centerDefect_fixed_legs_shift center radius displacement

theorem centeredSecondDifference_neg_radius (f : Int → Int) (center radius : Int) :
    centeredSecondDifference f center (-radius) =
      centeredSecondDifference f center radius := by
  unfold centeredSecondDifference
  rw [leftLeg_neg_radius, rightLeg_neg_radius]
  unfold secondDifferenceAt
  omega

theorem centeredSecondDifference_zero_radius (f : Int → Int) (center : Int) :
    centeredSecondDifference f center 0 = 0 := by
  have hl : leftLeg center 0 = center := by unfold leftLeg; omega
  have hr : rightLeg center 0 = center := by unfold rightLeg; omega
  unfold centeredSecondDifference
  rw [hl, hr]
  unfold secondDifferenceAt
  omega

/-- Symmetry does not annihilate the response of a nonlinear observable. -/
theorem centeredSecondDifference_square (center radius : Int) :
    centeredSecondDifference (fun x => x * x) center radius = 2 * (radius * radius) := by
  unfold centeredSecondDifference secondDifferenceAt leftLeg rightLeg
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul]
  rw [Int.mul_comm radius center]
  omega

end GeometryOfNumbers.Geometry
