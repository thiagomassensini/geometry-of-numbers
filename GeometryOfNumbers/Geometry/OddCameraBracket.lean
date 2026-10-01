import GeometryOfNumbers.Geometry.OddCamera
import GeometryOfNumbers.Geometry.CenteredSecondDifference

/-!
# Discrete camera bracket, defined independently of saturation

Integer-valued observables retain the existing discrete carrier. The camera
first sums its geometric legs and subtracts the counted copies of the center.
Its equality with a sum of existing second differences is a finite theorem,
not a definition or an imported historical pairing result.
-/

namespace GeometryOfNumbers.Geometry

theorem sumPositiveRadii_int_add (half : Nat) (f g : Nat → Int) :
    sumPositiveRadii half (fun r => f r + g r) =
      sumPositiveRadii half f + sumPositiveRadii half g := by
  induction half with
  | zero => rfl
  | succ half ih =>
    rw [sumPositiveRadii_succ, sumPositiveRadii_succ, sumPositiveRadii_succ, ih]
    omega

theorem sumPositiveRadii_int_sub (half : Nat) (f g : Nat → Int) :
    sumPositiveRadii half (fun r => f r - g r) =
      sumPositiveRadii half f - sumPositiveRadii half g := by
  induction half with
  | zero => rfl
  | succ half ih =>
    rw [sumPositiveRadii_succ, sumPositiveRadii_succ, sumPositiveRadii_succ, ih]
    omega

theorem sumPositiveRadii_int_constant (half : Nat) (value : Int) :
    sumPositiveRadii half (fun _ => value) = (half : Int) * value := by
  induction half with
  | zero => simp only [sumPositiveRadii_zero, Int.natCast_zero, Int.zero_mul]
  | succ half ih =>
    rw [sumPositiveRadii_succ, ih, Int.natCast_succ, Int.add_mul, Int.one_mul]

def oddCameraLegSum (half : Nat) (f : Int → Int) (center : Int) : Int :=
  sumPositiveRadii half (fun r => f (leftLeg center r) + f (rightLeg center r))

def oddCameraBracket (half : Nat) (f : Int → Int) (center : Int) : Int :=
  oddCameraLegSum half f center - (2 * (half : Int)) * f center

def oddCameraSaturatedSecondDifference (half : Nat) (f : Int → Int) (center : Int) : Int :=
  sumPositiveRadii half (fun r => centeredSecondDifference f center r)

theorem oddCameraBracket_eq_saturatedSecondDifference
    (half : Nat) (f : Int → Int) (center : Int) :
    oddCameraBracket half f center = oddCameraSaturatedSecondDifference half f center := by
  have hlocal : ∀ r : Nat,
      (f (leftLeg center r) + f (rightLeg center r)) - 2 * f center =
        centeredSecondDifference f center r := by
    intro r
    unfold centeredSecondDifference secondDifferenceAt
    omega
  unfold oddCameraBracket oddCameraLegSum oddCameraSaturatedSecondDifference
  rw [← Int.mul_comm (half : Int) 2, Int.mul_assoc,
    ← sumPositiveRadii_int_constant half (2 * f center), ← sumPositiveRadii_int_sub]
  exact sumPositiveRadii_congr half _ _ (fun r _ _ => hlocal r)

theorem oddCameraBracket_zero (f : Int → Int) (center : Int) :
    oddCameraBracket 0 f center = 0 := by
  unfold oddCameraBracket oddCameraLegSum
  simp only [sumPositiveRadii_zero, Int.natCast_zero, Int.mul_zero, Int.zero_mul, Int.sub_self]

theorem oddCameraBracket_C3 (f : Int → Int) (center : Int) :
    oddCameraBracket 1 f center = f (center - 1) - 2 * f center + f (center + 1) := by
  rw [oddCameraBracket_eq_saturatedSecondDifference]
  change 0 + (f (center - 1) - 2 * f center + f (center + 1)) = _
  omega

theorem oddCameraBracket_two_pairs (f : Int → Int) (center : Int) :
    oddCameraBracket 2 f center = centeredSecondDifference f center 1 +
      centeredSecondDifference f center 2 := by
  rw [oddCameraBracket_eq_saturatedSecondDifference]
  change (0 + centeredSecondDifference f center 1) +
    centeredSecondDifference f center 2 = _
  omega

theorem oddCameraBracket_identity (half : Nat) (center : Int) :
    oddCameraBracket half (fun x => x) center = 0 := by
  rw [oddCameraBracket_eq_saturatedSecondDifference]
  unfold oddCameraSaturatedSecondDifference
  have hsum := sumPositiveRadii_congr half
    (fun r => centeredSecondDifference (fun x => x) center r) (fun _ => (0 : Int))
    (fun _ _ _ => centeredSecondDifference_identity _ _)
  rw [hsum, sumPositiveRadii_int_constant, Int.mul_zero]

end GeometryOfNumbers.Geometry
