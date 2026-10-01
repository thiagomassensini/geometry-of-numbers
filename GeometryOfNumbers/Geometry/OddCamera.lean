import GeometryOfNumbers.Geometry.CenterLegReflection
import GeometryOfNumbers.Geometry.BalancedCarryOffset

/-!
# An odd camera is an explicitly indexed family of reflected pairs

The half-capacity is DATA, not extracted from a propositional witness by
choice. Positive radii are 1,...,half, with two existing geometric legs per
radius. A small polymorphic recursive sum keeps this discrete layer in Init
and will also supply the SAME enumeration to its later real realization.
-/

namespace GeometryOfNumbers.Geometry

def sumPositiveRadii {A : Type u} [OfNat A 0] [Add A] : Nat → (Nat → A) → A
  | 0, _ => 0
  | half + 1, term => sumPositiveRadii half term + term (half + 1)

theorem sumPositiveRadii_zero {A : Type u} [OfNat A 0] [Add A] (term : Nat → A) :
    sumPositiveRadii 0 term = 0 := rfl

theorem sumPositiveRadii_succ {A : Type u} [OfNat A 0] [Add A]
    (half : Nat) (term : Nat → A) :
    sumPositiveRadii (half + 1) term = sumPositiveRadii half term + term (half + 1) := rfl

theorem sumPositiveRadii_congr {A : Type u} [OfNat A 0] [Add A]
    (half : Nat) (f g : Nat → A)
    (h : ∀ r, 1 ≤ r → r ≤ half → f r = g r) :
    sumPositiveRadii half f = sumPositiveRadii half g := by
  induction half with
  | zero => rfl
  | succ half ih =>
    rw [sumPositiveRadii_succ, sumPositiveRadii_succ,
      ih (fun r hr hbound => h r hr (Nat.le_trans hbound (Nat.le_succ half))),
      h (half + 1) (by omega) (Nat.le_refl _)]

def oddCameraCapacity (half : Nat) : Nat := 2 * half + 1

def positiveCameraRadius {half : Nat} (index : Fin half) : Nat := index.val + 1

def oddCameraPair {half : Nat} (center : Int) (index : Fin half) : Int × Int :=
  (leftLeg center (positiveCameraRadius index), rightLeg center (positiveCameraRadius index))

theorem positiveCameraRadius_bounds {half : Nat} (index : Fin half) :
    1 ≤ positiveCameraRadius index ∧ positiveCameraRadius index ≤ half := by
  have hi := index.isLt
  unfold positiveCameraRadius
  constructor <;> omega

theorem positiveCameraRadius_exists (half r : Nat) (hl : 1 ≤ r) (hr : r ≤ half) :
    ∃ index : Fin half, positiveCameraRadius index = r := by
  refine ⟨⟨r - 1, by omega⟩, ?_⟩
  change r - 1 + 1 = r
  omega

theorem positiveCameraRadius_injective {half : Nat} (i j : Fin half)
    (h : positiveCameraRadius i = positiveCameraRadius j) : i = j := by
  apply Fin.ext
  unfold positiveCameraRadius at h
  omega

theorem oddCameraPair_reflection {half : Nat} (center : Int) (index : Fin half) :
    reflect center (oddCameraPair center index).1 = (oddCameraPair center index).2 ∧
      reflect center (oddCameraPair center index).2 = (oddCameraPair center index).1 :=
  ⟨reflect_leftLeg center _, reflect_rightLeg center _⟩

theorem oddCameraPair_straddles_center {half : Nat} (center : Int) (index : Fin half) :
    (oddCameraPair center index).1 < center ∧ center < (oddCameraPair center index).2 := by
  have hr := (positiveCameraRadius_bounds index).1
  unfold oddCameraPair leftLeg rightLeg
  constructor <;> omega

theorem oddCameraPair_injective {half : Nat} (center : Int) (i j : Fin half)
    (h : oddCameraPair center i = oddCameraPair center j) : i = j := by
  have hleft := congrArg Prod.fst h
  unfold oddCameraPair leftLeg at hleft
  apply positiveCameraRadius_injective
  omega

theorem oddCameraCapacity_isOdd (half : Nat) : IsOddCapacity (oddCameraCapacity half) :=
  ⟨half, rfl⟩

theorem oddCameraCapacity_pos (half : Nat) : 0 < oddCameraCapacity half :=
  oddCapacity_pos (oddCameraCapacity_isOdd half)

theorem oddCameraHalf_unique (b h₁ h₂ : Nat)
    (h₁spec : b = oddCameraCapacity h₁) (h₂spec : b = oddCameraCapacity h₂) : h₁ = h₂ := by
  unfold oddCameraCapacity at h₁spec h₂spec
  omega

/-- A witness may be opened inside a proof; no camera definition uses choice. -/
theorem oddCapacity_exists_cameraHalf {b : Nat} (hodd : IsOddCapacity b) :
    ∃ half, b = oddCameraCapacity half ∧
      ∀ other, b = oddCameraCapacity other → other = half := by
  obtain ⟨half, hb⟩ := hodd
  exact ⟨half, hb, fun other ho => oddCameraHalf_unique b other half ho hb⟩

/-- Count two legs at each actual radius, before simplifying the count. -/
def oddCameraLegCount (half : Nat) : Nat := sumPositiveRadii half (fun _ => 2)

theorem oddCameraLegCount_eq_twice_half (half : Nat) : oddCameraLegCount half = 2 * half := by
  induction half with
  | zero => rfl
  | succ half ih =>
    change oddCameraLegCount half + 2 = 2 * (half + 1)
    omega

theorem oddCameraLegCount_eq_capacity_sub_one (b half : Nat)
    (hb : b = oddCameraCapacity half) : oddCameraLegCount half = b - 1 := by
  rw [oddCameraLegCount_eq_twice_half]
  unfold oddCameraCapacity at hb
  omega

end GeometryOfNumbers.Geometry
