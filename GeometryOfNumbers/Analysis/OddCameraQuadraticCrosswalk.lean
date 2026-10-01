import GeometryOfNumbers.Analysis.CenteredMultiplicativeProfile
import GeometryOfNumbers.Analysis.QuadraticCameraBracket

/-!
# The camera readout in two compatible realizations

The real lift uses the SAME radius enumeration and legs as Geometry. Its
generic saturation theorem precedes specialization to a multiplicative
profile. Horizontal transport compatibility is explicit; its positive step
is not selected by the camera's capacity or by vertical depth.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

def realOddCameraLegSum (half : Nat) (F : Int → ℝ) (c : Int) : ℝ :=
  sumPositiveRadii half (fun r => F (leftLeg c (r : Int)) + F (rightLeg c (r : Int)))

def realOddCameraBracket (half : Nat) (F : Int → ℝ) (c : Int) : ℝ :=
  realOddCameraLegSum half F c - (2 * (half : ℝ)) * F c

def realOddCameraSaturatedSecondDifference (half : Nat) (F : Int → ℝ) (c : Int) : ℝ :=
  sumPositiveRadii half (fun r => realCenteredSecondDifference F c r)

theorem realOddCameraBracket_eq_saturatedSecondDifference
    (half : Nat) (F : Int → ℝ) (c : Int) :
    realOddCameraBracket half F c = realOddCameraSaturatedSecondDifference half F c := by
  have hlocal := sumPositiveRadii_congr half
    (fun r => realCenteredSecondDifference F c r)
    (fun r => (F (leftLeg c (r : Int)) + F (rightLeg c (r : Int))) - 2 * F c)
    (fun r _ _ => by unfold realCenteredSecondDifference realCenteredReadout; ring)
  unfold realOddCameraBracket realOddCameraLegSum realOddCameraSaturatedSecondDifference
  rw [hlocal, sumPositiveRadii_real_sub, sumPositiveRadii_real_constant]
  ring

theorem realOddCameraBracket_zero (F : Int → ℝ) (c : Int) :
    realOddCameraBracket 0 F c = 0 := by simp [realOddCameraBracket, realOddCameraLegSum,
      sumPositiveRadii_zero]

theorem realOddCameraBracket_C3 (F : Int → ℝ) (c : Int) :
    realOddCameraBracket 1 F c = realCenteredSecondDifference F c 1 := by
  rw [realOddCameraBracket_eq_saturatedSecondDifference]
  simp [realOddCameraSaturatedSecondDifference, sumPositiveRadii]

def cameraOffsetDeformations (Q : Int → ℝ) (r : Nat) : ℝ := Q (r : Int)

theorem cameraOffsetDeformations_eq_pow {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (r : Nat) :
    cameraOffsetDeformations Q r = (Q 1) ^ r := multiplicativeOffsetTransport_natCast hQ r

theorem profile_realOddCameraBracket_eq_quadratic (half : Nat) (C : ℝ)
    {Q : Int → ℝ} (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) :
    realOddCameraBracket half (centeredMultiplicativeProfile C Q c) c =
      quadraticCameraBracket half C (cameraOffsetDeformations Q) := by
  rw [realOddCameraBracket_eq_saturatedSecondDifference]
  exact sumPositiveRadii_congr half _ _ (fun r _ _ =>
    profile_realCenteredSecondDifference_eq_local C hQ c r)

theorem profile_realOddCameraBracket_eq_pow (half : Nat) (C : ℝ)
    {Q : Int → ℝ} (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) :
    realOddCameraBracket half (centeredMultiplicativeProfile C Q c) c =
      quadraticCameraBracket half C (fun r => (Q 1) ^ r) := by
  rw [profile_realOddCameraBracket_eq_quadratic half C hQ]
  exact sumPositiveRadii_congr half _ _ (fun r _ _ => by
    rw [cameraOffsetDeformations_eq_pow hQ])

theorem stepProfile_realOddCameraBracket_eq_quadratic (half : Nat) (C : ℝ)
    {rho : ℝ} (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c =
        quadraticCameraBracket half C (fun r => rho ^ r) := by
  simpa only [canonicalMultiplicativeOffsetTransport_one] using
    profile_realOddCameraBracket_eq_pow half C
      (canonicalMultiplicativeOffsetTransport_isPositive hrho) c

theorem stepProfile_realOddCameraBracket_eq_closed (half : Nat) (C : ℝ)
    {rho : ℝ} (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c =
        C * sumPositiveRadii half (fun r => rho ^ r + (rho ^ r)⁻¹ - 2) := by
  rw [stepProfile_realOddCameraBracket_eq_quadratic half C hrho, quadraticCameraBracket_eq_closed]

theorem stepProfile_realOddCameraBracket_eq_factor (half : Nat) (C : ℝ)
    {rho : ℝ} (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c =
        C * sumPositiveRadii half (fun r => (rho ^ r - 1) ^ 2 * (rho ^ r)⁻¹) := by
  rw [stepProfile_realOddCameraBracket_eq_quadratic half C hrho]
  exact quadraticCameraBracket_eq_factor half C _ (fun r _ _ => ne_of_gt (pow_pos hrho r))

theorem stepProfile_realOddCameraBracket_nonneg (half : Nat) {C rho : ℝ}
    (hC : 0 < C) (hrho : 0 < rho) (c : Int) :
    0 ≤ realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c := by
  rw [stepProfile_realOddCameraBracket_eq_quadratic half C hrho]
  exact quadraticCameraBracket_nonneg half hC _ (fun r _ _ => pow_pos hrho r)

theorem stepProfile_realOddCameraBracket_zero_iff (half : Nat) (hhalf : 0 < half)
    {C rho : ℝ} (hC : 0 < C) (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c = 0 ↔
        rho = 1 := by
  rw [stepProfile_realOddCameraBracket_eq_quadratic half C hrho,
    quadraticCameraBracket_zero_iff half hC _ (fun r _ _ => pow_pos hrho r)]
  constructor
  · intro h
    simpa using h 1 (Nat.le_refl 1) hhalf
  · intro h r _ _
    simp [h]

theorem stepProfile_inverse_left_eq_right (C : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho⁻¹) c
      (leftLeg c (r : Int)) =
    centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c
      (rightLeg c (r : Int)) := by
  rw [centeredMultiplicativeProfile_leftLeg_eq_pow C
      (canonicalMultiplicativeOffsetTransport_isPositive (inv_pos.mpr hrho)),
    centeredMultiplicativeProfile_rightLeg_eq_inv_pow C
      (canonicalMultiplicativeOffsetTransport_isPositive hrho)]
  simp only [canonicalMultiplicativeOffsetTransport_one, inv_pow]

theorem stepProfile_inverse_right_eq_left (C : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho⁻¹) c
      (rightLeg c (r : Int)) =
    centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c
      (leftLeg c (r : Int)) := by
  simpa only [inv_inv] using
    (stepProfile_inverse_left_eq_right C (inv_pos.mpr hrho) c r).symm

theorem stepProfile_realOddCameraBracket_reflection (half : Nat) (C : ℝ)
    {rho : ℝ} (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho⁻¹) c) c =
    realOddCameraBracket half
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c := by
  rw [stepProfile_realOddCameraBracket_eq_quadratic half C (inv_pos.mpr hrho),
    stepProfile_realOddCameraBracket_eq_quadratic half C hrho]
  have hfamily : (fun r : Nat => rho⁻¹ ^ r) = (fun r => reciprocalReflection (rho ^ r)) := by
    funext r
    exact inv_pow rho r
  rw [hfamily]
  exact quadraticCameraBracket_reflection half C _

theorem stepProfile_realOddCameraBracket_C3 (C : ℝ) {rho : ℝ} (hrho : 0 < rho) (c : Int) :
    realOddCameraBracket 1
      (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport rho) c) c =
        quadraticCenteredBracket C rho := by
  rw [realOddCameraBracket_C3,
    profile_realCenteredSecondDifference_eq_pow C
      (canonicalMultiplicativeOffsetTransport_isPositive hrho)]
  simp only [canonicalMultiplicativeOffsetTransport_one, pow_one]

theorem criticalProfile_realOddCameraBracket_eq_quadratic (half k : Nat)
    {Q : Int → ℝ} (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) :
    realOddCameraBracket half
      (criticalCenteredMultiplicativeProfile (oddCameraCapacity half) k
        (oddCameraCapacity_pos half) Q c) c =
      criticalQuadraticCameraBracket half k (cameraOffsetDeformations Q) :=
  profile_realOddCameraBracket_eq_quadratic half _ hQ c

/-- The supported vertical index supplies the existing mass, while the
horizontal step remains a separate positive input. -/
theorem balancedCarryDepth_multiplicativeProfile_provenance (half n k : Nat)
    (hdepth : HasIntegerCarryDepthAtLeast (oddCameraCapacity half)
      (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) k)
    {rho : ℝ} (hrho : 0 < rho) :
    HasIntegerCarryDepthAtLeast (oddCameraCapacity half)
      ((n : Int) - balancedCarryOffset (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) k ∧
    (∀ r, 1 ≤ r → r ≤ half →
      criticalCenteredMultiplicativeProfile (oddCameraCapacity half) k (oddCameraCapacity_pos half)
        (canonicalMultiplicativeOffsetTransport rho)
        (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half))
        (leftLeg (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) (r : Int)) *
      criticalCenteredMultiplicativeProfile (oddCameraCapacity half) k (oddCameraCapacity_pos half)
        (canonicalMultiplicativeOffsetTransport rho)
        (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half))
        (rightLeg (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) (r : Int)) =
      realizeCountingShare (canonicalResidualDepthMass (oddCameraCapacity half) k
        (oddCameraCapacity_pos half))) := by
  refine ⟨(balancedCarry_canonical_offset_depth_iff _ _ _ _).2 hdepth, ?_⟩
  intro r _ _
  exact criticalCenteredMultiplicativeProfile_product _ _ _
    (canonicalMultiplicativeOffsetTransport_isPositive hrho) _ r

end

end GeometryOfNumbers.Analysis
