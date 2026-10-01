import GeometryOfNumbers.Analysis
import Lean

/-! Zone B reports standard Mathlib axioms separately from Foundation's empty
footprint. Examples test scalar realization, angular quadratic energy and
reciprocal legs with their derived bracket, and the explicitly compatible
offset profile. They do not select a physical law for any parameter. -/

open Lean Elab Command

/-- Zone B permits the standard library axioms, but rejects any additional ones. -/
elab "#assert_analysis_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Zone B unexpected axiom: {decl} depends on {axiomName}"

namespace GeometryOfNumbers.Analysis

open Foundation

-- Integer transport and the same discrete points, with a FREE positive step.
example : IsPositiveMultiplicativeOffsetTransport (canonicalMultiplicativeOffsetTransport 2) :=
  canonicalMultiplicativeOffsetTransport_isPositive (by norm_num)

example : canonicalMultiplicativeOffsetTransport 2 0 = 1 ∧
    canonicalMultiplicativeOffsetTransport 2 1 = 2 ∧
    canonicalMultiplicativeOffsetTransport 2 2 = 4 ∧
    canonicalMultiplicativeOffsetTransport 2 3 = 8 ∧
    canonicalMultiplicativeOffsetTransport 2 (-1) = 1 / 2 ∧
    canonicalMultiplicativeOffsetTransport 2 (-2) = 1 / 4 := by
  norm_num [canonicalMultiplicativeOffsetTransport]

example : canonicalMultiplicativeOffsetTransport 2 (1 + 2) =
    canonicalMultiplicativeOffsetTransport 2 1 * canonicalMultiplicativeOffsetTransport 2 2 := by
  norm_num [canonicalMultiplicativeOffsetTransport]

example : centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 10 = 1 / 3 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 9 = 2 / 3 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 11 = 1 / 6 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 8 = 4 / 3 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 12 = 1 / 12 := by
  norm_num [centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example : centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 9 *
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 11 = 1 / 9 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 8 *
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10 12 = 1 / 9 := by
  norm_num [centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example : realCenteredSecondDifference
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10) 10 1 = 1 / 6 ∧
    realCenteredSecondDifference
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10) 10 2 = 3 / 4 := by
  norm_num [realCenteredSecondDifference, realCenteredReadout, Geometry.leftLeg, Geometry.rightLeg,
    centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example : realOddCameraBracket 2
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10) 10 = 11 / 12 := by
  norm_num [realOddCameraBracket, realOddCameraLegSum, Geometry.sumPositiveRadii,
    Geometry.leftLeg, Geometry.rightLeg, centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example : realOddCameraBracket 2
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport (1 / 2)) 10) 10 = 11 / 12 := by
  norm_num [realOddCameraBracket, realOddCameraLegSum, Geometry.sumPositiveRadii,
    Geometry.leftLeg, Geometry.rightLeg, centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example : realOddCameraBracket 2
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 1) 10) 10 = 0 := by
  norm_num [realOddCameraBracket, realOddCameraLegSum, Geometry.sumPositiveRadii,
    Geometry.leftLeg, Geometry.rightLeg, centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

-- Inverting the single step swaps EVERY displayed leg, not just the total.
example : centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport (1 / 2)) 10 9 = 1 / 6 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport (1 / 2)) 10 11 = 2 / 3 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport (1 / 2)) 10 8 = 1 / 12 ∧
    centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport (1 / 2)) 10 12 = 4 / 3 := by
  norm_num [centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

example (C : ℝ) (c x : Int) :
    centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport 1) c x = C := by
  simp [centeredMultiplicativeProfile, canonicalMultiplicativeOffsetTransport]

-- The composite-capacity readout also has an exact rational total.
example : Geometry.oddCameraCapacity 4 = 9 ∧ realOddCameraBracket 4
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10) 10 = 367 / 48 := by
  constructor
  · rfl
  · norm_num [realOddCameraBracket, realOddCameraLegSum, Geometry.sumPositiveRadii,
      Geometry.leftLeg, Geometry.rightLeg, centeredMultiplicativeProfile,
      canonicalMultiplicativeOffsetTransport]

-- Empty camera: zero does NOT select the step (here it is 2, not 1).
example : realOddCameraBracket 0
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) 10) 10 = 0 ∧
    (2 : ℝ) ≠ 1 := ⟨realOddCameraBracket_zero _ _, by norm_num⟩

example (F : Int → ℝ) (c : Int) : realOddCameraBracket 1 F c =
    F (c - 1) - 2 * F c + F (c + 1) := by
  simpa [realCenteredSecondDifference, realCenteredReadout, Geometry.leftLeg, Geometry.rightLeg]
    using realOddCameraBracket_C3 F c

-- Capacity 9 is composite; the four-pair crosswalk has no prime hypothesis.
example (C : ℝ) (c : Int) : realOddCameraBracket 4
    (centeredMultiplicativeProfile C (canonicalMultiplicativeOffsetTransport 2) c) c =
    quadraticCameraBracket 4 C (fun r => 2 ^ r) :=
  stepProfile_realOddCameraBracket_eq_quadratic 4 C (by norm_num) c

example : Geometry.oddCameraCapacity 4 = 9 := rfl

example (c : Int) : realOddCameraBracket 1
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) c) c =
      quadraticCenteredBracket (1 / 3) 2 :=
  stepProfile_realOddCameraBracket_C3 _ (by norm_num) c

example (c : Int) : realOddCameraBracket 2
    (centeredMultiplicativeProfile (1 / 3) (canonicalMultiplicativeOffsetTransport 2) c) c ≠ 0 := by
  intro hz
  have hstep := (stepProfile_realOddCameraBracket_zero_iff 2 (by decide)
    (C := 1 / 3) (rho := 2) (by norm_num) (by norm_num) c).1 hz
  norm_num at hstep

#assert_analysis_axioms realOddCameraLegSum
#assert_analysis_axioms realOddCameraBracket
#assert_analysis_axioms realOddCameraSaturatedSecondDifference
#assert_analysis_axioms realOddCameraBracket_eq_saturatedSecondDifference
#assert_analysis_axioms realOddCameraBracket_zero
#assert_analysis_axioms realOddCameraBracket_C3
#assert_analysis_axioms cameraOffsetDeformations
#assert_analysis_axioms cameraOffsetDeformations_eq_pow
#assert_analysis_axioms profile_realOddCameraBracket_eq_quadratic
#assert_analysis_axioms profile_realOddCameraBracket_eq_pow
#assert_analysis_axioms stepProfile_realOddCameraBracket_eq_quadratic
#assert_analysis_axioms stepProfile_realOddCameraBracket_eq_closed
#assert_analysis_axioms stepProfile_realOddCameraBracket_eq_factor
#assert_analysis_axioms stepProfile_realOddCameraBracket_eq_factor_div
#assert_analysis_axioms stepProfile_realOddCameraBracket_nonneg
#assert_analysis_axioms stepProfile_realOddCameraBracket_zero_iff
#assert_analysis_axioms stepProfile_inverse_left_eq_right
#assert_analysis_axioms stepProfile_inverse_right_eq_left
#assert_analysis_axioms stepProfile_realOddCameraBracket_reflection
#assert_analysis_axioms stepProfile_realOddCameraBracket_C3
#assert_analysis_axioms stepProfile_realOddCameraBracket_C3_readout
#assert_analysis_axioms criticalProfile_realOddCameraBracket_eq_quadratic
#assert_analysis_axioms balancedCarryDepth_multiplicativeProfile_provenance
#assert_analysis_axioms centeredMultiplicativeProfile
#assert_analysis_axioms centeredMultiplicativeProfile_center
#assert_analysis_axioms centeredMultiplicativeProfile_leftLeg
#assert_analysis_axioms centeredMultiplicativeProfile_rightLeg
#assert_analysis_axioms profile_leftLeg_eq_quadraticLeftLeg
#assert_analysis_axioms profile_rightLeg_eq_quadraticRightLeg
#assert_analysis_axioms centeredMultiplicativeProfile_leftLeg_eq_pow
#assert_analysis_axioms centeredMultiplicativeProfile_rightLeg_eq_inv_pow
#assert_analysis_axioms centeredMultiplicativeProfile_reflected_product
#assert_analysis_axioms realCenteredSecondDifference
#assert_analysis_axioms profile_realCenteredSecondDifference_eq_local
#assert_analysis_axioms profile_realCenteredSecondDifference_eq_pow
#assert_analysis_axioms profile_realCenteredSecondDifference_eq_closed
#assert_analysis_axioms profile_realCenteredSecondDifference_eq_factor
#assert_analysis_axioms profile_realCenteredSecondDifference_eq_factor_div
#assert_analysis_axioms criticalCenteredMultiplicativeProfile
#assert_analysis_axioms criticalCenteredMultiplicativeProfile_product
#assert_analysis_axioms IsPositiveMultiplicativeOffsetTransport
#assert_analysis_axioms multiplicativeOffsetTransport_zero
#assert_analysis_axioms multiplicativeOffsetTransport_add
#assert_analysis_axioms multiplicativeOffsetTransport_product_neg
#assert_analysis_axioms multiplicativeOffsetTransport_ne_zero
#assert_analysis_axioms multiplicativeOffsetTransport_neg
#assert_analysis_axioms multiplicativeOffsetTransport_natCast
#assert_analysis_axioms multiplicativeOffsetTransport_neg_natCast
#assert_analysis_axioms multiplicativeOffsetTransport_eq_zpow
#assert_analysis_axioms multiplicativeOffsetTransport_pos
#assert_analysis_axioms canonicalMultiplicativeOffsetTransport
#assert_analysis_axioms canonicalMultiplicativeOffsetTransport_isPositive
#assert_analysis_axioms canonicalMultiplicativeOffsetTransport_one
#assert_analysis_axioms multiplicativeOffsetTransport_eq_canonical
#assert_analysis_axioms multiplicativeOffsetTransport_unique
#assert_analysis_axioms existsUnique_multiplicativeOffsetTransport
#print axioms realOddCameraBracket_eq_saturatedSecondDifference
#print axioms realOddCameraBracket_zero
#print axioms realOddCameraBracket_C3
#print axioms cameraOffsetDeformations_eq_pow
#print axioms profile_realOddCameraBracket_eq_quadratic
#print axioms profile_realOddCameraBracket_eq_pow
#print axioms stepProfile_realOddCameraBracket_eq_quadratic
#print axioms stepProfile_realOddCameraBracket_eq_closed
#print axioms stepProfile_realOddCameraBracket_eq_factor
#print axioms stepProfile_realOddCameraBracket_eq_factor_div
#print axioms stepProfile_realOddCameraBracket_nonneg
#print axioms stepProfile_realOddCameraBracket_zero_iff
#print axioms stepProfile_inverse_left_eq_right
#print axioms stepProfile_inverse_right_eq_left
#print axioms stepProfile_realOddCameraBracket_reflection
#print axioms stepProfile_realOddCameraBracket_C3
#print axioms stepProfile_realOddCameraBracket_C3_readout
#print axioms criticalProfile_realOddCameraBracket_eq_quadratic
#print axioms balancedCarryDepth_multiplicativeProfile_provenance
#print axioms centeredMultiplicativeProfile_center
#print axioms centeredMultiplicativeProfile_leftLeg
#print axioms centeredMultiplicativeProfile_rightLeg
#print axioms profile_leftLeg_eq_quadraticLeftLeg
#print axioms profile_rightLeg_eq_quadraticRightLeg
#print axioms centeredMultiplicativeProfile_leftLeg_eq_pow
#print axioms centeredMultiplicativeProfile_rightLeg_eq_inv_pow
#print axioms centeredMultiplicativeProfile_reflected_product
#print axioms profile_realCenteredSecondDifference_eq_local
#print axioms profile_realCenteredSecondDifference_eq_pow
#print axioms profile_realCenteredSecondDifference_eq_closed
#print axioms profile_realCenteredSecondDifference_eq_factor
#print axioms profile_realCenteredSecondDifference_eq_factor_div
#print axioms criticalCenteredMultiplicativeProfile_product
#print axioms multiplicativeOffsetTransport_zero
#print axioms multiplicativeOffsetTransport_add
#print axioms multiplicativeOffsetTransport_product_neg
#print axioms multiplicativeOffsetTransport_ne_zero
#print axioms multiplicativeOffsetTransport_neg
#print axioms multiplicativeOffsetTransport_natCast
#print axioms multiplicativeOffsetTransport_neg_natCast
#print axioms multiplicativeOffsetTransport_eq_zpow
#print axioms multiplicativeOffsetTransport_pos
#print axioms canonicalMultiplicativeOffsetTransport_isPositive
#print axioms canonicalMultiplicativeOffsetTransport_one
#print axioms multiplicativeOffsetTransport_eq_canonical
#print axioms multiplicativeOffsetTransport_unique
#print axioms existsUnique_multiplicativeOffsetTransport

#assert_analysis_axioms quadraticCameraLegSum
#assert_analysis_axioms quadraticCameraBracket
#assert_analysis_axioms reflectCameraPairs
#assert_analysis_axioms criticalQuadraticCameraBracket
#assert_analysis_axioms sumPositiveRadii_real_sub
#assert_analysis_axioms sumPositiveRadii_real_constant
#assert_analysis_axioms sumPositiveRadii_real_mul
#assert_analysis_axioms sumPositiveRadii_real_nonneg
#assert_analysis_axioms sumPositiveRadii_real_zero_iff
#assert_analysis_axioms quadraticCameraBracket_eq_legs_sub_centers
#assert_analysis_axioms quadraticCameraBracket_eq_closed
#assert_analysis_axioms quadraticCameraBracket_eq_factor
#assert_analysis_axioms quadraticCameraBracket_nonneg
#assert_analysis_axioms quadraticCameraBracket_zero_iff
#assert_analysis_axioms quadraticCameraBracket_zero_pairs
#assert_analysis_axioms quadraticCameraBracket_reflection
#assert_analysis_axioms quadraticCameraBracket_independent_reflections
#assert_analysis_axioms quadraticCameraBracket_reflect_one_pair
#assert_analysis_axioms criticalQuadraticCameraBracket_eq_sum_local
#assert_analysis_axioms criticalQuadraticCameraBracket_eq_closed
#assert_analysis_axioms criticalQuadraticCameraBracket_eq_factor
#assert_analysis_axioms criticalQuadraticCameraBracket_nonneg
#assert_analysis_axioms criticalQuadraticCameraBracket_zero_iff
#assert_analysis_axioms criticalQuadraticCameraBracket_independent_reflections
#assert_analysis_axioms criticalQuadraticCameraBracket_reflection
#assert_analysis_axioms criticalQuadraticCameraBracket_zero_pairs
#assert_analysis_axioms criticalQuadraticCameraPair_product
#assert_analysis_axioms balancedCarryDepth_quadraticCamera_provenance
#print axioms sumPositiveRadii_real_sub
#print axioms sumPositiveRadii_real_constant
#print axioms sumPositiveRadii_real_mul
#print axioms sumPositiveRadii_real_nonneg
#print axioms sumPositiveRadii_real_zero_iff
#print axioms quadraticCameraBracket_eq_legs_sub_centers
#print axioms quadraticCameraBracket_eq_closed
#print axioms quadraticCameraBracket_eq_factor
#print axioms quadraticCameraBracket_nonneg
#print axioms quadraticCameraBracket_zero_iff
#print axioms quadraticCameraBracket_zero_pairs
#print axioms quadraticCameraBracket_reflection
#print axioms quadraticCameraBracket_independent_reflections
#print axioms quadraticCameraBracket_reflect_one_pair
#print axioms criticalQuadraticCameraBracket_eq_sum_local
#print axioms criticalQuadraticCameraBracket_eq_closed
#print axioms criticalQuadraticCameraBracket_eq_factor
#print axioms criticalQuadraticCameraBracket_nonneg
#print axioms criticalQuadraticCameraBracket_zero_iff
#print axioms criticalQuadraticCameraBracket_independent_reflections
#print axioms criticalQuadraticCameraBracket_reflection
#print axioms criticalQuadraticCameraBracket_zero_pairs
#print axioms criticalQuadraticCameraPair_product
#print axioms balancedCarryDepth_quadraticCamera_provenance

#assert_analysis_axioms reciprocalReflection
#assert_analysis_axioms quadraticLeftLeg
#assert_analysis_axioms quadraticRightLeg
#assert_analysis_axioms criticalQuadraticLeftLeg
#assert_analysis_axioms criticalQuadraticRightLeg
#assert_analysis_axioms realCenteredReadout
#assert_analysis_axioms quadraticCenteredBracket
#assert_analysis_axioms criticalQuadraticBracket
#assert_analysis_axioms realCenteredReadout_swap
#assert_analysis_axioms realCenteredReadout_additiveLegs
#assert_analysis_axioms quadraticCenteredBracket_eq_closed
#assert_analysis_axioms quadraticCenteredBracket_eq_factor
#assert_analysis_axioms quadraticCenteredBracket_nonneg
#assert_analysis_axioms quadraticCenteredBracket_at_one
#assert_analysis_axioms quadraticCenteredBracket_zero_iff
#assert_analysis_axioms quadraticCenteredBracket_pos
#assert_analysis_axioms quadraticCenteredBracket_reflection
#assert_analysis_axioms quadraticCenteredBracket_zero_parameter
#assert_analysis_axioms criticalQuadraticBracket_eq_readout
#assert_analysis_axioms criticalQuadraticBracket_eq_closed
#assert_analysis_axioms criticalQuadraticBracket_eq_factor
#assert_analysis_axioms criticalQuadraticBracket_nonneg
#assert_analysis_axioms criticalQuadraticBracket_zero_iff
#assert_analysis_axioms criticalQuadraticBracket_pos
#assert_analysis_axioms criticalQuadraticBracket_reflection
#assert_analysis_axioms criticalQuadraticBracket_zero_depth
#assert_analysis_axioms criticalQuadraticBracket_capacity_one
#assert_analysis_axioms balancedCarryDepth_quadraticReflection_provenance
#assert_analysis_axioms reciprocalReflection_involutive
#assert_analysis_axioms reciprocalReflection_pos
#assert_analysis_axioms quadraticLeftLeg_reflection
#assert_analysis_axioms quadraticRightLeg_reflection
#assert_analysis_axioms quadraticReflectedLegs_at_one
#assert_analysis_axioms quadraticReflectedLegs_product
#assert_analysis_axioms quadraticReflection_product
#assert_analysis_axioms criticalQuadraticLegs_product
#assert_analysis_axioms criticalQuadraticReflection_product
#assert_analysis_axioms criticalQuadraticLegs_product_realizes_formalMass
#assert_analysis_axioms balancedCarryDepth_quadraticLegs_product

#print axioms realCenteredReadout_swap
#print axioms realCenteredReadout_additiveLegs
#print axioms quadraticCenteredBracket_eq_closed
#print axioms quadraticCenteredBracket_eq_factor
#print axioms quadraticCenteredBracket_nonneg
#print axioms quadraticCenteredBracket_at_one
#print axioms quadraticCenteredBracket_zero_iff
#print axioms quadraticCenteredBracket_pos
#print axioms quadraticCenteredBracket_reflection
#print axioms quadraticCenteredBracket_zero_parameter
#print axioms criticalQuadraticBracket_eq_readout
#print axioms criticalQuadraticBracket_eq_closed
#print axioms criticalQuadraticBracket_eq_factor
#print axioms criticalQuadraticBracket_nonneg
#print axioms criticalQuadraticBracket_zero_iff
#print axioms criticalQuadraticBracket_pos
#print axioms criticalQuadraticBracket_reflection
#print axioms criticalQuadraticBracket_zero_depth
#print axioms criticalQuadraticBracket_capacity_one
#print axioms balancedCarryDepth_quadraticReflection_provenance
#print axioms reciprocalReflection_involutive
#print axioms reciprocalReflection_pos
#print axioms quadraticLeftLeg_reflection
#print axioms quadraticRightLeg_reflection
#print axioms quadraticReflectedLegs_at_one
#print axioms quadraticReflectedLegs_product
#print axioms quadraticReflection_product
#print axioms criticalQuadraticLegs_product
#print axioms criticalQuadraticReflection_product
#print axioms criticalQuadraticLegs_product_realizes_formalMass
#print axioms balancedCarryDepth_quadraticLegs_product

#assert_analysis_axioms RealPlaneState
#assert_analysis_axioms realPlaneEnergy
#assert_analysis_axioms rotateRealPlane
#assert_analysis_axioms realCriticalDepthSeed
#assert_analysis_axioms realCriticalDepthState
#assert_analysis_axioms rotateRealPlane_energy
#assert_analysis_axioms rotateRealPlane_zero
#assert_analysis_axioms rotateRealPlane_add
#assert_analysis_axioms realCriticalDepthSeed_energy_eq_amplitude_sq
#assert_analysis_axioms realCriticalDepthSeed_energy
#assert_analysis_axioms realCriticalAmplitude_pos
#assert_analysis_axioms realCriticalDepthState_eq_coordinates
#assert_analysis_axioms realCriticalDepthState_energy
#assert_analysis_axioms realCriticalDepthState_zero_angle
#assert_analysis_axioms realCriticalDepthSeed_zero_depth
#assert_analysis_axioms realCriticalDepthState_zero_depth_energy
#assert_analysis_axioms realCriticalDepthSeed_capacity_one
#assert_analysis_axioms realCriticalDepthState_capacity_one_energy
#assert_analysis_axioms balancedCarryDepth_realState_energy
#assert_analysis_axioms balancedCarryDepth_realState_realizes_formalMass
#print axioms rotateRealPlane_energy
#print axioms rotateRealPlane_zero
#print axioms rotateRealPlane_add
#print axioms realCriticalDepthSeed_energy_eq_amplitude_sq
#print axioms realCriticalDepthSeed_energy
#print axioms realCriticalAmplitude_pos
#print axioms realCriticalDepthState_eq_coordinates
#print axioms realCriticalDepthState_energy
#print axioms realCriticalDepthState_zero_angle
#print axioms realCriticalDepthSeed_zero_depth
#print axioms realCriticalDepthState_zero_depth_energy
#print axioms realCriticalDepthSeed_capacity_one
#print axioms realCriticalDepthState_capacity_one_energy
#print axioms balancedCarryDepth_realState_energy
#print axioms balancedCarryDepth_realState_realizes_formalMass

#assert_analysis_axioms realizeCountingShare
#assert_analysis_axioms realDepthMass
#assert_analysis_axioms realizeFormalExponent
#assert_analysis_axioms realAmplitudeOfFormalExponent
#assert_analysis_axioms realCriticalAmplitude
#assert_analysis_axioms realizeCountingShare_eq_iff_sameCountingShare
#assert_analysis_axioms realDepthMass_eq_one_div_pow
#assert_analysis_axioms realDepthMass_eq_inv_pow
#assert_analysis_axioms realize_canonicalResidualDepthMass
#assert_analysis_axioms realDepthMass_zero
#assert_analysis_axioms realDepthMass_one
#assert_analysis_axioms realDepthMass_pos
#assert_analysis_axioms formalHalf_realizes_half
#assert_analysis_axioms realCriticalAmplitude_eq_rpow
#assert_analysis_axioms formalHalf_realizes_realCriticalAmplitude
#assert_analysis_axioms realCriticalAmplitude_sq_eq_realDepthMass
#assert_analysis_axioms realCriticalAmplitude_zero
#assert_analysis_axioms realCriticalAmplitude_one
#assert_analysis_axioms quadraticScaleCompatible_realizes_realCriticalAmplitude

#print axioms realizeCountingShare_eq_iff_sameCountingShare
#print axioms realDepthMass_eq_one_div_pow
#print axioms realDepthMass_eq_inv_pow
#print axioms realize_canonicalResidualDepthMass
#print axioms realDepthMass_zero
#print axioms realDepthMass_one
#print axioms realDepthMass_pos
#print axioms formalHalf_realizes_half
#print axioms realCriticalAmplitude_eq_rpow
#print axioms formalHalf_realizes_realCriticalAmplitude
#print axioms realCriticalAmplitude_sq_eq_realDepthMass
#print axioms realCriticalAmplitude_zero
#print axioms realCriticalAmplitude_one
#print axioms quadraticScaleCompatible_realizes_realCriticalAmplitude

example : realDepthMass 2 0 (by decide) = 1 := realDepthMass_zero 2 (by decide)
example : realDepthMass 2 1 (by decide) = 1 / 2 := by
  rw [realDepthMass_eq_one_div_pow]
  norm_num
example : realDepthMass 3 2 (by decide) = 1 / 9 := by
  rw [realDepthMass_eq_one_div_pow]
  norm_num
example : realCriticalAmplitude 3 0 (by decide) = 1 :=
  realCriticalAmplitude_zero 3 (by decide)
example : realCriticalAmplitude 2 1 (by decide) ^ 2 = 1 / 2 := by
  rw [realCriticalAmplitude_sq_eq_realDepthMass, realDepthMass_eq_one_div_pow]
  norm_num
example : realCriticalAmplitude 3 2 (by decide) = 1 / 3 := by
  rw [realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : realAmplitudeOfFormalExponent 3 2 17 34 (by decide) (by decide) =
    realCriticalAmplitude 3 2 (by decide) :=
  formalHalf_realizes_realCriticalAmplitude 3 2 17 34 (by decide) ⟨by decide, rfl⟩
example : realDepthMass 1 5 Nat.zero_lt_one = 1 := realDepthMass_one 5
example : realCriticalAmplitude 1 5 Nat.zero_lt_one = 1 := realCriticalAmplitude_one 5
example : realizeCountingShare ⟨2, 18, by decide⟩ =
    realizeCountingShare ⟨1, 9, by decide⟩ := by
  apply (realizeCountingShare_eq_iff_sameCountingShare _ _).2
  change 2 * 9 = 1 * 18
  decide

-- Coordinate tests: the same radial amplitude, with no angular law.
example : realCriticalDepthSeed 3 2 (by decide) = ((1 : ℝ) / 3, 0) := by
  unfold realCriticalDepthSeed
  rw [realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : realPlaneEnergy (realCriticalDepthSeed 3 2 (by decide)) = 1 / 9 := by
  rw [realCriticalDepthSeed_energy, realDepthMass_eq_one_div_pow]
  norm_num
example : realCriticalDepthState 3 2 (by decide) 0 =
    realCriticalDepthSeed 3 2 (by decide) :=
  realCriticalDepthState_zero_angle 3 2 (by decide)
example : realCriticalDepthState 3 2 (by decide) (Real.pi / 2) =
    (0, (1 : ℝ) / 3) := by
  rw [realCriticalDepthState_eq_coordinates, Real.cos_pi_div_two, Real.sin_pi_div_two,
    realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState 3 2 (by decide) theta) = 1 / 9 := by
  rw [realCriticalDepthState_energy, realDepthMass_eq_one_div_pow]
  norm_num
example (theta : ℝ) : realPlaneEnergy (rotateRealPlane theta (3, 4)) = 25 := by
  rw [rotateRealPlane_energy]
  norm_num [realPlaneEnergy]
example (b : ℕ) (hb : 0 < b) (theta : ℝ) :
    realCriticalDepthSeed b 0 hb = (1, 0) ∧
      realPlaneEnergy (realCriticalDepthState b 0 hb theta) = 1 :=
  ⟨realCriticalDepthSeed_zero_depth b hb,
    realCriticalDepthState_zero_depth_energy b hb theta⟩
example (k : ℕ) (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState 1 k Nat.zero_lt_one theta) = 1 :=
  realCriticalDepthState_capacity_one_energy k theta
set_option maxRecDepth 2048 in
example (theta : ℝ) :
    realPlaneEnergy (realCriticalDepthState 5 2 (Geometry.oddCapacity_pos ⟨2, rfl⟩) theta) =
      realDepthMass 5 2 (Geometry.oddCapacity_pos ⟨2, rfl⟩) := by
  apply balancedCarryDepth_realState_energy 5 26 2 ⟨2, rfl⟩
  change (5 : Int) ^ 2 ∣ (25 : Int)
  exact ⟨1, rfl⟩

-- Reciprocal legs: central product is unchanged, while the additive readout changes.
example : criticalQuadraticLeftLeg 3 2 (by decide) 2 = (2 : ℝ) / 3 := by
  unfold criticalQuadraticLeftLeg quadraticLeftLeg
  rw [realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : criticalQuadraticRightLeg 3 2 (by decide) 2 = (1 : ℝ) / 6 := by
  unfold criticalQuadraticRightLeg quadraticRightLeg reciprocalReflection
  rw [realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : criticalQuadraticLeftLeg 3 2 (by decide) 2 *
    criticalQuadraticRightLeg 3 2 (by decide) 2 = (1 : ℝ) / 9 := by
  rw [criticalQuadraticLegs_product _ _ _ _ (by norm_num), realDepthMass_eq_one_div_pow]
  norm_num
example : criticalQuadraticBracket 3 2 (by decide) 2 = (1 : ℝ) / 6 := by
  rw [criticalQuadraticBracket_eq_closed, realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : criticalQuadraticBracket 3 2 (by decide) ((1 : ℝ) / 2) = (1 : ℝ) / 6 := by
  rw [criticalQuadraticBracket_eq_closed, realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example : criticalQuadraticLeftLeg 3 2 (by decide) 1 = (1 : ℝ) / 3 ∧
    criticalQuadraticRightLeg 3 2 (by decide) 1 = (1 : ℝ) / 3 ∧
    criticalQuadraticBracket 3 2 (by decide) 1 = 0 := by
  simp only [criticalQuadraticLeftLeg, criticalQuadraticRightLeg, quadraticLeftLeg,
    quadraticRightLeg, reciprocalReflection, inv_one, mul_one]
  rw [criticalQuadraticBracket_eq_closed, realCriticalAmplitude_eq_rpow]
  norm_num [Real.rpow_neg_one]
example (b : ℕ) (hb : 0 < b) {q : ℝ} (hq : 0 < q) :
    criticalQuadraticLeftLeg b 0 hb q * criticalQuadraticRightLeg b 0 hb q = 1 := by
  rw [criticalQuadraticLegs_product _ _ _ _ (ne_of_gt hq), realDepthMass_zero]
example (k : ℕ) {q : ℝ} (hq : 0 < q) :
    criticalQuadraticLeftLeg 1 k Nat.zero_lt_one q *
      criticalQuadraticRightLeg 1 k Nat.zero_lt_one q = 1 := by
  rw [criticalQuadraticLegs_product _ _ _ _ (ne_of_gt hq), realDepthMass_one]
example : quadraticLeftLeg 1 0 * quadraticRightLeg 1 0 ≠ (1 : ℝ) ^ 2 := by
  norm_num [quadraticLeftLeg, quadraticRightLeg, reciprocalReflection]
example : quadraticCenteredBracket 1 0 = -2 := by
  simpa using quadraticCenteredBracket_zero_parameter 1
example : quadraticCenteredBracket 0 2 = 0 := by
  rw [quadraticCenteredBracket_eq_closed]
  norm_num
set_option maxRecDepth 2048 in
example : criticalQuadraticLeftLeg 5 2 (Geometry.oddCapacity_pos ⟨2, rfl⟩) 2 *
    criticalQuadraticRightLeg 5 2 (Geometry.oddCapacity_pos ⟨2, rfl⟩) 2 =
      realizeCountingShare (canonicalResidualDepthMass 5 2 (Geometry.oddCapacity_pos ⟨2, rfl⟩)) := by
  apply balancedCarryDepth_quadraticLegs_product 5 26 2 ⟨2, rfl⟩
  · change (5 : Int) ^ 2 ∣ (25 : Int)
    exact ⟨1, rfl⟩
  · norm_num

-- The following family is a test INPUT, not a canonical law selected for the radii.
example : quadraticCameraBracket 2 ((1 : ℝ) / 3)
    (fun r => if r = 1 then 2 else 3) = (11 : ℝ) / 18 := by
  change (0 + quadraticCenteredBracket ((1 : ℝ) / 3) 2) +
    quadraticCenteredBracket ((1 : ℝ) / 3) 3 = _
  rw [quadraticCenteredBracket_eq_closed, quadraticCenteredBracket_eq_closed]
  norm_num
example : quadraticCameraBracket 2 ((1 : ℝ) / 3)
    (fun r => reciprocalReflection (if r = 1 then 2 else 3)) = (11 : ℝ) / 18 := by
  rw [quadraticCameraBracket_reflection]
  change (0 + quadraticCenteredBracket ((1 : ℝ) / 3) 2) +
    quadraticCenteredBracket ((1 : ℝ) / 3) 3 = _
  rw [quadraticCenteredBracket_eq_closed, quadraticCenteredBracket_eq_closed]
  norm_num
example : quadraticCameraBracket 2 ((1 : ℝ) / 3)
    (reflectCameraPairs (fun r => if r = 1 then 2 else 3) (fun r => r == 1)) = (11 : ℝ) / 18 := by
  rw [quadraticCameraBracket_independent_reflections]
  change (0 + quadraticCenteredBracket ((1 : ℝ) / 3) 2) +
    quadraticCenteredBracket ((1 : ℝ) / 3) 3 = _
  rw [quadraticCenteredBracket_eq_closed, quadraticCenteredBracket_eq_closed]
  norm_num
example : quadraticCameraBracket 2 ((1 : ℝ) / 3) (fun _ => 1) = 0 :=
  (quadraticCameraBracket_zero_iff 2 (by norm_num) _ (fun _ _ _ => by norm_num)).2
    (fun _ _ _ => rfl)
example (q : ℕ → ℝ) : quadraticCameraBracket 0 ((1 : ℝ) / 3) q = 0 ↔
    ∀ r, 1 ≤ r → r ≤ 0 → q r = 1 :=
  quadraticCameraBracket_zero_iff 0 (by norm_num) q (fun r hr hbound => by omega)
example (k : ℕ) (q : ℕ → ℝ) : criticalQuadraticCameraBracket 0 k q = 0 :=
  criticalQuadraticCameraBracket_zero_pairs k q
example : criticalQuadraticCameraBracket 4 2 (fun _ => 2) = (2 : ℝ) / 9 := by
  rw [criticalQuadraticCameraBracket_eq_closed, sumPositiveRadii_real_constant,
    realCriticalAmplitude_eq_rpow]
  norm_num [Geometry.oddCameraCapacity, Real.rpow_neg_one]
example (r : ℕ) (hr : 1 ≤ r) (hbound : r ≤ 2) :
    criticalQuadraticLeftLeg 5 2 (by decide) 2 *
      criticalQuadraticRightLeg 5 2 (by decide) 2 = realDepthMass 5 2 (by decide) :=
  criticalQuadraticCameraPair_product 2 2 (fun _ => 2) r hr hbound (by norm_num)

end GeometryOfNumbers.Analysis
