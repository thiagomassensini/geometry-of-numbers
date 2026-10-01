import GeometryOfNumbers.Analysis
import Lean

/-! Zone B reports standard Mathlib axioms separately from Foundation's empty
footprint. Examples test scalar realization, angular quadratic energy and
reciprocal legs with their derived bracket, not exponent selection or a
physical law for either parameter. -/

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

end GeometryOfNumbers.Analysis
