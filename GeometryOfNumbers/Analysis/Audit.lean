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

-- Coordinate atlas: partition is explicit INPUT; conservation is derived.
#assert_analysis_axioms AtlasBase
#print axioms AtlasBase
#assert_analysis_axioms AdmissibleAtlasPartition
#print axioms AdmissibleAtlasPartition
#assert_analysis_axioms atlasPartition_support_finite
#print axioms atlasPartition_support_finite
#assert_analysis_axioms atlasPartition_finsum_eq_one
#print axioms atlasPartition_finsum_eq_one
#assert_analysis_axioms atlasPartition_support_nonempty
#print axioms atlasPartition_support_nonempty
#assert_analysis_axioms atlasActiveBases
#print axioms atlasActiveBases
#assert_analysis_axioms atlasPartition_support_subset_active
#print axioms atlasPartition_support_subset_active
#assert_analysis_axioms atlasPartition_sum_active_eq_one
#print axioms atlasPartition_sum_active_eq_one
#assert_analysis_axioms atlasCoordinate
#print axioms atlasCoordinate
#assert_analysis_axioms atlasCoordinate_energy
#print axioms atlasCoordinate_energy
#assert_analysis_axioms atlasCoordinate_off_support
#print axioms atlasCoordinate_off_support
#assert_analysis_axioms atlasCoordinate_energy_sum
#print axioms atlasCoordinate_energy_sum
#assert_analysis_axioms atlasCoordinate_energy_finsum
#print axioms atlasCoordinate_energy_finsum
#assert_analysis_axioms atlasCoordinate_energy_sum_active
#print axioms atlasCoordinate_energy_sum_active
#assert_analysis_axioms sumPositiveRadii_finset_sum
#print axioms sumPositiveRadii_finset_sum
#assert_analysis_axioms atlasResolvedEnergy
#print axioms atlasResolvedEnergy
#assert_analysis_axioms atlasResolvedEnergy_eq_input
#print axioms atlasResolvedEnergy_eq_input
#assert_analysis_axioms atlasResolvedEnergy_nonneg
#print axioms atlasResolvedEnergy_nonneg
#assert_analysis_axioms centerLegAtlasEnergy
#print axioms centerLegAtlasEnergy
#assert_analysis_axioms centerLegAtlasEnergy_eq_sum_cameras
#print axioms centerLegAtlasEnergy_eq_sum_cameras
#assert_analysis_axioms centerLegAtlasEnergy_eq_sum_local
#print axioms centerLegAtlasEnergy_eq_sum_local
#assert_analysis_axioms centerLegAtlasEnergy_eq_factor
#print axioms centerLegAtlasEnergy_eq_factor
#assert_analysis_axioms centerLegAtlasEnergy_angle_independent
#print axioms centerLegAtlasEnergy_angle_independent
#assert_analysis_axioms centerLegAtlasEnergy_nonneg
#print axioms centerLegAtlasEnergy_nonneg
#assert_analysis_axioms centerLegAtlasEnergy_zero_iff_local_zero
#print axioms centerLegAtlasEnergy_zero_iff_local_zero
#assert_analysis_axioms centerLegAtlasEnergy_common_eq_resolved
#print axioms centerLegAtlasEnergy_common_eq_resolved
#assert_analysis_axioms centerLegAtlasEnergy_common_eq_input
#print axioms centerLegAtlasEnergy_common_eq_input
#assert_analysis_axioms centerLegAtlasEnergy_common_partition_independent
#print axioms centerLegAtlasEnergy_common_partition_independent
#assert_analysis_axioms centerLegAtlasEnergy_common_zero_iff
#print axioms centerLegAtlasEnergy_common_zero_iff
#assert_analysis_axioms centerLegAtlasEnergy_zero_pairs
#print axioms centerLegAtlasEnergy_zero_pairs
#assert_analysis_axioms centerLegAtlasEnergy_zero_input
#print axioms centerLegAtlasEnergy_zero_input

#assert_analysis_axioms AdmissibleAtlasPartition.weight
#print axioms AdmissibleAtlasPartition.weight
#assert_analysis_axioms AdmissibleAtlasPartition.support
#print axioms AdmissibleAtlasPartition.support
#assert_analysis_axioms AdmissibleAtlasPartition.nonneg
#print axioms AdmissibleAtlasPartition.nonneg
#assert_analysis_axioms AdmissibleAtlasPartition.off_support
#print axioms AdmissibleAtlasPartition.off_support
#assert_analysis_axioms AdmissibleAtlasPartition.sum_eq_one
#print axioms AdmissibleAtlasPartition.sum_eq_one

-- A supplied test partition splits every coordinate between bases 2 and 9.
-- These numerical test weights are NOT a selection from carry geometry.
private noncomputable def atlasTwoBaseTestPartition : AdmissibleAtlasPartition := by
  refine {
    weight := fun b _ => if b = (⟨2, by decide⟩ : AtlasBase) then 1 / 4
      else if b = (⟨9, by decide⟩ : AtlasBase) then 3 / 4 else 0
    support := fun _ => {(⟨2, by decide⟩ : AtlasBase), (⟨9, by decide⟩ : AtlasBase)}
    nonneg := ?_
    off_support := ?_
    sum_eq_one := ?_ }
  · intro b n; split_ifs <;> norm_num
  · intro b n hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [hb.1, hb.2]
  · intro n; norm_num

#assert_analysis_axioms atlasTwoBaseTestPartition
#print axioms atlasTwoBaseTestPartition

-- The interface admits different weight laws; it does not select one.
private def atlasSingleBaseTestPartition (base : AtlasBase) : AdmissibleAtlasPartition where
  weight b _ := if b = base then 1 else 0
  support _ := {base}
  nonneg := by intro b n; split_ifs <;> norm_num
  off_support := by
    intro b n hb
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  sum_eq_one := by intro n; simp

#assert_analysis_axioms atlasSingleBaseTestPartition
#print axioms atlasSingleBaseTestPartition

example : ∃ P₁ P₂ : AdmissibleAtlasPartition,
    P₁.weight ⟨2, by decide⟩ 1 ≠ P₂.weight ⟨2, by decide⟩ 1 := by
  refine ⟨atlasSingleBaseTestPartition ⟨2, by decide⟩,
    atlasSingleBaseTestPartition ⟨9, by decide⟩, ?_⟩
  norm_num [atlasSingleBaseTestPartition]

example : atlasCoordinate atlasTwoBaseTestPartition ⟨2, by decide⟩ 1 (2, 0) = (1, 0) := by
  have hs : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [atlasCoordinate, atlasTwoBaseTestPartition, scaleRealPlane,
    Real.sqrt_div, hs]

example (theta : AtlasBase → Nat → ℝ) :
    centerLegAtlasEnergy atlasTwoBaseTestPartition 2 (fun _ _ => 2) theta
      (fun r => if r = 1 then (3, 4) else (0, 2)) = 29 / 4 := by
  rw [centerLegAtlasEnergy_common_eq_input _ _ _ _ _ (by norm_num)]
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy]

-- Positive total energy; a zero input channel and zero-weight bases are allowed.
example (P : AdmissibleAtlasPartition) (theta : AtlasBase → Nat → ℝ)
    (q : ℝ) (hq : 0 < q) :
    centerLegAtlasEnergy P 2 (fun _ _ => q) theta
      (fun r => if r = 1 then (0, 0) else (1, 0)) = 0 ↔ q = 1 := by
  apply centerLegAtlasEnergy_common_zero_iff _ _ _ _ _ (ne_of_gt hq)
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy]

example (P : AdmissibleAtlasPartition) (theta : AtlasBase → Nat → ℝ) :
    centerLegAtlasEnergy P 0 (fun _ _ => 2) theta (fun _ => (1, 0)) = 0 ∧
      (2 : ℝ) ≠ 1 := ⟨centerLegAtlasEnergy_zero_pairs _ _ _ _, by norm_num⟩

example (P : AdmissibleAtlasPartition) (theta : AtlasBase → Nat → ℝ) :
    centerLegAtlasEnergy P 2 (fun _ _ => 2) theta (fun _ => (0, 0)) = 0 :=
  centerLegAtlasEnergy_zero_input _ _ _ _

-- The quotient form deliberately excludes q=0; the actual readout has energy 4.
example (P : AdmissibleAtlasPartition) (theta : AtlasBase → Nat → ℝ) :
    centerLegAtlasEnergy P 1 (fun _ _ => 0) theta (fun _ => (1, 0)) = 4 := by
  rw [centerLegAtlasEnergy_eq_sum_local, sumPositiveRadii_finset_sum]
  simp only [Geometry.sumPositiveRadii, zero_add, centerLegForm_energy_eq_closed,
    inv_zero, add_zero, zero_sub, neg_sq, atlasCoordinate_energy]
  have h := atlasPartition_sum_active_eq_one P 1 1 (by decide) (by decide)
  simp only [realPlaneEnergy, one_pow, zero_pow (by decide : 2 ≠ 0), add_zero, mul_one]
  rw [← Finset.mul_sum, h]
  norm_num


-- Resolved camera energy: sum AFTER each local vector's quadratic readout.
#assert_analysis_axioms centerLegCameraEnergy
#assert_analysis_axioms centerLegCameraEnergy_eq_sum_local
#assert_analysis_axioms centerLegCameraEnergy_eq_factor
#assert_analysis_axioms centerLegCameraEnergy_angle_independent
#assert_analysis_axioms realPlaneEnergy_nonneg
#assert_analysis_axioms centerLegCameraEnergy_nonneg
#assert_analysis_axioms centerLegCameraEnergy_zero_iff_local_zero
#assert_analysis_axioms centerLegCameraEnergy_zero_iff
#assert_analysis_axioms centerLegCameraEnergy_zero_pairs
#assert_analysis_axioms centerLegCameraEnergy_common_eq_factor
#assert_analysis_axioms centerLegCameraEnergy_common_zero_iff
#assert_analysis_axioms centerLegForm_energy_eq_unitBracket
#assert_analysis_axioms centerLegCameraEnergy_eq_sum_sq_brackets
#assert_analysis_axioms centerLegCameraEnergy_zero_iff_quadraticCameraBracket_zero
#assert_analysis_axioms centerLegCameraEnergy_criticalSeed_eq_mass
#assert_analysis_axioms centerLegCameraEnergy_criticalSeed_common_eq_mass
#print axioms centerLegCameraEnergy
#print axioms centerLegCameraEnergy_eq_sum_local
#print axioms centerLegCameraEnergy_eq_factor
#print axioms centerLegCameraEnergy_angle_independent
#print axioms realPlaneEnergy_nonneg
#print axioms centerLegCameraEnergy_nonneg
#print axioms centerLegCameraEnergy_zero_iff_local_zero
#print axioms centerLegCameraEnergy_zero_iff
#print axioms centerLegCameraEnergy_zero_pairs
#print axioms centerLegCameraEnergy_common_eq_factor
#print axioms centerLegCameraEnergy_common_zero_iff
#print axioms centerLegForm_energy_eq_unitBracket
#print axioms centerLegCameraEnergy_eq_sum_sq_brackets
#print axioms centerLegCameraEnergy_zero_iff_quadraticCameraBracket_zero
#print axioms centerLegCameraEnergy_criticalSeed_eq_mass
#print axioms centerLegCameraEnergy_criticalSeed_common_eq_mass

-- Different states and arbitrary local angles, with one common radial factor.
example (theta : Nat → ℝ) : centerLegCameraEnergy 2 (fun _ => 2) theta
    (fun r => if r = 1 then (3, 4) else (0, 2)) = 29 / 4 := by
  rw [centerLegCameraEnergy_common_eq_factor _ _ _ _ (by norm_num)]
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy]

-- A common defect needs positive TOTAL energy; a zero-energy channel is allowed.
example (q : ℝ) (hq : 0 < q) (theta : Nat → ℝ) :
    centerLegCameraEnergy 2 (fun _ => q) theta
      (fun r => if r = 1 then (0, 0) else (1, 0)) = 0 ↔ q = 1 := by
  apply centerLegCameraEnergy_common_zero_iff _ _ _ _ (ne_of_gt hq)
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy]

example (theta : Nat → ℝ) : centerLegCameraEnergy 2
    (fun r => if r = 1 then 2 else 3) theta
    (fun _ => realCriticalDepthSeed 3 2 (by decide)) = 73 / 324 := by
  rw [centerLegCameraEnergy_criticalSeed_eq_mass _ _ _ _ _ _ (by
    intro r _ _
    split_ifs <;> norm_num), realDepthMass_eq_one_div_pow]
  norm_num [Geometry.sumPositiveRadii]

example (theta : Nat → ℝ) : centerLegCameraEnergy 4 (fun _ => 2) theta
    (fun _ => realCriticalDepthSeed 9 2 (by decide)) = 1 / 81 := by
  rw [centerLegCameraEnergy_criticalSeed_common_eq_mass _ _ _ _ _ _ (by norm_num),
    realDepthMass_eq_one_div_pow]
  norm_num

-- An unobserved state cannot identify its local radial parameter.
example (theta : Nat → ℝ) : centerLegCameraEnergy 2
    (fun r => if r = 1 then 2 else 1) theta
    (fun r => if r = 1 then (0, 0) else (1, 0)) = 0 := by
  rw [centerLegCameraEnergy_eq_factor _ _ _ _ (by
    intro r _ _
    split_ifs <;> norm_num)]
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy]

example (theta : Nat → ℝ) :
    centerLegCameraEnergy 0 (fun _ => 2) theta (fun _ => (1, 0)) = 0 ∧ (2 : ℝ) ≠ 1 :=
  ⟨centerLegCameraEnergy_zero_pairs _ _ _, by norm_num⟩

-- Scalarizing the vector sum first can cancel two nonzero local defects.
example :
    let D₁ := centerLegForm 2 0 (2, 0)
    let D₂ := centerLegForm 2 0 (-2, 0)
    realPlaneEnergy D₁ + realPlaneEnergy D₂ = 2 ∧
      realPlaneEnergy (D₁ + D₂) = 0 ∧
      realPlaneEnergy D₁ + realPlaneEnergy D₂ ≠ realPlaneEnergy (D₁ + D₂) := by
  norm_num [centerLegForm_eq_closed, rotateRealPlane_zero, scaleRealPlane, realPlaneEnergy]

-- Sum of squared local brackets is not the square of the scalar camera bracket.
example : centerLegCameraEnergy 2 (fun _ => 2) (fun _ => 0) (fun _ => (1, 0)) ≠
    quadraticCameraBracket 2 1 (fun _ => 2) ^ 2 := by
  rw [centerLegCameraEnergy_common_eq_factor _ _ _ _ (by norm_num)]
  norm_num [Geometry.sumPositiveRadii, realPlaneEnergy, quadraticCameraBracket,
    quadraticCenteredBracket_eq_closed]

-- Vector center-leg synthesis precedes its quadratic energy readout.
#assert_analysis_axioms scaleRealPlane
#assert_analysis_axioms realPlaneCenteredReadout
#assert_analysis_axioms centerLegFormLeftLeg
#assert_analysis_axioms centerLegFormRightLeg
#assert_analysis_axioms centerLegForm
#assert_analysis_axioms centerLegForm_eq_closed
#assert_analysis_axioms centerLegForm_eq_factor
#assert_analysis_axioms scaleRealPlane_energy
#assert_analysis_axioms centerLegForm_energy_eq_closed
#assert_analysis_axioms centerLegForm_energy_eq_factor
#assert_analysis_axioms centerLegForm_energy_eq_fourth
#assert_analysis_axioms centerLegForm_energy_angle_independent
#assert_analysis_axioms centerLegForm_energy_zero_iff
#assert_analysis_axioms centerLegForm_criticalSeed_eq_factor
#assert_analysis_axioms centerLegForm_criticalSeed_energy_eq_amplitude_sq
#assert_analysis_axioms centerLegForm_criticalSeed_energy_eq_mass
#print axioms scaleRealPlane
#print axioms realPlaneCenteredReadout
#print axioms centerLegFormLeftLeg
#print axioms centerLegFormRightLeg
#print axioms centerLegForm
#print axioms centerLegForm_eq_closed
#print axioms centerLegForm_eq_factor
#print axioms scaleRealPlane_energy
#print axioms centerLegForm_energy_eq_closed
#print axioms centerLegForm_energy_eq_factor
#print axioms centerLegForm_energy_eq_fourth
#print axioms centerLegForm_energy_angle_independent
#print axioms centerLegForm_energy_zero_iff
#print axioms centerLegForm_criticalSeed_eq_factor
#print axioms centerLegForm_criticalSeed_energy_eq_amplitude_sq
#print axioms centerLegForm_criticalSeed_energy_eq_mass

example : centerLegForm 2 0 (3, 4) = (3 / 2, 2) := by
  rw [centerLegForm_eq_factor _ _ _ (by norm_num), rotateRealPlane_zero]
  norm_num [scaleRealPlane]

example (theta : ℝ) : realPlaneEnergy (centerLegForm 2 theta (3, 4)) = 25 / 4 := by
  rw [centerLegForm_energy_eq_fourth _ _ _ (by norm_num)]
  norm_num [realPlaneEnergy]

example (theta : ℝ) : realPlaneEnergy (centerLegForm (1 / 2) theta (3, 4)) = 25 / 4 := by
  rw [centerLegForm_energy_eq_fourth _ _ _ (by norm_num)]
  norm_num [realPlaneEnergy]

example (theta : ℝ) {q : ℝ} (hq : 0 < q) :
    realPlaneEnergy (centerLegForm q theta (3, 4)) = 0 ↔ q = 1 :=
  centerLegForm_energy_zero_iff q theta _ hq (by norm_num [realPlaneEnergy])

example (theta : ℝ) :
    realPlaneEnergy (centerLegForm 2 theta (realCriticalDepthSeed 3 2 (by decide))) = 1 / 36 := by
  rw [centerLegForm_criticalSeed_energy_eq_mass _ _ _ _ _ (by norm_num),
    realDepthMass_eq_one_div_pow]
  norm_num

-- Positive initial energy is essential for the zero criterion.
example (theta : ℝ) : realPlaneEnergy (centerLegForm 2 theta (0, 0)) = 0 ∧ (2 : ℝ) ≠ 1 := by
  rw [centerLegForm_energy_eq_closed]
  norm_num [realPlaneEnergy]

-- Total inversion at zero does not satisfy the nonzero quotient formula.
example (theta : ℝ) : realPlaneEnergy (centerLegForm 0 theta (3, 4)) = 100 := by
  rw [centerLegForm_energy_eq_closed]
  norm_num [realPlaneEnergy]

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


-- Prime quantity voices: depth is represented downstream; no channel identification.
#assert_analysis_axioms primeResidualDepth_iff_le_factorization
#print axioms primeResidualDepth_iff_le_factorization
#assert_analysis_axioms primeResidualDepth_factorization_characterized
#print axioms primeResidualDepth_factorization_characterized
#assert_analysis_axioms primeResidualDepth_one_iff
#print axioms primeResidualDepth_one_iff
#assert_analysis_axioms primeResidualDepth_zero_obstruction
#print axioms primeResidualDepth_zero_obstruction
#assert_analysis_axioms primeResidualDepth_reconstruction
#print axioms primeResidualDepth_reconstruction
#assert_analysis_axioms primeResidualDepth_quantity_ext
#print axioms primeResidualDepth_quantity_ext
#assert_analysis_axioms primeCarryVoice
#print axioms primeCarryVoice
#assert_analysis_axioms primeCarryVoice_eq_of_residual_thresholds
#print axioms primeCarryVoice_eq_of_residual_thresholds
#assert_analysis_axioms primeCarryVoice_nonneg
#print axioms primeCarryVoice_nonneg
#assert_analysis_axioms primeCarryVoice_off_support
#print axioms primeCarryVoice_off_support
#assert_analysis_axioms primeCarryVoice_nonprime
#print axioms primeCarryVoice_nonprime
#assert_analysis_axioms log_eq_sum_primeCarryVoice
#print axioms log_eq_sum_primeCarryVoice
#assert_analysis_axioms primeVoiceWeight
#print axioms primeVoiceWeight
#assert_analysis_axioms primeVoiceWeight_nonneg
#print axioms primeVoiceWeight_nonneg
#assert_analysis_axioms primeVoiceWeight_off_support
#print axioms primeVoiceWeight_off_support
#assert_analysis_axioms primeVoiceWeight_nonprime
#print axioms primeVoiceWeight_nonprime
#assert_analysis_axioms primeVoiceWeight_support_finite
#print axioms primeVoiceWeight_support_finite
#assert_analysis_axioms primeVoiceWeight_sum_eq_one
#print axioms primeVoiceWeight_sum_eq_one
#assert_analysis_axioms primeVoiceWeight_finsum_eq_one
#print axioms primeVoiceWeight_finsum_eq_one
#assert_analysis_axioms primeVoiceWeight_prime_pow
#print axioms primeVoiceWeight_prime_pow
#assert_analysis_axioms primeVoiceWeight_prime
#print axioms primeVoiceWeight_prime
#assert_analysis_axioms primeCarryVoice_one
#print axioms primeCarryVoice_one
#assert_analysis_axioms primeVoiceWeight_one
#print axioms primeVoiceWeight_one
#assert_analysis_axioms primeVoiceWeight_one_sum
#print axioms primeVoiceWeight_one_sum
#assert_analysis_axioms primeVoiceWeight_one_finsum
#print axioms primeVoiceWeight_one_finsum
#assert_analysis_axioms primeVoiceWeight_no_total_atlas_partition
#print axioms primeVoiceWeight_no_total_atlas_partition

-- The prime threshold crosswalk includes base 2, odd primes and level zero.
example : (12 : Nat).factorization 2 = 2 ∧ (12 : Nat).factorization 3 = 1 := by
  have h12 : (12 : Nat).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    rw [show (12 : Nat) = 2 ^ 2 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3)]
  simp [h12]

example : Geometry.HasCarryDepthAtLeast 2 12 2 ∧
    ¬ Geometry.HasCarryDepthAtLeast 2 12 3 ∧
    Geometry.HasCarryDepthAtLeast 3 12 1 ∧
    ¬ Geometry.HasCarryDepthAtLeast 3 12 2 := by
  rw [Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 12 2 (by decide),
    Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 12 3 (by decide),
    Geometry.hasCarryDepthAtLeast_iff_dvd_pow 3 12 1 (by decide),
    Geometry.hasCarryDepthAtLeast_iff_dvd_pow 3 12 2 (by decide)]
  decide

example (p n : Nat) (hp : Nat.Prime p) (hn : n ≠ 0) :
    Geometry.HasCarryDepthAtLeast p n 0 :=
  (primeResidualDepth_iff_le_factorization hp hn).2 (Nat.zero_le _)

example (p k : Nat) (hp : Nat.Prime p) :
    Geometry.HasCarryDepthAtLeast p 1 k ↔ k = 0 := primeResidualDepth_one_iff hp

example (p : Nat) (hp : Nat.Prime p) :
    Geometry.HasCarryDepthAtLeast p 0 1 ∧ ¬ 1 ≤ (0 : Nat).factorization p :=
  primeResidualDepth_zero_obstruction hp

example : 2 * Real.log 2 + Real.log 3 = Real.log 12 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 from by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num

example : primeVoiceWeight 12 2 = 2 * Real.log 2 / Real.log 12 ∧
    primeVoiceWeight 12 3 = Real.log 3 / Real.log 12 := by
  have h12 : (12 : Nat).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    rw [show (12 : Nat) = 2 ^ 2 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3)]
  norm_num [primeVoiceWeight, primeCarryVoice, h12]

example : primeVoiceWeight 12 2 + primeVoiceWeight 12 3 = 1 := by
  have h12 : (12 : Nat).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    rw [show (12 : Nat) = 2 ^ 2 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3)]
  have hs := primeVoiceWeight_sum_eq_one (n := 12) (by decide)
  have hsupport : (12 : Nat).factorization.support = {2, 3} := by
    rw [h12]
    ext p
    by_cases h2 : p = 2 <;> by_cases h3 : p = 3 <;>
      simp_all [Finsupp.mem_support_iff]
  rw [hsupport] at hs
  simpa using hs

example : primeVoiceWeight 64 2 = 1 := by
  rw [show (64 : Nat) = 2 ^ 6 from rfl]
  exact primeVoiceWeight_prime_pow (p := 2) (k := 6) (by decide) (by decide)

example : ∀ p, p ≠ 2 → primeVoiceWeight 64 p = 0 := by
  intro p hp
  apply primeVoiceWeight_off_support
  change p ∉ (2 ^ 6 : Nat).factorization.support
  rw [Nat.Prime.factorization_pow (by decide : Nat.Prime 2)]
  simpa using hp

example : primeVoiceWeight 5 5 = 1 := primeVoiceWeight_prime (by decide)

-- Composite cameras still exist, but composite labels are not prime voices.
example : primeVoiceWeight 12 4 = 0 := primeVoiceWeight_nonprime (by decide)

-- Quantity one has no prime voice: Lean's total division returns zero,
-- which fails the unit sum and supplies no seed camera.
example : (1 : Nat).factorization.support = ∅ ∧ Real.log (1 : ℝ) = 0 ∧
    (∑ᶠ p : Nat, primeVoiceWeight 1 p) = 0 := by
  simp [primeVoiceWeight_one]

example : ¬ ∃ P : AdmissibleAtlasPartition,
    ∀ (b : AtlasBase) (n : Nat), P.weight b n = primeVoiceWeight n b.val :=
  primeVoiceWeight_no_total_atlas_partition

end GeometryOfNumbers.Analysis

-- R2 audit coverage

namespace GeometryOfNumbers.Analysis.DiscreteValve
#assert_analysis_axioms fdiff
#print axioms fdiff
#assert_analysis_axioms bracket
#print axioms bracket
#assert_analysis_axioms bracket_eq_fdiff_sub
#print axioms bracket_eq_fdiff_sub
#assert_analysis_axioms greenSum
#print axioms greenSum
#assert_analysis_axioms sum_range_bracket
#print axioms sum_range_bracket
#assert_analysis_axioms greenSum_succ
#print axioms greenSum_succ
#assert_analysis_axioms realDiscreteGreenReconstruction
#print axioms realDiscreteGreenReconstruction
#assert_analysis_axioms bracket_greenSum
#print axioms bracket_greenSum
#assert_analysis_axioms greenSum_zero
#print axioms greenSum_zero
#assert_analysis_axioms bracket_eq_zero_iff_affine
#print axioms bracket_eq_zero_iff_affine
#assert_analysis_axioms bracket_add
#print axioms bracket_add
#assert_analysis_axioms greenSum_add
#print axioms greenSum_add
#assert_analysis_axioms bracket_eq_realCenteredReadout
#print axioms bracket_eq_realCenteredReadout
#assert_analysis_axioms X_mul_mk_fdiff
#print axioms X_mul_mk_fdiff
#assert_analysis_axioms X_sq_mul_mk_bracket
#print axioms X_sq_mul_mk_bracket
#assert_analysis_axioms geometricSeries
#print axioms geometricSeries
#assert_analysis_axioms greenKernelSeries
#print axioms greenKernelSeries
#assert_analysis_axioms one_sub_X_mul_geometricSeries
#print axioms one_sub_X_mul_geometricSeries
#assert_analysis_axioms one_sub_X_mul_greenKernelSeries
#print axioms one_sub_X_mul_greenKernelSeries
#assert_analysis_axioms one_sub_X_sq_mul_greenKernelSeries
#print axioms one_sub_X_sq_mul_greenKernelSeries
#assert_analysis_axioms X_mul_greenKernelSeries
#print axioms X_mul_greenKernelSeries
#assert_analysis_axioms mk_greenSum
#print axioms mk_greenSum
#assert_analysis_axioms mk_discrete_valve
#print axioms mk_discrete_valve
end GeometryOfNumbers.Analysis.DiscreteValve

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms causalUnitBracket
#print axioms causalUnitBracket
#assert_analysis_axioms rightLeg_eq_bracket_sub_left_add_two_center
#print axioms rightLeg_eq_bracket_sub_left_add_two_center
#assert_analysis_axioms rightLeg_eq_of_left_center_bracket_eq
#print axioms rightLeg_eq_of_left_center_bracket_eq
#assert_analysis_axioms CausalBracketData
#print axioms CausalBracketData
#assert_analysis_axioms causalBracketReconstruction
#print axioms causalBracketReconstruction
#assert_analysis_axioms causalBracketReconstruction_zero
#print axioms causalBracketReconstruction_zero
#assert_analysis_axioms causalBracketReconstruction_one
#print axioms causalBracketReconstruction_one
#assert_analysis_axioms causalBracketReconstruction_step
#print axioms causalBracketReconstruction_step
#assert_analysis_axioms causalUnitBracket_reconstruction
#print axioms causalUnitBracket_reconstruction
#assert_analysis_axioms eq_of_seed_eq_of_causalUnitBracket_eq
#print axioms eq_of_seed_eq_of_causalUnitBracket_eq
#assert_analysis_axioms criticalVerticalAmplitudeRatio
#print axioms criticalVerticalAmplitudeRatio
#assert_analysis_axioms criticalVerticalAmplitudeRatio_eq_rpow
#print axioms criticalVerticalAmplitudeRatio_eq_rpow
#assert_analysis_axioms criticalVerticalAmplitudeRatio_pos
#print axioms criticalVerticalAmplitudeRatio_pos
#assert_analysis_axioms criticalVerticalAmplitudeRatio_lt_one
#print axioms criticalVerticalAmplitudeRatio_lt_one
#assert_analysis_axioms realCriticalAmplitude_eq_verticalRatio_pow
#print axioms realCriticalAmplitude_eq_verticalRatio_pow
#assert_analysis_axioms realCriticalAmplitude_succ_verticalRatio
#print axioms realCriticalAmplitude_succ_verticalRatio
#assert_analysis_axioms realCarryAmplitudeGauge
#print axioms realCarryAmplitudeGauge
#assert_analysis_axioms realCarryWeightedFirstDifference_gauge
#print axioms realCarryWeightedFirstDifference_gauge
#assert_analysis_axioms realCarryWeightedSecondDifference_gauge
#print axioms realCarryWeightedSecondDifference_gauge
#assert_analysis_axioms realCarryWeightedGreenSum_gauge
#print axioms realCarryWeightedGreenSum_gauge
#assert_analysis_axioms realCarryTfvdAnalysis
#print axioms realCarryTfvdAnalysis
#assert_analysis_axioms realCarryTfvdSynthesis
#print axioms realCarryTfvdSynthesis
#assert_analysis_axioms realCarryTfvdSynthesis_comp_analysis
#print axioms realCarryTfvdSynthesis_comp_analysis
#assert_analysis_axioms realCriticalCarryTfvd_identity
#print axioms realCriticalCarryTfvd_identity
#assert_analysis_axioms realCriticalCarryTfvdSynthesis_comp_analysis
#print axioms realCriticalCarryTfvdSynthesis_comp_analysis
#assert_analysis_axioms RealCriticalCarryTfvdGreenValveCertificate
#print axioms RealCriticalCarryTfvdGreenValveCertificate
#assert_analysis_axioms realCriticalCarryTfvdGreenValveCapstone
#print axioms realCriticalCarryTfvdGreenValveCapstone
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis.TowerValve
#assert_analysis_axioms IsTowerChannel
#print axioms IsTowerChannel
#assert_analysis_axioms tower_channel_unique
#print axioms tower_channel_unique
#assert_analysis_axioms IsLogDerivChannel
#print axioms IsLogDerivChannel
#assert_analysis_axioms isLogDerivChannel_mul
#print axioms isLogDerivChannel_mul
#assert_analysis_axioms isTowerChannel_iff_isLogDerivChannel
#print axioms isTowerChannel_iff_isLogDerivChannel
#assert_analysis_axioms towerMass
#print axioms towerMass
#assert_analysis_axioms towerMass_zero
#print axioms towerMass_zero
#assert_analysis_axioms isTowerChannel_towerMass
#print axioms isTowerChannel_towerMass
#assert_analysis_axioms towerMass_unique
#print axioms towerMass_unique
#assert_analysis_axioms towerMass_eq_of_isTowerChannel
#print axioms towerMass_eq_of_isTowerChannel
#assert_analysis_axioms expSeries
#print axioms expSeries
#assert_analysis_axioms isLogDerivChannel_expSeries
#print axioms isLogDerivChannel_expSeries
#assert_analysis_axioms constantCoeff_expSeries
#print axioms constantCoeff_expSeries
#assert_analysis_axioms logIntegral
#print axioms logIntegral
#assert_analysis_axioms constantCoeff_logIntegral
#print axioms constantCoeff_logIntegral
#assert_analysis_axioms X_mul_derivativeFun_logIntegral
#print axioms X_mul_derivativeFun_logIntegral
#assert_analysis_axioms mk_towerMass_eq_expSeries
#print axioms mk_towerMass_eq_expSeries
#assert_analysis_axioms canonicalTowerChannel
#print axioms canonicalTowerChannel
#assert_analysis_axioms canonicalTowerChannel_eq
#print axioms canonicalTowerChannel_eq
#assert_analysis_axioms canonicalTowerChannel_zero
#print axioms canonicalTowerChannel_zero
#assert_analysis_axioms canonicalTowerChannel_isTowerChannel
#print axioms canonicalTowerChannel_isTowerChannel
#assert_analysis_axioms canonicalTowerChannel_eq_of_isTowerChannel
#print axioms canonicalTowerChannel_eq_of_isTowerChannel
#assert_analysis_axioms existsUnique_towerChannel
#print axioms existsUnique_towerChannel
#assert_analysis_axioms towerMass_canonicalTowerChannel
#print axioms towerMass_canonicalTowerChannel
#assert_analysis_axioms canonicalTowerChannel_towerMass
#print axioms canonicalTowerChannel_towerMass
#assert_analysis_axioms mk_eq_expSeries_logIntegral_canonicalTowerChannel
#print axioms mk_eq_expSeries_logIntegral_canonicalTowerChannel
end GeometryOfNumbers.Analysis.TowerValve

namespace GeometryOfNumbers.Analysis.ProjectiveDepth
#assert_analysis_axioms coordinate
#print axioms coordinate
#assert_analysis_axioms coordinate_constantCoeff
#print axioms coordinate_constantCoeff
#assert_analysis_axioms one_sub_X_mul_coordinate
#print axioms one_sub_X_mul_coordinate
#assert_analysis_axioms one_add_coordinate_eq_geometricSeries
#print axioms one_add_coordinate_eq_geometricSeries
#assert_analysis_axioms geometricSeries_mul_self_eq_greenKernelSeries
#print axioms geometricSeries_mul_self_eq_greenKernelSeries
#assert_analysis_axioms coordinate_derivativeFun
#print axioms coordinate_derivativeFun
#assert_analysis_axioms greenVelocity
#print axioms greenVelocity
#assert_analysis_axioms euler_coordinate
#print axioms euler_coordinate
#assert_analysis_axioms greenVelocity_eq_coordinate_mul_one_add
#print axioms greenVelocity_eq_coordinate_mul_one_add
#assert_analysis_axioms coordinate_sq_eq_X_sq_mul_greenKernelSeries
#print axioms coordinate_sq_eq_X_sq_mul_greenKernelSeries
#assert_analysis_axioms euler_subst_coordinate
#print axioms euler_subst_coordinate
#assert_analysis_axioms inverseGeometricSeries
#print axioms inverseGeometricSeries
#assert_analysis_axioms one_add_X_mul_inverseGeometricSeries
#print axioms one_add_X_mul_inverseGeometricSeries
#assert_analysis_axioms inverseCoordinate
#print axioms inverseCoordinate
#assert_analysis_axioms inverseCoordinate_constantCoeff
#print axioms inverseCoordinate_constantCoeff
#assert_analysis_axioms one_add_X_mul_inverseCoordinate
#print axioms one_add_X_mul_inverseCoordinate
#assert_analysis_axioms one_sub_inverseCoordinate_eq_inverseGeometricSeries
#print axioms one_sub_inverseCoordinate_eq_inverseGeometricSeries
#assert_analysis_axioms coordinate_hasSubst
#print axioms coordinate_hasSubst
#assert_analysis_axioms inverseCoordinate_hasSubst
#print axioms inverseCoordinate_hasSubst
#assert_analysis_axioms coordinate_subst_inverseCoordinate
#print axioms coordinate_subst_inverseCoordinate
#assert_analysis_axioms inverseCoordinate_subst_coordinate
#print axioms inverseCoordinate_subst_coordinate
#assert_analysis_axioms subst_X_eq_self
#print axioms subst_X_eq_self
#assert_analysis_axioms toProjective
#print axioms toProjective
#assert_analysis_axioms fromProjective
#print axioms fromProjective
#assert_analysis_axioms fromProjective_toProjective
#print axioms fromProjective_toProjective
#assert_analysis_axioms toProjective_fromProjective
#print axioms toProjective_fromProjective
#assert_analysis_axioms coordinateChangeEquiv
#print axioms coordinateChangeEquiv
#assert_analysis_axioms toProjective_add
#print axioms toProjective_add
#assert_analysis_axioms toProjective_mul
#print axioms toProjective_mul
#assert_analysis_axioms fromProjective_add
#print axioms fromProjective_add
#assert_analysis_axioms fromProjective_mul
#print axioms fromProjective_mul
#assert_analysis_axioms coordinate_inverse_jacobian
#print axioms coordinate_inverse_jacobian
#assert_analysis_axioms inverse_coordinate_jacobian
#print axioms inverse_coordinate_jacobian
#assert_analysis_axioms greenKernel_subst_inverse_mul_inverseDerivative
#print axioms greenKernel_subst_inverse_mul_inverseDerivative
#assert_analysis_axioms inverseDerivative_subst_coordinate_mul_greenKernel
#print axioms inverseDerivative_subst_coordinate_mul_greenKernel
#assert_analysis_axioms constantCoeff_toProjective
#print axioms constantCoeff_toProjective
end GeometryOfNumbers.Analysis.ProjectiveDepth

namespace GeometryOfNumbers.Analysis.GreenValve
#assert_analysis_axioms greenChannelSeries
#print axioms greenChannelSeries
#assert_analysis_axioms greenChannel
#print axioms greenChannel
#assert_analysis_axioms greenChannel_zero
#print axioms greenChannel_zero
#assert_analysis_axioms mk_greenChannel
#print axioms mk_greenChannel
#assert_analysis_axioms greenLogPotential
#print axioms greenLogPotential
#assert_analysis_axioms greenLogPotential_constantCoeff
#print axioms greenLogPotential_constantCoeff
#assert_analysis_axioms X_mul_derivative_greenLogPotential
#print axioms X_mul_derivative_greenLogPotential
#assert_analysis_axioms derivative_greenLogPotential
#print axioms derivative_greenLogPotential
#assert_analysis_axioms derivative_toProjective_greenLogPotential
#print axioms derivative_toProjective_greenLogPotential
#assert_analysis_axioms greenMassSeries
#print axioms greenMassSeries
#assert_analysis_axioms greenMassSeries_constantCoeff
#print axioms greenMassSeries_constantCoeff
#assert_analysis_axioms isLogDerivChannel_greenMassSeries
#print axioms isLogDerivChannel_greenMassSeries
#assert_analysis_axioms mk_towerMass_greenChannel
#print axioms mk_towerMass_greenChannel
#assert_analysis_axioms derivative_greenMassSeries
#print axioms derivative_greenMassSeries
#assert_analysis_axioms projectiveGreenMass
#print axioms projectiveGreenMass
#assert_analysis_axioms projectiveGreenMass_constantCoeff
#print axioms projectiveGreenMass_constantCoeff
#assert_analysis_axioms derivative_projectiveGreenMass
#print axioms derivative_projectiveGreenMass
end GeometryOfNumbers.Analysis.GreenValve

namespace GeometryOfNumbers.Analysis.ProjectiveValve
#assert_analysis_axioms projectiveValveMass
#print axioms projectiveValveMass
#assert_analysis_axioms projectiveValveMass_constantCoeff
#print axioms projectiveValveMass_constantCoeff
#assert_analysis_axioms derivative_projectiveValveMass
#print axioms derivative_projectiveValveMass
#assert_analysis_axioms normalized_projective_ode_unique
#print axioms normalized_projective_ode_unique
#assert_analysis_axioms projectiveValveMass_unique
#print axioms projectiveValveMass_unique
#assert_analysis_axioms existsUnique_projectiveValveMass
#print axioms existsUnique_projectiveValveMass
#assert_analysis_axioms projectiveValveMass_toProjective
#print axioms projectiveValveMass_toProjective
#assert_analysis_axioms projectiveValveCurvature
#print axioms projectiveValveCurvature
#assert_analysis_axioms projectiveValveCurvature_mul_self
#print axioms projectiveValveCurvature_mul_self
#assert_analysis_axioms projectiveValveCurvature_eq_of_ode
#print axioms projectiveValveCurvature_eq_of_ode
#assert_analysis_axioms projectiveValveCurvature_projectiveValveMass
#print axioms projectiveValveCurvature_projectiveValveMass
#assert_analysis_axioms projectiveValveMass_projectiveValveCurvature
#print axioms projectiveValveMass_projectiveValveCurvature
#assert_analysis_axioms NormalizedProjectiveMass
#print axioms NormalizedProjectiveMass
#assert_analysis_axioms projectiveValveEquiv
#print axioms projectiveValveEquiv
#assert_analysis_axioms projectiveValveMass_injective
#print axioms projectiveValveMass_injective
#assert_analysis_axioms projectiveValveCurvature_surjective
#print axioms projectiveValveCurvature_surjective
#assert_analysis_axioms projectiveValveMass_zero
#print axioms projectiveValveMass_zero
#assert_analysis_axioms projectiveValveMass_add
#print axioms projectiveValveMass_add
end GeometryOfNumbers.Analysis.ProjectiveValve

namespace GeometryOfNumbers.Analysis.DiscreteProjective
#assert_analysis_axioms discreteBracket_eq_causalUnitBracket
#print axioms discreteBracket_eq_causalUnitBracket
#assert_analysis_axioms ReconstructionData
#print axioms ReconstructionData
#assert_analysis_axioms reconstructionBracketData
#print axioms reconstructionBracketData
#assert_analysis_axioms reconstruct
#print axioms reconstruct
#assert_analysis_axioms reconstruct_zero
#print axioms reconstruct_zero
#assert_analysis_axioms reconstruct_fdiff_zero
#print axioms reconstruct_fdiff_zero
#assert_analysis_axioms bracket_reconstruct
#print axioms bracket_reconstruct
#assert_analysis_axioms mk_bracket_reconstruct
#print axioms mk_bracket_reconstruct
#assert_analysis_axioms mk_reconstruct_eq_green
#print axioms mk_reconstruct_eq_green
#assert_analysis_axioms stateMass
#print axioms stateMass
#assert_analysis_axioms stateMass_eq_projectiveGreenMass
#print axioms stateMass_eq_projectiveGreenMass
#assert_analysis_axioms stateMass_constantCoeff
#print axioms stateMass_constantCoeff
#assert_analysis_axioms projectiveValveCurvature_stateMass
#print axioms projectiveValveCurvature_stateMass
#assert_analysis_axioms stateMass_eq_iff_bracket_eq
#print axioms stateMass_eq_iff_bracket_eq
#assert_analysis_axioms eq_of_boundary_and_stateMass_eq
#print axioms eq_of_boundary_and_stateMass_eq
#assert_analysis_axioms eq_iff_boundary_and_stateMass_eq
#print axioms eq_iff_boundary_and_stateMass_eq
#assert_analysis_axioms stateMass_reconstruct
#print axioms stateMass_reconstruct
#assert_analysis_axioms encode
#print axioms encode
#assert_analysis_axioms reconstruct_encode
#print axioms reconstruct_encode
#assert_analysis_axioms encode_reconstruct
#print axioms encode_reconstruct
#assert_analysis_axioms realDiscreteProjectiveReconstructionEquiv
#print axioms realDiscreteProjectiveReconstructionEquiv
#assert_analysis_axioms encode_injective
#print axioms encode_injective
#assert_analysis_axioms existsUnique_state_of_boundary_and_mass
#print axioms existsUnique_state_of_boundary_and_mass
end GeometryOfNumbers.Analysis.DiscreteProjective

namespace GeometryOfNumbers.Analysis.RealCarry
#assert_analysis_axioms carryWeightedVerticalGreenKernel
#print axioms carryWeightedVerticalGreenKernel
#assert_analysis_axioms carryWeightedVerticalGreenKernel_zero
#print axioms carryWeightedVerticalGreenKernel_zero
#assert_analysis_axioms carryWeightedVerticalGreenKernel_nonneg
#print axioms carryWeightedVerticalGreenKernel_nonneg
#assert_analysis_axioms carryConjugatedVerticalGreenKernel
#print axioms carryConjugatedVerticalGreenKernel
#assert_analysis_axioms carryConjugatedVerticalGreenKernel_of_lt
#print axioms carryConjugatedVerticalGreenKernel_of_lt
#assert_analysis_axioms carryConjugatedVerticalGreenKernel_of_not_lt
#print axioms carryConjugatedVerticalGreenKernel_of_not_lt
#assert_analysis_axioms carryWeightedVerticalGreenKernel_summable
#print axioms carryWeightedVerticalGreenKernel_summable
#assert_analysis_axioms CarryVerticalShiftFamily
#print axioms CarryVerticalShiftFamily
#assert_analysis_axioms carryWeightedVerticalGreenTerm
#print axioms carryWeightedVerticalGreenTerm
#assert_analysis_axioms carryWeightedVerticalGreenTerm_norm_le
#print axioms carryWeightedVerticalGreenTerm_norm_le
#assert_analysis_axioms carryWeightedVerticalGreenTerm_summable
#print axioms carryWeightedVerticalGreenTerm_summable
#assert_analysis_axioms carryWeightedVerticalGreen
#print axioms carryWeightedVerticalGreen
#assert_analysis_axioms carryWeightedVerticalGreen_norm_le_kernelMass
#print axioms carryWeightedVerticalGreen_norm_le_kernelMass
#assert_analysis_axioms CarryVerticalL2
#print axioms CarryVerticalL2
#assert_analysis_axioms carryVerticalL2BackwardShiftLinear
#print axioms carryVerticalL2BackwardShiftLinear
#assert_analysis_axioms carryVerticalL2BackwardShiftLinear_apply
#print axioms carryVerticalL2BackwardShiftLinear_apply
#assert_analysis_axioms carryVerticalL2BackwardShiftLinear_norm_le
#print axioms carryVerticalL2BackwardShiftLinear_norm_le
#assert_analysis_axioms carryVerticalL2BackwardShift
#print axioms carryVerticalL2BackwardShift
#assert_analysis_axioms carryVerticalL2BackwardShift_apply
#print axioms carryVerticalL2BackwardShift_apply
#assert_analysis_axioms carryVerticalL2BackwardShift_norm_le_one
#print axioms carryVerticalL2BackwardShift_norm_le_one
#assert_analysis_axioms carryVerticalL2BackwardShift_single
#print axioms carryVerticalL2BackwardShift_single
#assert_analysis_axioms carryVerticalL2UnilateralShift
#print axioms carryVerticalL2UnilateralShift
#assert_analysis_axioms carryVerticalL2UnilateralShift_apply
#print axioms carryVerticalL2UnilateralShift_apply
#assert_analysis_axioms carryVerticalL2UnilateralShift_norm_le_one
#print axioms carryVerticalL2UnilateralShift_norm_le_one
#assert_analysis_axioms carryVerticalL2ShiftFamily
#print axioms carryVerticalL2ShiftFamily
#assert_analysis_axioms carryVerticalL2WeightedGreen
#print axioms carryVerticalL2WeightedGreen
#assert_analysis_axioms carryVerticalL2EvalLinear
#print axioms carryVerticalL2EvalLinear
#assert_analysis_axioms carryVerticalL2Eval
#print axioms carryVerticalL2Eval
#assert_analysis_axioms carryVerticalL2Eval_apply
#print axioms carryVerticalL2Eval_apply
#assert_analysis_axioms carryVerticalL2ZeroHeadProjection
#print axioms carryVerticalL2ZeroHeadProjection
#assert_analysis_axioms carryVerticalL2ZeroHeadProjection_apply
#print axioms carryVerticalL2ZeroHeadProjection_apply
#assert_analysis_axioms carryWeightedVerticalCenteredBracketCore
#print axioms carryWeightedVerticalCenteredBracketCore
#assert_analysis_axioms carryWeightedVerticalCenteredBracketCore_apply
#print axioms carryWeightedVerticalCenteredBracketCore_apply
#assert_analysis_axioms carryWeightedVerticalCenteredBracket
#print axioms carryWeightedVerticalCenteredBracket
#assert_analysis_axioms carryWeightedVerticalCenteredBracket_zero
#print axioms carryWeightedVerticalCenteredBracket_zero
#assert_analysis_axioms carryWeightedVerticalCenteredBracket_succ
#print axioms carryWeightedVerticalCenteredBracket_succ
#assert_analysis_axioms carryWeightedVerticalTrace
#print axioms carryWeightedVerticalTrace
#assert_analysis_axioms carryWeightedVerticalTrace_apply
#print axioms carryWeightedVerticalTrace_apply
#assert_analysis_axioms carryGeometricAmplitudeVector
#print axioms carryGeometricAmplitudeVector
#assert_analysis_axioms carryGeometricAmplitudeVector_apply
#print axioms carryGeometricAmplitudeVector_apply
#assert_analysis_axioms carryAffineSlopeAmplitudeVector
#print axioms carryAffineSlopeAmplitudeVector
#assert_analysis_axioms carryAffineSlopeAmplitudeVector_apply
#print axioms carryAffineSlopeAmplitudeVector_apply
#assert_analysis_axioms carryWeightedVerticalReturn
#print axioms carryWeightedVerticalReturn
#assert_analysis_axioms carryWeightedVerticalReturn_apply
#print axioms carryWeightedVerticalReturn_apply
#assert_analysis_axioms carryWeightedVerticalTrace_comp_return
#print axioms carryWeightedVerticalTrace_comp_return
#assert_analysis_axioms carryWeightedVerticalCenteredBracket_comp_return
#print axioms carryWeightedVerticalCenteredBracket_comp_return
#assert_analysis_axioms carryVerticalL2OperatorApply
#print axioms carryVerticalL2OperatorApply
#assert_analysis_axioms carryVerticalL2OperatorApply_apply
#print axioms carryVerticalL2OperatorApply_apply
#assert_analysis_axioms carryVerticalL2OperatorCoordinate
#print axioms carryVerticalL2OperatorCoordinate
#assert_analysis_axioms carryVerticalL2OperatorCoordinate_apply
#print axioms carryVerticalL2OperatorCoordinate_apply
#assert_analysis_axioms carryVerticalL2WeightedGreen_apply
#print axioms carryVerticalL2WeightedGreen_apply
#assert_analysis_axioms carryVerticalL2WeightedGreen_apply_reindexed
#print axioms carryVerticalL2WeightedGreen_apply_reindexed
#assert_analysis_axioms carryWeightedScalarFirstDifference
#print axioms carryWeightedScalarFirstDifference
#assert_analysis_axioms carryWeightedScalarSecondDifference
#print axioms carryWeightedScalarSecondDifference
#assert_analysis_axioms carryWeightedScalarSecondDifference_eq
#print axioms carryWeightedScalarSecondDifference_eq
#assert_analysis_axioms carryWeightedScalarGreenSum
#print axioms carryWeightedScalarGreenSum
#assert_analysis_axioms carryWeightedScalarSecondDifference_telescope
#print axioms carryWeightedScalarSecondDifference_telescope
#assert_analysis_axioms carryWeightedScalarGreenSum_succ
#print axioms carryWeightedScalarGreenSum_succ
#assert_analysis_axioms carryWeightedScalarReconstruction
#print axioms carryWeightedScalarReconstruction
#assert_analysis_axioms carryVerticalL2WeightedGreen_bracket_apply
#print axioms carryVerticalL2WeightedGreen_bracket_apply
#assert_analysis_axioms carryWeightedVerticalTfvd_apply
#print axioms carryWeightedVerticalTfvd_apply
#assert_analysis_axioms carryWeightedVerticalTfvd_identity
#print axioms carryWeightedVerticalTfvd_identity
end GeometryOfNumbers.Analysis.RealCarry

namespace GeometryOfNumbers.Analysis
open DiscreteValve RealCarry ProjectiveDepth ProjectiveValve
open scoped lp ENNReal NNReal

-- Affine curvature and its Green interior vanish.
example (a slope : ℝ) (k : ℕ) :
    bracket (fun n => a + (n : ℝ) * slope) k = 0 := by
  simp only [bracket, nsmul_eq_mul]
  push_cast
  ring

example (a slope : ℝ) (n : ℕ) :
    greenSum (fun k => a + (k : ℝ) * slope) n = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  simp only [bracket, nsmul_eq_mul]
  push_cast
  ring

-- Constant quadratic curvature and concrete reconstruction endpoints.
example (k : ℕ) : bracket (fun n => (n : ℝ) ^ 2) k = 2 := by
  simp only [bracket, nsmul_eq_mul]
  push_cast
  ring

example : greenSum (fun n => (n : ℝ) ^ 2) 3 = 12 := by
  norm_num [greenSum, bracket, nsmul_eq_mul, Finset.sum_range_succ]

example : (4 : ℝ) ^ 2 = 0 + 4 * 1 + greenSum (fun n => (n : ℝ) ^ 2) 3 := by
  have h := realDiscreteGreenReconstruction (fun n => (n : ℝ) ^ 2) 3
  norm_num [nsmul_eq_mul] at h ⊢
  exact h

-- Base two: the gauge is symbolic, with the locally derived b^(-1/2).
example (f : ℕ → ℝ) (k : ℕ) :
    carryWeightedScalarSecondDifference (criticalVerticalAmplitudeRatio 2 (by decide))
        (realCarryAmplitudeGauge (criticalVerticalAmplitudeRatio 2 (by decide)) f) k =
      criticalVerticalAmplitudeRatio 2 (by decide) ^ (k + 1) * bracket f k :=
  realCarryWeightedSecondDifference_gauge _ (criticalVerticalAmplitudeRatio_pos 2 _).ne' f k

example : criticalVerticalAmplitudeRatio 2 (by decide) = (2 : ℝ) ^ (-(1 : ℝ) / 2) :=
  criticalVerticalAmplitudeRatio_eq_rpow 2 _

example (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a slope : ℝ) :
    carryWeightedVerticalTrace eta (carryWeightedVerticalReturn eta h0.le h1 (a, slope)) =
      (a, slope) := by
  have h := congrArg (fun T => T (a, slope)) (carryWeightedVerticalTrace_comp_return eta h0 h1)
  exact h

-- All initial coordinates, with no numerical substitution for the general proof.
example (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : CarryVerticalL2) (i : Fin 3) :
    carryVerticalL2WeightedGreen eta (carryWeightedVerticalCenteredBracket eta x) i.val +
      carryWeightedVerticalReturn eta h0.le h1 (carryWeightedVerticalTrace eta x) i.val = x i.val :=
  carryWeightedVerticalTfvd_apply eta h0 h1 x i.val

-- The projective round trips specialize to real coefficients.
example (f : ℕ → ℝ) : DiscreteProjective.reconstruct (DiscreteProjective.encode f) = f :=
  DiscreteProjective.reconstruct_encode f
example (D : PowerSeries ℝ) : projectiveValveCurvature (projectiveValveMass D) = D :=
  projectiveValveCurvature_projectiveValveMass D

-- Local phase canary; no post-synthesis phase is defined or assumed.
#assert_analysis_axioms rotateRealPlane_neg_comp
#print axioms rotateRealPlane_neg_comp
#assert_analysis_axioms rotateRealPlane_eq_zero_iff
#print axioms rotateRealPlane_eq_zero_iff
#assert_analysis_axioms centerLegForm_eq_rotate_zero
#print axioms centerLegForm_eq_rotate_zero
#assert_analysis_axioms centerLegForm_zero_iff_zero_angle
#print axioms centerLegForm_zero_iff_zero_angle
#assert_analysis_axioms centerLegForm_independent_angles_not_common_rotation
#print axioms centerLegForm_independent_angles_not_common_rotation

-- One material log time, separate vertical depth: downstream finite canary.
#assert_analysis_axioms materialLogAngle
#print axioms materialLogAngle
#assert_analysis_axioms materialLogRotate
#print axioms materialLogRotate
#assert_analysis_axioms materialLogRotate_zero
#print axioms materialLogRotate_zero
#assert_analysis_axioms materialLogRotate_add
#print axioms materialLogRotate_add
#assert_analysis_axioms materialLogRotate_energy
#print axioms materialLogRotate_energy
#assert_analysis_axioms materialLogRotate_neg_comp
#print axioms materialLogRotate_neg_comp
#assert_analysis_axioms materialLogRotate_eq_zero_iff
#print axioms materialLogRotate_eq_zero_iff
#assert_analysis_axioms realQuadratureRotate
#print axioms realQuadratureRotate
#assert_analysis_axioms realQuadratureMap
#print axioms realQuadratureMap
#assert_analysis_axioms realQuadratureRotate_zero
#print axioms realQuadratureRotate_zero
#assert_analysis_axioms realQuadratureRotate_add
#print axioms realQuadratureRotate_add
#assert_analysis_axioms realQuadratureRotate_neg_comp
#print axioms realQuadratureRotate_neg_comp
#assert_analysis_axioms realQuadratureRotate_eq_zero_iff
#print axioms realQuadratureRotate_eq_zero_iff
#assert_analysis_axioms realQuadratureMap_rotate
#print axioms realQuadratureMap_rotate
#assert_analysis_axioms materialLogPhase
#print axioms materialLogPhase
#assert_analysis_axioms materialLogPhase_zero
#print axioms materialLogPhase_zero
#assert_analysis_axioms materialLogPhase_add
#print axioms materialLogPhase_add
#assert_analysis_axioms materialLogPhase_neg_comp
#print axioms materialLogPhase_neg_comp
#assert_analysis_axioms materialLogPhase_eq_zero_iff
#print axioms materialLogPhase_eq_zero_iff
#assert_analysis_axioms realQuadratureRotate_eq_rotateRealPlane
#print axioms realQuadratureRotate_eq_rotateRealPlane
#assert_analysis_axioms MaterialVerticalCarrier
#print axioms MaterialVerticalCarrier
#assert_analysis_axioms MaterialVerticalAnalysisCarrier
#print axioms MaterialVerticalAnalysisCarrier
#assert_analysis_axioms materialTfvdAnalysis
#print axioms materialTfvdAnalysis
#assert_analysis_axioms materialTfvdSynthesis
#print axioms materialTfvdSynthesis
#assert_analysis_axioms materialTfvdSynthesis_comp_analysis
#print axioms materialTfvdSynthesis_comp_analysis
#assert_analysis_axioms materialTfvdAnalysis_phase
#print axioms materialTfvdAnalysis_phase
#assert_analysis_axioms materialTfvdSynthesis_phase
#print axioms materialTfvdSynthesis_phase
#assert_analysis_axioms materialTfvdSynthesized_logOrbit
#print axioms materialTfvdSynthesized_logOrbit
#assert_analysis_axioms materialVerticalPlaneAt
#print axioms materialVerticalPlaneAt
#assert_analysis_axioms materialLogPhase_planeAt
#print axioms materialLogPhase_planeAt
#assert_analysis_axioms materialLogPhase_planeEnergy
#print axioms materialLogPhase_planeEnergy
#assert_analysis_axioms materialLogPhase_centerLeg_orbit
#print axioms materialLogPhase_centerLeg_orbit
#assert_analysis_axioms materialLogPhase_centerLeg_zero_iff
#print axioms materialLogPhase_centerLeg_zero_iff
#assert_analysis_axioms materialTfvdSynthesized_centerLeg_zero_iff
#print axioms materialTfvdSynthesized_centerLeg_zero_iff
#assert_analysis_axioms materialTfvdSynthesis_phase_zero_iff
#print axioms materialTfvdSynthesis_phase_zero_iff
#assert_analysis_axioms materialLogPhase_finiteEnergy
#print axioms materialLogPhase_finiteEnergy

-- Material index zero has frequency log 1 = 0, at every vertical coordinate.
example (t : ℝ) (v : RealPlaneState) : materialLogRotate t 0 v = v := by
  simp [materialLogRotate, materialLogAngle, rotateRealPlane_zero]

-- The same material angle is used at all vertical coordinates.
example (t : ℝ) (X : MaterialVerticalCarrier 3) (n : Fin 3) (k j : ℕ) :
    materialVerticalPlaneAt (materialLogPhase t X) n k =
      materialLogRotate t n.val (materialVerticalPlaneAt X n k) ∧
    materialVerticalPlaneAt (materialLogPhase t X) n j =
      materialLogRotate t n.val (materialVerticalPlaneAt X n j) :=
  ⟨materialLogPhase_planeAt _ _ _ _, materialLogPhase_planeAt _ _ _ _⟩

-- Critical base two uses the existing R2 ratio, without an index crosswalk.
example (t : ℝ) (X : MaterialVerticalCarrier 3) :
    let eta := criticalVerticalAmplitudeRatio 2 (by decide)
    materialTfvdSynthesis eta (criticalVerticalAmplitudeRatio_pos 2 _).le
      (criticalVerticalAmplitudeRatio_lt_one 2 (by decide))
      (materialLogPhase t (materialTfvdAnalysis eta X)) = materialLogPhase t X :=
  materialTfvdSynthesized_logOrbit _ (criticalVerticalAmplitudeRatio_pos 2 _)
    (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) t X


-- Intrinsic binary depth differs from the historical material sample index.
#assert_analysis_axioms sampleTwo_materialThree_binaryDepth_iff
#print axioms sampleTwo_materialThree_binaryDepth_iff
#assert_analysis_axioms materialSampleIndex_not_intrinsicBinaryDepth
#print axioms materialSampleIndex_not_intrinsicBinaryDepth


-- Exact geometric C2 fiber dynamics, downstream of the frozen R2.
#assert_analysis_axioms c2FiberPoint
#print axioms c2FiberPoint
#assert_analysis_axioms c2FiberPoint_centered
#print axioms c2FiberPoint_centered
#assert_analysis_axioms c2FiberPoint_center_eq_nat
#print axioms c2FiberPoint_center_eq_nat
#assert_analysis_axioms c2FiberPoint_succ
#print axioms c2FiberPoint_succ
#assert_analysis_axioms c2FiberCenter_hasCarryDepthAtLeast
#print axioms c2FiberCenter_hasCarryDepthAtLeast
#assert_analysis_axioms c2FiberCenter_not_hasCarryDepthAtLeast_succ
#print axioms c2FiberCenter_not_hasCarryDepthAtLeast_succ
#assert_analysis_axioms c2FiberPoint_center_pos
#print axioms c2FiberPoint_center_pos
#assert_analysis_axioms c2FiberPoint_right_pos
#print axioms c2FiberPoint_right_pos
#assert_analysis_axioms c2FiberPoint_left_pos
#print axioms c2FiberPoint_left_pos
#assert_analysis_axioms c2FiberPoint_centered_log
#print axioms c2FiberPoint_centered_log
#assert_analysis_axioms c2FiberPoint_centered_log_increment
#print axioms c2FiberPoint_centered_log_increment
#assert_analysis_axioms c2FiberLogDefect
#print axioms c2FiberLogDefect
#assert_analysis_axioms c2FiberLogDefect_center
#print axioms c2FiberLogDefect_center
#assert_analysis_axioms c2FiberPoint_log_center_defect
#print axioms c2FiberPoint_log_center_defect
#assert_analysis_axioms c2FiberPoint_log_eq_depth_core_defect
#print axioms c2FiberPoint_log_eq_depth_core_defect
#assert_analysis_axioms c2FiberPoint_log_increment_defect
#print axioms c2FiberPoint_log_increment_defect
#assert_analysis_axioms c2FiberLogDefect_right_pos
#print axioms c2FiberLogDefect_right_pos
#assert_analysis_axioms c2FiberPoint_right_log_increment_lt
#print axioms c2FiberPoint_right_log_increment_lt
#assert_analysis_axioms c2FiberRealState
#print axioms c2FiberRealState
#assert_analysis_axioms c2FiberRealState_energy
#print axioms c2FiberRealState_energy
#assert_analysis_axioms c2FiberRealState_succ_eq_logIncrement
#print axioms c2FiberRealState_succ_eq_logIncrement
#assert_analysis_axioms c2CenterFiberStep
#print axioms c2CenterFiberStep
#assert_analysis_axioms c2CenterFiberRealState_succ_eq_fixedStep
#print axioms c2CenterFiberRealState_succ_eq_fixedStep
#assert_analysis_axioms c2CenterFiberRealState_eq_iterate_step
#print axioms c2CenterFiberRealState_eq_iterate_step
#assert_analysis_axioms c2CenterFiber_phase_factorization
#print axioms c2CenterFiber_phase_factorization
#assert_analysis_axioms c2LegFiberRealState_succ_eq_correctedStep
#print axioms c2LegFiberRealState_succ_eq_correctedStep
#assert_analysis_axioms c2LegFiberRealState_succ_eq_fixedStep_add_logDefect
#print axioms c2LegFiberRealState_succ_eq_fixedStep_add_logDefect

-- Positive C2 legs keep the actual material points and their exact defects.
example : c2FiberPoint 1 (-1) 2 = 3 := by norm_num [c2FiberPoint]
example : c2FiberPoint 1 0 2 = 4 := by norm_num [c2FiberPoint]
example : c2FiberPoint 1 1 2 = 5 := by norm_num [c2FiberPoint]
example : c2FiberLogDefect 1 (-1) 2 = Real.log ((3 : ℝ) / 4) := by
  norm_num [c2FiberLogDefect]
example : c2FiberLogDefect 1 1 2 = Real.log ((5 : ℝ) / 4) := by
  norm_num [c2FiberLogDefect]
example (t : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (c2CenterFiberStep t v) =
      criticalVerticalAmplitudeRatio 2 (by decide) ^ 2 * realPlaneEnergy v := by
  rw [c2CenterFiberStep, scaleRealPlane_energy, rotateRealPlane_energy]
example : (0 : ℝ) < criticalVerticalAmplitudeRatio 2 (by decide) :=
  criticalVerticalAmplitudeRatio_pos 2 (by decide)
example : criticalVerticalAmplitudeRatio 2 (by decide) < 1 :=
  criticalVerticalAmplitudeRatio_lt_one 2 (by decide)
example (t : ℝ) :
    c2FiberRealState 1 0 t 0 (by decide) (by norm_num [c2FiberPoint]) = (1, 0) := by
  simp [c2FiberRealState, c2FiberPoint, realCriticalDepthState_zero_angle,
    realCriticalDepthSeed_zero_depth]
example : Geometry.HasCarryDepthAtLeast 2 (2 ^ 2 * 1) 2 :=
  c2FiberCenter_hasCarryDepthAtLeast 1 2
example : ¬ Geometry.HasCarryDepthAtLeast 2 (2 ^ 2 * 1) 3 :=
  c2FiberCenter_not_hasCarryDepthAtLeast_succ 1 2 (by decide)


-- Downstream C2 radial comparison orbit and exact legacy branch mass.
#assert_analysis_axioms c2BranchDepth_ge_two_iff_center_four_dvd
#print axioms c2BranchDepth_ge_two_iff_center_four_dvd
#assert_analysis_axioms c2BranchDirections_distinct
#print axioms c2BranchDirections_distinct
#assert_analysis_axioms c2BranchDirections_card
#print axioms c2BranchDirections_card
#assert_analysis_axioms c2RadialAmplitudeRatio
#print axioms c2RadialAmplitudeRatio
#assert_analysis_axioms c2RadialEnergyRatio
#print axioms c2RadialEnergyRatio
#assert_analysis_axioms c2RadialEnergyRatio_eq_rpow
#print axioms c2RadialEnergyRatio_eq_rpow
#assert_analysis_axioms c2RadialEnergyRatio_pos
#print axioms c2RadialEnergyRatio_pos
#assert_analysis_axioms c2RadialEnergyRatio_lt_one
#print axioms c2RadialEnergyRatio_lt_one
#assert_analysis_axioms c2DeformedFiberStep
#print axioms c2DeformedFiberStep
#assert_analysis_axioms c2DeformedFiberStep_energy
#print axioms c2DeformedFiberStep_energy
#assert_analysis_axioms c2DeformedFiberStep_energy_independent_time
#print axioms c2DeformedFiberStep_energy_independent_time
#assert_analysis_axioms c2DeformedFiberStep_iterate_energy
#print axioms c2DeformedFiberStep_iterate_energy
#assert_analysis_axioms c2DeformedUnitOrbit_energy
#print axioms c2DeformedUnitOrbit_energy
#assert_analysis_axioms c2RadialAmplitudeRatio_half
#print axioms c2RadialAmplitudeRatio_half
#assert_analysis_axioms c2RadialEnergyRatio_half
#print axioms c2RadialEnergyRatio_half
#assert_analysis_axioms c2DeformedFiberStep_half_eq_c2CenterFiberStep
#print axioms c2DeformedFiberStep_half_eq_c2CenterFiberStep
#assert_analysis_axioms c2BranchOrbitMass
#print axioms c2BranchOrbitMass
#assert_analysis_axioms c2BranchOrbitMass_eq_geometric_series
#print axioms c2BranchOrbitMass_eq_geometric_series
#assert_analysis_axioms c2BranchOrbitMass_independent_time
#print axioms c2BranchOrbitMass_independent_time
#assert_analysis_axioms legacyC2BranchWeight
#print axioms legacyC2BranchWeight
#assert_analysis_axioms legacyC2BranchNormSq
#print axioms legacyC2BranchNormSq
#assert_analysis_axioms c2RadialEnergyRatio_eq_legacyBranchWeight
#print axioms c2RadialEnergyRatio_eq_legacyBranchWeight
#assert_analysis_axioms c2BranchOrbitMass_eq_legacyBranchNormSq
#print axioms c2BranchOrbitMass_eq_legacyBranchNormSq
#assert_analysis_axioms c2BranchUnitOrbitEnergy_summable
#print axioms c2BranchUnitOrbitEnergy_summable
#assert_analysis_axioms c2BranchOrbitMass_closed_form
#print axioms c2BranchOrbitMass_closed_form
#assert_analysis_axioms c2BranchOrbitMass_half
#print axioms c2BranchOrbitMass_half
#assert_analysis_axioms c2BranchOrbitMass_eq_one_iff
#print axioms c2BranchOrbitMass_eq_one_iff
#assert_analysis_axioms c2BranchOrbitMass_lt_one_iff
#print axioms c2BranchOrbitMass_lt_one_iff
#assert_analysis_axioms c2BranchOrbitMass_gt_one_iff
#print axioms c2BranchOrbitMass_gt_one_iff

-- Exact formal examples: count, energy, operator equality and barrier.
example : ({c2FiberPoint 1 (-1) 2, c2FiberPoint 1 1 2} : Finset ℝ).card = 2 :=
  c2BranchDirections_card 1 2
example : 4 ∣ 2 ^ 2 * 1 :=
  (c2BranchDepth_ge_two_iff_center_four_dvd 1 2 (by decide)).mpr (by decide)
example : ¬ 4 ∣ 2 ^ 1 * 1 := by decide
example : c2RadialEnergyRatio ((1 : ℝ) / 2) = (1 : ℝ) / 2 :=
  c2RadialEnergyRatio_half
example (t : ℝ) : c2DeformedFiberStep ((1 : ℝ) / 2) t = c2CenterFiberStep t :=
  c2DeformedFiberStep_half_eq_c2CenterFiberStep t
example (t : ℝ) : c2BranchOrbitMass ((1 : ℝ) / 2) t = 1 :=
  c2BranchOrbitMass_half t
example (t : ℝ) : c2BranchOrbitMass 1 t = (1 : ℝ) / 6 := by
  rw [c2BranchOrbitMass_closed_form _ _ (by norm_num)]
  norm_num [c2RadialEnergyRatio_eq_rpow, Real.rpow_neg]
example (t : ℝ) : 1 < c2BranchOrbitMass ((1 : ℝ) / 4) t :=
  (c2BranchOrbitMass_gt_one_iff _ t (by norm_num)).mpr (by norm_num)
example (sigma t : ℝ) : c2BranchOrbitMass sigma t = legacyC2BranchNormSq sigma :=
  c2BranchOrbitMass_eq_legacyBranchNormSq sigma t
example (t : ℝ) : Summable (fun j : ℕ => realPlaneEnergy
    ((c2DeformedFiberStep ((1 : ℝ) / 2) t)^[j + 2]
      (realCriticalDepthSeed 2 0 (by decide)))) :=
  c2BranchUnitOrbitEnergy_summable _ t (by norm_num)

-- C2 pure branch: actual real Hilbert operator, before any whitening.
#assert_analysis_axioms RealPlaneHilbert
#print axioms RealPlaneHilbert
#assert_analysis_axioms C2BranchDirection
#print axioms C2BranchDirection
#assert_analysis_axioms c2BranchDirectionSign
#print axioms c2BranchDirectionSign
#assert_analysis_axioms c2BranchDirectionSign_values
#print axioms c2BranchDirectionSign_values
#assert_analysis_axioms C2BranchCarrier
#print axioms C2BranchCarrier
#assert_analysis_axioms realPlaneHilbertEquiv
#print axioms realPlaneHilbertEquiv
#assert_analysis_axioms realPlaneHilbert_energy_eq_norm_sq
#print axioms realPlaneHilbert_energy_eq_norm_sq
#assert_analysis_axioms c2DeformedFiberStepLinear
#print axioms c2DeformedFiberStepLinear
#assert_analysis_axioms c2DeformedFiberStep_iterate_eq_radial_rotation
#print axioms c2DeformedFiberStep_iterate_eq_radial_rotation
#assert_analysis_axioms realBranchCoordinates
#print axioms realBranchCoordinates
#assert_analysis_axioms realBranchCoordinates_norm_sq
#print axioms realBranchCoordinates_norm_sq
#assert_analysis_axioms realBranchCoordinates_square_summable
#print axioms realBranchCoordinates_square_summable
#assert_analysis_axioms realBranchCoordinates_mem_l2
#print axioms realBranchCoordinates_mem_l2
#assert_analysis_axioms realBranchOperator
#print axioms realBranchOperator
#assert_analysis_axioms realBranchOperator_apply
#print axioms realBranchOperator_apply
#assert_analysis_axioms realBranchOperator_apply_closed_form
#print axioms realBranchOperator_apply_closed_form
#assert_analysis_axioms realBranchOperatorLinear
#print axioms realBranchOperatorLinear
#assert_analysis_axioms realBranchOperator_norm_sq
#print axioms realBranchOperator_norm_sq
#assert_analysis_axioms realBranchOperator_norm_sq_eq_legacyBranchNormSq
#print axioms realBranchOperator_norm_sq_eq_legacyBranchNormSq
#assert_analysis_axioms realBranchOperator_norm_sq_of_realPlaneState
#print axioms realBranchOperator_norm_sq_of_realPlaneState
#assert_analysis_axioms realBranchOperator_norm_independent_time
#print axioms realBranchOperator_norm_independent_time
#assert_analysis_axioms realCriticalBranchOperator_norm
#print axioms realCriticalBranchOperator_norm
#assert_analysis_axioms realCriticalBranchIsometry
#print axioms realCriticalBranchIsometry
#assert_analysis_axioms realCriticalBranchIsometry_apply_centerStep
#print axioms realCriticalBranchIsometry_apply_centerStep
#assert_analysis_axioms realCriticalBranch_adjoint_comp_self
#print axioms realCriticalBranch_adjoint_comp_self

-- Exact examples at arbitrary time, including both branch labels and depth two.
example (v : RealPlaneHilbert) :
    realPlaneEnergy (realPlaneHilbertEquiv.symm v) = ‖v‖ ^ 2 :=
  realPlaneHilbert_energy_eq_norm_sq v
example (t : ℝ) (v : RealPlaneHilbert) :
    realBranchOperator ((1 : ℝ) / 2) t (by norm_num) v (0, 0) =
      realBranchOperator ((1 : ℝ) / 2) t (by norm_num) v (1, 0) := rfl
example (t : ℝ) (v : RealPlaneHilbert) :
    ‖realBranchOperator ((1 : ℝ) / 2) t (by norm_num) v (0, 0)‖ ^ 2 =
      (1 / 4 : ℝ) * ‖v‖ ^ 2 := by
  change ‖realBranchCoordinates ((1 : ℝ) / 2) t v (0, 0)‖ ^ 2 = _
  rw [realBranchCoordinates_norm_sq, c2RadialEnergyRatio_half]
  norm_num
example (sigma t : ℝ) (hsigma : 0 < sigma) (v w : RealPlaneHilbert) :
    realBranchOperatorLinear sigma t hsigma (v + w) =
      realBranchOperatorLinear sigma t hsigma v + realBranchOperatorLinear sigma t hsigma w :=
  (realBranchOperatorLinear sigma t hsigma).map_add v w
example (t : ℝ) :
    ‖realCriticalBranchIsometry t (realPlaneHilbertEquiv (1, 0))‖ = 1 := by
  rw [(realCriticalBranchIsometry t).norm_map]
  have h : ‖realPlaneHilbertEquiv (1, 0)‖ ^ 2 = 1 := by
    rw [← realPlaneHilbert_energy_eq_norm_sq, LinearEquiv.symm_apply_apply]
    norm_num [realPlaneEnergy]
  nlinarith [norm_nonneg (realPlaneHilbertEquiv (1, 0))]
example (t : ℝ) (v : RealPlaneHilbert) :
    (realCriticalBranchIsometry t).toContinuousLinearMap.adjoint
      (realCriticalBranchIsometry t v) = v := by
  change ((realCriticalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
    (realCriticalBranchIsometry t).toContinuousLinearMap) v = v
  rw [realCriticalBranch_adjoint_comp_self]
  rfl

-- Physical C2 incidence: sign, depth, core and exact leg log-defect.
#assert_analysis_axioms C2BranchAddress
#print axioms C2BranchAddress
#assert_analysis_axioms RealMaterialState
#print axioms RealMaterialState
#assert_analysis_axioms c2BranchDepth
#print axioms c2BranchDepth
#assert_analysis_axioms c2BranchMaterialNat
#print axioms c2BranchMaterialNat
#assert_analysis_axioms c2BranchMaterialNat_ge_three
#print axioms c2BranchMaterialNat_ge_three
#assert_analysis_axioms c2BranchMaterialAddress
#print axioms c2BranchMaterialAddress
#assert_analysis_axioms c2BranchMaterialNat_sign_mod_four
#print axioms c2BranchMaterialNat_sign_mod_four
#assert_analysis_axioms c2BranchMaterialAddress_injective
#print axioms c2BranchMaterialAddress_injective
#assert_analysis_axioms c2BranchMaterialAddress_eq_iff
#print axioms c2BranchMaterialAddress_eq_iff
#assert_analysis_axioms c2BranchMaterialNat_core_recovery
#print axioms c2BranchMaterialNat_core_recovery
#assert_analysis_axioms C2LegHasCarryDepthAtLeast
#print axioms C2LegHasCarryDepthAtLeast
#assert_analysis_axioms c2BranchMaterialAddress_depth_recovery
#print axioms c2BranchMaterialAddress_depth_recovery
#assert_analysis_axioms c2BranchMaterialAddress_cast_eq_fiberPoint
#print axioms c2BranchMaterialAddress_cast_eq_fiberPoint
#assert_analysis_axioms branchIncidenceCoordinates
#print axioms branchIncidenceCoordinates
#assert_analysis_axioms branchIncidenceIsometry
#print axioms branchIncidenceIsometry
#assert_analysis_axioms branchIncidenceIsometry_apply_address
#print axioms branchIncidenceIsometry_apply_address
#assert_analysis_axioms branchIncidenceIsometry_apply_off_range
#print axioms branchIncidenceIsometry_apply_off_range
#assert_analysis_axioms branchIncidenceIsometry_norm
#print axioms branchIncidenceIsometry_norm
#assert_analysis_axioms branchIncidenceIsometry_coordinate_roundtrip
#print axioms branchIncidenceIsometry_coordinate_roundtrip
#assert_analysis_axioms c2PhysicalLegCorrectionAngle
#print axioms c2PhysicalLegCorrectionAngle
#assert_analysis_axioms c2PhysicalLegPhase_factorization
#print axioms c2PhysicalLegPhase_factorization
#assert_analysis_axioms realPlaneHilbertRotation
#print axioms realPlaneHilbertRotation
#assert_analysis_axioms realPlaneHilbertRotation_neg_comp
#print axioms realPlaneHilbertRotation_neg_comp
#assert_analysis_axioms physicalLegCorrection
#print axioms physicalLegCorrection
#assert_analysis_axioms physicalLegCorrection_apply
#print axioms physicalLegCorrection_apply
#assert_analysis_axioms physicalLegCorrection_norm
#print axioms physicalLegCorrection_norm
#assert_analysis_axioms physicalLegCorrection_neg_comp
#print axioms physicalLegCorrection_neg_comp
#assert_analysis_axioms physicalBranchOperator
#print axioms physicalBranchOperator
#assert_analysis_axioms physicalBranchOperator_apply_address
#print axioms physicalBranchOperator_apply_address
#assert_analysis_axioms physicalBranchOperator_apply_off_range
#print axioms physicalBranchOperator_apply_off_range
#assert_analysis_axioms physicalBranchOperator_norm
#print axioms physicalBranchOperator_norm
#assert_analysis_axioms physicalBranchOperator_norm_sq
#print axioms physicalBranchOperator_norm_sq
#assert_analysis_axioms realCriticalPhysicalBranchIsometry
#print axioms realCriticalPhysicalBranchIsometry
#assert_analysis_axioms realCriticalPhysicalBranchIsometry_eq_operator
#print axioms realCriticalPhysicalBranchIsometry_eq_operator
#assert_analysis_axioms realCriticalPhysicalBranchIsometry_norm
#print axioms realCriticalPhysicalBranchIsometry_norm
#assert_analysis_axioms realCriticalPhysicalBranch_adjoint_comp_self
#print axioms realCriticalPhysicalBranch_adjoint_comp_self
#assert_analysis_axioms c2BranchMaterialAddress_range_unique
#print axioms c2BranchMaterialAddress_range_unique
#assert_analysis_axioms physicalBranchOperator_nonzero_provenance
#print axioms physicalBranchOperator_nonzero_provenance

#assert_analysis_axioms physicalBranchOperator_branch_coordinate_roundtrip
#print axioms physicalBranchOperator_branch_coordinate_roundtrip

-- Addresses of core one at the first genuine level are exactly 3 and 5.
example : (c2BranchMaterialAddress 1 (by decide) (0, 0) : ℕ) = 3 := by
  norm_num [c2BranchMaterialAddress, c2BranchMaterialNat, c2BranchDepth]
example : (c2BranchMaterialAddress 1 (by decide) (1, 0) : ℕ) = 5 := by
  norm_num [c2BranchMaterialAddress, c2BranchMaterialNat, c2BranchDepth]
example : C2LegHasCarryDepthAtLeast 3 2 ∧ ¬ C2LegHasCarryDepthAtLeast 3 3 := by
  have h := c2BranchMaterialAddress_depth_recovery 1 (by decide) (by decide) (0,0)
  constructor
  · simpa [c2BranchMaterialNat, c2BranchDepth] using (h 2).mpr (by decide)
  · simpa [c2BranchMaterialNat, c2BranchDepth] using (h 3).not.mpr (by decide)
example (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) :
    ‖branchIncidenceIsometry m hm x‖ = ‖x‖ := branchIncidenceIsometry_norm m hm x
example (m : ℕ) (t : ℝ) (x : C2BranchCarrier) :
    physicalLegCorrection m (-t) (physicalLegCorrection m t x) = x :=
  physicalLegCorrection_neg_comp m t x
example (t : ℝ) (v : RealPlaneHilbert) :
    realPlaneHilbertEquiv.symm
      (physicalBranchOperator ((1 : ℝ) / 2) t (by norm_num) 1 (by decide) v ⟨3, by decide⟩) =
      scaleRealPlane ((2 : ℝ) ^ (-2 * ((1 : ℝ) / 2)))
        (rotateRealPlane (-t * Real.log 3) (realPlaneHilbertEquiv.symm v)) := by
  simpa [c2BranchMaterialAddress, c2BranchMaterialNat, c2BranchDepth] using
    physicalBranchOperator_apply_address ((1 : ℝ) / 2) t (by norm_num)
      1 (by decide) v (0,0)
example (sigma t : ℝ) (hsigma : 0 < sigma) (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) :
    physicalBranchOperator sigma t hsigma m hm v ⟨2, by decide⟩ = 0 := by
  apply physicalBranchOperator_apply_off_range
  rintro ⟨i,h⟩
  have hg := c2BranchMaterialNat_ge_three m hm i
  have hn := congrArg PNat.val h
  change c2BranchMaterialNat m i = 2 at hn
  omega
example (m : ℕ) (hm : 0 < m) (t : ℝ) (v : RealPlaneHilbert) :
    ‖realCriticalPhysicalBranchIsometry m hm t v‖ = ‖v‖ :=
  realCriticalPhysicalBranchIsometry_norm m hm t v
example (m : ℕ) (hm : 0 < m) (t : ℝ) :
    (realCriticalPhysicalBranchIsometry m hm t).toContinuousLinearMap.adjoint ∘L
      (realCriticalPhysicalBranchIsometry m hm t).toContinuousLinearMap = 1 :=
  realCriticalPhysicalBranch_adjoint_comp_self m hm t

-- Global physical C2: canonical odd-material addresses and orthogonal core sum.
#assert_analysis_axioms PositiveOddCore
#print axioms PositiveOddCore
#assert_analysis_axioms GlobalC2BranchAddress
#print axioms GlobalC2BranchAddress
#assert_analysis_axioms OddMaterialIndex
#print axioms OddMaterialIndex
#assert_analysis_axioms globalC2MaterialAddress
#print axioms globalC2MaterialAddress
#assert_analysis_axioms globalC2MaterialAddress_odd
#print axioms globalC2MaterialAddress_odd
#assert_analysis_axioms globalC2OddMaterialAddress
#print axioms globalC2OddMaterialAddress
#assert_analysis_axioms globalC2MaterialAddress_injective
#print axioms globalC2MaterialAddress_injective
#assert_analysis_axioms oddMaterialNeighborCenter
#print axioms oddMaterialNeighborCenter
#assert_analysis_axioms oddMaterialNeighbor_depth_crosswalk
#print axioms oddMaterialNeighbor_depth_crosswalk
#assert_analysis_axioms oddMaterialC2Address
#print axioms oddMaterialC2Address
#assert_analysis_axioms oddMaterialC2Address_depth
#print axioms oddMaterialC2Address_depth
#assert_analysis_axioms globalC2MaterialAddress_decode
#print axioms globalC2MaterialAddress_decode
#assert_analysis_axioms oddMaterialC2Address_encode
#print axioms oddMaterialC2Address_encode
#assert_analysis_axioms globalC2BranchAddressEquivOddMaterial
#print axioms globalC2BranchAddressEquivOddMaterial
#assert_analysis_axioms globalC2MaterialAddress_unique
#print axioms globalC2MaterialAddress_unique
#assert_analysis_axioms GlobalC2BranchCarrier
#print axioms GlobalC2BranchCarrier
#assert_analysis_axioms OddMaterialState
#print axioms OddMaterialState
#assert_analysis_axioms CoreState
#print axioms CoreState
#assert_analysis_axioms globalBranchIncidenceIsometry
#print axioms globalBranchIncidenceIsometry
#assert_analysis_axioms globalBranchIncidenceIsometry_apply_address
#print axioms globalBranchIncidenceIsometry_apply_address
#assert_analysis_axioms globalBranchIncidenceIsometry_norm
#print axioms globalBranchIncidenceIsometry_norm
#assert_analysis_axioms criticalPhysicalCoreFiber
#print axioms criticalPhysicalCoreFiber
#assert_analysis_axioms criticalPhysicalCoreFiber_eq_local_physical
#print axioms criticalPhysicalCoreFiber_eq_local_physical
#assert_analysis_axioms globalCriticalPhysicalBranch
#print axioms globalCriticalPhysicalBranch
#assert_analysis_axioms globalCriticalPhysicalBranchIsometry
#print axioms globalCriticalPhysicalBranchIsometry
#assert_analysis_axioms globalCriticalPhysicalBranchIsometry_norm
#print axioms globalCriticalPhysicalBranchIsometry_norm
#assert_analysis_axioms globalCriticalPhysicalBranchIsometry_norm_sq
#print axioms globalCriticalPhysicalBranchIsometry_norm_sq
#assert_analysis_axioms globalCriticalPhysicalBranchIsometry_apply_address
#print axioms globalCriticalPhysicalBranchIsometry_apply_address
#assert_analysis_axioms globalCriticalPhysicalBranchIsometry_pointwise
#print axioms globalCriticalPhysicalBranchIsometry_pointwise
#assert_analysis_axioms physicalBranch_support_disjoint_of_core_ne
#print axioms physicalBranch_support_disjoint_of_core_ne
#assert_analysis_axioms globalCriticalPhysicalBranch_core_orthogonal
#print axioms globalCriticalPhysicalBranch_core_orthogonal
#assert_analysis_axioms globalC2_provenance_roundtrip
#print axioms globalC2_provenance_roundtrip
#assert_analysis_axioms globalC2Address_components_roundtrip
#print axioms globalC2Address_components_roundtrip
#assert_analysis_axioms oddMaterialC2Address_sign
#print axioms oddMaterialC2Address_sign
#assert_analysis_axioms oddMaterialC2Address_core
#print axioms oddMaterialC2Address_core
#assert_analysis_axioms globalCriticalPhysicalBranch_single_core
#print axioms globalCriticalPhysicalBranch_single_core
#assert_analysis_axioms globalCriticalPhysicalBranch_zero_of_core_zero
#print axioms globalCriticalPhysicalBranch_zero_of_core_zero

-- Kernel-checked coordinate and provenance examples; no numerical evidence.
example : (globalC2MaterialAddress (⟨1, by norm_num⟩, (0,0)) : ℕ) = 3 := by decide
example : (globalC2MaterialAddress (⟨1, by norm_num⟩, (1,0)) : ℕ) = 5 := by decide
example : (globalC2MaterialAddress (⟨1, by norm_num⟩, (0,1)) : ℕ) = 7 := by decide
example : (globalC2MaterialAddress (⟨3, by norm_num⟩, (1,0)) : ℕ) = 13 := by decide
example : oddMaterialC2Address ⟨⟨3, by decide⟩, by decide⟩ =
    (⟨1, by norm_num⟩, (0,0)) :=
  oddMaterialC2Address_encode (⟨1, by norm_num⟩, (0,0))
example : oddMaterialC2Address ⟨⟨13, by decide⟩, by decide⟩ =
    (⟨3, by norm_num⟩, (1,0)) :=
  oddMaterialC2Address_encode (⟨3, by norm_num⟩, (1,0))
example (i : GlobalC2BranchAddress) :
    oddMaterialC2Address (globalC2OddMaterialAddress i) = i :=
  oddMaterialC2Address_encode i
example (n : OddMaterialIndex) : ∃! i : GlobalC2BranchAddress,
    globalC2MaterialAddress i = n.val := globalC2MaterialAddress_unique n
example (t : ℝ) (v : CoreState) :
    ‖globalCriticalPhysicalBranchIsometry t v‖ = ‖v‖ :=
  globalCriticalPhysicalBranchIsometry_norm t v
example (t : ℝ) (m : PositiveOddCore) (v : RealPlaneHilbert) (n : OddMaterialIndex) :
    globalCriticalPhysicalBranchIsometry t (lp.single 2 m v) n =
      realCriticalPhysicalBranchIsometry m.val m.property.1 t v n.val :=
  globalCriticalPhysicalBranch_single_core t m v n
end GeometryOfNumbers.Analysis

-- Recovery round 9: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis
#print axioms c2GlobalGreenAnalysis
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_apply
#print axioms c2GlobalGreenAnalysis_apply
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_norm_sq_bounds
#print axioms c2GlobalGreenAnalysis_norm_sq_bounds
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_split_external_bulk
#print axioms c2GlobalGreenAnalysis_split_external_bulk
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_split_residual_depthOne_bulk
#print axioms c2GlobalGreenAnalysis_split_residual_depthOne_bulk
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_split_seedResidual_green
#print axioms c2GlobalGreenAnalysis_split_seedResidual_green
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenAnalysis_split_three
#print axioms c2GlobalGreenAnalysis_split_three
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInputIsometry
#print axioms c2GlobalGreenInputIsometry
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_adjoint_comp_self
#print axioms c2GlobalGreenInput_adjoint_comp_self
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_apply
#print axioms c2GlobalGreenInput_apply
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_closed_form
#print axioms c2GlobalGreenInput_closed_form
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_even
#print axioms c2GlobalGreenInput_even
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_norm
#print axioms c2GlobalGreenInput_norm
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_one
#print axioms c2GlobalGreenInput_one
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_provenance
#print axioms c2GlobalGreenInput_provenance
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_quadrature_roundtrip
#print axioms c2GlobalGreenInput_quadrature_roundtrip
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalGreenInput_seedResidual_eq_residual
#print axioms c2GlobalGreenInput_seedResidual_eq_residual
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRawGreenDefect
#print axioms c2GlobalRawGreenDefect
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRawGreenDefect_bounds
#print axioms c2GlobalRawGreenDefect_bounds
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRawGreenDefect_eq_gram_defect
#print axioms c2GlobalRawGreenDefect_eq_gram_defect
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRawGreenDefect_split
#print axioms c2GlobalRawGreenDefect_split
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRawGreenDefect_zero
#print axioms c2GlobalRawGreenDefect_zero
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram
#print axioms c2GlobalRestrictedGreenGram
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_bijective
#print axioms c2GlobalRestrictedGreenGram_bijective
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_bounds
#print axioms c2GlobalRestrictedGreenGram_bounds
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_compression
#print axioms c2GlobalRestrictedGreenGram_compression
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero
#print axioms c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_eq_one_iff_norm
#print axioms c2GlobalRestrictedGreenGram_eq_one_iff_norm
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_inner
#print axioms c2GlobalRestrictedGreenGram_inner
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_isUnit
#print axioms c2GlobalRestrictedGreenGram_isUnit
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_positive
#print axioms c2GlobalRestrictedGreenGram_positive
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_source_factors
#print axioms c2GlobalRestrictedGreenGram_source_factors
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalRestrictedGreenGram_strictlyPositive
#print axioms c2GlobalRestrictedGreenGram_strictlyPositive
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms c2GlobalSource_adjoint_comp_self
#print axioms c2GlobalSource_adjoint_comp_self
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialGreenCoordinates
#print axioms oddMaterialGreenCoordinates
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState
#print axioms oddMaterialToGreenState
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_adjoint_comp_self
#print axioms oddMaterialToGreenState_adjoint_comp_self
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_apply
#print axioms oddMaterialToGreenState_apply
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_apply_off_sector
#print axioms oddMaterialToGreenState_apply_off_sector
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_even
#print axioms oddMaterialToGreenState_even
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_norm
#print axioms oddMaterialToGreenState_norm
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms oddMaterialToGreenState_one
#print axioms oddMaterialToGreenState_one
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry
#print axioms realPlaneToComplexIsometry
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry_coordinate_roundtrip
#print axioms realPlaneToComplexIsometry_coordinate_roundtrip
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry_im
#print axioms realPlaneToComplexIsometry_im
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry_normSq
#print axioms realPlaneToComplexIsometry_normSq
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry_re
#print axioms realPlaneToComplexIsometry_re
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
#assert_analysis_axioms realPlaneToComplexIsometry_scale_rotate
#print axioms realPlaneToComplexIsometry_scale_rotate
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge

-- Recovery round 10: named kernel guards for the ported declarations.
namespace GreenFrame.Concrete
#assert_analysis_axioms canonicalCarryElementaryAtlas_isometry
#print axioms canonicalCarryElementaryAtlas_isometry
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms elementaryAtlasLinearIsometry
#print axioms elementaryAtlasLinearIsometry
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms elementaryAtlas_isometry
#print axioms elementaryAtlas_isometry
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms elementaryAtlas_norm_sq_eq
#print axioms elementaryAtlas_norm_sq_eq
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms greenCoordinate_eq_canonicalNormalizedTowerTFVD
#print axioms greenCoordinate_eq_canonicalNormalizedTowerTFVD
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms greenMass_add_residualMass
#print axioms greenMass_add_residualMass
end GreenFrame.Concrete
namespace GreenFrame.Concrete
#assert_analysis_axioms verticalGreenStencil_eq_canonicalNormalizedTowerTFVD
#print axioms verticalGreenStencil_eq_canonicalNormalizedTowerTFVD
end GreenFrame.Concrete
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms PreStencilSpace
#print axioms PreStencilSpace
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms c2GlobalPreStencilIsometry
#print axioms c2GlobalPreStencilIsometry
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms c2GlobalPreStencil_apply
#print axioms c2GlobalPreStencil_apply
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms c2GlobalPreStencil_norm
#print axioms c2GlobalPreStencil_norm
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms c2GlobalRawGreenDefect_eq_stencil_defect
#print axioms c2GlobalRawGreenDefect_eq_stencil_defect
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms c2GlobalRestrictedGreenGram_stencil_defect
#print axioms c2GlobalRestrictedGreenGram_stencil_defect
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms canonicalDirectGreenMass_add_residualEventMass
#print axioms canonicalDirectGreenMass_add_residualEventMass
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms concreteAnalysis_norm_defect_eq_stencil_defect
#print axioms concreteAnalysis_norm_defect_eq_stencil_defect
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms concreteAnalysis_norm_sq_sub_preStencil_norm_sq
#print axioms concreteAnalysis_norm_sq_sub_preStencil_norm_sq
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis
#print axioms directGreenAnalysis
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysisLinearMap
#print axioms directGreenAnalysisLinearMap
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysisOperator
#print axioms directGreenAnalysisOperator
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis_add
#print axioms directGreenAnalysis_add
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis_apply
#print axioms directGreenAnalysis_apply
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis_norm_le
#print axioms directGreenAnalysis_norm_le
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis_norm_sq_eq
#print axioms directGreenAnalysis_norm_sq_eq
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenAnalysis_smul
#print axioms directGreenAnalysis_smul
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenCoordinate
#print axioms directGreenCoordinate
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenCoordinate_normSq_eq
#print axioms directGreenCoordinate_normSq_eq
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenCoordinate_normSq_summable
#print axioms directGreenCoordinate_normSq_summable
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenEnergyTerm
#print axioms directGreenEnergyTerm
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenEnergyTerm_nonneg
#print axioms directGreenEnergyTerm_nonneg
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenEnergyTerm_summable
#print axioms directGreenEnergyTerm_summable
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreenMass_add_residualEventMass
#print axioms directGreenMass_add_residualEventMass
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms directGreen_add_residual_eq_elementaryCamera
#print axioms directGreen_add_residual_eq_elementaryCamera
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenCoordinate_eq_direct_add_ancestorCorrection
#print axioms greenCoordinate_eq_direct_add_ancestorCorrection
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrection
#print axioms greenStencilCorrection
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrectionAnalysis
#print axioms greenStencilCorrectionAnalysis
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrectionAnalysis_apply
#print axioms greenStencilCorrectionAnalysis_apply
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrectionOperator
#print axioms greenStencilCorrectionOperator
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrectionOperator_apply
#print axioms greenStencilCorrectionOperator_apply
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms greenStencilCorrection_eq
#print axioms greenStencilCorrection_eq
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis
#print axioms preStencilAnalysis
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis_add
#print axioms preStencilAnalysis_add
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis_norm
#print axioms preStencilAnalysis_norm
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis_norm_sq_eq
#print axioms preStencilAnalysis_norm_sq_eq
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis_norm_sq_eq_components
#print axioms preStencilAnalysis_norm_sq_eq_components
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilAnalysis_smul
#print axioms preStencilAnalysis_smul
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilLinearIsometry
#print axioms preStencilLinearIsometry
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
#assert_analysis_axioms preStencilRealLinearIsometry
#print axioms preStencilRealLinearIsometry
end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary

-- Recovery round 11: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms allBaseActivity_two_two_mul_odd
#print axioms allBaseActivity_two_two_mul_odd
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoDefect
#print axioms baseTwoDefect
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoDefect_eq_stencilEnergy
#print axioms baseTwoDefect_eq_stencilEnergy
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoDefect_independent_time
#print axioms baseTwoDefect_independent_time
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoDefect_pos
#print axioms baseTwoDefect_pos
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGenerationEvent
#print axioms baseTwoGenerationEvent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGenerationEvent_injective
#print axioms baseTwoGenerationEvent_injective
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenProjection
#print axioms baseTwoGreenProjection
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenProjection_apply
#print axioms baseTwoGreenProjection_apply
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenProjection_idempotent
#print axioms baseTwoGreenProjection_idempotent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenProjection_isSelfAdjoint
#print axioms baseTwoGreenProjection_isSelfAdjoint
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenStencilEnergy_eq_odd_diagonal
#print axioms baseTwoGreenStencilEnergy_eq_odd_diagonal
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenStencilEnergy_pos_of_c2Source_ne_zero
#print axioms baseTwoGreenStencilEnergy_pos_of_c2Source_ne_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreenStencilEnergy_pos_of_core_ne_zero
#print axioms baseTwoGreenStencilEnergy_pos_of_core_ne_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoGreen_c2Source_eq_zero_off_generations
#print axioms baseTwoGreen_c2Source_eq_zero_off_generations
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoOddDiagonalWeight
#print axioms baseTwoOddDiagonalWeight
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwoOddDiagonalWeight_pos
#print axioms baseTwoOddDiagonalWeight_pos
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_code
#print axioms baseTwo_code
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_directGreenAnalysis_c2Source_eq_zero
#print axioms baseTwo_directGreenAnalysis_c2Source_eq_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_firstGeneration_greenCoordinate_normSq
#print axioms baseTwo_firstGeneration_greenCoordinate_normSq
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_nonBaseTwo_norm_sq_add
#print axioms baseTwo_nonBaseTwo_norm_sq_add
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_positive_code
#print axioms baseTwo_positive_code
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_real_code
#print axioms baseTwo_real_code
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms baseTwo_secondGeneration_greenCoordinate_normSq
#print axioms baseTwo_secondGeneration_greenCoordinate_normSq
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms c2GlobalGreenInput_even_eq_zero
#print axioms c2GlobalGreenInput_even_eq_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms c2GlobalGreenInput_exists_nonzero_odd_coordinate
#print axioms c2GlobalGreenInput_exists_nonzero_odd_coordinate
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms c2GlobalGreenInput_normSq_independent_time
#print axioms c2GlobalGreenInput_normSq_independent_time
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms c2GlobalRawGreenDefect_eq_camera_ledger
#print axioms c2GlobalRawGreenDefect_eq_camera_ledger
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms carryCameraWeight_two_four_mul_odd_pos
#print axioms carryCameraWeight_two_four_mul_odd_pos
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms carryCameraWeight_two_pos_of_dvd
#print axioms carryCameraWeight_two_pos_of_dvd
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms carryCameraWeight_two_two_mul_odd_pos
#print axioms carryCameraWeight_two_two_mul_odd_pos
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms carryRatio_baseTwo_sq
#print axioms carryRatio_baseTwo_sq
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms directGreenCoordinate_baseTwo_c2Source_eq_zero
#print axioms directGreenCoordinate_baseTwo_c2Source_eq_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms grandparentIndex_baseTwo_twice
#print axioms grandparentIndex_baseTwo_twice
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms nonBaseTwoDefect
#print axioms nonBaseTwoDefect
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms nonBaseTwoGreenProjection
#print axioms nonBaseTwoGreenProjection
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms nonBaseTwoGreenProjection_apply
#print axioms nonBaseTwoGreenProjection_apply
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms nonBaseTwoGreenProjection_idempotent
#print axioms nonBaseTwoGreenProjection_idempotent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms nonBaseTwoGreenProjection_isSelfAdjoint
#print axioms nonBaseTwoGreenProjection_isSelfAdjoint
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms positionalDepth_two_four_mul_odd
#print axioms positionalDepth_two_four_mul_odd
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms positionalDepth_two_two_mul_odd
#print axioms positionalDepth_two_two_mul_odd
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms restrictedGram_eq_identity_implies_nonBaseTwo_exact_cancellation
#print axioms restrictedGram_eq_identity_implies_nonBaseTwo_exact_cancellation
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms restrictedGram_eq_identity_implies_nonBaseTwo_negative
#print axioms restrictedGram_eq_identity_implies_nonBaseTwo_negative
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms verticalGreenStencil_baseTwo_oddParent
#print axioms verticalGreenStencil_baseTwo_oddParent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms verticalGreenStencil_baseTwo_parent_four_dvd_eq_zero
#print axioms verticalGreenStencil_baseTwo_parent_four_dvd_eq_zero
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms verticalGreenStencil_baseTwo_twiceOddParent
#print axioms verticalGreenStencil_baseTwo_twiceOddParent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
#assert_analysis_axioms verticalGreenStencil_baseTwo_twiceParent
#print axioms verticalGreenStencil_baseTwo_twiceParent
end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger

-- Recovery round 12: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms baseTwoDefect_le_totalDiagonal
#print axioms baseTwoDefect_le_totalDiagonal
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms baseTwoDefect_timeAverage
#print axioms baseTwoDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms c2Source_coordinate_continuous
#print axioms c2Source_coordinate_continuous
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms c2Source_normSq_time
#print axioms c2Source_normSq_time
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms c2Source_phase
#print axioms c2Source_phase
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms camera_log_frequency_pos
#print axioms camera_log_frequency_pos
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms complexTemporalMean
#print axioms complexTemporalMean
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect
#print axioms eventCrossDefect
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_baseTwo_eq_zero
#print axioms eventCrossDefect_baseTwo_eq_zero
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_continuous
#print axioms eventCrossDefect_continuous
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_eq_frequencies
#print axioms eventCrossDefect_eq_frequencies
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_summable
#print axioms eventCrossDefect_summable
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_timeAverage
#print axioms eventCrossDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventCrossDefect_uniform_bound
#print axioms eventCrossDefect_uniform_bound
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect
#print axioms eventDiagonalDefect
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect_baseTwo_eq_green
#print axioms eventDiagonalDefect_baseTwo_eq_green
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect_eq_explicit
#print axioms eventDiagonalDefect_eq_explicit
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect_nonneg
#print axioms eventDiagonalDefect_nonneg
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect_summable
#print axioms eventDiagonalDefect_summable
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventDiagonalDefect_uniform_bound
#print axioms eventDiagonalDefect_uniform_bound
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect
#print axioms eventGreenDefect
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect_continuous
#print axioms eventGreenDefect_continuous
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect_eq_diagonal_add_cross
#print axioms eventGreenDefect_eq_diagonal_add_cross
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect_summable
#print axioms eventGreenDefect_summable
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect_timeAverage
#print axioms eventGreenDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventGreenDefect_uniform_bound
#print axioms eventGreenDefect_uniform_bound
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventUniformBound
#print axioms eventUniformBound
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms eventUniformBound_summable
#print axioms eventUniformBound_summable
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms exists_time_rawGreenDefect_ne_zero
#print axioms exists_time_rawGreenDefect_ne_zero
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms exists_time_rawGreenDefect_pos
#print axioms exists_time_rawGreenDefect_pos
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms exists_time_restrictedGram_ne_identity
#print axioms exists_time_restrictedGram_ne_identity
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms finiteGreenDefect_timeAverage
#print axioms finiteGreenDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms globalCrossDefect_timeAverage
#print axioms globalCrossDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms globalGreenDefect_timeAverage
#print axioms globalGreenDefect_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms globalGreenDefect_timeAverage_positive
#print axioms globalGreenDefect_timeAverage_positive
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms greenMajorant_c2Source_time
#print axioms greenMajorant_c2Source_time
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms not_forall_restrictedGram_eq_identity
#print axioms not_forall_restrictedGram_eq_identity
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms oscillatoryCross
#print axioms oscillatoryCross
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms oscillatoryCross_continuous
#print axioms oscillatoryCross_continuous
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms oscillatoryCross_timeAverage
#print axioms oscillatoryCross_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor
#print axioms phaseFactor
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_add
#print axioms phaseFactor_add
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_conj
#print axioms phaseFactor_conj
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_eq_mk
#print axioms phaseFactor_eq_mk
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_norm
#print axioms phaseFactor_norm
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_timeAverage
#print axioms phaseFactor_timeAverage
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms phaseFactor_zero
#print axioms phaseFactor_zero
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms rawGreenDefect_eq_diagonal_add_cross_tsum
#print axioms rawGreenDefect_eq_diagonal_add_cross_tsum
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms rawGreenDefect_eq_tsum_event
#print axioms rawGreenDefect_eq_tsum_event
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms realPlanePackaging_rotate
#print axioms realPlanePackaging_rotate
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms temporalMean
#print axioms temporalMean
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
#assert_analysis_axioms totalDiagonal_pos
#print axioms totalDiagonal_pos
end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary

-- Recovery round 13: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2GreenInput_gram_identity
#print axioms c2GreenInput_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2PreStencil_gram_identity
#print axioms c2PreStencil_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawGreenDefect_eq_material_norm_sq_sub
#print axioms c2RawGreenDefect_eq_material_norm_sq_sub
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawMetricDefect_is_stencil_defect
#print axioms c2RawMetricDefect_is_stencil_defect
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawMetricWitness
#print axioms c2RawMetricWitness
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawMetricWitness_exists_time_defect_pos
#print axioms c2RawMetricWitness_exists_time_defect_pos
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawMetricWitness_ne_zero
#print axioms c2RawMetricWitness_ne_zero
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RawMetricWitness_norm
#print axioms c2RawMetricWitness_norm
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RestrictedGreenGram_eq_W_J_frame_J_W
#print axioms c2RestrictedGreenGram_eq_W_J_frame_J_W
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RestrictedGreenGram_eq_source_frame_compression
#print axioms c2RestrictedGreenGram_eq_source_frame_compression
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms c2RestrictedGreenGram_not_uniform_identity
#print axioms c2RestrictedGreenGram_not_uniform_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalC2GreenAnalysis_norm
#print axioms canonicalC2GreenAnalysis_norm
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalGreenAnalysis_eq_raw_comp_inverseSqrt
#print axioms canonicalGreenAnalysis_eq_raw_comp_inverseSqrt
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalGreenAnalysis_gram_identity
#print axioms canonicalGreenAnalysis_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalGreenAnalysis_isometry
#print axioms canonicalGreenAnalysis_isometry
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalGreenAnalysis_norm
#print axioms canonicalGreenAnalysis_norm
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreenAnalysis
#print axioms canonicalRawGreenAnalysis
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreenAnalysis_ne_canonicalAnalysis
#print axioms canonicalRawGreenAnalysis_ne_canonicalAnalysis
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreenAnalysis_not_isometry
#print axioms canonicalRawGreenAnalysis_not_isometry
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreenFrameBounds
#print axioms canonicalRawGreenFrameBounds
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreen_frameOperator_ne_identity
#print axioms canonicalRawGreen_frameOperator_ne_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreen_inverseSqrtFrame_ne_identity
#print axioms canonicalRawGreen_inverseSqrtFrame_ne_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms canonicalRawGreen_inverseSqrt_normalization
#print axioms canonicalRawGreen_inverseSqrt_normalization
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms criticalBranch_gram_identity
#print axioms criticalBranch_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms elementaryAtlas_gram_identity
#print axioms elementaryAtlas_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms exists_c2_state_rawGreen_norm_gt
#print axioms exists_c2_state_rawGreen_norm_gt
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms exists_c2_time_rawGreen_norm_gt
#print axioms exists_c2_time_rawGreen_norm_gt
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms exists_c2_time_rawGreen_norm_sq_gt
#print axioms exists_c2_time_rawGreen_norm_sq_gt
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms exists_c2_unit_state_rawGreen_norm_gt
#print axioms exists_c2_unit_state_rawGreen_norm_gt
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms globalPhysicalBranch_gram_identity
#print axioms globalPhysicalBranch_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms materialInclusion_gram_identity
#print axioms materialInclusion_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms preStencil_gram_identity
#print axioms preStencil_gram_identity
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
#assert_analysis_axioms rawGreen_realGram_eq_frameOperator_restrictScalars
#print axioms rawGreen_realGram_eq_frameOperator_restrictScalars
end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy

-- Recovery round 14: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms c2Source_log_domain_iff
#print axioms c2Source_log_domain_iff
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms c2Source_log_domain_time_independent
#print axioms c2Source_log_domain_time_independent
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms c2Source_materialLog_hasDerivAt
#print axioms c2Source_materialLog_hasDerivAt
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenMaterialBasisVector
#print axioms greenMaterialBasisVector
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenMaterialBasisVector_mem_domain
#print axioms greenMaterialBasisVector_mem_domain
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator
#print axioms greenStateMaterialLogGenerator
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_apply
#print axioms greenStateMaterialLogGenerator_apply
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_basisVector_log
#print axioms greenStateMaterialLogGenerator_basisVector_log
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_dense_domain
#print axioms greenStateMaterialLogGenerator_dense_domain
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_domain_iff_log_moment
#print axioms greenStateMaterialLogGenerator_domain_iff_log_moment
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_domain_iff_memℓp
#print axioms greenStateMaterialLogGenerator_domain_iff_memℓp
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_isClosed
#print axioms greenStateMaterialLogGenerator_isClosed
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_isSelfAdjoint
#print axioms greenStateMaterialLogGenerator_isSelfAdjoint
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms greenStateMaterialLogGenerator_mem_domain_iff
#print axioms greenStateMaterialLogGenerator_mem_domain_iff
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms materialLogPhase_hasDerivAt
#print axioms materialLogPhase_hasDerivAt
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms natEquivPNat
#print axioms natEquivPNat
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms natEquivPNat_symm
#print axioms natEquivPNat_symm
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms natEquivPNat_symm_add_one
#print axioms natEquivPNat_symm_add_one
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms natEquivPNat_val
#print axioms natEquivPNat_val
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms nativeLogHilbertEquivGreenState
#print axioms nativeLogHilbertEquivGreenState
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms nativeLogHilbertEquivGreenState_apply
#print axioms nativeLogHilbertEquivGreenState_apply
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms nativeLogHilbertEquivGreenState_basisVector
#print axioms nativeLogHilbertEquivGreenState_basisVector
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms nativeLogHilbertEquivGreenState_norm
#print axioms nativeLogHilbertEquivGreenState_norm
end GeometryOfNumbers.Analysis.GreenStateMaterialLog
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
#assert_analysis_axioms nativeLogHilbertEquivGreenState_symm_apply
#print axioms nativeLogHilbertEquivGreenState_symm_apply
end GeometryOfNumbers.Analysis.GreenStateMaterialLog

-- Recovery round 14: minimal prerequisite NativeMaterialLogClock.
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms InfiniteRealSpectralHilbert
#print axioms InfiniteRealSpectralHilbert
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralFrequency
#print axioms infiniteRealSpectralFrequency
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralMaximalDomain
#print axioms infiniteRealSpectralMaximalDomain
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator
#print axioms infiniteRealSpectralGenerator
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_domain_eq
#print axioms infiniteRealSpectralGenerator_domain_eq
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_apply
#print axioms infiniteRealSpectralGenerator_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms mem_infiniteRealSpectralGenerator_domain
#print axioms mem_infiniteRealSpectralGenerator_domain
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralBasisVector
#print axioms infiniteRealSpectralBasisVector
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralBasisVector_mem_domain
#print axioms infiniteRealSpectralBasisVector_mem_domain
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_basisVector
#print axioms infiniteRealSpectralGenerator_basisVector
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralHilbertBasis
#print axioms infiniteRealSpectralHilbertBasis
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralHilbertBasis_apply
#print axioms infiniteRealSpectralHilbertBasis_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_dense_domain
#print axioms infiniteRealSpectralGenerator_dense_domain
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_isFormalAdjoint
#print axioms infiniteRealSpectralGenerator_isFormalAdjoint
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_adjoint_apply
#print axioms infiniteRealSpectralGenerator_adjoint_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_adjoint_domain_le
#print axioms infiniteRealSpectralGenerator_adjoint_domain_le
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_isSelfAdjoint
#print axioms infiniteRealSpectralGenerator_isSelfAdjoint
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralGenerator_isClosed
#print axioms infiniteRealSpectralGenerator_isClosed
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase
#print axioms infiniteRealSpectralPhase
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase_zero
#print axioms infiniteRealSpectralPhase_zero
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase_add
#print axioms infiniteRealSpectralPhase_add
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase_neg_mul
#print axioms infiniteRealSpectralPhase_neg_mul
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase_mul_neg
#print axioms infiniteRealSpectralPhase_mul_neg
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms conj_infiniteRealSpectralPhase
#print axioms conj_infiniteRealSpectralPhase
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms norm_infiniteRealSpectralPhase
#print axioms norm_infiniteRealSpectralPhase
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralPhase_mul_memℓp
#print axioms infiniteRealSpectralPhase_mul_memℓp
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolutionLinearEquiv
#print axioms infiniteRealSpectralEvolutionLinearEquiv
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolutionLinearEquiv_apply
#print axioms infiniteRealSpectralEvolutionLinearEquiv_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution
#print axioms infiniteRealSpectralEvolution
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution_apply
#print axioms infiniteRealSpectralEvolution_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution_zero
#print axioms infiniteRealSpectralEvolution_zero
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution_add
#print axioms infiniteRealSpectralEvolution_add
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution_neg
#print axioms infiniteRealSpectralEvolution_neg
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms infiniteRealSpectralEvolution_norm
#print axioms infiniteRealSpectralEvolution_norm
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms NativeLogHilbert
#print axioms NativeLogHilbert
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeLogGenerator
#print axioms nativeLogGenerator
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeLogGenerator_isSelfAdjoint
#print axioms nativeLogGenerator_isSelfAdjoint
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeLogBasisVector_mem_domain
#print axioms nativeLogBasisVector_mem_domain
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeLogGenerator_basisVector
#print axioms nativeLogGenerator_basisVector
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeLogGenerator_basisVector_log
#print axioms nativeLogGenerator_basisVector_log
end GeometryOfNumbers.Analysis

-- Recovery round 15: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms ParsevalOrthogonal
#print axioms ParsevalOrthogonal
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms ParsevalRange
#print axioms ParsevalRange
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalAnalysis
#print axioms greenParsevalAnalysis
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalAnalysis_gram_identity
#print axioms greenParsevalAnalysis_gram_identity
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalAnalysis_isometry
#print axioms greenParsevalAnalysis_isometry
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator
#print axioms greenParsevalMaterialLogOperator
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_P_mem_domain_iff
#print axioms greenParsevalMaterialLogOperator_P_mem_domain_iff
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_c2Source_domain_iff_log_moment
#print axioms greenParsevalMaterialLogOperator_c2Source_domain_iff_log_moment
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_c2Source_intertwining
#print axioms greenParsevalMaterialLogOperator_c2Source_intertwining
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_c2Source_mem_domain
#print axioms greenParsevalMaterialLogOperator_c2Source_mem_domain
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_domain_iff
#print axioms greenParsevalMaterialLogOperator_domain_iff
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_eq_zero_of_mem_orthogonal
#print axioms greenParsevalMaterialLogOperator_eq_zero_of_mem_orthogonal
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_intertwining
#print axioms greenParsevalMaterialLogOperator_intertwining
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_isSelfAdjoint
#print axioms greenParsevalMaterialLogOperator_isSelfAdjoint
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal
#print axioms greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_transported_basis
#print axioms greenParsevalMaterialLogOperator_transported_basis
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalMaterialLogOperator_transported_basis_ne_zero
#print axioms greenParsevalMaterialLogOperator_transported_basis_ne_zero
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms greenParsevalOrthogonalDecomposition
#print axioms greenParsevalOrthogonalDecomposition
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeMaterialLogGenerator
#print axioms parsevalRangeMaterialLogGenerator
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeMaterialLogGenerator_domain_iff
#print axioms parsevalRangeMaterialLogGenerator_domain_iff
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeMaterialLogGenerator_intertwines
#print axioms parsevalRangeMaterialLogGenerator_intertwines
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeMaterialLogGenerator_isSelfAdjoint
#print axioms parsevalRangeMaterialLogGenerator_isSelfAdjoint
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff
#print axioms parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeSubmodule
#print axioms parsevalRangeSubmodule
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeUnitary
#print axioms parsevalRangeUnitary
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRangeUnitary_apply
#print axioms parsevalRangeUnitary_apply
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRange_completeSpace
#print axioms parsevalRange_completeSpace
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
#assert_analysis_axioms parsevalRange_isClosed
#print axioms parsevalRange_isClosed
end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms hilbertPartialProdZero
#print axioms hilbertPartialProdZero
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms hilbertPartialProdZero_apply
#print axioms hilbertPartialProdZero_apply
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms hilbertPartialProdZero_dense_domain
#print axioms hilbertPartialProdZero_dense_domain
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms hilbertPartialProdZero_isSelfAdjoint
#print axioms hilbertPartialProdZero_isSelfAdjoint
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms hilbertPartialProdZero_mem_domain_iff
#print axioms hilbertPartialProdZero_mem_domain_iff
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms selfAdjointZeroExtension
#print axioms selfAdjointZeroExtension
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms selfAdjointZeroExtension_apply
#print axioms selfAdjointZeroExtension_apply
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms selfAdjointZeroExtension_domain_iff
#print axioms selfAdjointZeroExtension_domain_iff
end GeometryOfNumbers.Analysis.UnitaryZeroExtension
namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension
#assert_analysis_axioms selfAdjointZeroExtension_isSelfAdjoint
#print axioms selfAdjointZeroExtension_isSelfAdjoint
end GeometryOfNumbers.Analysis.UnitaryZeroExtension

-- Recovery round 16: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution
#print axioms greenParsevalMaterialEvolution
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_add
#print axioms greenParsevalMaterialEvolution_add
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_apply
#print axioms greenParsevalMaterialEvolution_apply
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_apply_adjoint
#print axioms greenParsevalMaterialEvolution_apply_adjoint
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_c2Source
#print axioms greenParsevalMaterialEvolution_c2Source
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_c2Source_add
#print axioms greenParsevalMaterialEvolution_c2Source_add
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_derivative_on_range
#print axioms greenParsevalMaterialEvolution_derivative_on_range
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_eq_self_of_mem_orthogonal
#print axioms greenParsevalMaterialEvolution_eq_self_of_mem_orthogonal
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_hasDerivative_zero
#print axioms greenParsevalMaterialEvolution_hasDerivative_zero
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_intertwining
#print axioms greenParsevalMaterialEvolution_intertwining
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_neg
#print axioms greenParsevalMaterialEvolution_neg
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_norm
#print axioms greenParsevalMaterialEvolution_norm
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_stronglyContinuous
#print axioms greenParsevalMaterialEvolution_stronglyContinuous
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms greenParsevalMaterialEvolution_zero
#print axioms greenParsevalMaterialEvolution_zero
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms parsevalRangeMaterialEvolution
#print axioms parsevalRangeMaterialEvolution
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms parsevalRangeMaterialEvolution_add
#print axioms parsevalRangeMaterialEvolution_add
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms parsevalRangeMaterialEvolution_apply
#print axioms parsevalRangeMaterialEvolution_apply
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms parsevalRangeMaterialEvolution_zero
#print axioms parsevalRangeMaterialEvolution_zero
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
#assert_analysis_axioms parsevalRange_inverse_projection_eq_adjoint
#print axioms parsevalRange_inverse_projection_eq_adjoint
end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms c2GlobalGreenInput_evolution_add
#print axioms c2GlobalGreenInput_evolution_add
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution
#print axioms greenStateMaterialEvolution
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_add
#print axioms greenStateMaterialEvolution_add
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_apply
#print axioms greenStateMaterialEvolution_apply
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_basis
#print axioms greenStateMaterialEvolution_basis
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_differentiableAt_zero_iff
#print axioms greenStateMaterialEvolution_differentiableAt_zero_iff
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_hasDerivative_zero
#print axioms greenStateMaterialEvolution_hasDerivative_zero
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_mem_domain_of_hasDerivative_zero
#print axioms greenStateMaterialEvolution_mem_domain_of_hasDerivative_zero
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_native_intertwining
#print axioms greenStateMaterialEvolution_native_intertwining
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_neg
#print axioms greenStateMaterialEvolution_neg
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_norm
#print axioms greenStateMaterialEvolution_norm
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_stronglyContinuous
#print axioms greenStateMaterialEvolution_stronglyContinuous
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_stronglyContinuous_at_zero
#print axioms greenStateMaterialEvolution_stronglyContinuous_at_zero
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialEvolution_zero
#print axioms greenStateMaterialEvolution_zero
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase
#print axioms greenStateMaterialPhase
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_add
#print axioms greenStateMaterialPhase_add
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_eq_native
#print axioms greenStateMaterialPhase_eq_native
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_eq_phaseFactor
#print axioms greenStateMaterialPhase_eq_phaseFactor
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_neg
#print axioms greenStateMaterialPhase_neg
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_norm
#print axioms greenStateMaterialPhase_norm
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
namespace GeometryOfNumbers.Analysis.GreenStateMaterialDynamics
#assert_analysis_axioms greenStateMaterialPhase_zero
#print axioms greenStateMaterialPhase_zero
end GeometryOfNumbers.Analysis.GreenStateMaterialDynamics

-- Recovery round 17: named kernel guards for the ported declarations.
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms closedResponseSeries
#print axioms closedResponseSeries
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms closedResponseSeries_camera_quotient
#print axioms closedResponseSeries_camera_quotient
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms externalTail_changes_phi_zero
#print axioms externalTail_changes_phi_zero
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteClockJets_determine_JacobiSection
#print axioms finiteClockJets_determine_JacobiSection
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteClockJets_determine_phiPrefix
#print axioms finiteClockJets_determine_phiPrefix
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteClockJets_to_phi_with_external_germs
#print axioms finiteClockJets_to_phi_with_external_germs
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment
#print axioms finiteLogMoment
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_eq_existing
#print axioms finiteLogMoment_eq_existing
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_formal_logDerivative
#print axioms finiteLogMoment_formal_logDerivative
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_formal_quotient
#print axioms finiteLogMoment_formal_quotient
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_isSequence
#print axioms finiteLogMoment_isSequence
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_recurrence
#print axioms finiteLogMoment_recurrence
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finiteLogMoment_triangular
#print axioms finiteLogMoment_triangular
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finitePhiPrefix_determine_Hankel
#print axioms finitePhiPrefix_determine_Hankel
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms finitePhiPrefix_determine_JacobiSection
#print axioms finitePhiPrefix_determine_JacobiSection
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms headSeries
#print axioms headSeries
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms historicalPhi
#print axioms historicalPhi
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms historicalPhi_congr_head
#print axioms historicalPhi_congr_head
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms historicalScale
#print axioms historicalScale
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms historicalScale_pos
#print axioms historicalScale_pos
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms historicalScaledMoment
#print axioms historicalScaledMoment
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledFiniteHeightOperator
#print axioms scaledFiniteHeightOperator
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledFiniteHeightOperator_charpoly
#print axioms scaledFiniteHeightOperator_charpoly
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledFiniteHeightOperator_eigenvector_formula
#print axioms scaledFiniteHeightOperator_eigenvector_formula
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledFiniteHeightOperator_one
#print axioms scaledFiniteHeightOperator_one
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledFiniteHeight_positive
#print axioms scaledFiniteHeight_positive
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledMoment
#print axioms scaledMoment
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockHeightLedger
#assert_analysis_axioms scaledMoment_hankel_entries
#print axioms scaledMoment_hankel_entries
end GeometryOfNumbers.Analysis.FiniteClockHeightLedger
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms clockJetOrbit
#print axioms clockJetOrbit
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms clockRate
#print axioms clockRate
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteClockJets_to_head
#print axioms finiteClockJets_to_head
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteClockStrongGenerator
#print axioms finiteClockStrongGenerator
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteClockStrongGenerator_pow_apply
#print axioms finiteClockStrongGenerator_pow_apply
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteHeadReadout
#print axioms finiteHeadReadout
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteHeadReadout_hasSum
#print axioms finiteHeadReadout_hasSum
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteHeadReadout_iteratedDerivative
#print axioms finiteHeadReadout_iteratedDerivative
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialBasis
#print axioms finiteMaterialBasis
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialClock
#print axioms finiteMaterialClock
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialClockJet_all_times
#print axioms finiteMaterialClockJet_all_times
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialClockJet_basis
#print axioms finiteMaterialClockJet_basis
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialClockJet_eq_generatorPow
#print axioms finiteMaterialClockJet_eq_generatorPow
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialClock_basis
#print axioms finiteMaterialClock_basis
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialOrbit
#print axioms finiteMaterialOrbit
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialOrbit_basis
#print axioms finiteMaterialOrbit_basis
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finiteMaterialOrbit_coordinate_hasSum
#print axioms finiteMaterialOrbit_coordinate_hasSum
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms finitePhase_eq_exp
#print axioms finitePhase_eq_exp
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalCameraPeriod
#print axioms historicalCameraPeriod
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalCameraRadiiCount
#print axioms historicalCameraRadiiCount
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalCameraWeight
#print axioms historicalCameraWeight
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalCameraWeights
#print axioms historicalCameraWeights
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalCameraWeights_default
#print axioms historicalCameraWeights_default
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalFiniteHeadCoefficient
#print axioms historicalFiniteHeadCoefficient
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalHeadDimension
#print axioms historicalHeadDimension
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalInitialState
#print axioms historicalInitialState
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalQuarter
#print axioms historicalQuarter
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalQuarter_eq_I_pow
#print axioms historicalQuarter_eq_I_pow
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalRotationCoefficient
#print axioms historicalRotationCoefficient
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms historicalRotationCoefficient_exact
#print axioms historicalRotationCoefficient_exact
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms nativeStateSeries_eq_normalizedClockJet
#print axioms nativeStateSeries_eq_normalizedClockJet
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms nativeStateSeries_quadratures
#print axioms nativeStateSeries_quadratures
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteClockJets
#assert_analysis_axioms normalizedClockJet
#print axioms normalizedClockJet
end GeometryOfNumbers.Analysis.FiniteClockJets
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms ChebyshevState
#print axioms ChebyshevState
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms HistoricalChebyshevAdmissible
#print axioms HistoricalChebyshevAdmissible
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms chebyshevRun
#print axioms chebyshevRun
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms chebyshevSeed
#print axioms chebyshevSeed
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms chebyshevStep
#print axioms chebyshevStep
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms chebyshevUpdated
#print axioms chebyshevUpdated
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms finiteClockJets_determine_historicalChebyshev
#print axioms finiteClockJets_determine_historicalChebyshev
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms finiteClockJets_determine_historicalHeight
#print axioms finiteClockJets_determine_historicalHeight
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms historicalChebyshevHeight
#print axioms historicalChebyshevHeight
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms historicalChebyshevHeight_charpoly
#print axioms historicalChebyshevHeight_charpoly
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms historicalChebyshevJacobi
#print axioms historicalChebyshevJacobi
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms historicalChebyshevJacobi_isSymm
#print axioms historicalChebyshevJacobi_isSymm
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
namespace GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev
#assert_analysis_axioms historicalChebyshevJacobi_prefix
#print axioms historicalChebyshevJacobi_prefix
end GeometryOfNumbers.Analysis.FiniteHistoricalChebyshev

-- Recovery round 17: minimal prerequisite FiniteNativeMaterialClock.
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms FiniteRealSpectralHilbert
#print axioms FiniteRealSpectralHilbert
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralFrequency
#print axioms finiteRealSpectralFrequency
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralGenerator
#print axioms finiteRealSpectralGenerator
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralGenerator_apply
#print axioms finiteRealSpectralGenerator_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralGenerator_isSymmetric
#print axioms finiteRealSpectralGenerator_isSymmetric
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralSelfAdjointGenerator
#print axioms finiteRealSpectralSelfAdjointGenerator
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralPhase
#print axioms finiteRealSpectralPhase
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralPhase_zero
#print axioms finiteRealSpectralPhase_zero
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralPhase_add
#print axioms finiteRealSpectralPhase_add
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralPhase_neg_mul
#print axioms finiteRealSpectralPhase_neg_mul
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralPhase_mul_neg
#print axioms finiteRealSpectralPhase_mul_neg
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms conj_finiteRealSpectralPhase
#print axioms conj_finiteRealSpectralPhase
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolutionLinearEquiv
#print axioms finiteRealSpectralEvolutionLinearEquiv
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolutionLinearEquiv_apply
#print axioms finiteRealSpectralEvolutionLinearEquiv_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolution
#print axioms finiteRealSpectralEvolution
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolution_apply
#print axioms finiteRealSpectralEvolution_apply
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolution_zero
#print axioms finiteRealSpectralEvolution_zero
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralEvolution_add
#print axioms finiteRealSpectralEvolution_add
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralBasisVector
#print axioms finiteRealSpectralBasisVector
end GeometryOfNumbers.Analysis.NativeMaterialClock
namespace GeometryOfNumbers.Analysis.NativeMaterialClock
#assert_analysis_axioms finiteRealSpectralGenerator_basisVector
#print axioms finiteRealSpectralGenerator_basisVector
end GeometryOfNumbers.Analysis.NativeMaterialClock

-- Recovery round 17: minimal prerequisite LogarithmicMomentHankel.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms IsLogDerivativeMomentSequence
#print axioms IsLogDerivativeMomentSequence
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms logarithmicMoment_eq
#print axioms logarithmicMoment_eq
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms IsLogDerivativeMomentSequence.unique
#print axioms IsLogDerivativeMomentSequence.unique
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms logarithmicMoment_eq_of_two_relations
#print axioms logarithmicMoment_eq_of_two_relations
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram
#print axioms hankelGram
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel
#print axioms shiftedHankel
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram_apply
#print axioms hankelGram_apply
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel_apply
#print axioms shiftedHankel_apply
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram_isSymm
#print axioms hankelGram_isSymm
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel_isSymm
#print axioms shiftedHankel_isSymm
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram_succ_principal
#print axioms hankelGram_succ_principal
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel_succ_principal
#print axioms shiftedHankel_succ_principal
end GeometryOfNumbers.Analysis

-- Recovery round 17: minimal prerequisite MomentGramPositivity.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms IsMomentGramRepresentation
#print axioms IsMomentGramRepresentation
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms IsShiftedMomentGramRepresentation
#print axioms IsShiftedMomentGramRepresentation
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram_posSemidef_of_gramRepresentation
#print axioms hankelGram_posSemidef_of_gramRepresentation
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms hankelGram_posDef_of_gramRepresentation
#print axioms hankelGram_posDef_of_gramRepresentation
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel_posSemidef_of_gramRepresentation
#print axioms shiftedHankel_posSemidef_of_gramRepresentation
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms shiftedHankel_posDef_of_gramRepresentation
#print axioms shiftedHankel_posDef_of_gramRepresentation
end GeometryOfNumbers.Analysis

-- Recovery round 17: minimal prerequisite FiniteJacobiTransport.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms jacobiCongruence
#print axioms jacobiCongruence
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiTransport
#print axioms finiteJacobiTransport
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiTransport_eq_jacobiCongruence
#print axioms finiteJacobiTransport_eq_jacobiCongruence
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiTransport_posSemidef
#print axioms finiteJacobiTransport_posSemidef
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiTransport_isSymm
#print axioms finiteJacobiTransport_isSymm
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiTransport_posDef
#print axioms finiteJacobiTransport_posDef
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms inverseFactor_vecMul_injective_of_whitening
#print axioms inverseFactor_vecMul_injective_of_whitening
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms FiniteGramWhitening
#print axioms FiniteGramWhitening
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms FiniteGramWhitening.ofIdentity
#print axioms FiniteGramWhitening.ofIdentity
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiSection
#print axioms finiteJacobiSection
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteGramWhitening_identity
#print axioms finiteGramWhitening_identity
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiSection_posSemidef_of_shiftedGram
#print axioms finiteJacobiSection_posSemidef_of_shiftedGram
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiSection_posDef_of_shiftedGram
#print axioms finiteJacobiSection_posDef_of_shiftedGram
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteJacobiSection_isSymm_of_shiftedGram
#print axioms finiteJacobiSection_isSymm_of_shiftedGram
end GeometryOfNumbers.Analysis

-- Recovery round 17: minimal prerequisite CanonicalLDLWhitening.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms LDL_diagEntries_pos
#print axioms LDL_diagEntries_pos
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDLScale
#print axioms canonicalLDLScale
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDLScale_pos
#print axioms canonicalLDLScale_pos
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDLInverseFactor
#print axioms canonicalLDLInverseFactor
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDLInverseFactor_triangular
#print axioms canonicalLDLInverseFactor_triangular
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDL_diagonal_normalization
#print axioms canonicalLDL_diagonal_normalization
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalLDLInverseFactor_whitens
#print axioms canonicalLDLInverseFactor_whitens
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalHankelWhitening
#print axioms canonicalHankelWhitening
end GeometryOfNumbers.Analysis

-- Recovery round 17: minimal prerequisite FiniteHeightOperator.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteHeightEigenvalue
#print axioms finiteHeightEigenvalue
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteHeightEigenvalue_pos
#print axioms finiteHeightEigenvalue_pos
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteHeightOperator
#print axioms finiteHeightOperator
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteHeightOperator_isSymm
#print axioms finiteHeightOperator_isSymm
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms finiteHeightOperator_charpoly
#print axioms finiteHeightOperator_charpoly
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeFiniteHeightOperator
#print axioms nativeFiniteHeightOperator
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms nativeFiniteHeightOperator_charpoly
#print axioms nativeFiniteHeightOperator_charpoly
end GeometryOfNumbers.Analysis

-- Recovery round 17: minimal prerequisite CanonicalFiniteHeight.
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalFiniteJacobiSection
#print axioms canonicalFiniteJacobiSection
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalFiniteJacobiSection_posDef_of_shiftedGram
#print axioms canonicalFiniteJacobiSection_posDef_of_shiftedGram
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalFiniteHeightOperator
#print axioms canonicalFiniteHeightOperator
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalFiniteHeightOperator_isSymm
#print axioms canonicalFiniteHeightOperator_isSymm
end GeometryOfNumbers.Analysis
namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms canonicalFiniteHeightOperator_charpoly
#print axioms canonicalFiniteHeightOperator_charpoly
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

#assert_analysis_axioms criticalMaterialSample
#print axioms criticalMaterialSample
#assert_analysis_axioms criticalMaterialSample_eq_finiteMaterialOrbit
#print axioms criticalMaterialSample_eq_finiteMaterialOrbit
#assert_analysis_axioms baseTwoCenter
#print axioms baseTwoCenter
#assert_analysis_axioms baseTwoLeftLeg
#print axioms baseTwoLeftLeg
#assert_analysis_axioms baseTwoRightLeg
#print axioms baseTwoRightLeg
#assert_analysis_axioms baseTwo_center_eq
#print axioms baseTwo_center_eq
#assert_analysis_axioms baseTwo_leftLeg_eq
#print axioms baseTwo_leftLeg_eq
#assert_analysis_axioms baseTwo_rightLeg_eq
#print axioms baseTwo_rightLeg_eq
#assert_analysis_axioms baseTwoCriticalCenterCell
#print axioms baseTwoCriticalCenterCell
#assert_analysis_axioms baseTwoCriticalCenterCell_eq_causalUnitBracket
#print axioms baseTwoCriticalCenterCell_eq_causalUnitBracket
#assert_analysis_axioms baseTwoFiniteHead
#print axioms baseTwoFiniteHead
#assert_analysis_axioms baseTwo_headDimension
#print axioms baseTwo_headDimension
#assert_analysis_axioms baseTwo_retained_cell_in_head
#print axioms baseTwo_retained_cell_in_head
#assert_analysis_axioms baseTwo_endpoint_incidence
#print axioms baseTwo_endpoint_incidence
#assert_analysis_axioms baseTwoFiniteHead_eq_historicalFiniteHeadReadout
#print axioms baseTwoFiniteHead_eq_historicalFiniteHeadReadout
#assert_analysis_axioms baseTwoFiniteHead_iteratedDerivative
#print axioms baseTwoFiniteHead_iteratedDerivative
#assert_analysis_axioms baseTwoFiniteHead_normalizedClockJet
#print axioms baseTwoFiniteHead_normalizedClockJet
#assert_analysis_axioms criticalMaterialExponent
#print axioms criticalMaterialExponent
#assert_analysis_axioms criticalMaterialSample_eq_cpow
#print axioms criticalMaterialSample_eq_cpow
#assert_analysis_axioms criticalMaterialSample_eq_rpow_phase
#print axioms criticalMaterialSample_eq_rpow_phase
#assert_analysis_axioms baseTwoCriticalCenterCell_norm_le
#print axioms baseTwoCriticalCenterCell_norm_le
#assert_analysis_axioms summable_norm_baseTwoCriticalCenterCell
#print axioms summable_norm_baseTwoCriticalCenterCell
#assert_analysis_axioms summable_baseTwoCriticalCenterCell
#print axioms summable_baseTwoCriticalCenterCell
#assert_analysis_axioms baseTwoCriticalCompleteTail
#print axioms baseTwoCriticalCompleteTail
#assert_analysis_axioms baseTwoCriticalCompleteSignal
#print axioms baseTwoCriticalCompleteSignal
#assert_analysis_axioms baseTwoFiniteHead_add_completeTail
#print axioms baseTwoFiniteHead_add_completeTail
#assert_analysis_axioms baseTwoCompletedSignal_cutoff_independent
#print axioms baseTwoCompletedSignal_cutoff_independent
#assert_analysis_axioms criticalMaterialSample_one
#print axioms criticalMaterialSample_one
#assert_analysis_axioms baseTwo_firstOmittedCell_points
#print axioms baseTwo_firstOmittedCell_points
#assert_analysis_axioms baseTwoCriticalCompleteTail_hasSum
#print axioms baseTwoCriticalCompleteTail_hasSum
#assert_analysis_axioms baseTwoHistoricalReadout_add_completeTail
#print axioms baseTwoHistoricalReadout_add_completeTail

end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

#assert_analysis_axioms baseTwoSynthesizedSignal
#print axioms baseTwoSynthesizedSignal
#assert_analysis_axioms baseTwoSynthesizedSignal_eq_complete
#print axioms baseTwoSynthesizedSignal_eq_complete
#assert_analysis_axioms baseTwoCompletedClockCoefficient
#print axioms baseTwoCompletedClockCoefficient
#assert_analysis_axioms baseTwoSynthesizedClockCoefficient
#print axioms baseTwoSynthesizedClockCoefficient
#assert_analysis_axioms baseTwoSynthesizedSignal_iteratedDeriv
#print axioms baseTwoSynthesizedSignal_iteratedDeriv
#assert_analysis_axioms baseTwoSynthesizedClockCoefficient_eq_complete
#print axioms baseTwoSynthesizedClockCoefficient_eq_complete
#assert_analysis_axioms baseTwoCompletedClockJet_cutoff_independent
#print axioms baseTwoCompletedClockJet_cutoff_independent
#assert_analysis_axioms baseTwoSynthesizedTailCoefficient
#print axioms baseTwoSynthesizedTailCoefficient
#assert_analysis_axioms baseTwoHeadCoefficient_add_synthesizedTailCoefficient
#print axioms baseTwoHeadCoefficient_add_synthesizedTailCoefficient
#assert_analysis_axioms baseTwoSynthesizedTailCoefficient_eq_jetResidual
#print axioms baseTwoSynthesizedTailCoefficient_eq_jetResidual
#assert_analysis_axioms baseTwoSynthesizedTailCoefficient_cutoff_balance
#print axioms baseTwoSynthesizedTailCoefficient_cutoff_balance
#assert_analysis_axioms baseTwoCompletedClockSeries
#print axioms baseTwoCompletedClockSeries
#assert_analysis_axioms baseTwoSynthesizedTailSeries
#print axioms baseTwoSynthesizedTailSeries
#assert_analysis_axioms baseTwoCompletedClockSeries_coeff
#print axioms baseTwoCompletedClockSeries_coeff
#assert_analysis_axioms baseTwoSynthesizedTailSeries_coeff
#print axioms baseTwoSynthesizedTailSeries_coeff
#assert_analysis_axioms baseTwoHeadSeries_add_synthesizedTailSeries
#print axioms baseTwoHeadSeries_add_synthesizedTailSeries
#assert_analysis_axioms baseTwoSynthesizedTailSeries_unique
#print axioms baseTwoSynthesizedTailSeries_unique
#assert_analysis_axioms baseTwoCompletedClockCoefficient_zero
#print axioms baseTwoCompletedClockCoefficient_zero
#assert_analysis_axioms baseTwoSynthesizedTailCoefficient_zero
#print axioms baseTwoSynthesizedTailCoefficient_zero

end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

#assert_analysis_axioms baseTwoClosedResponseSeries
#print axioms baseTwoClosedResponseSeries
#assert_analysis_axioms baseTwoSynthesizedResponseSeries
#print axioms baseTwoSynthesizedResponseSeries
#assert_analysis_axioms baseTwoClosedResponseSeries_eq_synthesized
#print axioms baseTwoClosedResponseSeries_eq_synthesized
#assert_analysis_axioms baseTwoClosedResponseSeries_cutoff_independent
#print axioms baseTwoClosedResponseSeries_cutoff_independent
#assert_analysis_axioms baseTwoClosedResponseSeries_camera_quotient
#print axioms baseTwoClosedResponseSeries_camera_quotient
#assert_analysis_axioms baseTwoHistoricalPhi
#print axioms baseTwoHistoricalPhi
#assert_analysis_axioms baseTwoSynthesizedPhi
#print axioms baseTwoSynthesizedPhi
#assert_analysis_axioms baseTwoHistoricalPhi_eq_synthesized
#print axioms baseTwoHistoricalPhi_eq_synthesized
#assert_analysis_axioms baseTwoHistoricalPhi_cutoff_independent
#print axioms baseTwoHistoricalPhi_cutoff_independent
#assert_analysis_axioms baseTwoSynthesizedPhi_coefficient_formula
#print axioms baseTwoSynthesizedPhi_coefficient_formula
#assert_analysis_axioms baseTwoSynthesizedLogMoment
#print axioms baseTwoSynthesizedLogMoment
#assert_analysis_axioms baseTwoHistoricalLogMoment
#print axioms baseTwoHistoricalLogMoment
#assert_analysis_axioms baseTwoHistoricalLogMoment_eq_synthesized
#print axioms baseTwoHistoricalLogMoment_eq_synthesized
#assert_analysis_axioms baseTwoSynthesizedLogMoment_cutoff_independent
#print axioms baseTwoSynthesizedLogMoment_cutoff_independent
#assert_analysis_axioms baseTwoSynthesizedLogMoment_isSequence
#print axioms baseTwoSynthesizedLogMoment_isSequence
#assert_analysis_axioms baseTwoSynthesizedLogMoment_unique
#print axioms baseTwoSynthesizedLogMoment_unique
#assert_analysis_axioms baseTwoSynthesizedLogMoment_formal_logDerivative
#print axioms baseTwoSynthesizedLogMoment_formal_logDerivative
#assert_analysis_axioms baseTwoSynthesizedLogMoment_formal_quotient
#print axioms baseTwoSynthesizedLogMoment_formal_quotient
#assert_analysis_axioms baseTwoLogMoment_relation_of_formal_identity
#print axioms baseTwoLogMoment_relation_of_formal_identity
#assert_analysis_axioms baseTwoSynthesizedLogMoment_unique_of_formal_identity
#print axioms baseTwoSynthesizedLogMoment_unique_of_formal_identity
#assert_analysis_axioms baseTwoLogMoment_two_formal_constructions_eq
#print axioms baseTwoLogMoment_two_formal_constructions_eq
#assert_analysis_axioms baseTwoSynthesizedLogMoment_depends_only_on_phi
#print axioms baseTwoSynthesizedLogMoment_depends_only_on_phi

end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoSecondDifference_norm_le
#print axioms baseTwoSecondDifference_norm_le
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoComplexMaterialExponent
#print axioms baseTwoComplexMaterialExponent
#assert_analysis_axioms baseTwoComplexCenterCell
#print axioms baseTwoComplexCenterCell
#assert_analysis_axioms baseTwoComplexCompleteSignal
#print axioms baseTwoComplexCompleteSignal
#assert_analysis_axioms baseTwoComplexCenterCell_ofReal
#print axioms baseTwoComplexCenterCell_ofReal
#assert_analysis_axioms baseTwoComplexCompleteSignal_ofReal
#print axioms baseTwoComplexCompleteSignal_ofReal
#assert_analysis_axioms baseTwoComplexCenterCell_norm_le
#print axioms baseTwoComplexCenterCell_norm_le
#assert_analysis_axioms baseTwoComplexCompleteSignal_differentiableOn_ball
#print axioms baseTwoComplexCompleteSignal_differentiableOn_ball
#assert_analysis_axioms baseTwoCriticalCompleteSignal_contDiff
#print axioms baseTwoCriticalCompleteSignal_contDiff
#assert_analysis_axioms baseTwoCriticalCompleteSignal_analyticAt
#print axioms baseTwoCriticalCompleteSignal_analyticAt
#assert_analysis_axioms baseTwoFiniteHead_contDiff
#print axioms baseTwoFiniteHead_contDiff
#assert_analysis_axioms baseTwoCriticalCompleteTail_contDiff
#print axioms baseTwoCriticalCompleteTail_contDiff
#assert_analysis_axioms baseTwoSynthesizedTailCoefficient_eq_normalizedTailJet
#print axioms baseTwoSynthesizedTailCoefficient_eq_normalizedTailJet
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoDressingParameter
#print axioms baseTwoDressingParameter
#assert_analysis_axioms baseTwoCanonicalCameraFactorComplex
#print axioms baseTwoCanonicalCameraFactorComplex
#assert_analysis_axioms baseTwoCanonicalCameraFactor
#print axioms baseTwoCanonicalCameraFactor
#assert_analysis_axioms baseTwoCanonicalCameraFactor_formula
#print axioms baseTwoCanonicalCameraFactor_formula
#assert_analysis_axioms baseTwoCanonicalCameraFactorComplex_differentiable
#print axioms baseTwoCanonicalCameraFactorComplex_differentiable
#assert_analysis_axioms baseTwoCanonicalCameraFactor_analyticAt
#print axioms baseTwoCanonicalCameraFactor_analyticAt
#assert_analysis_axioms baseTwoCanonicalCameraFactor_contDiff
#print axioms baseTwoCanonicalCameraFactor_contDiff
#assert_analysis_axioms baseTwoCanonicalCameraFactor_ne_zero
#print axioms baseTwoCanonicalCameraFactor_ne_zero
#assert_analysis_axioms baseTwoCanonicalCameraFactor_zero
#print axioms baseTwoCanonicalCameraFactor_zero
#assert_analysis_axioms baseTwoCanonicalCameraFactorSeries
#print axioms baseTwoCanonicalCameraFactorSeries
#assert_analysis_axioms baseTwoCanonicalCameraFactorSeries_coeff
#print axioms baseTwoCanonicalCameraFactorSeries_coeff
#assert_analysis_axioms baseTwoCanonicalCameraFactorSeries_constantCoeff
#print axioms baseTwoCanonicalCameraFactorSeries_constantCoeff
#assert_analysis_axioms baseTwoCanonicalCameraFactorSeries_constantCoeff_ne_zero
#print axioms baseTwoCanonicalCameraFactorSeries_constantCoeff_ne_zero
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms canonicalArchimedeanCompletionComplex
#print axioms canonicalArchimedeanCompletionComplex
#assert_analysis_axioms canonicalArchimedeanCompletion
#print axioms canonicalArchimedeanCompletion
#assert_analysis_axioms canonicalArchimedeanCompletion_formula
#print axioms canonicalArchimedeanCompletion_formula
#assert_analysis_axioms canonicalArchimedeanCompletionComplex_differentiableOn_ball
#print axioms canonicalArchimedeanCompletionComplex_differentiableOn_ball
#assert_analysis_axioms canonicalArchimedeanCompletion_analyticAt
#print axioms canonicalArchimedeanCompletion_analyticAt
#assert_analysis_axioms canonicalArchimedeanCompletion_contDiff
#print axioms canonicalArchimedeanCompletion_contDiff
#assert_analysis_axioms canonicalArchimedeanCompletion_zero
#print axioms canonicalArchimedeanCompletion_zero
#assert_analysis_axioms canonicalArchimedeanCompletion_zero_re_neg
#print axioms canonicalArchimedeanCompletion_zero_re_neg
#assert_analysis_axioms canonicalArchimedeanCompletion_zero_ne_zero
#print axioms canonicalArchimedeanCompletion_zero_ne_zero
#assert_analysis_axioms baseTwoCanonicalCompletionSeries
#print axioms baseTwoCanonicalCompletionSeries
#assert_analysis_axioms baseTwoCanonicalCompletionSeries_coeff
#print axioms baseTwoCanonicalCompletionSeries_coeff
#assert_analysis_axioms baseTwoCanonicalCompletionSeries_constantCoeff
#print axioms baseTwoCanonicalCompletionSeries_constantCoeff
#assert_analysis_axioms baseTwoCanonicalCompletionSeries_constantCoeff_ne_zero
#print axioms baseTwoCanonicalCompletionSeries_constantCoeff_ne_zero
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoCanonicalResponse
#print axioms baseTwoCanonicalResponse
#assert_analysis_axioms baseTwoCanonicalResponseSeries
#print axioms baseTwoCanonicalResponseSeries
#assert_analysis_axioms baseTwoCanonicalResponse_analyticAt
#print axioms baseTwoCanonicalResponse_analyticAt
#assert_analysis_axioms baseTwoCanonicalResponseSeries_eq_normalizedJets
#print axioms baseTwoCanonicalResponseSeries_eq_normalizedJets
#assert_analysis_axioms baseTwoCanonicalResponseSeries_coeff
#print axioms baseTwoCanonicalResponseSeries_coeff
#assert_analysis_axioms baseTwoCanonicalClosedResponse_eq
#print axioms baseTwoCanonicalClosedResponse_eq
#assert_analysis_axioms baseTwoCriticalCenterCell_zero_re_nonneg
#print axioms baseTwoCriticalCenterCell_zero_re_nonneg
#assert_analysis_axioms baseTwoCriticalCompleteSignal_zero_re_pos
#print axioms baseTwoCriticalCompleteSignal_zero_re_pos
#assert_analysis_axioms baseTwoCriticalCompleteSignal_zero_im
#print axioms baseTwoCriticalCompleteSignal_zero_im
#assert_analysis_axioms baseTwoCanonicalPhi
#print axioms baseTwoCanonicalPhi
#assert_analysis_axioms baseTwoCanonicalLogMoment
#print axioms baseTwoCanonicalLogMoment
#assert_analysis_axioms baseTwoCanonicalMomentSequence
#print axioms baseTwoCanonicalMomentSequence
#assert_analysis_axioms baseTwoCanonicalPhi_eq_synthesized
#print axioms baseTwoCanonicalPhi_eq_synthesized
#assert_analysis_axioms baseTwoCanonicalLogMoment_eq_synthesized
#print axioms baseTwoCanonicalLogMoment_eq_synthesized
#assert_analysis_axioms baseTwoCanonicalMomentSequence_eq_logMoment
#print axioms baseTwoCanonicalMomentSequence_eq_logMoment
#assert_analysis_axioms baseTwoCanonicalPhi_eq_normalizedEvenJet
#print axioms baseTwoCanonicalPhi_eq_normalizedEvenJet
#assert_analysis_axioms baseTwoCanonicalPhi_zero_pos
#print axioms baseTwoCanonicalPhi_zero_pos
#assert_analysis_axioms baseTwoCanonicalPhi_zero_ne_zero
#print axioms baseTwoCanonicalPhi_zero_ne_zero
#assert_analysis_axioms baseTwoCanonicalLogMoment_isSequence
#print axioms baseTwoCanonicalLogMoment_isSequence
#assert_analysis_axioms baseTwoCanonicalLogMoment_unique
#print axioms baseTwoCanonicalLogMoment_unique
#assert_analysis_axioms baseTwoCanonicalLogMoment_formal_logDerivative
#print axioms baseTwoCanonicalLogMoment_formal_logDerivative
#assert_analysis_axioms baseTwoCanonicalLogMoment_unique_of_formal_identity
#print axioms baseTwoCanonicalLogMoment_unique_of_formal_identity
#assert_analysis_axioms baseTwoCanonicalLogMoment_cutoff_independent
#print axioms baseTwoCanonicalLogMoment_cutoff_independent
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms parityMomentKernel
#print axioms parityMomentKernel
#assert_analysis_axioms IsParityMomentGramRepresentation
#print axioms IsParityMomentGramRepresentation
#assert_analysis_axioms parityMomentGram_even
#print axioms parityMomentGram_even
#assert_analysis_axioms parityMomentGram_odd
#print axioms parityMomentGram_odd
#assert_analysis_axioms parityMomentGram_even_odd_orthogonal
#print axioms parityMomentGram_even_odd_orthogonal
#assert_analysis_axioms hankelPair_posSemidef_of_parityMomentGram
#print axioms hankelPair_posSemidef_of_parityMomentGram
#assert_analysis_axioms hankelPair_posDef_of_parityMomentGram
#print axioms hankelPair_posDef_of_parityMomentGram
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis.CanonicalGreenMomentSeam
#assert_analysis_axioms greenParseval_differentiableAt_iff
#print axioms greenParseval_differentiableAt_iff
#assert_analysis_axioms greenParseval_deriv
#print axioms greenParseval_deriv
#assert_analysis_axioms greenParseval_iteratedDeriv
#print axioms greenParseval_iteratedDeriv
#assert_analysis_axioms greenParseval_contDiffAt_iff
#print axioms greenParseval_contDiffAt_iff
#assert_analysis_axioms greenParseval_inner_real
#print axioms greenParseval_inner_real
#assert_analysis_axioms greenParseval_parityMomentGram_iff
#print axioms greenParseval_parityMomentGram_iff
#assert_analysis_axioms c2MaterialOrbitJet
#print axioms c2MaterialOrbitJet
#assert_analysis_axioms c2ParsevalOrbitJet
#print axioms c2ParsevalOrbitJet
#assert_analysis_axioms c2ParsevalOrbitJet_eq_transport
#print axioms c2ParsevalOrbitJet_eq_transport
#assert_analysis_axioms c2ParsevalOrbitJet_inner
#print axioms c2ParsevalOrbitJet_inner
#assert_analysis_axioms c2ParsevalOrbit_differentiableAt_zero_iff_log_moment
#print axioms c2ParsevalOrbit_differentiableAt_zero_iff_log_moment
#assert_analysis_axioms c2ParsevalOrbit_contDiffAt_iff
#print axioms c2ParsevalOrbit_contDiffAt_iff
#assert_analysis_axioms c2ParsevalOrbitFirstColumn
#print axioms c2ParsevalOrbitFirstColumn
#assert_analysis_axioms baseTwoCanonicalGreenFirstColumnResidual
#print axioms baseTwoCanonicalGreenFirstColumnResidual
#assert_analysis_axioms c2ParsevalOrbitFirstColumn_eq_material
#print axioms c2ParsevalOrbitFirstColumn_eq_material
#assert_analysis_axioms baseTwoCanonicalGreenFirstColumnResidual_eq_material
#print axioms baseTwoCanonicalGreenFirstColumnResidual_eq_material
#assert_analysis_axioms c2ParsevalOrbitFirstColumn_zero
#print axioms c2ParsevalOrbitFirstColumn_zero
#assert_analysis_axioms baseTwoCanonicalGreenFirstColumnResidual_zero
#print axioms baseTwoCanonicalGreenFirstColumnResidual_zero
end GeometryOfNumbers.Analysis.CanonicalGreenMomentSeam

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms parityJetNumber
#print axioms parityJetNumber
#assert_analysis_axioms realMomentDiagonalCoefficient
#print axioms realMomentDiagonalCoefficient
#assert_analysis_axioms polarizedRealMomentCoefficient
#print axioms polarizedRealMomentCoefficient
#assert_analysis_axioms parityJetNumber_injective
#print axioms parityJetNumber_injective
#assert_analysis_axioms realMomentDiagonalCoefficient_even
#print axioms realMomentDiagonalCoefficient_even
#assert_analysis_axioms realMomentDiagonalCoefficient_odd
#print axioms realMomentDiagonalCoefficient_odd
#assert_analysis_axioms polarizedRealMomentCoefficient_even_even
#print axioms polarizedRealMomentCoefficient_even_even
#assert_analysis_axioms polarizedRealMomentCoefficient_odd_odd
#print axioms polarizedRealMomentCoefficient_odd_odd
#assert_analysis_axioms polarizedRealMomentCoefficient_even_odd
#print axioms polarizedRealMomentCoefficient_even_odd
#assert_analysis_axioms polarizedRealMomentCoefficient_odd_even
#print axioms polarizedRealMomentCoefficient_odd_even
#assert_analysis_axioms polarizedRealMomentCoefficient_eq_parityMomentKernel
#print axioms polarizedRealMomentCoefficient_eq_parityMomentKernel
#assert_analysis_axioms polarizedRealMomentCoefficient_shift
#print axioms polarizedRealMomentCoefficient_shift
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms C2RealVerticalChannels
#print axioms C2RealVerticalChannels
#assert_analysis_axioms C2RealTfvdChannels
#print axioms C2RealTfvdChannels
#assert_analysis_axioms c2BranchVerticalCoordinate
#print axioms c2BranchVerticalCoordinate
#assert_analysis_axioms c2BranchVerticalCoordinate_apply
#print axioms c2BranchVerticalCoordinate_apply
#assert_analysis_axioms c2BranchVerticalCoordinates
#print axioms c2BranchVerticalCoordinates
#assert_analysis_axioms c2BranchVerticalCoordinates_injective
#print axioms c2BranchVerticalCoordinates_injective
#assert_analysis_axioms c2FiberTfvdAnalysis
#print axioms c2FiberTfvdAnalysis
#assert_analysis_axioms c2FiberTfvdSynthesis
#print axioms c2FiberTfvdSynthesis
#assert_analysis_axioms c2FiberTfvdSynthesis_analysis
#print axioms c2FiberTfvdSynthesis_analysis
#assert_analysis_axioms c2FiberTfvdAnalysis_injective
#print axioms c2FiberTfvdAnalysis_injective
#assert_analysis_axioms c2OddMaterialTfvdAnalysis
#print axioms c2OddMaterialTfvdAnalysis
#assert_analysis_axioms c2OddMaterialTfvdAnalysis_injective
#print axioms c2OddMaterialTfvdAnalysis_injective
#assert_analysis_axioms c2OddMaterial_verticalCoordinate
#print axioms c2OddMaterial_verticalCoordinate
#assert_analysis_axioms c2UnitOddCore
#print axioms c2UnitOddCore
#assert_analysis_axioms c2ParityIncidenceAddress
#print axioms c2ParityIncidenceAddress
#assert_analysis_axioms c2ParityIncidenceAddress_injective
#print axioms c2ParityIncidenceAddress_injective
#assert_analysis_axioms c2ParityIncidenceCenter
#print axioms c2ParityIncidenceCenter
#assert_analysis_axioms c2ParityIncidenceLeg
#print axioms c2ParityIncidenceLeg
#assert_analysis_axioms c2ParityIncidence_left
#print axioms c2ParityIncidence_left
#assert_analysis_axioms c2ParityIncidence_right
#print axioms c2ParityIncidence_right
#assert_analysis_axioms c2ParityIncidence_depth_recovery
#print axioms c2ParityIncidence_depth_recovery
#assert_analysis_axioms c2ParityIncidence_center_ne_leg
#print axioms c2ParityIncidence_center_ne_leg
#assert_analysis_axioms c2RealIncidenceJet
#print axioms c2RealIncidenceJet
#assert_analysis_axioms c2RealIncidenceJet_linearIndependent
#print axioms c2RealIncidenceJet_linearIndependent
#assert_analysis_axioms c2RealTfvdIncidenceJet
#print axioms c2RealTfvdIncidenceJet
#assert_analysis_axioms c2RealTfvdIncidenceJet_linearIndependent
#print axioms c2RealTfvdIncidenceJet_linearIndependent
#assert_analysis_axioms c2RealTfvdIncidenceJet_even_linearIndependent
#print axioms c2RealTfvdIncidenceJet_even_linearIndependent
#assert_analysis_axioms c2RealTfvdIncidenceJet_odd_linearIndependent
#print axioms c2RealTfvdIncidenceJet_odd_linearIndependent
#assert_analysis_axioms c2RealTfvdIncidenceJet_even_prefix_linearIndependent
#print axioms c2RealTfvdIncidenceJet_even_prefix_linearIndependent
#assert_analysis_axioms c2RealTfvdIncidenceJet_odd_prefix_linearIndependent
#print axioms c2RealTfvdIncidenceJet_odd_prefix_linearIndependent
#assert_analysis_axioms c2CriticalOddMaterialTfvdAnalysis_injective
#print axioms c2CriticalOddMaterialTfvdAnalysis_injective
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms HasC2RealTfvdCenterLegReadout
#print axioms HasC2RealTfvdCenterLegReadout
#assert_analysis_axioms HasBaseTwoCanonicalTfvdCenterLegReadout
#print axioms HasBaseTwoCanonicalTfvdCenterLegReadout
#assert_analysis_axioms c2RealTfvdCenterLegReadout_iff_parityGram
#print axioms c2RealTfvdCenterLegReadout_iff_parityGram
#assert_analysis_axioms c2RealIncidenceJet_inner
#print axioms c2RealIncidenceJet_inner
#assert_analysis_axioms c2RealIncidenceJet_not_parityMomentGram
#print axioms c2RealIncidenceJet_not_parityMomentGram
#assert_analysis_axioms baseTwoRealTfvdCenterLegResidual
#print axioms baseTwoRealTfvdCenterLegResidual
#assert_analysis_axioms baseTwoRealTfvdCenterLegResidual_zero_iff
#print axioms baseTwoRealTfvdCenterLegResidual_zero_iff
#assert_analysis_axioms c2RealIncidenceJet_not_canonicalCenterLegReadout
#print axioms c2RealIncidenceJet_not_canonicalCenterLegReadout
#assert_analysis_axioms c2RealIncidenceJet_residual_not_all_zero
#print axioms c2RealIncidenceJet_residual_not_all_zero
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms c2TfvdReconstructedBranchState
#print axioms c2TfvdReconstructedBranchState
#assert_analysis_axioms c2TfvdReconstructedBranchState_eq
#print axioms c2TfvdReconstructedBranchState_eq
#assert_analysis_axioms c2TfvdReconstructedBranchState_inner
#print axioms c2TfvdReconstructedBranchState_inner
#assert_analysis_axioms c2TfvdReconstructedIncidence_not_parityMomentGram
#print axioms c2TfvdReconstructedIncidence_not_parityMomentGram
#assert_analysis_axioms c2IsometricIncidenceSynthesis_inner
#print axioms c2IsometricIncidenceSynthesis_inner
#assert_analysis_axioms c2IsometricIncidenceSynthesis_linearIndependent
#print axioms c2IsometricIncidenceSynthesis_linearIndependent
#assert_analysis_axioms c2IsometricIncidenceSynthesis_gramPair_posDef
#print axioms c2IsometricIncidenceSynthesis_gramPair_posDef
#assert_analysis_axioms c2IsometricIncidenceSynthesis_hankel_three_ne_gram
#print axioms c2IsometricIncidenceSynthesis_hankel_three_ne_gram
#assert_analysis_axioms c2IsometricIncidenceSynthesis_not_parityMomentGram
#print axioms c2IsometricIncidenceSynthesis_not_parityMomentGram
#assert_analysis_axioms c2IsometricIncidenceSynthesis_not_canonicalParityMomentGram
#print axioms c2IsometricIncidenceSynthesis_not_canonicalParityMomentGram
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis
#assert_analysis_axioms symmetricKrylov_inner_add
#print axioms symmetricKrylov_inner_add
#assert_analysis_axioms krylovSpectralMoment
#print axioms krylovSpectralMoment
#assert_analysis_axioms krylovSpectralMoment_gramRepresentation
#print axioms krylovSpectralMoment_gramRepresentation
#assert_analysis_axioms firstColumn_of_symmetric_implies_hankelGram
#print axioms firstColumn_of_symmetric_implies_hankelGram
#assert_analysis_axioms krylovSpectralMoment_hankel_posSemidef
#print axioms krylovSpectralMoment_hankel_posSemidef
#assert_analysis_axioms krylovSpectralMoment_hankel_posDef
#print axioms krylovSpectralMoment_hankel_posDef
#assert_analysis_axioms krylovSpectralMoment_eq_of_logDerivativeRelations
#print axioms krylovSpectralMoment_eq_of_logDerivativeRelations
end GeometryOfNumbers.Analysis

namespace GeometryOfNumbers.Analysis.FiniteClockKrylov
#assert_analysis_axioms finiteMaterialClock_pow_apply
#print axioms finiteMaterialClock_pow_apply
#assert_analysis_axioms finiteClockStrongGenerator_pow_eq_clockPow
#print axioms finiteClockStrongGenerator_pow_eq_clockPow
#assert_analysis_axioms finiteMaterialClockJet_eq_krylov
#print axioms finiteMaterialClockJet_eq_krylov
#assert_analysis_axioms normalizedClockJet_eq_krylov
#print axioms normalizedClockJet_eq_krylov
#assert_analysis_axioms finiteClockKrylov_eq_dephasedClockJet
#print axioms finiteClockKrylov_eq_dephasedClockJet
#assert_analysis_axioms finiteClockStrongGenerator_skew_inner
#print axioms finiteClockStrongGenerator_skew_inner
#assert_analysis_axioms finiteClockSpectralMoment
#print axioms finiteClockSpectralMoment
#assert_analysis_axioms finiteClockSpectralMoment_gramRepresentation
#print axioms finiteClockSpectralMoment_gramRepresentation
#assert_analysis_axioms normalizedClockJet_inner_eq_krylov
#print axioms normalizedClockJet_inner_eq_krylov
#assert_analysis_axioms finiteClockHeadCoefficient_eq_krylovReadout
#print axioms finiteClockHeadCoefficient_eq_krylovReadout
#assert_analysis_axioms finiteClockKrylov_inner_complex
#print axioms finiteClockKrylov_inner_complex
#assert_analysis_axioms finiteClockEvenJet_firstColumn
#print axioms finiteClockEvenJet_firstColumn
#assert_analysis_axioms finiteClockOddJet_firstColumn
#print axioms finiteClockOddJet_firstColumn
#assert_analysis_axioms finiteClockRawKrylov_even_odd_pairing
#print axioms finiteClockRawKrylov_even_odd_pairing
#assert_analysis_axioms finiteClockRawKrylov_even_odd_pairing_pos
#print axioms finiteClockRawKrylov_even_odd_pairing_pos
#assert_analysis_axioms finiteClockParityKrylov
#print axioms finiteClockParityKrylov
#assert_analysis_axioms finiteClockParityKrylov_even_eq_normalizedJet
#print axioms finiteClockParityKrylov_even_eq_normalizedJet
#assert_analysis_axioms finiteClockParityKrylov_odd_eq_normalizedJet
#print axioms finiteClockParityKrylov_odd_eq_normalizedJet
#assert_analysis_axioms finiteClockParityKrylov_gramRepresentation
#print axioms finiteClockParityKrylov_gramRepresentation
#assert_analysis_axioms finiteClockEvenSpectralMoment_hankelPair_posSemidef
#print axioms finiteClockEvenSpectralMoment_hankelPair_posSemidef
end GeometryOfNumbers.Analysis.FiniteClockKrylov

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms canonicalArchimedeanCompletion_ne_zero
#print axioms canonicalArchimedeanCompletion_ne_zero
#assert_analysis_axioms baseTwoCanonicalDressingScalar
#print axioms baseTwoCanonicalDressingScalar
#assert_analysis_axioms baseTwoCanonicalDressingScalar_ne_zero
#print axioms baseTwoCanonicalDressingScalar_ne_zero
#assert_analysis_axioms baseTwoCanonicalDressingScalar_analyticAt
#print axioms baseTwoCanonicalDressingScalar_analyticAt
#assert_analysis_axioms baseTwoCanonicalResponse_eq_dressing_mul_signal
#print axioms baseTwoCanonicalResponse_eq_dressing_mul_signal
#assert_analysis_axioms baseTwoVectorDressing
#print axioms baseTwoVectorDressing
#assert_analysis_axioms baseTwoVectorDressing_apply
#print axioms baseTwoVectorDressing_apply
#assert_analysis_axioms baseTwoVectorDressing_norm
#print axioms baseTwoVectorDressing_norm
#assert_analysis_axioms baseTwoVectorDressing_injective
#print axioms baseTwoVectorDressing_injective
#assert_analysis_axioms baseTwoVectorDressing_readout_residual
#print axioms baseTwoVectorDressing_readout_residual
#assert_analysis_axioms baseTwoVectorDressing_readout_eq_response_iff
#print axioms baseTwoVectorDressing_readout_eq_response_iff
#assert_analysis_axioms baseTwoVectorDressing_function_readout_iff
#print axioms baseTwoVectorDressing_function_readout_iff
#assert_analysis_axioms baseTwoVectorDressing_hasDerivAt
#print axioms baseTwoVectorDressing_hasDerivAt
#assert_analysis_axioms baseTwoVectorDressing_clock_derivative_residual
#print axioms baseTwoVectorDressing_clock_derivative_residual
#assert_analysis_axioms baseTwoVectorDressing_same_clock_iff
#print axioms baseTwoVectorDressing_same_clock_iff
#assert_analysis_axioms baseTwoGreenVectorDressing
#print axioms baseTwoGreenVectorDressing
#assert_analysis_axioms baseTwoDressedFiniteOrbit_add_tail
#print axioms baseTwoDressedFiniteOrbit_add_tail
#assert_analysis_axioms baseTwoVectorDressing_parseval
#print axioms baseTwoVectorDressing_parseval
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms criticalMaterialGradient
#print axioms criticalMaterialGradient
#assert_analysis_axioms criticalMaterialGradient_eq_nativeLinePowerDifference
#print axioms criticalMaterialGradient_eq_nativeLinePowerDifference
#assert_analysis_axioms criticalMaterialGradient_norm_le
#print axioms criticalMaterialGradient_norm_le
#assert_analysis_axioms summable_norm_criticalMaterialGradient
#print axioms summable_norm_criticalMaterialGradient
#assert_analysis_axioms MaterialGradientL1
#print axioms MaterialGradientL1
#assert_analysis_axioms baseTwoCompletedMaterialGradient
#print axioms baseTwoCompletedMaterialGradient
#assert_analysis_axioms baseTwoCompletedMaterialGradient_apply
#print axioms baseTwoCompletedMaterialGradient_apply
#assert_analysis_axioms baseTwoCompletedMaterialGradientL2
#print axioms baseTwoCompletedMaterialGradientL2
#assert_analysis_axioms baseTwoCompletedMaterialGradientL2_apply
#print axioms baseTwoCompletedMaterialGradientL2_apply
#assert_analysis_axioms criticalMaterialSample_eq_seed_add_gradientPrefix
#print axioms criticalMaterialSample_eq_seed_add_gradientPrefix
#assert_analysis_axioms BaseTwoSeededGradientCarrier
#print axioms BaseTwoSeededGradientCarrier
#assert_analysis_axioms baseTwoCompletedUndressedState
#print axioms baseTwoCompletedUndressedState
#assert_analysis_axioms baseTwoCompletedUndressedState_recover
#print axioms baseTwoCompletedUndressedState_recover
#assert_analysis_axioms baseTwoCellLeftEdge
#print axioms baseTwoCellLeftEdge
#assert_analysis_axioms baseTwoCellRightEdge
#print axioms baseTwoCellRightEdge
#assert_analysis_axioms baseTwoCellLeftEdge_eq
#print axioms baseTwoCellLeftEdge_eq
#assert_analysis_axioms baseTwoCellRightEdge_eq
#print axioms baseTwoCellRightEdge_eq
#assert_analysis_axioms baseTwoCriticalCenterCell_eq_gradientEdges
#print axioms baseTwoCriticalCenterCell_eq_gradientEdges
#assert_analysis_axioms baseTwoCompletedUndressedReadout
#print axioms baseTwoCompletedUndressedReadout
#assert_analysis_axioms baseTwoCompletedUndressedReadout_apply
#print axioms baseTwoCompletedUndressedReadout_apply
#assert_analysis_axioms baseTwoCompletedUndressedReadout_eq_signal
#print axioms baseTwoCompletedUndressedReadout_eq_signal
#assert_analysis_axioms baseTwoCompletedUndressedReadout_dressed_eq_response
#print axioms baseTwoCompletedUndressedReadout_dressed_eq_response
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms MaterialEdgeL2
#print axioms MaterialEdgeL2
#assert_analysis_axioms baseTwoSignedEdge
#print axioms baseTwoSignedEdge
#assert_analysis_axioms baseTwoSignedEdge_injective
#print axioms baseTwoSignedEdge_injective
#assert_analysis_axioms baseTwoRawEdgeCoefficient
#print axioms baseTwoRawEdgeCoefficient
#assert_analysis_axioms baseTwoRawEdgeCoefficient_signedEdge
#print axioms baseTwoRawEdgeCoefficient_signedEdge
#assert_analysis_axioms baseTwoCompletedUndressedReadout_single
#print axioms baseTwoCompletedUndressedReadout_single
#assert_analysis_axioms baseTwoRawL2Witness
#print axioms baseTwoRawL2Witness
#assert_analysis_axioms baseTwoRawL2Witness_apply
#print axioms baseTwoRawL2Witness_apply
#assert_analysis_axioms baseTwoRawL2Witness_signedEdge
#print axioms baseTwoRawL2Witness_signedEdge
#assert_analysis_axioms baseTwoRawL2Witness_norm_sq
#print axioms baseTwoRawL2Witness_norm_sq
#assert_analysis_axioms baseTwoRawL2Witness_norm
#print axioms baseTwoRawL2Witness_norm
#assert_analysis_axioms baseTwoRawL2Witness_readout
#print axioms baseTwoRawL2Witness_readout
#assert_analysis_axioms baseTwoRawL2Readout_not_exists
#print axioms baseTwoRawL2Readout_not_exists
#assert_analysis_axioms baseTwoCompletedReadout_no_rawL2_extension
#print axioms baseTwoCompletedReadout_no_rawL2_extension
#assert_analysis_axioms baseTwoRawL2_no_bounded_boundary_factorization
#print axioms baseTwoRawL2_no_bounded_boundary_factorization
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoCompletedBoundaryPrefix
#print axioms baseTwoCompletedBoundaryPrefix
#assert_analysis_axioms baseTwoCompletedBoundaryValue
#print axioms baseTwoCompletedBoundaryValue
#assert_analysis_axioms baseTwoCompletedBoundaryPrefix_eq_head_sub_seed
#print axioms baseTwoCompletedBoundaryPrefix_eq_head_sub_seed
#assert_analysis_axioms baseTwoCompletedBoundaryPrefix_tendsto
#print axioms baseTwoCompletedBoundaryPrefix_tendsto
#assert_analysis_axioms baseTwoCompletedBoundaryValue_eq_readout_sub_seed
#print axioms baseTwoCompletedBoundaryValue_eq_readout_sub_seed
#assert_analysis_axioms baseTwoCompletedBoundaryValue_add_seed_eq_signal
#print axioms baseTwoCompletedBoundaryValue_add_seed_eq_signal
#assert_analysis_axioms baseTwoCompletedMaterialInteriorPrefix
#print axioms baseTwoCompletedMaterialInteriorPrefix
#assert_analysis_axioms baseTwoCompletedMaterialInteriorPrefix_tendsto
#print axioms baseTwoCompletedMaterialInteriorPrefix_tendsto
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms BaseTwoCompletedBoundaryHilbertCarrier
#print axioms BaseTwoCompletedBoundaryHilbertCarrier
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertPrefixState
#print axioms baseTwoCompletedBoundaryHilbertPrefixState
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertState
#print axioms baseTwoCompletedBoundaryHilbertState
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertState_seed
#print axioms baseTwoCompletedBoundaryHilbertState_seed
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertState_interior
#print axioms baseTwoCompletedBoundaryHilbertState_interior
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertState_boundary
#print axioms baseTwoCompletedBoundaryHilbertState_boundary
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertPrefixState_tendsto
#print axioms baseTwoCompletedBoundaryHilbertPrefixState_tendsto
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertReadout
#print axioms baseTwoCompletedBoundaryHilbertReadout
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertReadout_apply
#print axioms baseTwoCompletedBoundaryHilbertReadout_apply
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertReadout_eq_signal
#print axioms baseTwoCompletedBoundaryHilbertReadout_eq_signal
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertReadout_eq_banachReadout
#print axioms baseTwoCompletedBoundaryHilbertReadout_eq_banachReadout
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertPrefixState_readout
#print axioms baseTwoCompletedBoundaryHilbertPrefixState_readout
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertPrefixState_readout_tendsto
#print axioms baseTwoCompletedBoundaryHilbertPrefixState_readout_tendsto
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoRawL2NormalizedWitness
#print axioms baseTwoRawL2NormalizedWitness
#assert_analysis_axioms baseTwoRawL2NormalizedWitness_norm_sq
#print axioms baseTwoRawL2NormalizedWitness_norm_sq
#assert_analysis_axioms baseTwoRawL2NormalizedWitness_tendsto
#print axioms baseTwoRawL2NormalizedWitness_tendsto
#assert_analysis_axioms baseTwoRawL2Witness_mem_graph
#print axioms baseTwoRawL2Witness_mem_graph
#assert_analysis_axioms baseTwoRawL2NormalizedWitness_mem_graph
#print axioms baseTwoRawL2NormalizedWitness_mem_graph
#assert_analysis_axioms baseTwoRawL2Readout_vertical_graph_limit
#print axioms baseTwoRawL2Readout_vertical_graph_limit
#assert_analysis_axioms baseTwoRawL2Readout_not_closable
#print axioms baseTwoRawL2Readout_not_closable
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms criticalMaterialSample_hasDerivAt
#print axioms criticalMaterialSample_hasDerivAt
#assert_analysis_axioms criticalMaterialGradient_hasDerivAt
#print axioms criticalMaterialGradient_hasDerivAt
#assert_analysis_axioms baseTwoMaterialGradientDiagonalClockResidual
#print axioms baseTwoMaterialGradientDiagonalClockResidual
#assert_analysis_axioms criticalMaterialGradient_deriv_eq_diagonalClock_add_residual
#print axioms criticalMaterialGradient_deriv_eq_diagonalClock_add_residual
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertClockCoordinate
#print axioms baseTwoCompletedBoundaryHilbertClockCoordinate
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertClockCoordinate_eq
#print axioms baseTwoCompletedBoundaryHilbertClockCoordinate_eq
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertInterior_coordinate_hasDerivAt
#print axioms baseTwoCompletedBoundaryHilbertInterior_coordinate_hasDerivAt
#assert_analysis_axioms baseTwoMaterialGradientDiagonalClockResidual_zeroEdge_ne_zero
#print axioms baseTwoMaterialGradientDiagonalClockResidual_zeroEdge_ne_zero
#assert_analysis_axioms criticalMaterialGradient_deriv_zeroEdge_ne_diagonalClock
#print axioms criticalMaterialGradient_deriv_zeroEdge_ne_diagonalClock
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertSeed_hasDerivAt
#print axioms baseTwoCompletedBoundaryHilbertSeed_hasDerivAt
#assert_analysis_axioms baseTwoCompletedBoundaryValue_hasDerivAt
#print axioms baseTwoCompletedBoundaryValue_hasDerivAt
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms FiniteSeedGradientCarrier
#print axioms FiniteSeedGradientCarrier
#assert_analysis_axioms finiteGradientPrefix
#print axioms finiteGradientPrefix
#assert_analysis_axioms finiteGradientPrefix_zero
#print axioms finiteGradientPrefix_zero
#assert_analysis_axioms finiteGradientPrefix_succ
#print axioms finiteGradientPrefix_succ
#assert_analysis_axioms finiteSeedGradientEncode
#print axioms finiteSeedGradientEncode
#assert_analysis_axioms finiteSeedGradientDecode
#print axioms finiteSeedGradientDecode
#assert_analysis_axioms finiteSeedGradientEncode_seed
#print axioms finiteSeedGradientEncode_seed
#assert_analysis_axioms finiteSeedGradientEncode_gradient
#print axioms finiteSeedGradientEncode_gradient
#assert_analysis_axioms finiteSeedGradientDecode_apply
#print axioms finiteSeedGradientDecode_apply
#assert_analysis_axioms finiteSeedGradientDecode_encode
#print axioms finiteSeedGradientDecode_encode
#assert_analysis_axioms finiteSeedGradientEncode_decode
#print axioms finiteSeedGradientEncode_decode
#assert_analysis_axioms finiteSeedGradientEquiv
#print axioms finiteSeedGradientEquiv
#assert_analysis_axioms finiteSeedGradientClock
#print axioms finiteSeedGradientClock
#assert_analysis_axioms finiteSeedGradientClock_seed
#print axioms finiteSeedGradientClock_seed
#assert_analysis_axioms finiteSeedGradientClock_gradient
#print axioms finiteSeedGradientClock_gradient
#assert_analysis_axioms finiteSeedGradientClock_intertwining
#print axioms finiteSeedGradientClock_intertwining
#assert_analysis_axioms finiteSeedGradientOrbit
#print axioms finiteSeedGradientOrbit
#assert_analysis_axioms finiteMaterialOrbit_hasDerivAt
#print axioms finiteMaterialOrbit_hasDerivAt
#assert_analysis_axioms finiteSeedGradientOrbit_hasDerivAt
#print axioms finiteSeedGradientOrbit_hasDerivAt
#assert_analysis_axioms baseTwoCell_materialCutoff
#print axioms baseTwoCell_materialCutoff
#assert_analysis_axioms finiteSeedGradientMaterialPairing
#print axioms finiteSeedGradientMaterialPairing
#assert_analysis_axioms finiteSeedGradientClock_materialPairing_symmetric
#print axioms finiteSeedGradientClock_materialPairing_symmetric
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms finiteBaseTwoLeftEdge
#print axioms finiteBaseTwoLeftEdge
#assert_analysis_axioms finiteBaseTwoRightEdge
#print axioms finiteBaseTwoRightEdge
#assert_analysis_axioms finiteCompletedBoundaryReturn
#print axioms finiteCompletedBoundaryReturn
#assert_analysis_axioms FiniteCompletedBoundaryCarrier
#print axioms FiniteCompletedBoundaryCarrier
#assert_analysis_axioms finiteCompletedBoundaryEmbed
#print axioms finiteCompletedBoundaryEmbed
#assert_analysis_axioms finiteCompletedBoundaryForget
#print axioms finiteCompletedBoundaryForget
#assert_analysis_axioms finiteCompletedBoundaryForget_embed
#print axioms finiteCompletedBoundaryForget_embed
#assert_analysis_axioms finiteCompletedBoundaryGraph
#print axioms finiteCompletedBoundaryGraph
#assert_analysis_axioms finiteCompletedBoundaryGraph_mem_iff
#print axioms finiteCompletedBoundaryGraph_mem_iff
#assert_analysis_axioms finiteCompletedBoundaryClock
#print axioms finiteCompletedBoundaryClock
#assert_analysis_axioms finiteCompletedBoundaryClock_graph_invariant
#print axioms finiteCompletedBoundaryClock_graph_invariant
#assert_analysis_axioms finiteCompletedBoundaryClock_boundary
#print axioms finiteCompletedBoundaryClock_boundary
#assert_analysis_axioms finiteCompletedBoundaryGraphEmbed
#print axioms finiteCompletedBoundaryGraphEmbed
#assert_analysis_axioms finiteCompletedBoundaryClock_intertwining
#print axioms finiteCompletedBoundaryClock_intertwining
#assert_analysis_axioms finiteCompletedBoundaryOrbit
#print axioms finiteCompletedBoundaryOrbit
#assert_analysis_axioms finiteCompletedBoundaryOrbit_hasDerivAt
#print axioms finiteCompletedBoundaryOrbit_hasDerivAt
#assert_analysis_axioms finiteSeedGradientOrbit_historical_gradient
#print axioms finiteSeedGradientOrbit_historical_gradient
#assert_analysis_axioms finiteCompletedBoundaryOrbit_historical_boundary
#print axioms finiteCompletedBoundaryOrbit_historical_boundary
#assert_analysis_axioms finiteCompletedBoundaryOrbit_boundary_hasDerivAt
#print axioms finiteCompletedBoundaryOrbit_boundary_hasDerivAt
#assert_analysis_axioms finiteCompletedBoundaryMaterialBasis
#print axioms finiteCompletedBoundaryMaterialBasis
#assert_analysis_axioms finiteCompletedBoundaryClock_materialBasis
#print axioms finiteCompletedBoundaryClock_materialBasis
#assert_analysis_axioms finiteCompletedBoundaryMaterialBasis_one_two_inner
#print axioms finiteCompletedBoundaryMaterialBasis_one_two_inner
#assert_analysis_axioms finiteCompletedBoundaryClock_not_standard_symmetric
#print axioms finiteCompletedBoundaryClock_not_standard_symmetric
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoComplexMaterialGradient
#print axioms baseTwoComplexMaterialGradient
#assert_analysis_axioms baseTwoComplexMaterialGradient_ofReal
#print axioms baseTwoComplexMaterialGradient_ofReal
#assert_analysis_axioms baseTwoComplexMaterialGradient_norm_le
#print axioms baseTwoComplexMaterialGradient_norm_le
#assert_analysis_axioms baseTwoComplexMaterialGradientLp
#print axioms baseTwoComplexMaterialGradientLp
#assert_analysis_axioms baseTwoComplexMaterialGradientLp_differentiableOn_ball
#print axioms baseTwoComplexMaterialGradientLp_differentiableOn_ball
#assert_analysis_axioms baseTwoComplexMaterialGradientLp_ofReal
#print axioms baseTwoComplexMaterialGradientLp_ofReal
#assert_analysis_axioms baseTwoCompletedMaterialGradient_differentiableAt
#print axioms baseTwoCompletedMaterialGradient_differentiableAt
#assert_analysis_axioms baseTwoCompletedMaterialGradientL2_differentiableAt
#print axioms baseTwoCompletedMaterialGradientL2_differentiableAt
#assert_analysis_axioms baseTwoCompletedMaterialGradient_deriv_apply
#print axioms baseTwoCompletedMaterialGradient_deriv_apply
#assert_analysis_axioms baseTwoCompletedMaterialGradientL2_deriv_apply
#print axioms baseTwoCompletedMaterialGradientL2_deriv_apply
#assert_analysis_axioms baseTwoCompletedMaterialClock_memLp_one
#print axioms baseTwoCompletedMaterialClock_memLp_one
#assert_analysis_axioms baseTwoCompletedMaterialClockL1
#print axioms baseTwoCompletedMaterialClockL1
#assert_analysis_axioms baseTwoCompletedMaterialClockL2
#print axioms baseTwoCompletedMaterialClockL2
#assert_analysis_axioms baseTwoCompletedMaterialClockL1_apply
#print axioms baseTwoCompletedMaterialClockL1_apply
#assert_analysis_axioms baseTwoCompletedMaterialClockL2_apply
#print axioms baseTwoCompletedMaterialClockL2_apply
#assert_analysis_axioms baseTwoCompletedMaterialGradient_hasDerivAt_clock
#print axioms baseTwoCompletedMaterialGradient_hasDerivAt_clock
#assert_analysis_axioms baseTwoCompletedMaterialGradientL2_hasDerivAt_clock
#print axioms baseTwoCompletedMaterialGradientL2_hasDerivAt_clock
#assert_analysis_axioms baseTwoCompletedBoundaryClockReturn
#print axioms baseTwoCompletedBoundaryClockReturn
#assert_analysis_axioms summable_baseTwoCompletedBoundaryClockReturn
#print axioms summable_baseTwoCompletedBoundaryClockReturn
#assert_analysis_axioms baseTwoCompletedBoundaryValue_hasDerivAt_clock
#print axioms baseTwoCompletedBoundaryValue_hasDerivAt_clock
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms completedBoundaryClockCoordinates
#print axioms completedBoundaryClockCoordinates
#assert_analysis_axioms completedBoundaryCellReturnCoordinates
#print axioms completedBoundaryCellReturnCoordinates
#assert_analysis_axioms completedBoundaryClockCellCoordinates
#print axioms completedBoundaryClockCellCoordinates
#assert_analysis_axioms completedBoundaryTransportedClockDomain
#print axioms completedBoundaryTransportedClockDomain
#assert_analysis_axioms completedBoundaryTransportedClock
#print axioms completedBoundaryTransportedClock
#assert_analysis_axioms completedBoundaryTransportedClock_seed
#print axioms completedBoundaryTransportedClock_seed
#assert_analysis_axioms completedBoundaryTransportedClock_interior
#print axioms completedBoundaryTransportedClock_interior
#assert_analysis_axioms completedBoundaryTransportedClock_boundary
#print axioms completedBoundaryTransportedClock_boundary
#assert_analysis_axioms completedBoundaryTransportedClock_image_boundary
#print axioms completedBoundaryTransportedClock_image_boundary
#assert_analysis_axioms baseTwoCompletedBoundaryHilbertState_mem_clockDomain
#print axioms baseTwoCompletedBoundaryHilbertState_mem_clockDomain
#assert_analysis_axioms completedBoundaryState_hasDerivAt_clock
#print axioms completedBoundaryState_hasDerivAt_clock
#assert_analysis_axioms completedBoundaryMaterialDeltaOne
#print axioms completedBoundaryMaterialDeltaOne
#assert_analysis_axioms completedBoundaryMaterialDeltaTwo
#print axioms completedBoundaryMaterialDeltaTwo
#assert_analysis_axioms completedBoundaryMaterialDeltaOne_mem_domain
#print axioms completedBoundaryMaterialDeltaOne_mem_domain
#assert_analysis_axioms completedBoundaryMaterialDeltaTwo_mem_domain
#print axioms completedBoundaryMaterialDeltaTwo_mem_domain
#assert_analysis_axioms completedBoundaryTransportedClock_deltaOne
#print axioms completedBoundaryTransportedClock_deltaOne
#assert_analysis_axioms completedBoundaryTransportedClock_deltaTwo
#print axioms completedBoundaryTransportedClock_deltaTwo
#assert_analysis_axioms completedBoundaryMaterialDelta_inner
#print axioms completedBoundaryMaterialDelta_inner
#assert_analysis_axioms completedBoundaryTransportedClock_not_standard_symmetric
#print axioms completedBoundaryTransportedClock_not_standard_symmetric
#assert_analysis_axioms completedBoundaryTransportedClock_not_selfAdjoint
#print axioms completedBoundaryTransportedClock_not_selfAdjoint
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms criticalMaterialSample_norm_sq
#print axioms criticalMaterialSample_norm_sq
#assert_analysis_axioms criticalMaterialSample_not_memℓp
#print axioms criticalMaterialSample_not_memℓp
#assert_analysis_axioms c2PhysicalSource_unitCore_left_energy_ratio
#print axioms c2PhysicalSource_unitCore_left_energy_ratio
#assert_analysis_axioms no_direct_c2PhysicalSource_match
#print axioms no_direct_c2PhysicalSource_match
#assert_analysis_axioms completedClock_isometric_intertwiner_impossible
#print axioms completedClock_isometric_intertwiner_impossible
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms ordinaryGradient_isometric_intertwiner_impossible
#print axioms ordinaryGradient_isometric_intertwiner_impossible
#assert_analysis_axioms finiteMaterialGreenDomain
#print axioms finiteMaterialGreenDomain
#assert_analysis_axioms finiteMaterialGreenEmbedding
#print axioms finiteMaterialGreenEmbedding
#assert_analysis_axioms finiteMaterialGreenEmbedding_sum
#print axioms finiteMaterialGreenEmbedding_sum
#assert_analysis_axioms finiteMaterialGreenEmbedding_apply_index
#print axioms finiteMaterialGreenEmbedding_apply_index
#assert_analysis_axioms finiteMaterialGreenEmbedding_inner
#print axioms finiteMaterialGreenEmbedding_inner
#assert_analysis_axioms finiteMaterialGreenEmbedding_norm
#print axioms finiteMaterialGreenEmbedding_norm
#assert_analysis_axioms finiteMaterialGreenEmbedding_injective
#print axioms finiteMaterialGreenEmbedding_injective
#assert_analysis_axioms finiteMaterialGreenEmbedding_clock
#print axioms finiteMaterialGreenEmbedding_clock
#assert_analysis_axioms finiteCompletedEnrichedSource
#print axioms finiteCompletedEnrichedSource
#assert_analysis_axioms finiteCompletedEnrichedSource_fst
#print axioms finiteCompletedEnrichedSource_fst
#assert_analysis_axioms finiteCompletedEnrichedSource_snd
#print axioms finiteCompletedEnrichedSource_snd
#assert_analysis_axioms finiteCompletedEnrichedSource_injective
#print axioms finiteCompletedEnrichedSource_injective
#assert_analysis_axioms finiteCompletedEnrichedSource_ordinary_orbit
#print axioms finiteCompletedEnrichedSource_ordinary_orbit
#assert_analysis_axioms finiteCompletedEnrichedSource_clockGradient_orbit
#print axioms finiteCompletedEnrichedSource_clockGradient_orbit
#assert_analysis_axioms finiteCompletedGraphDecode
#print axioms finiteCompletedGraphDecode
#assert_analysis_axioms finiteCompletedGraphDecode_injective
#print axioms finiteCompletedGraphDecode_injective
#assert_analysis_axioms finiteCompletedGraphDecode_clock
#print axioms finiteCompletedGraphDecode_clock
#assert_analysis_axioms finiteCompletedGreenIntertwiner
#print axioms finiteCompletedGreenIntertwiner
#assert_analysis_axioms finiteCompletedGreenIntertwiner_injective
#print axioms finiteCompletedGreenIntertwiner_injective
#assert_analysis_axioms finiteCompletedGreenIntertwiner_mem_domain
#print axioms finiteCompletedGreenIntertwiner_mem_domain
#assert_analysis_axioms finiteCompletedGreenIntertwiner_clock
#print axioms finiteCompletedGreenIntertwiner_clock
#assert_analysis_axioms finiteCompletedGreenIntertwiner_norm
#print axioms finiteCompletedGreenIntertwiner_norm
#assert_analysis_axioms finiteCompletedGraphDecode_orbit
#print axioms finiteCompletedGraphDecode_orbit
#assert_analysis_axioms finiteCompletedGreenIntertwiner_pairing_symmetric
#print axioms finiteCompletedGreenIntertwiner_pairing_symmetric
#assert_analysis_axioms finiteCompletedGreenIntertwiner_critical_energy
#print axioms finiteCompletedGreenIntertwiner_critical_energy
#assert_analysis_axioms finiteCompletedGreenIntertwiner_critical_energy_tendsto
#print axioms finiteCompletedGreenIntertwiner_critical_energy_tendsto
#assert_analysis_axioms finiteCompletedGreenIntertwiner_critical_no_limit
#print axioms finiteCompletedGreenIntertwiner_critical_no_limit
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis
#print axioms finiteCompletedEnrichedGreenAnalysis
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis_injective
#print axioms finiteCompletedEnrichedGreenAnalysis_injective
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis_clock
#print axioms finiteCompletedEnrichedGreenAnalysis_clock
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis_critical_energy
#print axioms finiteCompletedEnrichedGreenAnalysis_critical_energy
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis_critical_energy_tendsto
#print axioms finiteCompletedEnrichedGreenAnalysis_critical_energy_tendsto
#assert_analysis_axioms finiteCompletedEnrichedGreenAnalysis_critical_no_limit
#print axioms finiteCompletedEnrichedGreenAnalysis_critical_no_limit
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoNativeOrdinaryGradientFormula
#print axioms baseTwoNativeOrdinaryGradientFormula
#assert_analysis_axioms baseTwoNativeLogGradientFormula
#print axioms baseTwoNativeLogGradientFormula
#assert_analysis_axioms criticalMaterialGradient_eq_nativeOrdinaryFormula
#print axioms criticalMaterialGradient_eq_nativeOrdinaryFormula
#assert_analysis_axioms baseTwoCompletedClockCoordinate_eq_nativeLogFormula
#print axioms baseTwoCompletedClockCoordinate_eq_nativeLogFormula
#assert_analysis_axioms criticalMaterialGradient_hasDerivAt_nativeLogFormula
#print axioms criticalMaterialGradient_hasDerivAt_nativeLogFormula
#assert_analysis_axioms criticalMaterialGradient_deriv_eq_nativeLogFormula
#print axioms criticalMaterialGradient_deriv_eq_nativeLogFormula
#assert_analysis_axioms BaseTwoOrdinaryLogGradientCarrier
#print axioms BaseTwoOrdinaryLogGradientCarrier
#assert_analysis_axioms baseTwoOrdinaryLogGradientState
#print axioms baseTwoOrdinaryLogGradientState
#assert_analysis_axioms baseTwoOrdinaryLogGradientState_ordinary
#print axioms baseTwoOrdinaryLogGradientState_ordinary
#assert_analysis_axioms baseTwoOrdinaryLogGradientState_log
#print axioms baseTwoOrdinaryLogGradientState_log
#assert_analysis_axioms baseTwoOrdinaryLogGradientState_ordinary_apply
#print axioms baseTwoOrdinaryLogGradientState_ordinary_apply
#assert_analysis_axioms baseTwoOrdinaryLogGradientState_log_apply
#print axioms baseTwoOrdinaryLogGradientState_log_apply
#assert_analysis_axioms baseTwoOrdinaryLogGradientState_norm_sq
#print axioms baseTwoOrdinaryLogGradientState_norm_sq
#assert_analysis_axioms baseTwoOrdinaryLogGradientPrefixState
#print axioms baseTwoOrdinaryLogGradientPrefixState
#assert_analysis_axioms baseTwoOrdinaryLogGradientPrefixState_tendsto
#print axioms baseTwoOrdinaryLogGradientPrefixState_tendsto
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms BaseTwoPhysicalEdge
#print axioms BaseTwoPhysicalEdge
#assert_analysis_axioms baseTwoPhysicalEdgeIndex
#print axioms baseTwoPhysicalEdgeIndex
#assert_analysis_axioms baseTwoPhysicalEdgeIndex_left
#print axioms baseTwoPhysicalEdgeIndex_left
#assert_analysis_axioms baseTwoPhysicalEdgeIndex_right
#print axioms baseTwoPhysicalEdgeIndex_right
#assert_analysis_axioms baseTwoPhysicalEdgeIndex_injective
#print axioms baseTwoPhysicalEdgeIndex_injective
#assert_analysis_axioms baseTwoPhysicalEdgeIndex_range
#print axioms baseTwoPhysicalEdgeIndex_range
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint
#print axioms baseTwoPhysicalEdgeOddEndpoint
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint_left
#print axioms baseTwoPhysicalEdgeOddEndpoint_left
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint_right
#print axioms baseTwoPhysicalEdgeOddEndpoint_right
#assert_analysis_axioms oddMaterialPhysicalEdge
#print axioms oddMaterialPhysicalEdge
#assert_analysis_axioms oddMaterialPhysicalEdge_endpoint
#print axioms oddMaterialPhysicalEdge_endpoint
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint_decode
#print axioms baseTwoPhysicalEdgeOddEndpoint_decode
#assert_analysis_axioms baseTwoPhysicalEdgeEquivOddMaterial
#print axioms baseTwoPhysicalEdgeEquivOddMaterial
#assert_analysis_axioms baseTwoPhysicalEdgeEquivC2Address
#print axioms baseTwoPhysicalEdgeEquivC2Address
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address
#print axioms baseTwoPhysicalEdgeC2Address
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address_eq
#print axioms baseTwoPhysicalEdgeC2Address_eq
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address_material
#print axioms baseTwoPhysicalEdgeC2Address_material
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint_neighbor
#print axioms baseTwoPhysicalEdgeOddEndpoint_neighbor
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address_direction
#print axioms baseTwoPhysicalEdgeC2Address_direction
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address_depth
#print axioms baseTwoPhysicalEdgeC2Address_depth
#assert_analysis_axioms baseTwoPhysicalEdgeC2Address_center
#print axioms baseTwoPhysicalEdgeC2Address_center
#assert_analysis_axioms baseTwoPhysicalEdgeOddEndpoint_incidence
#print axioms baseTwoPhysicalEdgeOddEndpoint_incidence
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoPhysicalEdgeRestriction
#print axioms baseTwoPhysicalEdgeRestriction
#assert_analysis_axioms baseTwoPhysicalEdgeRestriction_apply
#print axioms baseTwoPhysicalEdgeRestriction_apply
#assert_analysis_axioms baseTwoPhysicalEdgeRestriction_norm_le
#print axioms baseTwoPhysicalEdgeRestriction_norm_le
#assert_analysis_axioms baseTwoMaterialEdgeRealification
#print axioms baseTwoMaterialEdgeRealification
#assert_analysis_axioms baseTwoMaterialEdgeRealification_pack
#print axioms baseTwoMaterialEdgeRealification_pack
#assert_analysis_axioms baseTwoMaterialEdgeRealification_neg_I
#print axioms baseTwoMaterialEdgeRealification_neg_I
#assert_analysis_axioms baseTwoPhysicalEdgeC2State
#print axioms baseTwoPhysicalEdgeC2State
#assert_analysis_axioms baseTwoPhysicalEdgeC2State_apply
#print axioms baseTwoPhysicalEdgeC2State_apply
#assert_analysis_axioms baseTwoPhysicalEdgeC2State_apply_edge
#print axioms baseTwoPhysicalEdgeC2State_apply_edge
#assert_analysis_axioms baseTwoPhysicalEdgeC2State_norm_le
#print axioms baseTwoPhysicalEdgeC2State_norm_le
#assert_analysis_axioms baseTwoPhysicalEdgeProjection
#print axioms baseTwoPhysicalEdgeProjection
#assert_analysis_axioms baseTwoResidualEdgeProjection
#print axioms baseTwoResidualEdgeProjection
#assert_analysis_axioms baseTwoResidualEdgePredicate
#print axioms baseTwoResidualEdgePredicate
#assert_analysis_axioms baseTwoPhysicalResidual_reconstruction
#print axioms baseTwoPhysicalResidual_reconstruction
#assert_analysis_axioms baseTwoPhysicalResidual_orthogonal
#print axioms baseTwoPhysicalResidual_orthogonal
#assert_analysis_axioms baseTwoPhysicalResidual_norm_sq
#print axioms baseTwoPhysicalResidual_norm_sq
#assert_analysis_axioms baseTwoPhysicalEdgeC2State_projection
#print axioms baseTwoPhysicalEdgeC2State_projection
#assert_analysis_axioms baseTwoPhysicalResidualC2_injective
#print axioms baseTwoPhysicalResidualC2_injective
#assert_analysis_axioms baseTwoPhysicalEdgeC2State_norm_sq_projection
#print axioms baseTwoPhysicalEdgeC2State_norm_sq_projection
#assert_analysis_axioms baseTwoPhysicalC2Residual_norm_sq
#print axioms baseTwoPhysicalC2Residual_norm_sq
#assert_analysis_axioms baseTwoPhysicalOrdinaryC2State
#print axioms baseTwoPhysicalOrdinaryC2State
#assert_analysis_axioms baseTwoPhysicalLogGradientC2State
#print axioms baseTwoPhysicalLogGradientC2State
#assert_analysis_axioms baseTwoPhysicalOrdinaryC2State_apply
#print axioms baseTwoPhysicalOrdinaryC2State_apply
#assert_analysis_axioms baseTwoPhysicalLogGradientC2State_apply
#print axioms baseTwoPhysicalLogGradientC2State_apply
#assert_analysis_axioms baseTwoPhysicalOrdinaryC2State_hasDerivAt
#print axioms baseTwoPhysicalOrdinaryC2State_hasDerivAt
#assert_analysis_axioms baseTwoCompletedBoundaryValue_eq_physicalChannel
#print axioms baseTwoCompletedBoundaryValue_eq_physicalChannel
#assert_analysis_axioms summable_baseTwoPhysicalCellReturn
#print axioms summable_baseTwoPhysicalCellReturn
#assert_analysis_axioms baseTwoPhysicalOrdinaryTfvd
#print axioms baseTwoPhysicalOrdinaryTfvd
#assert_analysis_axioms baseTwoPhysicalLogGradientTfvd
#print axioms baseTwoPhysicalLogGradientTfvd
#assert_analysis_axioms baseTwoPhysicalOrdinaryTfvd_synthesis
#print axioms baseTwoPhysicalOrdinaryTfvd_synthesis
#assert_analysis_axioms baseTwoPhysicalLogGradientTfvd_synthesis
#print axioms baseTwoPhysicalLogGradientTfvd_synthesis
#assert_analysis_axioms baseTwoPhysicalResidualTfvdAnalysis
#print axioms baseTwoPhysicalResidualTfvdAnalysis
#assert_analysis_axioms baseTwoPhysicalResidualTfvdAnalysis_injective
#print axioms baseTwoPhysicalResidualTfvdAnalysis_injective
#assert_analysis_axioms baseTwoCompletedPhysicalResidualTfvdPair
#print axioms baseTwoCompletedPhysicalResidualTfvdPair
#assert_analysis_axioms baseTwoCompletedPhysicalResidualTfvdPair_ordinary
#print axioms baseTwoCompletedPhysicalResidualTfvdPair_ordinary
#assert_analysis_axioms baseTwoCompletedPhysicalResidualTfvdPair_log
#print axioms baseTwoCompletedPhysicalResidualTfvdPair_log
#assert_analysis_axioms baseTwoCriticalPhysicalResidualTfvdPair
#print axioms baseTwoCriticalPhysicalResidualTfvdPair
#assert_analysis_axioms baseTwoCriticalPhysicalTfvd_synthesis
#print axioms baseTwoCriticalPhysicalTfvd_synthesis
#assert_analysis_axioms baseTwoPhysicalTfvdChannel
#print axioms baseTwoPhysicalTfvdChannel
#assert_analysis_axioms baseTwoPhysicalTfvdChannel_apply
#print axioms baseTwoPhysicalTfvdChannel_apply
#assert_analysis_axioms baseTwoPhysicalOrdinaryTfvd_hasDerivAt
#print axioms baseTwoPhysicalOrdinaryTfvd_hasDerivAt
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoPhysicalOddEndpointLog
#print axioms baseTwoPhysicalOddEndpointLog
#assert_analysis_axioms baseTwoPhysicalEndpointClock
#print axioms baseTwoPhysicalEndpointClock
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect
#print axioms baseTwoPhysicalCenterClockDefect
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect_left
#print axioms baseTwoPhysicalCenterClockDefect_left
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect_right
#print axioms baseTwoPhysicalCenterClockDefect_right
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect_decoded_center
#print axioms baseTwoPhysicalCenterClockDefect_decoded_center
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect_norm_le
#print axioms baseTwoPhysicalCenterClockDefect_norm_le
#assert_analysis_axioms baseTwoPhysicalCenterClockDefect_memℓp
#print axioms baseTwoPhysicalCenterClockDefect_memℓp
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectL2
#print axioms baseTwoPhysicalCenterClockDefectL2
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectL2_apply
#print axioms baseTwoPhysicalCenterClockDefectL2_apply
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectC2State
#print axioms baseTwoPhysicalCenterClockDefectC2State
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectC2State_apply
#print axioms baseTwoPhysicalCenterClockDefectC2State_apply
end GeometryOfNumbers.Analysis.BaseTwoCompletion

namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
#assert_analysis_axioms baseTwoPhysicalOddEndpointDiagonalClock
#print axioms baseTwoPhysicalOddEndpointDiagonalClock
#assert_analysis_axioms baseTwoPhysicalOddEndpointDiagonalClock_apply
#print axioms baseTwoPhysicalOddEndpointDiagonalClock_apply
#assert_analysis_axioms baseTwoPhysicalClock_C2_decomposition
#print axioms baseTwoPhysicalClock_C2_decomposition
#assert_analysis_axioms baseTwoPhysicalC2GreenIsometry
#print axioms baseTwoPhysicalC2GreenIsometry
#assert_analysis_axioms baseTwoPhysicalC2GreenIsometry_apply
#print axioms baseTwoPhysicalC2GreenIsometry_apply
#assert_analysis_axioms baseTwoPhysicalC2GreenIsometry_off_sector
#print axioms baseTwoPhysicalC2GreenIsometry_off_sector
#assert_analysis_axioms baseTwoPhysicalC2GreenIsometry_norm
#print axioms baseTwoPhysicalC2GreenIsometry_norm
#assert_analysis_axioms baseTwoPhysicalOrdinaryGreenState
#print axioms baseTwoPhysicalOrdinaryGreenState
#assert_analysis_axioms baseTwoPhysicalLogGradientGreenState
#print axioms baseTwoPhysicalLogGradientGreenState
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectGreenState
#print axioms baseTwoPhysicalCenterClockDefectGreenState
#assert_analysis_axioms baseTwoPhysicalOddEndpointClockGreenState
#print axioms baseTwoPhysicalOddEndpointClockGreenState
#assert_analysis_axioms baseTwoPhysicalOrdinaryGreenState_apply
#print axioms baseTwoPhysicalOrdinaryGreenState_apply
#assert_analysis_axioms baseTwoPhysicalLogGradientGreenState_apply
#print axioms baseTwoPhysicalLogGradientGreenState_apply
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectGreenState_apply
#print axioms baseTwoPhysicalCenterClockDefectGreenState_apply
#assert_analysis_axioms baseTwoPhysicalOddEndpointClockGreenState_apply
#print axioms baseTwoPhysicalOddEndpointClockGreenState_apply
#assert_analysis_axioms baseTwoPhysicalClock_Green_decomposition
#print axioms baseTwoPhysicalClock_Green_decomposition
#assert_analysis_axioms baseTwoPhysicalOrdinaryGreenState_mem_domain
#print axioms baseTwoPhysicalOrdinaryGreenState_mem_domain
#assert_analysis_axioms baseTwoPhysicalMaterialLogGenerator_eq_endpoint
#print axioms baseTwoPhysicalMaterialLogGenerator_eq_endpoint
#assert_analysis_axioms baseTwoPhysicalClock_Green_generator_decomposition
#print axioms baseTwoPhysicalClock_Green_generator_decomposition
#assert_analysis_axioms baseTwoPhysicalOrdinaryParsevalState
#print axioms baseTwoPhysicalOrdinaryParsevalState
#assert_analysis_axioms baseTwoPhysicalLogGradientParsevalState
#print axioms baseTwoPhysicalLogGradientParsevalState
#assert_analysis_axioms baseTwoPhysicalCenterClockDefectParsevalState
#print axioms baseTwoPhysicalCenterClockDefectParsevalState
#assert_analysis_axioms baseTwoPhysicalOrdinaryParsevalState_mem_domain
#print axioms baseTwoPhysicalOrdinaryParsevalState_mem_domain
#assert_analysis_axioms baseTwoPhysicalClock_Parseval_decomposition
#print axioms baseTwoPhysicalClock_Parseval_decomposition
#assert_analysis_axioms baseTwoCenterSample_eq_seed_physical_residual_prefix
#print axioms baseTwoCenterSample_eq_seed_physical_residual_prefix
end GeometryOfNumbers.Analysis.BaseTwoCompletion
