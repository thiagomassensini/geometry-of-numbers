import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling
import GeometryOfNumbers.Analysis.CompleteVerticalObservationGram
import GeometryOfNumbers.Analysis.SeparatedCenterClockObstruction
import GeometryOfNumbers.Analysis.CompletedClockCandidateObstructions

open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section

-- The central coefficient is fixed by the same actual Y0, not chosen freely.
example : carryMaterialClockCentralCoefficient (baseTwoCompletedBoundaryHilbertState 0) = 1 :=
  carryMaterialClock_central_coefficient_zero

-- A nonzero source-derived material contrast survives the projection.
example : carryMaterialCentralEdgeContrast carryMaterialClockCentralForcing =
    ((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ) := carryMaterialClock_forcing_material_coordinate

example : carryMaterialClockCentralForcing ≠ 0 := carryMaterialClock_forcing_nonzero

-- At zero the compressed pair vanishes but its forcing companion remains.
example : carryMaterialCentralPairComplement (carryMaterialCompanionValuePair 0) =
    ((Complex.I*baseTwoCanonicalDressingScalar 0) • carryMaterialClockCentralForcing, 0) := by
  rw [carryMaterialClock_companion_complement, carryMaterialClock_compressed_pair_origin, zero_add]
  simp only [carryMaterialClockForcingPair, carryMaterialClockForcingScalar,
    carryMaterialClock_central_coefficient_zero, mul_one]

-- One nontrivial off-diagonal row, with independent phase parameter u.
example (u : ℝ) : carryMaterialPairGreen
    (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair 0))
    (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair u)) =
    2*Complex.I*conj (baseTwoCanonicalDressingScalar 0)*baseTwoCanonicalDressingScalar u*
      inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState u) :=
  carryMaterialClock_complement_green_origin u

-- Vanishing self-Green before reduction must not erase the reduced term.
example (t u : ℝ) : carryMaterialPairGreen (carryMaterialClockForcingPair t)
    (carryMaterialClockForcingPair u) = 0 := carryMaterialClock_forcing_pair_self_green t u

example (u : ℝ) : carryMaterialPairGreen
    (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))
    (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) =
    -((carryMaterialResponseScale*u : ℝ) : ℂ)*conj (carryMaterialClockForcingScalar 0)*
      carryMaterialClockForcingScalar u*inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing := by
  simpa only [sub_zero] using carryMaterialClock_reduced_forcing_green 0 u

example (t : ℝ) : carryMaterialPairGreen
    (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
    (carryMaterialPairReduction t (carryMaterialClockForcingPair t)) = 0 := by
  rw [carryMaterialClock_reduced_forcing_green]
  simp

-- Existing metric and clock obstructions retain their literal types.
#check completedBoundaryTransportedClock_not_standard_symmetric
#check completedBoundaryTransportedClock_not_selfAdjoint
#check completedClock_isometric_intertwiner_impossible
#check carryMaterialCentralComplement_clock_center_ne
#check completeCriticalVerticalObservabilityGram_not_canonicalHankel
#check separatedCenterBlock_not_complete_materialClock_realization

-- Global return, C2 physical channel and residual remain in the original norm.
example : ‖baseTwoCompletedBoundaryHilbertState 0‖^2 =
    1 + ‖baseTwoPhysicalOrdinaryC2State 0‖^2 +
      ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖^2 +
      ‖baseTwoCompletedBoundaryValue 0‖^2 := carryMaterial_origin_norm_physical_residual

end
