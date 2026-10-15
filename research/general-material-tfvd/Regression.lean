import GeometryOfNumbers.Analysis.CarryMaterialTfvdGreenReadout
import GeometryOfNumbers.Analysis.PrimeCameraProvenance
import GeometryOfNumbers.Analysis.CompleteVerticalObservationGram
import GeometryOfNumbers.Analysis.SeparatedCenterClockObstruction

open GeometryOfNumbers.Analysis GeometryOfNumbers.Geometry
open GeometryOfNumbers.Analysis.BaseTwoCompletion

-- The general law recovers the exact former 72 source correction.
example (t : ℝ) : carryMaterialRadiusCorrection 72 8 9 (baseTwoCompletedBoundaryHilbertState t) =
    criticalMaterialGradient t 79 - criticalMaterialGradient t 62 := by
  simpa only [baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using
      carryMaterialRadiusCorrection72 (baseTwoCompletedBoundaryHilbertState t)

example (t u : ℝ) : carryMaterialCameraNineTerms integerCamera72Two integerCamera72Three t u =
    carryMaterialCamera72NineTerms t u := carryMaterialCameraNineTerms72 t u

example : baseTwoPhysicalEdgeIndex (19, 1) = 79 ∧ baseTwoPhysicalEdgeIndex (15, 0) = 62 := ⟨rfl, rfl⟩

-- Use the preexisting critical ratio, never a fitted TFVD normalization.
example (e : BaseTwoPhysicalEdge) (r : Fin 2) (t : ℝ) :
    let eta := criticalVerticalAmplitudeRatio 2 (by decide)
    carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) r
        (baseTwoCompletedMaterialGradientL2 t) +
      carryMaterialTfvdReturnReadout eta (criticalVerticalAmplitudeRatio_pos 2 _)
        (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) (baseTwoPhysicalEdgeC2Address e) r
        (baseTwoCompletedMaterialGradientL2 t) =
      baseTwoMaterialEdgeRealification (criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e)) r :=
  carryMaterialTfvd_edge_source _ (criticalVerticalAmplitudeRatio_pos 2 _)
    (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) e r t

#check primeCamera72_depths_and_cores
#check integerCamera72_local_masses
#check carryMaterialCamera72_defect_zero_positive
#check carryMaterialCamera_clock_connection
#check carryMaterialTfvd_unit_cross
#check carryMaterialTfvd_return_zero_negative
#check baseTwoCompletedBoundaryValue_eq_physicalChannel
#check baseTwoPhysicalResidualTfvdAnalysis_injective
#check realCarryTfvdSynthesis_comp_analysis
#check completeCriticalVerticalObservabilityGram_not_canonicalHankel
#check separatedCenterBlock_not_complete_materialClock_realization
