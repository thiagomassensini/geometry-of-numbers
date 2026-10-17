import GeometryOfNumbers.Analysis.CarryMaterialTfvdProjectiveTransport
import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling
import GeometryOfNumbers.Analysis.CompleteVerticalObservationGram

open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open DiscreteProjective
open scoped InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

-- Both boundary coordinates, rather than the normalized mass alone.
example (eta : ℝ) (g : MaterialEdgeL2) (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) :
    ((carryMaterialProjectiveFiberData eta g m a r).initialValue,
      (carryMaterialProjectiveFiberData eta g m a r).initialSlope) =
      (baseTwoPhysicalTfvdChannel eta m a r g).2 := carryMaterialProjective_boundary _ _ _ _ _

-- The full encoding is faithful at the existing critical amplitude.
example : Function.Injective
    (carryMaterialProjectiveEncode (criticalVerticalAmplitudeRatio 2 (by decide))) :=
  carryMaterialProjectiveEncode_injective _ (criticalVerticalAmplitudeRatio_pos 2 _).ne'

-- Source-specific nonzero return, invisible to the normalized mass coordinate.
example (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    stateMass (carryMaterialProjectiveReturnProfile eta h0 h1
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0) = 1 ∧
    carryMaterialProjectiveReturnProfile eta h0 h1
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0 0 < 0 :=
  carryMaterialProjective_source_return_invisible eta h0 h1

-- The actual first real depth curvature has the proved sign, without decimals.
example : PowerSeries.constantCoeff (carryMaterialProjectiveCurvature
    (criticalVerticalAmplitudeRatio 2 (by decide))
    (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0) < 0 :=
  carryMaterialProjective_unit_origin_curvature_neg

-- Distinct material phases and quadratures at physical edges 2 and 14.
example (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) :
    carryMaterialProjectiveCoordinate eta
      (carryMaterialProjectiveEncode eta (baseTwoCompletedBoundaryHilbertState t))
      (c2UnitOddCore, (0, 0)) 0 *
    carryMaterialProjectiveCoordinate eta
      (carryMaterialProjectiveEncode eta (baseTwoCompletedBoundaryHilbertState u))
      (c2UnitOddCore, (0, 2)) 1 =
        (criticalMaterialGradient t 2).re * (criticalMaterialGradient u 14).im := by
  rw [carryMaterialProjective_coordinate_encode eta h0.ne',
    carryMaterialProjective_coordinate_encode eta h0.ne']
  have h := carryMaterialTfvd_unit_cross eta h0 h1 0 1 t u
  dsimp only at h
  simp only [carryMaterialTfvd_coordinate] at h
  change baseTwoPhysicalEdgeC2State (baseTwoCompletedMaterialGradientL2 t) (c2UnitOddCore, (0, 0)) 0 *
    baseTwoPhysicalEdgeC2State (baseTwoCompletedMaterialGradientL2 u) (c2UnitOddCore, (0, 2)) 1 =
      (criticalMaterialGradient t 2).re * (criticalMaterialGradient u 14).im at h
  simpa only [baseTwoCompletedBoundaryHilbertState_interior] using h

-- Earlier camera and metric frontiers retain their original declarations.
#check carryMaterialTfvd72_correction
#check carryMaterialTfvd_edge_pairing
#check carryMaterial_origin_norm_physical_residual
#check carryMaterialClock_reduced_green_ledger
#check completeCriticalVerticalObservabilityGram_not_canonicalHankel

end
