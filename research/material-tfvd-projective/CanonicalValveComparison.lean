import GeometryOfNumbers.Analysis.CarryMaterialTfvdProjectiveTransport
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy
import Lean

/-! Read-only cross-repository comparison at identical dependency pins.
Depth and height-squared remain distinct variables. Equality below is the
explicit TEST of their direct chart identification, never an assumed transport.
-/
namespace CarryMaterialProjectiveComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open PowerSeries CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The recovered real valve is the historical valve, by their same normalized
ODE. Neither source nor a metric is changed to establish this crosswalk. -/
theorem real_valve_eq_operator_valve (D : PowerSeries ℝ) :
    GeometryOfNumbers.Analysis.ProjectiveValve.projectiveValveMass D =
      CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass D := by
  exact CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass_unique D _
    (GeometryOfNumbers.Analysis.ProjectiveValve.projectiveValveMass_constantCoeff D)
    (GeometryOfNumbers.Analysis.ProjectiveValve.derivative_projectiveValveMass D)

theorem real_valve_first_coefficient (D : PowerSeries ℝ) :
    coeff 1 (GeometryOfNumbers.Analysis.ProjectiveValve.projectiveValveMass D) =
      constantCoeff D := by
  have hd := congrArg (coeff 0)
    (GeometryOfNumbers.Analysis.ProjectiveValve.derivative_projectiveValveMass D)
  simpa only [coeff_derivative, zero_add, Nat.cast_zero, mul_one,
    coeff_zero_eq_constantCoeff_apply, map_mul,
    GeometryOfNumbers.Analysis.ProjectiveValve.projectiveValveMass_constantCoeff] using hd

/-- The direct comparison has exactly this curvature obligation, with no fitted
normalization and no conclusion that a physical depth is a height jet. -/
theorem physical_mass_eq_native_iff (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 =
        normalizedCompletedNativeEvenFormalSeries⁻¹ ↔
      carryMaterialProjectiveCurvature eta g m a r =
        mk canonicalCompletedNativeLogDerivativeMoment := by
  rw [carryMaterialProjective_mass, real_valve_eq_operator_valve,
    ← projectiveValveMass_nativeMoments_eq_reciprocal]
  exact CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass_injective.eq_iff

/-- A necessary first coefficient of that *direct* depth/height comparison. -/
theorem physical_mass_native_necessary_zero (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2)
    (h : (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 =
      normalizedCompletedNativeEvenFormalSeries⁻¹) :
    (eta ^ 2)⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 2)) r -
        2 * (eta⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 1)) r) +
          baseTwoPhysicalEdgeC2State g (m, (a, 0)) r =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hc := congrArg constantCoeff ((physical_mass_eq_native_iff eta g m a r).mp h)
  rw [carryMaterialProjective_curvature_zero] at hc
  simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_mk] using hc

/-- Normalization at one is automatic on both sides; it does not calibrate
the first coefficient, much less the original Hilbert Gram. -/
theorem physical_native_mass_same_constant (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    constantCoeff ((carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 -
      normalizedCompletedNativeEvenFormalSeries⁻¹) = 0 := by
  rw [← projectiveValveMass_nativeMoments_eq_reciprocal,
    carryMaterialProjective_mass, map_sub]
  simp

/-- Exact inhomogeneous equation for the comparison defect. Its forcing is
the actual physical curvature discrepancy, not a discarded residual. -/
theorem physical_native_mass_defect_derivative (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    d⁄dX ℝ ((carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 -
        normalizedCompletedNativeEvenFormalSeries⁻¹) =
      carryMaterialProjectiveCurvature eta g m a r *
        ((carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 -
          normalizedCompletedNativeEvenFormalSeries⁻¹) +
      (carryMaterialProjectiveCurvature eta g m a r - mk canonicalCompletedNativeLogDerivativeMoment) *
        normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  rw [carryMaterialProjective_mass, ← projectiveValveMass_nativeMoments_eq_reciprocal,
    real_valve_eq_operator_valve]
  rw [map_sub, CarrySelfAdjointOperator.ProjectiveValve.derivative_projectiveValveMass,
    CarrySelfAdjointOperator.ProjectiveValve.derivative_projectiveValveMass]
  ring

theorem physical_native_mass_first_defect (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    coeff 1 ((carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 -
      normalizedCompletedNativeEvenFormalSeries⁻¹) =
      (eta ^ 2)⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 2)) r -
        2 * (eta⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 1)) r) +
          baseTwoPhysicalEdgeC2State g (m, (a, 0)) r -
            canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [map_sub, carryMaterialProjective_mass, real_valve_first_coefficient,
    ← projectiveValveMass_nativeMoments_eq_reciprocal,
    ← real_valve_eq_operator_valve, real_valve_first_coefficient,
    carryMaterialProjective_curvature_zero]
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]

/-- Only the direct identification of this one physical depth mass with the
native height-squared mass is excluded. No global synthesis is excluded. -/
theorem physical_unit_mass_not_native :
    (carryMaterialProjectiveFiberData (criticalVerticalAmplitudeRatio 2 (by decide))
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0).projectiveMass.1 ≠
      normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  intro h
  have hc := congrArg constantCoeff ((physical_mass_eq_native_iff _ _ _ _ _).mp h)
  have hn := carryMaterialProjective_unit_origin_curvature_neg
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_mk] using (ne_of_lt (lt_trans hn hp)) hc

theorem physical_unit_first_mass_defect_neg :
    coeff 1 ((carryMaterialProjectiveFiberData (criticalVerticalAmplitudeRatio 2 (by decide))
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0).projectiveMass.1 -
      normalizedCompletedNativeEvenFormalSeries⁻¹) < 0 := by
  have hd := physical_native_mass_first_defect (criticalVerticalAmplitudeRatio 2 (by decide))
    (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0
  have hc := carryMaterialProjective_curvature_zero (criticalVerticalAmplitudeRatio 2 (by decide))
    (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0
  have hn := carryMaterialProjective_unit_origin_curvature_neg
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  linarith

end
end CarryMaterialProjectiveComparison

open Lean Elab Command
elab "#assert_projective_comparison_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Projective comparison unexpected axiom: {decl} depends on {axiomName}"

namespace CarryMaterialProjectiveComparison
#assert_projective_comparison_axioms real_valve_eq_operator_valve
#print axioms real_valve_eq_operator_valve
#assert_projective_comparison_axioms real_valve_first_coefficient
#print axioms real_valve_first_coefficient
#assert_projective_comparison_axioms physical_mass_eq_native_iff
#print axioms physical_mass_eq_native_iff
#assert_projective_comparison_axioms physical_mass_native_necessary_zero
#print axioms physical_mass_native_necessary_zero
#assert_projective_comparison_axioms physical_native_mass_same_constant
#print axioms physical_native_mass_same_constant
#assert_projective_comparison_axioms physical_native_mass_defect_derivative
#print axioms physical_native_mass_defect_derivative
#assert_projective_comparison_axioms physical_native_mass_first_defect
#print axioms physical_native_mass_first_defect
#assert_projective_comparison_axioms physical_unit_mass_not_native
#print axioms physical_unit_mass_not_native
#assert_projective_comparison_axioms physical_unit_first_mass_defect_neg
#print axioms physical_unit_first_mass_defect_neg
end CarryMaterialProjectiveComparison
