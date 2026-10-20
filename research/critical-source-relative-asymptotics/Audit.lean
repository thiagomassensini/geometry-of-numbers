import InitialSource
import PolarizedLimit
import Lean

open Lean Elab Command
elab "#audit_critical_relative " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {decl}: {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
  logInfo m!"Critical source relative audit roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms CarryCriticalRelative.amp
#print axioms CarryCriticalRelative.step
#print axioms CarryCriticalRelative.amp_continuousAt_zero
#print axioms CarryCriticalRelative.amp_zero_ne
#print axioms CarryCriticalRelative.amp_tendsto
#print axioms CarryCriticalRelative.quotient_tendsto
#print axioms CarryCriticalRelative.step_factor
#print axioms CarryCriticalRelative.step_pow_inputMatrix
#print axioms CarryCriticalRelative.leadingCoefficients
#print axioms CarryCriticalRelative.scaled_input_tendsto
#print axioms CarryCriticalRelative.leadingState
#print axioms CarryCriticalRelative.leadingState_ne_zero
#print axioms CarryCriticalRelative.observationScale
#print axioms CarryCriticalRelative.observationScale_ne
#print axioms CarryCriticalRelative.synthesis_scale
#print axioms CarryCriticalRelative.scaled_incident_tendsto
#print axioms CarryCriticalRelative.scaled_returned_tendsto
#print axioms CarryCriticalRelative.scaled_whole_source_tendsto
#print axioms CarryCriticalRelative.leading_signed_form_zero
#print axioms CarryCriticalRelative.returned_incident_energy_ratio_tendsto_one
#print axioms CarryCriticalRelative.incident_eventually_ne_zero
#print axioms CarryCriticalRelative.no_fixed_relative_contraction
#print axioms CarryCriticalRelative.criticalOrder
#print axioms CarryCriticalRelative.criticalOrder_lt
#print axioms CarryCriticalRelative.criticalCoordinates_above
#print axioms CarryCriticalRelative.parityCoordinates_top
#print axioms CarryCriticalRelative.criticalCoordinates_top_phase
#print axioms CarryCriticalRelative.criticalCoordinates_top_ne
#print axioms CarryCriticalRelative.criticalLeadingState
#print axioms CarryCriticalRelative.critical_leading_eq
#print axioms CarryCriticalRelative.criticalLeadingState_ne
#print axioms CarryCriticalRelative.critical_pair_exact
#print axioms CarryCriticalRelative.critical_whole_source_tendsto
#print axioms CarryCriticalRelative.critical_energy_ratio_tendsto_one
#print axioms CarryCriticalRelative.critical_no_fixed_relative_contraction
#print axioms CarryCriticalRelative.physicalGrowth
#print axioms CarryCriticalRelative.physicalGrowth_pos
#print axioms CarryCriticalRelative.step_norm
#print axioms CarryCriticalRelative.observationScale_norm_sq
#print axioms CarryCriticalRelative.critical_incident_growth
#print axioms CarryCriticalRelative.critical_returned_growth
#print axioms CarryCriticalRelative.critical_incident_diverges
#print axioms CarryCriticalRelative.relativeDeficit
#print axioms CarryCriticalRelative.criticalGapCoefficient
#print axioms CarryCriticalRelative.critical_boundary_of_isUnit
#print axioms CarryCriticalRelative.critical_balance_tendsto_of_isUnit
#print axioms CarryCriticalRelative.critical_scaled_relative_deficit
#print axioms CarryCriticalRelative.critical_relative_corridor
#print axioms CarryCriticalRelative.critical_gap_coefficient_pos_iff
#print axioms CarryCriticalRelative.amp_zero
#print axioms CarryCriticalRelative.amp_zero_norm_sq
#print axioms CarryCriticalRelative.first_feature_norm_sq
#print axioms CarryCriticalRelative.first_leading_state
#print axioms CarryCriticalRelative.first_leading_energy
#print axioms CarryCriticalRelative.empty_prefix_posDef
#print axioms CarryCriticalRelative.first_gap_coefficient
#print axioms CarryCriticalRelative.first_scaled_relative_deficit
#print axioms CarryCriticalRelative.first_source_relative_contraction
#print axioms CarryCriticalRelative.critical_scaled_cross_tendsto_zero
#print axioms NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit
#print axioms CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource
#print axioms CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos

#audit_critical_relative
  CarryCriticalRelative.amp
  CarryCriticalRelative.step
  CarryCriticalRelative.amp_continuousAt_zero
  CarryCriticalRelative.amp_zero_ne
  CarryCriticalRelative.amp_tendsto
  CarryCriticalRelative.quotient_tendsto
  CarryCriticalRelative.step_factor
  CarryCriticalRelative.step_pow_inputMatrix
  CarryCriticalRelative.leadingCoefficients
  CarryCriticalRelative.scaled_input_tendsto
  CarryCriticalRelative.leadingState
  CarryCriticalRelative.leadingState_ne_zero
  CarryCriticalRelative.observationScale
  CarryCriticalRelative.observationScale_ne
  CarryCriticalRelative.synthesis_scale
  CarryCriticalRelative.scaled_incident_tendsto
  CarryCriticalRelative.scaled_returned_tendsto
  CarryCriticalRelative.scaled_whole_source_tendsto
  CarryCriticalRelative.leading_signed_form_zero
  CarryCriticalRelative.returned_incident_energy_ratio_tendsto_one
  CarryCriticalRelative.incident_eventually_ne_zero
  CarryCriticalRelative.no_fixed_relative_contraction
  CarryCriticalRelative.criticalOrder
  CarryCriticalRelative.criticalOrder_lt
  CarryCriticalRelative.criticalCoordinates_above
  CarryCriticalRelative.parityCoordinates_top
  CarryCriticalRelative.criticalCoordinates_top_phase
  CarryCriticalRelative.criticalCoordinates_top_ne
  CarryCriticalRelative.criticalLeadingState
  CarryCriticalRelative.critical_leading_eq
  CarryCriticalRelative.criticalLeadingState_ne
  CarryCriticalRelative.critical_pair_exact
  CarryCriticalRelative.critical_whole_source_tendsto
  CarryCriticalRelative.critical_energy_ratio_tendsto_one
  CarryCriticalRelative.critical_no_fixed_relative_contraction
  CarryCriticalRelative.physicalGrowth
  CarryCriticalRelative.physicalGrowth_pos
  CarryCriticalRelative.step_norm
  CarryCriticalRelative.observationScale_norm_sq
  CarryCriticalRelative.critical_incident_growth
  CarryCriticalRelative.critical_returned_growth
  CarryCriticalRelative.critical_incident_diverges
  CarryCriticalRelative.relativeDeficit
  CarryCriticalRelative.criticalGapCoefficient
  CarryCriticalRelative.critical_boundary_of_isUnit
  CarryCriticalRelative.critical_balance_tendsto_of_isUnit
  CarryCriticalRelative.critical_scaled_relative_deficit
  CarryCriticalRelative.critical_relative_corridor
  CarryCriticalRelative.critical_gap_coefficient_pos_iff
  CarryCriticalRelative.amp_zero
  CarryCriticalRelative.amp_zero_norm_sq
  CarryCriticalRelative.first_feature_norm_sq
  CarryCriticalRelative.first_leading_state
  CarryCriticalRelative.first_leading_energy
  CarryCriticalRelative.empty_prefix_posDef
  CarryCriticalRelative.first_gap_coefficient
  CarryCriticalRelative.first_scaled_relative_deficit
  CarryCriticalRelative.first_source_relative_contraction
  CarryCriticalRelative.critical_scaled_cross_tendsto_zero
  NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit
  CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource
  CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos
