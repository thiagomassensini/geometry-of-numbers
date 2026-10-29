import StationaryObstruction
import Lean

open Lean Elab Command
elab "#audit_conservative_transport " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
  let forbidden := if mode.getId == `stationary then forbidden else forbidden ++ #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos]
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
      if forbidden.contains name then
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"Conservative native transport audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryConservativeIntertwiner.conservativeReturn
#print axioms CarryConservativeIntertwiner.conservativeHead
#print axioms CarryConservativeIntertwiner.conservative_pairing
#print axioms CarryConservativeIntertwiner.conservative_energy
#print axioms CarryConservativeIntertwiner.transportDefect
#print axioms CarryConservativeIntertwiner.polarized_defect_ledger
#print axioms CarryConservativeIntertwiner.energy_defect_ledger
#print axioms CarryConservativeIntertwiner.physicalIncident
#print axioms CarryConservativeIntertwiner.physicalReturned
#print axioms CarryConservativeIntertwiner.physicalIncident_coe
#print axioms CarryConservativeIntertwiner.physicalReturned_coe
#print axioms CarryConservativeIntertwiner.physicalLeading
#print axioms CarryConservativeIntertwiner.physicalLeading_coe
#print axioms CarryConservativeIntertwiner.physicalLeading_ne
#print axioms CarryConservativeIntertwiner.physical_scaled_incident_tendsto
#print axioms CarryConservativeIntertwiner.physical_scaled_returned_tendsto
#print axioms CarryConservativeIntertwiner.physical_source_defect_pairing
#print axioms CarryConservativeIntertwiner.physical_signed_energy_tendsto
#print axioms CarryConservativeIntertwiner.original_incident_columns
#print axioms CarryConservativeIntertwiner.original_returned_columns
#print axioms CarryConservativeIntertwiner.original_transport_defect_columns
#print axioms CarryConservativeIntertwiner.material_address_from_shift
#print axioms CarryConservativeIntertwiner.radial_argument_from_shift
#print axioms CarryConservativeIntertwiner.physical_shift_fixed_eq_zero
#print axioms CarryConservativeIntertwiner.leadingTransportDefect
#print axioms CarryConservativeIntertwiner.leadingTransportDefect_ne
#print axioms CarryConservativeIntertwiner.scaled_transport_defect_tendsto
#print axioms CarryConservativeIntertwiner.conservative_return_not_eventually_source
#print axioms CarryConservativeIntertwiner.leading_conservative_cancellation
#print axioms CarryConservativeIntertwiner.pr41Incident
#print axioms CarryConservativeIntertwiner.pr41Returned
#print axioms CarryConservativeIntertwiner.pr41TransportCorrection
#print axioms CarryConservativeIntertwiner.pr41_conservative_ledger
#print axioms CarryConservativeIntertwiner.pr41_conservative_ledger_tendsto
#print axioms CarryConservativeIntertwiner.pr41Order
#print axioms CarryConservativeIntertwiner.pr41Order_lt
#print axioms CarryConservativeIntertwiner.pr41Boundary_above
#print axioms CarryConservativeIntertwiner.pr41_monic_top
#print axioms CarryConservativeIntertwiner.pr41Boundary_top
#print axioms CarryConservativeIntertwiner.pr41Boundary_top_ne
#print axioms CarryConservativeIntertwiner.pr41_conservative_return_fails
#print axioms CarryConservativeIntertwiner.firstEvenBoundary
#print axioms CarryConservativeIntertwiner.firstOddBoundary
#print axioms CarryConservativeIntertwiner.first_even_is_pr41
#print axioms CarryConservativeIntertwiner.first_odd_is_pr41
#print axioms CarryConservativeIntertwiner.evenLeading
#print axioms CarryConservativeIntertwiner.oddLeading
#print axioms CarryConservativeIntertwiner.even_leading_exact
#print axioms CarryConservativeIntertwiner.odd_leading_exact
#print axioms CarryConservativeIntertwiner.even_support
#print axioms CarryConservativeIntertwiner.first_incident_ray
#print axioms CarryConservativeIntertwiner.central_amp_norm
#print axioms CarryConservativeIntertwiner.physical_feature_inner
#print axioms CarryConservativeIntertwiner.evenLeading_norm
#print axioms CarryConservativeIntertwiner.even_leading_defect_energy
#print axioms CarryConservativeIntertwiner.even_leading_head_energy
#print axioms CarryConservativeIntertwiner.even_leading_cross
#print axioms CarryConservativeIntertwiner.two_column_energy
#print axioms CarryConservativeIntertwiner.oddLeading_norm
#print axioms CarryConservativeIntertwiner.odd_leading_defect_energy
#print axioms CarryConservativeIntertwiner.odd_leading_head_energy
#print axioms CarryConservativeIntertwiner.odd_leading_cross
#print axioms CarryConservativeIntertwiner.first_even_boundary_energy
#print axioms CarryConservativeIntertwiner.stationary_action_on_first_feature
#print axioms CarryConservativeIntertwiner.no_stationary_completed_return

#audit_conservative_transport conservative
  CarryConservativeIntertwiner.conservativeReturn
  CarryConservativeIntertwiner.conservativeHead
  CarryConservativeIntertwiner.conservative_pairing
  CarryConservativeIntertwiner.conservative_energy
  CarryConservativeIntertwiner.transportDefect
  CarryConservativeIntertwiner.polarized_defect_ledger
  CarryConservativeIntertwiner.energy_defect_ledger

#audit_conservative_transport source
  CarryConservativeIntertwiner.physicalIncident
  CarryConservativeIntertwiner.physicalReturned
  CarryConservativeIntertwiner.physicalIncident_coe
  CarryConservativeIntertwiner.physicalReturned_coe
  CarryConservativeIntertwiner.physicalLeading
  CarryConservativeIntertwiner.physicalLeading_coe
  CarryConservativeIntertwiner.physicalLeading_ne
  CarryConservativeIntertwiner.physical_scaled_incident_tendsto
  CarryConservativeIntertwiner.physical_scaled_returned_tendsto
  CarryConservativeIntertwiner.physical_source_defect_pairing
  CarryConservativeIntertwiner.physical_signed_energy_tendsto
  CarryConservativeIntertwiner.original_incident_columns
  CarryConservativeIntertwiner.original_returned_columns
  CarryConservativeIntertwiner.original_transport_defect_columns
  CarryConservativeIntertwiner.material_address_from_shift
  CarryConservativeIntertwiner.radial_argument_from_shift

#audit_conservative_transport leading
  CarryConservativeIntertwiner.physical_shift_fixed_eq_zero
  CarryConservativeIntertwiner.leadingTransportDefect
  CarryConservativeIntertwiner.leadingTransportDefect_ne
  CarryConservativeIntertwiner.scaled_transport_defect_tendsto
  CarryConservativeIntertwiner.conservative_return_not_eventually_source
  CarryConservativeIntertwiner.leading_conservative_cancellation

#audit_conservative_transport pr41
  CarryConservativeIntertwiner.pr41Incident
  CarryConservativeIntertwiner.pr41Returned
  CarryConservativeIntertwiner.pr41TransportCorrection
  CarryConservativeIntertwiner.pr41_conservative_ledger
  CarryConservativeIntertwiner.pr41_conservative_ledger_tendsto
  CarryConservativeIntertwiner.pr41Order
  CarryConservativeIntertwiner.pr41Order_lt
  CarryConservativeIntertwiner.pr41Boundary_above
  CarryConservativeIntertwiner.pr41_monic_top
  CarryConservativeIntertwiner.pr41Boundary_top
  CarryConservativeIntertwiner.pr41Boundary_top_ne
  CarryConservativeIntertwiner.pr41_conservative_return_fails

#audit_conservative_transport canaries
  CarryConservativeIntertwiner.firstEvenBoundary
  CarryConservativeIntertwiner.firstOddBoundary
  CarryConservativeIntertwiner.first_even_is_pr41
  CarryConservativeIntertwiner.first_odd_is_pr41
  CarryConservativeIntertwiner.evenLeading
  CarryConservativeIntertwiner.oddLeading
  CarryConservativeIntertwiner.even_leading_exact
  CarryConservativeIntertwiner.odd_leading_exact
  CarryConservativeIntertwiner.even_support
  CarryConservativeIntertwiner.first_incident_ray
  CarryConservativeIntertwiner.central_amp_norm
  CarryConservativeIntertwiner.physical_feature_inner
  CarryConservativeIntertwiner.evenLeading_norm
  CarryConservativeIntertwiner.even_leading_defect_energy
  CarryConservativeIntertwiner.even_leading_head_energy
  CarryConservativeIntertwiner.even_leading_cross
  CarryConservativeIntertwiner.two_column_energy
  CarryConservativeIntertwiner.oddLeading_norm
  CarryConservativeIntertwiner.odd_leading_defect_energy
  CarryConservativeIntertwiner.odd_leading_head_energy
  CarryConservativeIntertwiner.odd_leading_cross

#audit_conservative_transport stationary
  CarryConservativeIntertwiner.first_even_boundary_energy
  CarryConservativeIntertwiner.stationary_action_on_first_feature
  CarryConservativeIntertwiner.no_stationary_completed_return
