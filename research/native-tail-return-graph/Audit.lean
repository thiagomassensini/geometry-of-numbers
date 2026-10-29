import FourSourceBridge
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos]
  let forbidden := #[
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarryCubicOdd.critical_cauchy_row,
    `CarryCubicOdd.critical_readout_four_samples,
    `CarryCubicOdd.critical_rho_alternating,
    `CarryCubicOdd.critical_diagonal_four_samples_exact,
    `CarryOddEnergy.finite_odd_source_pairing,
    `CarryOddEnergy.finite_odd_energy_pairing,
    `CarryOddEnergy.finite_odd_energy_correction_tendsto,
    `CarryOddEnergy.finite_odd_green_correction_tendsto,
    `CarryCrossRadial.first_cross_exact,
    `CarryCrossRadial.doubled_first_exact,
    `CarryCrossRadial.doubled_scaled_tendsto,
    `CarryCrossRadial.doubled_scaled_expansion,
    `CarryCrossRadial.doubled_unscaled_expansion,
    `CarryCrossRadial.doubled_next_tendsto,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
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
      if forbidden.contains name ||
          (construction && (signRoots.contains name || name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name.toString.startsWith "CarryCriticalGrid." ||
          name == `CarryAddressSplit.principal_physical_grid ||
          name == `CarryAddressSplit.principal_physical_tendsto)) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden canonical/sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  unless construction do
    for name in #[`CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
        `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
        `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one] do
      unless seen.contains name do
        throwError "Missing expected four-source proof dependency (check theorem-body traversal): {name}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native tail return graph {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; finite source-sign roots excluded from construction; scalar-asymptotic shortcuts forbidden"

#print axioms CarryTailReturn.returnWeight
#print axioms CarryTailReturn.weightedIncident
#print axioms CarryTailReturn.window_reconstruct
#print axioms CarryTailReturn.weighted_window_reconstruct
#print axioms CarryTailReturn.finite_weighted_synthesis
#print axioms CarryTailReturn.weighted_incident_coe
#print axioms CarryTailReturn.weighted_incident_return
#print axioms CarryTailReturn.weighted_return_synthesis
#print axioms CarryTailReturn.sourceIncident
#print axioms CarryTailReturn.original_first_leg
#print axioms CarryTailReturn.original_return_leg
#print axioms CarryTailReturn.original_source_graph
#print axioms CarryTailReturn.tailIncident
#print axioms CarryTailReturn.principal_prefix
#print axioms CarryTailReturn.tail_first_leg
#print axioms CarryTailReturn.headIncident
#print axioms CarryTailReturn.head_first_leg
#print axioms CarryTailReturn.tailReturnDefect
#print axioms CarryTailReturn.weighted_return_defect
#print axioms CarryTailReturn.tail_return_defect_synthesis
#print axioms CarryTailReturn.tail_graph_defect
#print axioms CarryTailReturn.head_graph_defect
#print axioms CarryTailReturn.native_quotient_ne_one
#print axioms CarryTailReturn.native_return_response_relation
#print axioms CarryTailReturn.native_return_cayley_coordinate
#print axioms CarryTailReturn.weighted_cayley_vector
#print axioms CarryTailReturn.native_return_fixed_iff_zero
#print axioms CarryTailReturn.tail_in_graph_iff_zero
#print axioms CarryTailReturn.tail_in_graph_eventually_iff_zero
#print axioms CarryTailReturn.returnGraphDefect
#print axioms CarryTailReturn.graph_defect_polarized_balance
#print axioms CarryTailReturn.diagonal_pair_return_energy
#print axioms CarryTailReturn.original_source_energy_pairing
#print axioms CarryTailReturn.original_source_port_pairing
#print axioms CarryTailReturn.signed_diagonal_norm
#print axioms CarryTailReturn.original_source_storage
#print axioms CarryTailReturn.tail_energy_defect_cancellation
#print axioms CarryTailReturn.weighted_coordinates_ne_zero
#print axioms CarryTailReturn.address_zero_input
#print axioms CarryTailReturn.principal_coefficient_formula
#print axioms CarryTailReturn.principal_coefficients_sq
#print axioms CarryTailReturn.principal_coefficients_completed_square
#print axioms CarryTailReturn.principal_coefficients_sq_pos
#print axioms CarryTailReturn.principal_input_nonzero
#print axioms CarryTailReturn.four_original_physical_positive
#print axioms CarryTailReturn.four_original_port_gram
#print axioms CarryTailReturn.principal_four_port_gram
#print axioms CarryTailReturn.principal_four_eventually_positive

#audit_odd_green construction
  CarryTailReturn.returnWeight
  CarryTailReturn.weightedIncident
  CarryTailReturn.window_reconstruct
  CarryTailReturn.weighted_window_reconstruct
  CarryTailReturn.finite_weighted_synthesis
  CarryTailReturn.weighted_incident_coe
  CarryTailReturn.weighted_incident_return
  CarryTailReturn.weighted_return_synthesis
  CarryTailReturn.sourceIncident
  CarryTailReturn.original_first_leg
  CarryTailReturn.original_return_leg
  CarryTailReturn.original_source_graph
  CarryTailReturn.tailIncident
  CarryTailReturn.principal_prefix
  CarryTailReturn.tail_first_leg
  CarryTailReturn.headIncident
  CarryTailReturn.head_first_leg
  CarryTailReturn.tailReturnDefect
  CarryTailReturn.weighted_return_defect
  CarryTailReturn.tail_return_defect_synthesis
  CarryTailReturn.tail_graph_defect
  CarryTailReturn.head_graph_defect
  CarryTailReturn.native_quotient_ne_one
  CarryTailReturn.native_return_response_relation
  CarryTailReturn.native_return_cayley_coordinate
  CarryTailReturn.weighted_cayley_vector
  CarryTailReturn.native_return_fixed_iff_zero
  CarryTailReturn.tail_in_graph_iff_zero
  CarryTailReturn.tail_in_graph_eventually_iff_zero
  CarryTailReturn.returnGraphDefect
  CarryTailReturn.graph_defect_polarized_balance
  CarryTailReturn.diagonal_pair_return_energy
  CarryTailReturn.original_source_energy_pairing
  CarryTailReturn.original_source_port_pairing
  CarryTailReturn.signed_diagonal_norm
  CarryTailReturn.original_source_storage
  CarryTailReturn.tail_energy_defect_cancellation
  CarryTailReturn.weighted_coordinates_ne_zero
  CarryTailReturn.address_zero_input
  CarryTailReturn.principal_coefficient_formula
  CarryTailReturn.principal_coefficients_sq
  CarryTailReturn.principal_coefficients_completed_square
  CarryTailReturn.principal_coefficients_sq_pos
  CarryTailReturn.principal_input_nonzero


#audit_odd_green finite_control
  CarryTailReturn.four_original_physical_positive
  CarryTailReturn.four_original_port_gram
  CarryTailReturn.principal_four_port_gram
  CarryTailReturn.principal_four_eventually_positive
