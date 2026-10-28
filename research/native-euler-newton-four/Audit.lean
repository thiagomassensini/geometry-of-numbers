import TransportedEnergyControl
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let readout := group.getId == `transported_control
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
    `CarryBoundaryMargin.principal_uniform_physical_margin,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_boundary_coercive,
    `CarrySelfAdjointOperator.radialFourRegularizedStorage_eventually_unit_margin,
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos]
  let forbidden := #[
    `CarryCriticalComplete.critical_uniform_physical_margin,
    `CarryAddressSplit.defect_physical_tendsto_zero,
    `CarryAddressSplit.defect_physical_scaled_tendsto,
    `CarryTailReturn.principal_four_eventually_positive,
    `CarryTailReturn.four_original_physical_positive,
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
      if forbidden.contains name || signRoots.contains name ||
          (!readout && (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name == `CarrySelfAdjointOperator.nativeSourceFiniteBoundaryEnergy ||
          name == `CarrySelfAdjointOperator.storage_one_chiralJetInput_eventually_energy_control ||
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
    unless seen.contains `CarrySelfAdjointOperator.storage_one_chiralJetInput_eventually_energy_control do
      throwError "Missing actual native error-control dependency (check theorem-body traversal)"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native Euler/Newton four-source bridge {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment readout forbidden={!readout}; finite positivity/coercivity roots forbidden globally; scalar-asymptotic shortcuts forbidden"

#print axioms CarryEulerNewton.fourNewtonCoordinates
#print axioms CarryEulerNewton.four_newton_input_exact
#print axioms CarryEulerNewton.four_newton_coordinates_unique
#print axioms CarryEulerNewton.eulerToNewton
#print axioms CarryEulerNewton.newtonToEuler
#print axioms CarryEulerNewton.newton_euler_inverse
#print axioms CarryEulerNewton.euler_newton_inverse
#print axioms CarryEulerNewton.source_euler_newton_exact
#print axioms CarryEulerNewton.euler_newton_eventually_exact
#print axioms CarryEulerNewton.euler_to_newton_path_tendsto
#print axioms CarryEulerNewton.physical_source_newton
#print axioms CarryEulerNewton.physical_source_euler
#print axioms CarryEulerNewton.physical_pair_newton
#print axioms CarryEulerNewton.criticalJet
#print axioms CarryEulerNewton.critical_newton_coordinates
#print axioms CarryEulerNewton.critical_source_fixed_jet
#print axioms CarryEulerNewton.critical_jet_from_euler
#print axioms CarryEulerNewton.critical_pair_fixed_jet
#print axioms CarryEulerNewton.four_source_explicit_energy_control
#print axioms CarryEulerNewton.critical_jet_norm_sq_le
#print axioms CarryEulerNewton.critical_uniform_energy_control
#print axioms CarryEulerNewton.critical_boundary_energy_dictionary

#audit_odd_green construction
  CarryEulerNewton.fourNewtonCoordinates
  CarryEulerNewton.four_newton_input_exact
  CarryEulerNewton.four_newton_coordinates_unique
  CarryEulerNewton.eulerToNewton
  CarryEulerNewton.newtonToEuler
  CarryEulerNewton.newton_euler_inverse
  CarryEulerNewton.euler_newton_inverse
  CarryEulerNewton.source_euler_newton_exact
  CarryEulerNewton.euler_newton_eventually_exact
  CarryEulerNewton.euler_to_newton_path_tendsto
  CarryEulerNewton.physical_source_newton
  CarryEulerNewton.physical_source_euler
  CarryEulerNewton.physical_pair_newton
  CarryEulerNewton.criticalJet
  CarryEulerNewton.critical_newton_coordinates
  CarryEulerNewton.critical_source_fixed_jet
  CarryEulerNewton.critical_jet_from_euler
  CarryEulerNewton.critical_pair_fixed_jet
  CarryEulerNewton.critical_jet_norm_sq_le


#audit_odd_green transported_control
  CarryEulerNewton.four_source_explicit_energy_control
  CarryEulerNewton.critical_uniform_energy_control
  CarryEulerNewton.critical_boundary_energy_dictionary
