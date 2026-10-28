import MovingPolarizedPair
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let algebra := group.getId == `algebra
  let energy := group.getId == `energy
  let polarized := group.getId == `polarized
  let readout := !algebra
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
    `CarrySelfAdjointOperator.ChiralReturn.nativeSourceFiniteBoundaryEnergy_pos_iff_margin,
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
  if energy then
    for required in #[
      `CarrySelfAdjointOperator.storage_one_chiralJetInput_eventually_energy_control,
      `CarryEulerNewtonAll.source_newton_path_eventually_bounded,
      `CarryEulerNewtonAll.source_newton_path_tendsto] do
      unless seen.contains required do
        throwError "Missing actual native moving-energy dependency: {required}"
  if polarized then
    for required in #[
      `CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient,
      `CarryEulerNewtonAll.source_newton_path_tendsto,
      `CarryNativeBinomial.physical_source_newton_all_order] do
      unless seen.contains required do
        throwError "Missing actual physical polarized dependency: {required}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native moving Euler full balance/polarization {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment readout forbidden={!readout}; finite positivity/coercivity roots forbidden globally; scalar-asymptotic shortcuts forbidden"

#print axioms CarryMovingEulerBalance.uniform_quadratic_error_tendsto_zero
#print axioms CarryMovingEulerBalance.physical_balance_error_tendsto_zero
#print axioms CarryMovingEulerBalance.physical_balance_tendsto
#print axioms CarryMovingEulerBalance.physical_channel_balance_tendsto
#print axioms CarryMovingEulerBalance.originalBoundaryPair
#print axioms CarryMovingEulerBalance.original_boundary_pair_continuous
#print axioms CarryMovingEulerBalance.original_boundary_pair_diagonal
#print axioms CarryMovingEulerBalance.original_boundary_pair_euler_zero
#print axioms CarryMovingEulerBalance.boundary_energy_euler_zero
#print axioms CarryMovingEulerBalance.physical_euler_channel_balance_tendsto
#print axioms CarryMovingEulerBalance.native_moving_pairing_tendsto
#print axioms CarryMovingEulerBalance.physical_moving_pairing_tendsto
#print axioms CarryMovingEulerBalance.physical_green_pairing_tendsto
#print axioms CarryMovingEulerBalance.physical_green_pairing_euler_tendsto

#audit_odd_green algebra
  CarryMovingEulerBalance.uniform_quadratic_error_tendsto_zero


#audit_odd_green energy
  CarryMovingEulerBalance.physical_balance_error_tendsto_zero
  CarryMovingEulerBalance.physical_balance_tendsto
  CarryMovingEulerBalance.physical_channel_balance_tendsto
  CarryMovingEulerBalance.physical_euler_channel_balance_tendsto


#audit_odd_green polarized
  CarryMovingEulerBalance.originalBoundaryPair
  CarryMovingEulerBalance.original_boundary_pair_continuous
  CarryMovingEulerBalance.original_boundary_pair_diagonal
  CarryMovingEulerBalance.original_boundary_pair_euler_zero
  CarryMovingEulerBalance.boundary_energy_euler_zero
  CarryMovingEulerBalance.native_moving_pairing_tendsto
  CarryMovingEulerBalance.physical_moving_pairing_tendsto
  CarryMovingEulerBalance.physical_green_pairing_tendsto
  CarryMovingEulerBalance.physical_green_pairing_euler_tendsto
