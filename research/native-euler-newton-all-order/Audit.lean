import MovingEulerLimit
import MatrixCoherence
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
  logInfo m!"Native Euler-Newton all-finite-order vector transport {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment readout forbidden={!readout}; finite positivity/coercivity roots forbidden globally; scalar-asymptotic shortcuts forbidden"

#print axioms CarryEulerNewtonAll.shiftedFalling
#print axioms CarryEulerNewtonAll.shifted_falling_degree
#print axioms CarryEulerNewtonAll.shifted_falling_monic
#print axioms CarryEulerNewtonAll.shifted_falling_diagonal
#print axioms CarryEulerNewtonAll.shifted_falling_above
#print axioms CarryEulerNewtonAll.shifted_falling_address
#print axioms CarryEulerNewtonAll.shifted_falling_scaled_eval
#print axioms CarryEulerNewtonAll.eulerChart
#print axioms CarryEulerNewtonAll.eulerNewtonMatrix
#print axioms CarryEulerNewtonAll.eulerNewton
#print axioms CarryEulerNewtonAll.euler_newton_above
#print axioms CarryEulerNewtonAll.euler_newton_address
#print axioms CarryEulerNewtonAll.euler_newton_raw_exact
#print axioms CarryEulerNewtonAll.euler_newton_at_zero
#print axioms CarryEulerNewtonAll.physicalEulerChart
#print axioms CarryEulerNewtonAll.physical_euler_eq
#print axioms CarryEulerNewtonAll.source_euler_newton_all_order
#print axioms CarryEulerNewtonAll.source_euler_newton_eventually_all_order
#print axioms CarryEulerNewtonAll.physical_source_euler_all_order
#print axioms CarryEulerNewtonAll.physical_pair_euler_all_order
#print axioms CarryEulerNewtonAll.euler_newton_continuous
#print axioms CarryEulerNewtonAll.euler_newton_path_tendsto
#print axioms CarryEulerNewtonAll.source_newton_path_tendsto
#print axioms CarryEulerNewtonAll.source_newton_path_eventually_bounded
#print axioms CarryEulerNewtonAll.euler_newton_matrix_prefix
#print axioms CarryEulerNewtonAll.euler_newton_diagonal
#print axioms CarryEulerNewtonAll.euler_newton_diagonal_ne_zero
#print axioms CarryEulerNewtonAll.euler_newton_det_ne_zero
#print axioms CarryEulerNewtonAll.euler_newton_four_regression

#audit_odd_green construction
  CarryEulerNewtonAll.shiftedFalling
  CarryEulerNewtonAll.shifted_falling_degree
  CarryEulerNewtonAll.shifted_falling_monic
  CarryEulerNewtonAll.shifted_falling_diagonal
  CarryEulerNewtonAll.shifted_falling_above
  CarryEulerNewtonAll.shifted_falling_address
  CarryEulerNewtonAll.shifted_falling_scaled_eval
  CarryEulerNewtonAll.eulerChart
  CarryEulerNewtonAll.eulerNewtonMatrix
  CarryEulerNewtonAll.eulerNewton
  CarryEulerNewtonAll.euler_newton_above
  CarryEulerNewtonAll.euler_newton_address
  CarryEulerNewtonAll.euler_newton_raw_exact
  CarryEulerNewtonAll.euler_newton_at_zero
  CarryEulerNewtonAll.physicalEulerChart
  CarryEulerNewtonAll.physical_euler_eq
  CarryEulerNewtonAll.source_euler_newton_all_order
  CarryEulerNewtonAll.source_euler_newton_eventually_all_order
  CarryEulerNewtonAll.physical_source_euler_all_order
  CarryEulerNewtonAll.physical_pair_euler_all_order
  CarryEulerNewtonAll.euler_newton_continuous
  CarryEulerNewtonAll.euler_newton_path_tendsto
  CarryEulerNewtonAll.source_newton_path_tendsto
  CarryEulerNewtonAll.source_newton_path_eventually_bounded
  CarryEulerNewtonAll.euler_newton_matrix_prefix
  CarryEulerNewtonAll.euler_newton_diagonal
  CarryEulerNewtonAll.euler_newton_diagonal_ne_zero
  CarryEulerNewtonAll.euler_newton_det_ne_zero
  CarryEulerNewtonAll.euler_newton_four_regression
