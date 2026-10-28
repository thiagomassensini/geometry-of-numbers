import AllOrderEnergyControl
import CoordinateCoherence
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
  logInfo m!"Native explicit binomial all-finite-order transport {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment readout forbidden={!readout}; finite positivity/coercivity roots forbidden globally; scalar-asymptotic shortcuts forbidden"

#print axioms CarryNativeBinomial.inverse_binomial_kernel
#print axioms CarryNativeBinomial.binomialMatrix
#print axioms CarryNativeBinomial.signedBinomialMatrix
#print axioms CarryNativeBinomial.signed_binomial_mul
#print axioms CarryNativeBinomial.binomial_signed_mul
#print axioms CarryNativeBinomial.binomial_stencil_exact
#print axioms CarryNativeBinomial.newtonCoordinates
#print axioms CarryNativeBinomial.native_phase_self_inverse
#print axioms CarryNativeBinomial.newton_input_term
#print axioms CarryNativeBinomial.newton_input_exact
#print axioms CarryNativeBinomial.sourceNewtonCoefficient
#print axioms CarryNativeBinomial.newton_coordinates_of_support
#print axioms CarryNativeBinomial.newton_coordinates_prefix_coherent
#print axioms CarryNativeBinomial.source_newton_above_support
#print axioms CarryNativeBinomial.newton_coordinates_above_support
#print axioms CarryNativeBinomial.physical_source_newton_all_order
#print axioms CarryNativeBinomial.native_synthesis_prefix_coherent
#print axioms CarryNativeBinomial.physical_pair_newton_all_order
#print axioms CarryNativeBinomial.newton_coordinates_unique
#print axioms CarryNativeBinomial.four_coordinates_regression
#print axioms CarryNativeBinomial.critical_coordinates_regression
#print axioms CarryNativeBinomial.source_explicit_energy_control_all_order

#audit_odd_green construction
  CarryNativeBinomial.inverse_binomial_kernel
  CarryNativeBinomial.binomialMatrix
  CarryNativeBinomial.signedBinomialMatrix
  CarryNativeBinomial.signed_binomial_mul
  CarryNativeBinomial.binomial_signed_mul
  CarryNativeBinomial.binomial_stencil_exact
  CarryNativeBinomial.newtonCoordinates
  CarryNativeBinomial.native_phase_self_inverse
  CarryNativeBinomial.newton_input_term
  CarryNativeBinomial.newton_input_exact
  CarryNativeBinomial.sourceNewtonCoefficient
  CarryNativeBinomial.newton_coordinates_of_support
  CarryNativeBinomial.newton_coordinates_prefix_coherent
  CarryNativeBinomial.source_newton_above_support
  CarryNativeBinomial.newton_coordinates_above_support
  CarryNativeBinomial.physical_source_newton_all_order
  CarryNativeBinomial.native_synthesis_prefix_coherent
  CarryNativeBinomial.physical_pair_newton_all_order
  CarryNativeBinomial.newton_coordinates_unique
  CarryNativeBinomial.four_coordinates_regression
  CarryNativeBinomial.critical_coordinates_regression


#audit_odd_green transported_control
  CarryNativeBinomial.source_explicit_energy_control_all_order
