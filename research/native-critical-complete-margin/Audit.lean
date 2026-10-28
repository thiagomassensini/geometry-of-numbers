import CriticalCompleteMargin
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
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
      if forbidden.contains name ||
          (construction && signRoots.contains name) ||
          (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name.toString.startsWith "CarryCriticalGrid." ||
          name == `CarryAddressSplit.principal_physical_grid ||
          name == `CarryAddressSplit.principal_physical_tendsto) ||
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
    for name in #[`CarryBoundaryMargin.principal_uniform_physical_margin,
        `CarrySelfAdjointOperator.storage_one_fourSample_eventually_boundary_coercive,
        `CarrySelfAdjointOperator.radialFourRegularizedStorage_eventually_unit_margin] do
      unless seen.contains name do
        throwError "Missing expected native coercivity dependency (check theorem-body traversal): {name}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native critical complete margin {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden=true; finite source-sign roots excluded from construction; scalar-asymptotic shortcuts forbidden"

#print axioms CarryCriticalComplete.sourceBoundary
#print axioms CarryCriticalComplete.criticalBoundary
#print axioms CarryCriticalComplete.defectBoundary
#print axioms CarryCriticalComplete.physical_values_sub
#print axioms CarryCriticalComplete.source_boundary_sub
#print axioms CarryCriticalComplete.physical_values_smul
#print axioms CarryCriticalComplete.source_boundary_smul
#print axioms CarryCriticalComplete.critical_boundary_split
#print axioms CarryCriticalComplete.critical_four_support
#print axioms CarryCriticalComplete.defect_coefficient_formula
#print axioms CarryCriticalComplete.critical_coefficient_formula
#print axioms CarryCriticalComplete.criticalTemplate
#print axioms CarryCriticalComplete.defectTemplate
#print axioms CarryCriticalComplete.critical_boundary_exact
#print axioms CarryCriticalComplete.defect_boundary_exact
#print axioms CarryCriticalComplete.boundary_eventually_exact
#print axioms CarryCriticalComplete.critical_boundary_tendsto
#print axioms CarryCriticalComplete.defect_boundary_tendsto_zero
#print axioms CarryCriticalComplete.critical_template_norm_sq
#print axioms CarryCriticalComplete.critical_boundary_uniform_lower
#print axioms CarryCriticalComplete.physical_boundary_regularized
#print axioms CarryCriticalComplete.four_source_path_energy_tendsto
#print axioms CarryCriticalComplete.regular_imaginary_pair_exact
#print axioms CarryCriticalComplete.critical_input_imaginary
#print axioms CarryCriticalComplete.critical_split_uniform
#print axioms CarryCriticalComplete.defect_input_scale
#print axioms CarryCriticalComplete.defect_pair_factor
#print axioms CarryCriticalComplete.defect_energy_tendsto_zero
#print axioms CarryCriticalComplete.defect_pair_re_factor
#print axioms CarryCriticalComplete.defectRateTemplate
#print axioms CarryCriticalComplete.defect_scaled_boundary_tendsto
#print axioms CarryCriticalComplete.defect_scaled_energy_limit
#print axioms CarryCriticalComplete.defect_uniform_quadratic_rate
#print axioms CarryCriticalComplete.defect_uniform_relative_small
#print axioms CarryCriticalComplete.critical_principal_uniform_close
#print axioms CarryCriticalComplete.critical_uniform_physical_margin
#print axioms CarryCriticalComplete.critical_native_energy_limit

#audit_odd_green construction
  CarryCriticalComplete.sourceBoundary
  CarryCriticalComplete.criticalBoundary
  CarryCriticalComplete.defectBoundary
  CarryCriticalComplete.physical_values_sub
  CarryCriticalComplete.source_boundary_sub
  CarryCriticalComplete.physical_values_smul
  CarryCriticalComplete.source_boundary_smul
  CarryCriticalComplete.critical_boundary_split
  CarryCriticalComplete.critical_four_support
  CarryCriticalComplete.defect_coefficient_formula
  CarryCriticalComplete.critical_coefficient_formula
  CarryCriticalComplete.criticalTemplate
  CarryCriticalComplete.defectTemplate
  CarryCriticalComplete.critical_boundary_exact
  CarryCriticalComplete.defect_boundary_exact
  CarryCriticalComplete.boundary_eventually_exact
  CarryCriticalComplete.critical_boundary_tendsto
  CarryCriticalComplete.defect_boundary_tendsto_zero
  CarryCriticalComplete.critical_template_norm_sq
  CarryCriticalComplete.critical_boundary_uniform_lower
  CarryCriticalComplete.physical_boundary_regularized
  CarryCriticalComplete.four_source_path_energy_tendsto
  CarryCriticalComplete.regular_imaginary_pair_exact
  CarryCriticalComplete.critical_input_imaginary
  CarryCriticalComplete.critical_split_uniform
  CarryCriticalComplete.defect_input_scale
  CarryCriticalComplete.defect_pair_factor
  CarryCriticalComplete.defect_energy_tendsto_zero
  CarryCriticalComplete.defect_pair_re_factor
  CarryCriticalComplete.defectRateTemplate
  CarryCriticalComplete.defect_scaled_boundary_tendsto
  CarryCriticalComplete.defect_scaled_energy_limit
  CarryCriticalComplete.defect_uniform_quadratic_rate
  CarryCriticalComplete.defect_uniform_relative_small
  CarryCriticalComplete.critical_principal_uniform_close
  CarryCriticalComplete.critical_native_energy_limit


#audit_odd_green finite_margin
  CarryCriticalComplete.critical_uniform_physical_margin
