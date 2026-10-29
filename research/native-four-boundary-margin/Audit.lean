import CoercivePhysicalMargin
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let canonicalReadout := group.getId == `canonical_limit
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
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
          (!canonicalReadout && (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
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
    for name in #[`CarrySelfAdjointOperator.storage_one_fourSample_eventually_boundary_coercive,
        `CarrySelfAdjointOperator.radialFourRegularizedStorage_eventually_unit_margin] do
      unless seen.contains name do
        throwError "Missing expected native coercivity dependency (check theorem-body traversal): {name}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native four-boundary margin {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={!canonicalReadout}; finite source-sign roots excluded from construction; scalar-asymptotic shortcuts forbidden"

#print axioms CarryBoundaryMargin.physicalCoefficients
#print axioms CarryBoundaryMargin.physicalValues
#print axioms CarryBoundaryMargin.physical_values_eq
#print axioms CarryBoundaryMargin.physical_values_recover
#print axioms CarryBoundaryMargin.principalBoundary
#print axioms CarryBoundaryMargin.boundaryTemplate
#print axioms CarryBoundaryMargin.boundaryLimit
#print axioms CarryBoundaryMargin.principal_boundary_exact
#print axioms CarryBoundaryMargin.principal_boundary_eventually_exact
#print axioms CarryBoundaryMargin.boundary_template_continuous
#print axioms CarryBoundaryMargin.principal_boundary_tendsto
#print axioms CarryBoundaryMargin.boundary_template_norm_sq
#print axioms CarryBoundaryMargin.boundary_limit_norm_sq
#print axioms CarryBoundaryMargin.boundary_limit_ne_zero
#print axioms CarryBoundaryMargin.boundary_shear_lower
#print axioms CarryBoundaryMargin.principal_boundary_eventually_lower
#print axioms CarryBoundaryMargin.physical_four_boundary_coercive
#print axioms CarryBoundaryMargin.principal_uniform_physical_margin
#print axioms CarryBoundaryMargin.canonical_uniform_quadratic_margin
#print axioms CarryBoundaryMargin.canonical_second_shifted_schur_margin

#audit_odd_green construction
  CarryBoundaryMargin.physicalCoefficients
  CarryBoundaryMargin.physicalValues
  CarryBoundaryMargin.physical_values_eq
  CarryBoundaryMargin.physical_values_recover
  CarryBoundaryMargin.principalBoundary
  CarryBoundaryMargin.boundaryTemplate
  CarryBoundaryMargin.boundaryLimit
  CarryBoundaryMargin.principal_boundary_exact
  CarryBoundaryMargin.principal_boundary_eventually_exact
  CarryBoundaryMargin.boundary_template_continuous
  CarryBoundaryMargin.principal_boundary_tendsto
  CarryBoundaryMargin.boundary_template_norm_sq
  CarryBoundaryMargin.boundary_limit_norm_sq
  CarryBoundaryMargin.boundary_limit_ne_zero
  CarryBoundaryMargin.boundary_shear_lower
  CarryBoundaryMargin.principal_boundary_eventually_lower


#audit_odd_green finite_margin
  CarryBoundaryMargin.physical_four_boundary_coercive
  CarryBoundaryMargin.principal_uniform_physical_margin


#audit_odd_green canonical_limit
  CarryBoundaryMargin.canonical_uniform_quadratic_margin
  CarryBoundaryMargin.canonical_second_shifted_schur_margin
