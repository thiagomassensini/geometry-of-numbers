import PhysicalPrincipalSplit
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryCubicOdd.critical_cauchy_row,
    `CarryCubicOdd.critical_readout_four_samples,
    `CarryCubicOdd.critical_rho_alternating,
    `CarryCubicOdd.critical_diagonal_four_samples_exact,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
          (construction && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment) ||
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
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  logInfo m!"Native physical address split {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryAddressSplit.addressPower
#print axioms CarryAddressSplit.sourceEndpoint
#print axioms CarryAddressSplit.source_endpoint_sum
#print axioms CarryAddressSplit.source_endpoint_single
#print axioms CarryAddressSplit.source_endpoint_physical
#print axioms CarryAddressSplit.address_power_apply
#print axioms CarryAddressSplit.address_power_zero
#print axioms CarryAddressSplit.address_power_support
#print axioms CarryAddressSplit.address_power_comp
#print axioms CarryAddressSplit.address_power_add
#print axioms CarryAddressSplit.address_power_scale
#print axioms CarryAddressSplit.address_power_single
#print axioms CarryAddressSplit.address_power_sum
#print axioms CarryAddressSplit.kernel_address_green
#print axioms CarryAddressSplit.symKernel
#print axioms CarryAddressSplit.sym_kernel_swap
#print axioms CarryAddressSplit.sym_address_self_zero
#print axioms CarryAddressSplit.sym_second_first_zero
#print axioms CarryAddressSplit.kernel_source_add_left
#print axioms CarryAddressSplit.kernel_source_add_right
#print axioms CarryAddressSplit.kernel_source_neg_left
#print axioms CarryAddressSplit.kernel_source_neg_right
#print axioms CarryAddressSplit.sym_sub_sub
#print axioms CarryAddressSplit.kernel_address_right
#print axioms CarryAddressSplit.static_address_step
#print axioms CarryAddressSplit.static_address_two_step
#print axioms CarryAddressSplit.odd_address_lowering
#print axioms CarryAddressSplit.endpoint_static_power
#print axioms CarryAddressSplit.endpoint_odd_power
#print axioms CarryAddressSplit.endpoint_odd_power_zero
#print axioms CarryAddressSplit.endpoint_odd_first_survives
#print axioms CarryAddressSplit.endpoint_odd_first_nonzero
#print axioms CarryAddressSplit.address_even_odd_orthogonal
#print axioms CarryAddressSplit.native_odd_address_orthogonal
#print axioms CarryAddressSplit.principalInput
#print axioms CarryAddressSplit.defectInput
#print axioms CarryAddressSplit.critical_input_split
#print axioms CarryAddressSplit.principal_defect_kernel_orthogonal
#print axioms CarryAddressSplit.defect_principal_kernel_orthogonal
#print axioms CarryAddressSplit.completed_parts_split
#print axioms CarryAddressSplit.complete_physical_source_split
#print axioms CarryAddressSplit.weighted_odd_support
#print axioms CarryAddressSplit.principal_support
#print axioms CarryAddressSplit.defect_support
#print axioms CarryAddressSplit.weighted_odd_imaginary
#print axioms CarryAddressSplit.principal_imaginary
#print axioms CarryAddressSplit.defect_imaginary
#print axioms CarryAddressSplit.imaginary_families_exact
#print axioms CarryAddressSplit.principal_defect_green_orthogonal
#print axioms CarryAddressSplit.defect_principal_green_orthogonal
#print axioms CarryAddressSplit.critical_kernel_split
#print axioms CarryAddressSplit.cubic_kernel_grid
#print axioms CarryAddressSplit.defect_kernel_grid
#print axioms CarryAddressSplit.principalGrid
#print axioms CarryAddressSplit.defect_physical_grid
#print axioms CarryAddressSplit.critical_physical_split
#print axioms CarryAddressSplit.principal_physical_grid
#print axioms CarryAddressSplit.defect_physical_tendsto_zero
#print axioms CarryAddressSplit.defect_physical_scaled_tendsto
#print axioms CarryAddressSplit.principal_physical_tendsto
#print axioms CarryAddressSplit.principal_physical_schur_tendsto

#audit_odd_green construction
  CarryAddressSplit.addressPower
  CarryAddressSplit.sourceEndpoint
  CarryAddressSplit.source_endpoint_sum
  CarryAddressSplit.source_endpoint_single
  CarryAddressSplit.source_endpoint_physical
  CarryAddressSplit.address_power_apply
  CarryAddressSplit.address_power_zero
  CarryAddressSplit.address_power_support
  CarryAddressSplit.address_power_comp
  CarryAddressSplit.address_power_add
  CarryAddressSplit.address_power_scale
  CarryAddressSplit.address_power_single
  CarryAddressSplit.address_power_sum
  CarryAddressSplit.kernel_address_green
  CarryAddressSplit.symKernel
  CarryAddressSplit.sym_kernel_swap
  CarryAddressSplit.sym_address_self_zero
  CarryAddressSplit.sym_second_first_zero
  CarryAddressSplit.kernel_source_add_left
  CarryAddressSplit.kernel_source_add_right
  CarryAddressSplit.kernel_source_neg_left
  CarryAddressSplit.kernel_source_neg_right
  CarryAddressSplit.sym_sub_sub
  CarryAddressSplit.kernel_address_right
  CarryAddressSplit.static_address_step
  CarryAddressSplit.static_address_two_step
  CarryAddressSplit.odd_address_lowering
  CarryAddressSplit.endpoint_static_power
  CarryAddressSplit.endpoint_odd_power
  CarryAddressSplit.endpoint_odd_power_zero
  CarryAddressSplit.endpoint_odd_first_survives
  CarryAddressSplit.endpoint_odd_first_nonzero
  CarryAddressSplit.address_even_odd_orthogonal
  CarryAddressSplit.native_odd_address_orthogonal
  CarryAddressSplit.principalInput
  CarryAddressSplit.defectInput
  CarryAddressSplit.critical_input_split
  CarryAddressSplit.principal_defect_kernel_orthogonal
  CarryAddressSplit.defect_principal_kernel_orthogonal
  CarryAddressSplit.completed_parts_split
  CarryAddressSplit.complete_physical_source_split
  CarryAddressSplit.weighted_odd_support
  CarryAddressSplit.principal_support
  CarryAddressSplit.defect_support
  CarryAddressSplit.weighted_odd_imaginary
  CarryAddressSplit.principal_imaginary
  CarryAddressSplit.defect_imaginary
  CarryAddressSplit.imaginary_families_exact
  CarryAddressSplit.principal_defect_green_orthogonal
  CarryAddressSplit.defect_principal_green_orthogonal
  CarryAddressSplit.critical_kernel_split
  CarryAddressSplit.cubic_kernel_grid
  CarryAddressSplit.defect_kernel_grid
  CarryAddressSplit.principalGrid
  CarryAddressSplit.defect_physical_grid
  CarryAddressSplit.critical_physical_split
  CarryAddressSplit.principal_physical_grid


#audit_odd_green provenance
  CarryAddressSplit.defect_physical_tendsto_zero
  CarryAddressSplit.defect_physical_scaled_tendsto
  CarryAddressSplit.principal_physical_tendsto
  CarryAddressSplit.principal_physical_schur_tendsto
