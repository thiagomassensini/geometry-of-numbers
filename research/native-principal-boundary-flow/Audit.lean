import FluxObstruction
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
          (construction && (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
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
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  logInfo m!"Native principal boundary flow {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryPrincipalFlow.bareKernel
#print axioms CarryPrincipalFlow.bare_kernel_inner
#print axioms CarryPrincipalFlow.bare_kernel_conj
#print axioms CarryPrincipalFlow.boundaryFlux
#print axioms CarryPrincipalFlow.boundary_flux_succ
#print axioms CarryPrincipalFlow.source_green_all_order
#print axioms CarryPrincipalFlow.monomial_kernel_right
#print axioms CarryPrincipalFlow.monomial_kernel_reverse
#print axioms CarryPrincipalFlow.odd_monomial_flux
#print axioms CarryPrincipalFlow.principal_boundary_trace
#print axioms CarryPrincipalFlow.principal_trace_zero
#print axioms CarryPrincipalFlow.principal_trace_one
#print axioms CarryPrincipalFlow.principal_trace_two
#print axioms CarryPrincipalFlow.principal_trace_three
#print axioms CarryPrincipalFlow.principal_flux_first
#print axioms CarryPrincipalFlow.principal_flux_cubic
#print axioms CarryPrincipalFlow.principal_flux_quintic
#print axioms CarryPrincipalFlow.principal_monomial_one
#print axioms CarryPrincipalFlow.principal_monomial_three
#print axioms CarryPrincipalFlow.principal_monomial_five
#print axioms CarryPrincipalFlow.responseHead
#print axioms CarryPrincipalFlow.responseTail
#print axioms CarryPrincipalFlow.full_response_head_tail
#print axioms CarryPrincipalFlow.original_field_head_tail
#print axioms CarryPrincipalFlow.original_vector_head_tail
#print axioms CarryPrincipalFlow.sym_add_weight
#print axioms CarryPrincipalFlow.sym_scale_weight
#print axioms CarryPrincipalFlow.principal_head_flux
#print axioms CarryPrincipalFlow.principalTailFlux
#print axioms CarryPrincipalFlow.response_head_real
#print axioms CarryPrincipalFlow.response_tail_real
#print axioms CarryPrincipalFlow.principal_tail_flux_real
#print axioms CarryPrincipalFlow.principal_native_response
#print axioms CarryPrincipalFlow.principal_physical_flow
#print axioms CarryPrincipalFlow.tailComponent
#print axioms CarryPrincipalFlow.headComponent
#print axioms CarryPrincipalFlow.tailPartComponent
#print axioms CarryPrincipalFlow.tail_parts_reconstruct
#print axioms CarryPrincipalFlow.complete_state_head_tail
#print axioms CarryPrincipalFlow.tail_pairing_zero
#print axioms CarryPrincipalFlow.head_preserves_contrast
#print axioms CarryPrincipalFlow.tail_scale_calibration
#print axioms CarryPrincipalFlow.tail_mixed_physical_flux
#print axioms CarryPrincipalFlow.signed_sub_isotropic
#print axioms CarryPrincipalFlow.head_physical_flow
#print axioms CarryPrincipalFlow.nativePrincipalTail
#print axioms CarryPrincipalFlow.native_principal_flow
#print axioms CarryPrincipalFlow.critical_tail_budget_exact
#print axioms CarryPrincipalFlow.native_tail_samples
#print axioms CarryPrincipalFlow.native_tail_field_fixed
#print axioms CarryPrincipalFlow.native_principal_tail_fields
#print axioms CarryPrincipalFlow.native_principal_tail_tendsto
#print axioms CarryPrincipalFlow.oriented_cubic_value
#print axioms CarryPrincipalFlow.oriented_cubic_nonnegative
#print axioms CarryPrincipalFlow.oriented_quintic_value
#print axioms CarryPrincipalFlow.oriented_quintic_negative
#print axioms CarryPrincipalFlow.raw_quintic_counterexample
#print axioms CarryPrincipalFlow.positive_weight_not_sufficient

#audit_odd_green construction
  CarryPrincipalFlow.bareKernel
  CarryPrincipalFlow.bare_kernel_inner
  CarryPrincipalFlow.bare_kernel_conj
  CarryPrincipalFlow.boundaryFlux
  CarryPrincipalFlow.boundary_flux_succ
  CarryPrincipalFlow.source_green_all_order
  CarryPrincipalFlow.monomial_kernel_right
  CarryPrincipalFlow.monomial_kernel_reverse
  CarryPrincipalFlow.odd_monomial_flux
  CarryPrincipalFlow.principal_boundary_trace
  CarryPrincipalFlow.principal_trace_zero
  CarryPrincipalFlow.principal_trace_one
  CarryPrincipalFlow.principal_trace_two
  CarryPrincipalFlow.principal_trace_three
  CarryPrincipalFlow.principal_flux_first
  CarryPrincipalFlow.principal_flux_cubic
  CarryPrincipalFlow.principal_flux_quintic
  CarryPrincipalFlow.principal_monomial_one
  CarryPrincipalFlow.principal_monomial_three
  CarryPrincipalFlow.principal_monomial_five
  CarryPrincipalFlow.responseHead
  CarryPrincipalFlow.responseTail
  CarryPrincipalFlow.full_response_head_tail
  CarryPrincipalFlow.original_field_head_tail
  CarryPrincipalFlow.original_vector_head_tail
  CarryPrincipalFlow.sym_add_weight
  CarryPrincipalFlow.sym_scale_weight
  CarryPrincipalFlow.principal_head_flux
  CarryPrincipalFlow.principalTailFlux
  CarryPrincipalFlow.response_head_real
  CarryPrincipalFlow.response_tail_real
  CarryPrincipalFlow.principal_tail_flux_real
  CarryPrincipalFlow.principal_native_response
  CarryPrincipalFlow.principal_physical_flow
  CarryPrincipalFlow.tailComponent
  CarryPrincipalFlow.headComponent
  CarryPrincipalFlow.tailPartComponent
  CarryPrincipalFlow.tail_parts_reconstruct
  CarryPrincipalFlow.complete_state_head_tail
  CarryPrincipalFlow.tail_pairing_zero
  CarryPrincipalFlow.head_preserves_contrast
  CarryPrincipalFlow.tail_scale_calibration
  CarryPrincipalFlow.tail_mixed_physical_flux
  CarryPrincipalFlow.signed_sub_isotropic
  CarryPrincipalFlow.head_physical_flow
  CarryPrincipalFlow.oriented_cubic_value
  CarryPrincipalFlow.oriented_cubic_nonnegative
  CarryPrincipalFlow.oriented_quintic_value
  CarryPrincipalFlow.oriented_quintic_negative
  CarryPrincipalFlow.raw_quintic_counterexample
  CarryPrincipalFlow.positive_weight_not_sufficient


#audit_odd_green provenance
  CarryPrincipalFlow.nativePrincipalTail
  CarryPrincipalFlow.native_principal_flow
  CarryPrincipalFlow.critical_tail_budget_exact
  CarryPrincipalFlow.native_tail_samples
  CarryPrincipalFlow.native_tail_field_fixed
  CarryPrincipalFlow.native_principal_tail_fields
  CarryPrincipalFlow.native_principal_tail_tendsto
