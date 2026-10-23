import OriginalSourceDomain
import Lean

open Lean Elab Command
elab "#audit_completed_pairing " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let signs := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial]
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden downstream sign consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-defined construction: {name}"
      if tier.getNat <= 1 && signs.contains name then
        throwError "Finite sign or theta-moment dependency outside canary: {name}"
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
  logInfo m!"Physical material trace audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryPhysicalTrace.embedding_sum
#print axioms CarryPhysicalTrace.embedding_eq_finite
#print axioms CarryPhysicalTrace.physical_embedding_eq_zero
#print axioms CarryPhysicalTrace.physical_embedding_injective
#print axioms CarryPhysicalTrace.EndpointDomain
#print axioms CarryPhysicalTrace.coefficientEquiv
#print axioms CarryPhysicalTrace.coefficient_equiv_coe
#print axioms CarryPhysicalTrace.endpoint_domain_dense
#print axioms CarryPhysicalTrace.coefficientEndpoint
#print axioms CarryPhysicalTrace.endpointTrace
#print axioms CarryPhysicalTrace.coefficientDirichlet
#print axioms CarryPhysicalTrace.dirichletTrace
#print axioms CarryPhysicalTrace.domainColumn
#print axioms CarryPhysicalTrace.domain_column_coe
#print axioms CarryPhysicalTrace.endpoint_trace_coefficients
#print axioms CarryPhysicalTrace.endpoint_trace_column
#print axioms CarryPhysicalTrace.dirichlet_trace_column
#print axioms CarryPhysicalTrace.physical_column_inner
#print axioms CarryPhysicalTrace.physical_column_norm_sq
#print axioms CarryPhysicalTrace.physical_column_norm
#print axioms CarryPhysicalTrace.coefficientEuler
#print axioms CarryPhysicalTrace.coefficient_euler_single
#print axioms CarryPhysicalTrace.coefficient_euler_apply
#print axioms CarryPhysicalTrace.eulerAction
#print axioms CarryPhysicalTrace.euler_action_coefficients
#print axioms CarryPhysicalTrace.physical_embedding_single
#print axioms CarryPhysicalTrace.physical_euler_green
#print axioms CarryPhysicalTrace.endpoint_green
#print axioms CarryPhysicalTrace.endpoint_green_energy
#print axioms CarryPhysicalTrace.endpoint_graph_bound
#print axioms CarryPhysicalTrace.physical_column_tendsto_zero
#print axioms CarryPhysicalTrace.endpoint_graph_witness
#print axioms CarryPhysicalTrace.no_bounded_endpoint_extension
#print axioms CarryPhysicalTrace.unitColumn
#print axioms CarryPhysicalTrace.unit_column_norm
#print axioms CarryPhysicalTrace.unit_column_inner_sq
#print axioms CarryPhysicalTrace.unit_column_inner_bound
#print axioms CarryPhysicalTrace.column_inner_unit_tendsto
#print axioms CarryPhysicalTrace.finite_inner_unit_tendsto
#print axioms CarryPhysicalTrace.unit_column_weak_zero
#print axioms CarryPhysicalTrace.bounded_readout_unit_tendsto_zero
#print axioms CarryPhysicalTrace.critical_column_readout_norm_sq
#print axioms CarryPhysicalTrace.no_bounded_critical_dirichlet_columns
#print axioms CarryPhysicalTrace.no_bounded_critical_dirichlet_extension
#print axioms CarryPhysicalTrace.euler_polynomial
#print axioms CarryPhysicalTrace.finiteMaterialState
#print axioms CarryPhysicalTrace.finite_material_state_coe
#print axioms CarryPhysicalTrace.endpoint_trace_finite_material
#print axioms CarryPhysicalTrace.native_encoder_trace
#print axioms CarryPhysicalTrace.radial_finite_material
#print axioms CarryPhysicalTrace.radial_combination_in_domain
#print axioms CarryPhysicalTrace.original_incident_in_domain
#print axioms CarryPhysicalTrace.original_returned_in_domain
#print axioms CarryPhysicalTrace.original_value_in_domain
#print axioms CarryPhysicalTrace.original_companion_in_domain
#print axioms CarryPhysicalTrace.original_native_companion_in_domain
#print axioms CarryPhysicalTrace.original_completion_companion_in_domain

#audit_completed_pairing 0
  CarryPhysicalTrace.embedding_sum
  CarryPhysicalTrace.embedding_eq_finite
  CarryPhysicalTrace.physical_embedding_eq_zero
  CarryPhysicalTrace.physical_embedding_injective
  CarryPhysicalTrace.EndpointDomain
  CarryPhysicalTrace.coefficientEquiv
  CarryPhysicalTrace.coefficient_equiv_coe
  CarryPhysicalTrace.endpoint_domain_dense
  CarryPhysicalTrace.coefficientEndpoint
  CarryPhysicalTrace.endpointTrace
  CarryPhysicalTrace.coefficientDirichlet
  CarryPhysicalTrace.dirichletTrace
  CarryPhysicalTrace.domainColumn
  CarryPhysicalTrace.domain_column_coe
  CarryPhysicalTrace.endpoint_trace_coefficients
  CarryPhysicalTrace.endpoint_trace_column
  CarryPhysicalTrace.dirichlet_trace_column
  CarryPhysicalTrace.physical_column_inner
  CarryPhysicalTrace.physical_column_norm_sq
  CarryPhysicalTrace.physical_column_norm
  CarryPhysicalTrace.coefficientEuler
  CarryPhysicalTrace.coefficient_euler_single
  CarryPhysicalTrace.coefficient_euler_apply
  CarryPhysicalTrace.eulerAction
  CarryPhysicalTrace.euler_action_coefficients
  CarryPhysicalTrace.physical_embedding_single
  CarryPhysicalTrace.physical_euler_green
  CarryPhysicalTrace.endpoint_green
  CarryPhysicalTrace.endpoint_green_energy
  CarryPhysicalTrace.endpoint_graph_bound
  CarryPhysicalTrace.physical_column_tendsto_zero
  CarryPhysicalTrace.endpoint_graph_witness
  CarryPhysicalTrace.no_bounded_endpoint_extension
  CarryPhysicalTrace.unitColumn
  CarryPhysicalTrace.unit_column_norm
  CarryPhysicalTrace.unit_column_inner_sq
  CarryPhysicalTrace.unit_column_inner_bound
  CarryPhysicalTrace.column_inner_unit_tendsto
  CarryPhysicalTrace.finite_inner_unit_tendsto
  CarryPhysicalTrace.unit_column_weak_zero
  CarryPhysicalTrace.bounded_readout_unit_tendsto_zero
  CarryPhysicalTrace.critical_column_readout_norm_sq
  CarryPhysicalTrace.no_bounded_critical_dirichlet_columns
  CarryPhysicalTrace.no_bounded_critical_dirichlet_extension
  CarryPhysicalTrace.euler_polynomial
  CarryPhysicalTrace.finiteMaterialState
  CarryPhysicalTrace.finite_material_state_coe
  CarryPhysicalTrace.endpoint_trace_finite_material
  CarryPhysicalTrace.native_encoder_trace
  CarryPhysicalTrace.radial_finite_material
  CarryPhysicalTrace.radial_combination_in_domain
  CarryPhysicalTrace.original_incident_in_domain
  CarryPhysicalTrace.original_returned_in_domain
  CarryPhysicalTrace.original_value_in_domain
  CarryPhysicalTrace.original_companion_in_domain
  CarryPhysicalTrace.original_native_companion_in_domain
  CarryPhysicalTrace.original_completion_companion_in_domain

#audit_completed_pairing 0
  CarryPhysicalTrace.embedding_sum
  CarryPhysicalTrace.embedding_eq_finite
  CarryPhysicalTrace.physical_embedding_eq_zero
  CarryPhysicalTrace.physical_embedding_injective
  CarryPhysicalTrace.EndpointDomain
  CarryPhysicalTrace.coefficientEquiv
  CarryPhysicalTrace.coefficient_equiv_coe
  CarryPhysicalTrace.endpoint_domain_dense
  CarryPhysicalTrace.coefficientEndpoint
  CarryPhysicalTrace.endpointTrace
  CarryPhysicalTrace.coefficientDirichlet
  CarryPhysicalTrace.dirichletTrace
  CarryPhysicalTrace.domainColumn
  CarryPhysicalTrace.domain_column_coe
  CarryPhysicalTrace.endpoint_trace_coefficients
  CarryPhysicalTrace.endpoint_trace_column
  CarryPhysicalTrace.dirichlet_trace_column
  CarryPhysicalTrace.physical_column_inner
  CarryPhysicalTrace.physical_column_norm_sq
  CarryPhysicalTrace.physical_column_norm
  CarryPhysicalTrace.coefficientEuler
  CarryPhysicalTrace.coefficient_euler_single
  CarryPhysicalTrace.coefficient_euler_apply
  CarryPhysicalTrace.eulerAction
  CarryPhysicalTrace.euler_action_coefficients
  CarryPhysicalTrace.physical_embedding_single
  CarryPhysicalTrace.physical_euler_green
  CarryPhysicalTrace.endpoint_green
  CarryPhysicalTrace.endpoint_green_energy
  CarryPhysicalTrace.endpoint_graph_bound
  CarryPhysicalTrace.physical_column_tendsto_zero
  CarryPhysicalTrace.endpoint_graph_witness
  CarryPhysicalTrace.no_bounded_endpoint_extension
  CarryPhysicalTrace.unitColumn
  CarryPhysicalTrace.unit_column_norm
  CarryPhysicalTrace.unit_column_inner_sq
  CarryPhysicalTrace.unit_column_inner_bound
  CarryPhysicalTrace.column_inner_unit_tendsto
  CarryPhysicalTrace.finite_inner_unit_tendsto
  CarryPhysicalTrace.unit_column_weak_zero
  CarryPhysicalTrace.bounded_readout_unit_tendsto_zero
  CarryPhysicalTrace.critical_column_readout_norm_sq
  CarryPhysicalTrace.no_bounded_critical_dirichlet_columns
  CarryPhysicalTrace.no_bounded_critical_dirichlet_extension
  CarryPhysicalTrace.euler_polynomial
  CarryPhysicalTrace.finiteMaterialState
  CarryPhysicalTrace.finite_material_state_coe
  CarryPhysicalTrace.endpoint_trace_finite_material
  CarryPhysicalTrace.native_encoder_trace
  CarryPhysicalTrace.radial_finite_material
  CarryPhysicalTrace.radial_combination_in_domain
  CarryPhysicalTrace.original_incident_in_domain
  CarryPhysicalTrace.original_returned_in_domain
  CarryPhysicalTrace.original_value_in_domain
  CarryPhysicalTrace.original_companion_in_domain
  CarryPhysicalTrace.original_native_companion_in_domain
  CarryPhysicalTrace.original_completion_companion_in_domain
