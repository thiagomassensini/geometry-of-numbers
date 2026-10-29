import Cancellation
import Lean

open Lean Elab Command
elab "#audit_critical_tfvd " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let finiteSigns := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
      if name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." ||
          name == `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier then
        throwError "Forbidden downstream positivity consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-dependent physical construction: {name}"
      if finiteSigns.contains name then
        throwError "Finite moment sign outside source-free identities: {name}"
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
  logInfo m!"Critical TFVD audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryCriticalTfvd.mixedEnergy
#print axioms CarryCriticalTfvd.fullEnergy
#print axioms CarryCriticalTfvd.bulkBoundaryEnergy
#print axioms CarryCriticalTfvd.full_split
#print axioms CarryCriticalTfvd.commutator_response_field
#print axioms CarryCriticalTfvd.mixed_response_flux
#print axioms CarryCriticalTfvd.incident_response_coefficients
#print axioms CarryCriticalTfvd.source_mean_response
#print axioms CarryCriticalTfvd.full_response_flux
#print axioms CarryCriticalTfvd.triple
#print axioms CarryCriticalTfvd.triple_support
#print axioms CarryCriticalTfvd.curvatureInput
#print axioms CarryCriticalTfvd.seedInput
#print axioms CarryCriticalTfvd.criticalInput
#print axioms CarryCriticalTfvd.critical_input_triple
#print axioms CarryCriticalTfvd.critical_input_support
#print axioms CarryCriticalTfvd.synthesis_triple
#print axioms CarryCriticalTfvd.commutator_triple
#print axioms CarryCriticalTfvd.source_triple
#print axioms CarryCriticalTfvd.second_scale
#print axioms CarryCriticalTfvd.critical_source_jets
#print axioms CarryCriticalTfvd.h
#print axioms CarryCriticalTfvd.responseReadout
#print axioms CarryCriticalTfvd.responseCoefficient
#print axioms CarryCriticalTfvd.response_readout_analytic
#print axioms CarryCriticalTfvd.response_coefficient_derivative
#print axioms CarryCriticalTfvd.response_coefficient_even
#print axioms CarryCriticalTfvd.response_coefficient_odd
#print axioms CarryCriticalTfvd.response_seventh_remainder
#print axioms CarryCriticalTfvd.radialStep
#print axioms CarryCriticalTfvd.monomialWeight
#print axioms CarryCriticalTfvd.remainderWeight
#print axioms CarryCriticalTfvd.radial_step_tendsto
#print axioms CarryCriticalTfvd.response_radial_readout
#print axioms CarryCriticalTfvd.response_weight_taylor
#print axioms CarryCriticalTfvd.coefficientStencil
#print axioms CarryCriticalTfvd.sectorField
#print axioms CarryCriticalTfvd.sectorKernel
#print axioms CarryCriticalTfvd.stencil_add_weight
#print axioms CarryCriticalTfvd.stencil_scale_weight
#print axioms CarryCriticalTfvd.stencil_add_input
#print axioms CarryCriticalTfvd.stencil_scale_input
#print axioms CarryCriticalTfvd.stencil_congr
#print axioms CarryCriticalTfvd.field_add_weight
#print axioms CarryCriticalTfvd.field_scale_weight
#print axioms CarryCriticalTfvd.field_add_input
#print axioms CarryCriticalTfvd.field_scale_input
#print axioms CarryCriticalTfvd.kernel_add_weight
#print axioms CarryCriticalTfvd.kernel_scale_weight
#print axioms CarryCriticalTfvd.kernel_four_weights
#print axioms CarryCriticalTfvd.spatialU
#print axioms CarryCriticalTfvd.spatialV
#print axioms CarryCriticalTfvd.spatialW
#print axioms CarryCriticalTfvd.kernel_critical_real
#print axioms CarryCriticalTfvd.weight_triple
#print axioms CarryCriticalTfvd.remainder_field_continuous
#print axioms CarryCriticalTfvd.remainder_kernel_continuous
#print axioms CarryCriticalTfvd.sectorFlux
#print axioms CarryCriticalTfvd.full_original_flux
#print axioms CarryCriticalTfvd.mixed_original_flux
#print axioms CarryCriticalTfvd.poleFour
#print axioms CarryCriticalTfvd.poleTwo
#print axioms CarryCriticalTfvd.finitePart
#print axioms CarryCriticalTfvd.sectorError
#print axioms CarryCriticalTfvd.kernel_congr
#print axioms CarryCriticalTfvd.sector_flux_exact_expansion
#print axioms CarryCriticalTfvd.sector_error_continuous
#print axioms CarryCriticalTfvd.sector_finite_part_limit
#print axioms CarryCriticalTfvd.sector_second_order_error_bound
#print axioms CarryCriticalTfvd.full_kernel_triple
#print axioms CarryCriticalTfvd.full_spatial_constants
#print axioms CarryCriticalTfvd.canonicalQuadratic
#print axioms CarryCriticalTfvd.full_poles_zero
#print axioms CarryCriticalTfvd.full_finite_part
#print axioms CarryCriticalTfvd.complete_tfvd_expansion
#print axioms CarryCriticalTfvd.full_critical_limit
#print axioms CarryCriticalTfvd.mixed_renormalized_limit
#print axioms CarryCriticalTfvd.bulk_boundary_renormalized_limit
#print axioms CarryCriticalTfvd.criticalParameter
#print axioms CarryCriticalTfvd.canonical_quadratic_schur
#print axioms CarryCriticalTfvd.critical_tfvd_schur_limit
#print axioms CarryCriticalTfvd.first_schur_formula
#print axioms CarryCriticalTfvd.critical_tfvd_named_schur_limit

#audit_critical_tfvd 0
  CarryCriticalTfvd.mixedEnergy
  CarryCriticalTfvd.fullEnergy
  CarryCriticalTfvd.bulkBoundaryEnergy
  CarryCriticalTfvd.full_split
  CarryCriticalTfvd.commutator_response_field
  CarryCriticalTfvd.mixed_response_flux
  CarryCriticalTfvd.incident_response_coefficients
  CarryCriticalTfvd.source_mean_response
  CarryCriticalTfvd.full_response_flux
  CarryCriticalTfvd.triple
  CarryCriticalTfvd.triple_support
  CarryCriticalTfvd.curvatureInput
  CarryCriticalTfvd.seedInput
  CarryCriticalTfvd.criticalInput
  CarryCriticalTfvd.critical_input_triple
  CarryCriticalTfvd.critical_input_support
  CarryCriticalTfvd.synthesis_triple
  CarryCriticalTfvd.commutator_triple
  CarryCriticalTfvd.source_triple
  CarryCriticalTfvd.second_scale
  CarryCriticalTfvd.critical_source_jets
  CarryCriticalTfvd.coefficientStencil
  CarryCriticalTfvd.sectorField
  CarryCriticalTfvd.sectorKernel
  CarryCriticalTfvd.stencil_add_weight
  CarryCriticalTfvd.stencil_scale_weight
  CarryCriticalTfvd.stencil_add_input
  CarryCriticalTfvd.stencil_scale_input
  CarryCriticalTfvd.stencil_congr
  CarryCriticalTfvd.field_add_weight
  CarryCriticalTfvd.field_scale_weight
  CarryCriticalTfvd.field_add_input
  CarryCriticalTfvd.field_scale_input
  CarryCriticalTfvd.kernel_add_weight
  CarryCriticalTfvd.kernel_scale_weight
  CarryCriticalTfvd.kernel_four_weights
  CarryCriticalTfvd.spatialU
  CarryCriticalTfvd.spatialV
  CarryCriticalTfvd.spatialW
  CarryCriticalTfvd.kernel_critical_real
  CarryCriticalTfvd.weight_triple
  CarryCriticalTfvd.remainder_field_continuous
  CarryCriticalTfvd.remainder_kernel_continuous


#audit_critical_tfvd 1
  CarryCriticalTfvd.h
  CarryCriticalTfvd.responseReadout
  CarryCriticalTfvd.responseCoefficient
  CarryCriticalTfvd.response_readout_analytic
  CarryCriticalTfvd.response_coefficient_derivative
  CarryCriticalTfvd.response_coefficient_even
  CarryCriticalTfvd.response_coefficient_odd
  CarryCriticalTfvd.response_seventh_remainder
  CarryCriticalTfvd.radialStep
  CarryCriticalTfvd.monomialWeight
  CarryCriticalTfvd.remainderWeight
  CarryCriticalTfvd.radial_step_tendsto
  CarryCriticalTfvd.response_radial_readout
  CarryCriticalTfvd.response_weight_taylor
  CarryCriticalTfvd.sectorFlux
  CarryCriticalTfvd.full_original_flux
  CarryCriticalTfvd.mixed_original_flux
  CarryCriticalTfvd.poleFour
  CarryCriticalTfvd.poleTwo
  CarryCriticalTfvd.finitePart
  CarryCriticalTfvd.sectorError
  CarryCriticalTfvd.kernel_congr
  CarryCriticalTfvd.sector_flux_exact_expansion
  CarryCriticalTfvd.sector_error_continuous
  CarryCriticalTfvd.sector_finite_part_limit
  CarryCriticalTfvd.sector_second_order_error_bound
  CarryCriticalTfvd.full_kernel_triple
  CarryCriticalTfvd.full_spatial_constants
  CarryCriticalTfvd.canonicalQuadratic
  CarryCriticalTfvd.full_poles_zero
  CarryCriticalTfvd.full_finite_part
  CarryCriticalTfvd.complete_tfvd_expansion
  CarryCriticalTfvd.full_critical_limit
  CarryCriticalTfvd.mixed_renormalized_limit
  CarryCriticalTfvd.bulk_boundary_renormalized_limit
  CarryCriticalTfvd.criticalParameter
  CarryCriticalTfvd.canonical_quadratic_schur
  CarryCriticalTfvd.critical_tfvd_schur_limit
  CarryCriticalTfvd.first_schur_formula
  CarryCriticalTfvd.critical_tfvd_named_schur_limit
