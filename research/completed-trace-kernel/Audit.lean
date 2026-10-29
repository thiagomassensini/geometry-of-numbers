import NativeCanaries
import TracePairing
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
  logInfo m!"Completed trace kernel audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryCompletedTrace.valueCore
#print axioms CarryCompletedTrace.companionCore
#print axioms CarryCompletedTrace.nativeCore
#print axioms CarryCompletedTrace.completionCore
#print axioms CarryCompletedTrace.incidentCore
#print axioms CarryCompletedTrace.returnedCore
#print axioms CarryCompletedTrace.sourceWeight
#print axioms CarryCompletedTrace.radial_core_trace
#print axioms CarryCompletedTrace.value_core_trace
#print axioms CarryCompletedTrace.companion_core_trace
#print axioms CarryCompletedTrace.native_core_trace
#print axioms CarryCompletedTrace.completion_core_trace
#print axioms CarryCompletedTrace.incident_core_trace
#print axioms CarryCompletedTrace.returned_core_trace
#print axioms CarryCompletedTrace.companion_core_split
#print axioms CarryCompletedTrace.companion_trace_split
#print axioms CarryCompletedTrace.traceWedge
#print axioms CarryCompletedTrace.eulerWedge
#print axioms CarryCompletedTrace.euler_wedge_trace
#print axioms CarryCompletedTrace.mixed_wedge_scale
#print axioms CarryCompletedTrace.mixed_wedge_sum
#print axioms CarryCompletedTrace.completed_trace_pairing_mellin
#print axioms CarryCompletedTrace.completed_euler_pairing_mellin
#print axioms CarryCompletedTrace.physicalMixedPairing
#print axioms CarryCompletedTrace.physical_mixed_pairing_mellin
#print axioms CarryCompletedTrace.boundary_minus_bulk_mellin
#print axioms CarryCompletedTrace.completed_trace_split
#print axioms CarryCompletedTrace.radialMass
#print axioms CarryCompletedTrace.radialCrossGram
#print axioms CarryCompletedTrace.crossRadialFactor
#print axioms CarryCompletedTrace.crossRadialDefect
#print axioms CarryCompletedTrace.radial_cross_gram
#print axioms CarryCompletedTrace.mixed_radial_separation
#print axioms CarryCompletedTrace.mixed_radial_separation_ne
#print axioms CarryCompletedTrace.cross_factor_pos
#print axioms CarryCompletedTrace.radial_cross_gram_eq_factor
#print axioms CarryCompletedTrace.cross_defect_eq_factor_pick
#print axioms CarryCompletedTrace.cross_defect_is_original_pairing
#print axioms CarryCompletedTrace.native_kernel_cross_factor
#print axioms CarryCompletedTrace.cross_factor_same_radial
#print axioms CarryCompletedTrace.doubled_radial_mass
#print axioms CarryCompletedTrace.doubled_radial_sqrt_product
#print axioms CarryCompletedTrace.doubled_radial_same_point
#print axioms CarryCompletedTrace.cross_factor_same_point
#print axioms CarryCompletedTrace.same_point_factor_lt_one
#print axioms CarryCompletedTrace.radial_column_norm_sq
#print axioms CarryCompletedTrace.same_parameter_state_difference_norm_sq
#print axioms CarryCompletedTrace.same_parameter_states_ne
#print axioms CarryCompletedTrace.same_parameter_return_difference
#print axioms CarryCompletedTrace.cross_defect_same_point_residual
#print axioms CarryCompletedTrace.endpointBalance
#print axioms CarryCompletedTrace.endpoint_balance_is_native_flux
#print axioms CarryCompletedTrace.endpoint_balance_opposite_negative
#print axioms CarryCompletedTrace.radial_pick_first_re_pos_eventually
#print axioms CarryCompletedTrace.cross_radial_residual_re_negative_eventually

#audit_completed_pairing 0
  CarryCompletedTrace.valueCore
  CarryCompletedTrace.companionCore
  CarryCompletedTrace.nativeCore
  CarryCompletedTrace.completionCore
  CarryCompletedTrace.incidentCore
  CarryCompletedTrace.returnedCore
  CarryCompletedTrace.sourceWeight
  CarryCompletedTrace.radial_core_trace
  CarryCompletedTrace.value_core_trace
  CarryCompletedTrace.companion_core_trace
  CarryCompletedTrace.native_core_trace
  CarryCompletedTrace.completion_core_trace
  CarryCompletedTrace.incident_core_trace
  CarryCompletedTrace.returned_core_trace
  CarryCompletedTrace.companion_core_split
  CarryCompletedTrace.companion_trace_split
  CarryCompletedTrace.traceWedge
  CarryCompletedTrace.eulerWedge
  CarryCompletedTrace.euler_wedge_trace
  CarryCompletedTrace.mixed_wedge_scale
  CarryCompletedTrace.mixed_wedge_sum
  CarryCompletedTrace.completed_trace_pairing_mellin
  CarryCompletedTrace.completed_euler_pairing_mellin
  CarryCompletedTrace.physicalMixedPairing
  CarryCompletedTrace.physical_mixed_pairing_mellin
  CarryCompletedTrace.boundary_minus_bulk_mellin
  CarryCompletedTrace.completed_trace_split
  CarryCompletedTrace.radialMass
  CarryCompletedTrace.radialCrossGram
  CarryCompletedTrace.crossRadialFactor
  CarryCompletedTrace.crossRadialDefect
  CarryCompletedTrace.radial_cross_gram
  CarryCompletedTrace.mixed_radial_separation
  CarryCompletedTrace.mixed_radial_separation_ne
  CarryCompletedTrace.cross_factor_pos
  CarryCompletedTrace.radial_cross_gram_eq_factor
  CarryCompletedTrace.cross_defect_eq_factor_pick
  CarryCompletedTrace.cross_defect_is_original_pairing
  CarryCompletedTrace.native_kernel_cross_factor
  CarryCompletedTrace.cross_factor_same_radial
  CarryCompletedTrace.doubled_radial_mass
  CarryCompletedTrace.doubled_radial_sqrt_product
  CarryCompletedTrace.doubled_radial_same_point
  CarryCompletedTrace.cross_factor_same_point
  CarryCompletedTrace.same_point_factor_lt_one
  CarryCompletedTrace.radial_column_norm_sq
  CarryCompletedTrace.same_parameter_state_difference_norm_sq
  CarryCompletedTrace.same_parameter_states_ne
  CarryCompletedTrace.same_parameter_return_difference
  CarryCompletedTrace.cross_defect_same_point_residual
  CarryCompletedTrace.endpointBalance
  CarryCompletedTrace.endpoint_balance_is_native_flux

#audit_completed_pairing 2
  CarryCompletedTrace.endpoint_balance_opposite_negative
  CarryCompletedTrace.radial_pick_first_re_pos_eventually
  CarryCompletedTrace.cross_radial_residual_re_negative_eventually

#audit_completed_pairing 3
  CarryCompletedTrace.valueCore
  CarryCompletedTrace.companionCore
  CarryCompletedTrace.nativeCore
  CarryCompletedTrace.completionCore
  CarryCompletedTrace.incidentCore
  CarryCompletedTrace.returnedCore
  CarryCompletedTrace.sourceWeight
  CarryCompletedTrace.radial_core_trace
  CarryCompletedTrace.value_core_trace
  CarryCompletedTrace.companion_core_trace
  CarryCompletedTrace.native_core_trace
  CarryCompletedTrace.completion_core_trace
  CarryCompletedTrace.incident_core_trace
  CarryCompletedTrace.returned_core_trace
  CarryCompletedTrace.companion_core_split
  CarryCompletedTrace.companion_trace_split
  CarryCompletedTrace.traceWedge
  CarryCompletedTrace.eulerWedge
  CarryCompletedTrace.euler_wedge_trace
  CarryCompletedTrace.mixed_wedge_scale
  CarryCompletedTrace.mixed_wedge_sum
  CarryCompletedTrace.completed_trace_pairing_mellin
  CarryCompletedTrace.completed_euler_pairing_mellin
  CarryCompletedTrace.physicalMixedPairing
  CarryCompletedTrace.physical_mixed_pairing_mellin
  CarryCompletedTrace.boundary_minus_bulk_mellin
  CarryCompletedTrace.completed_trace_split
  CarryCompletedTrace.radialMass
  CarryCompletedTrace.radialCrossGram
  CarryCompletedTrace.crossRadialFactor
  CarryCompletedTrace.crossRadialDefect
  CarryCompletedTrace.radial_cross_gram
  CarryCompletedTrace.mixed_radial_separation
  CarryCompletedTrace.mixed_radial_separation_ne
  CarryCompletedTrace.cross_factor_pos
  CarryCompletedTrace.radial_cross_gram_eq_factor
  CarryCompletedTrace.cross_defect_eq_factor_pick
  CarryCompletedTrace.cross_defect_is_original_pairing
  CarryCompletedTrace.native_kernel_cross_factor
  CarryCompletedTrace.cross_factor_same_radial
  CarryCompletedTrace.doubled_radial_mass
  CarryCompletedTrace.doubled_radial_sqrt_product
  CarryCompletedTrace.doubled_radial_same_point
  CarryCompletedTrace.cross_factor_same_point
  CarryCompletedTrace.same_point_factor_lt_one
  CarryCompletedTrace.radial_column_norm_sq
  CarryCompletedTrace.same_parameter_state_difference_norm_sq
  CarryCompletedTrace.same_parameter_states_ne
  CarryCompletedTrace.same_parameter_return_difference
  CarryCompletedTrace.cross_defect_same_point_residual
  CarryCompletedTrace.endpointBalance
  CarryCompletedTrace.endpoint_balance_is_native_flux
  CarryCompletedTrace.endpoint_balance_opposite_negative
  CarryCompletedTrace.radial_pick_first_re_pos_eventually
  CarryCompletedTrace.cross_radial_residual_re_negative_eventually
