import NativeGaps
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
  logInfo m!"Full source norm audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryFullSource.FullCarrier
#print axioms CarryFullSource.originalNormalizedState
#print axioms CarryFullSource.sourceNormalization
#print axioms CarryFullSource.original_state_eq_scaled
#print axioms CarryFullSource.original_state_zero
#print axioms CarryFullSource.three_value_coordinates
#print axioms CarryFullSource.forced_value_norm_sq
#print axioms CarryFullSource.full_state_mass_exact
#print axioms CarryFullSource.full_state_mass_lower
#print axioms CarryFullSource.center_mass_lower
#print axioms CarryFullSource.value_preserving_mass_lower
#print axioms CarryFullSource.source_normalization_cancels_collision
#print axioms CarryFullSource.normalizedNormal
#print axioms CarryFullSource.normalizedPhysicalTangent
#print axioms CarryFullSource.normalized_normal_eq_scaled
#print axioms CarryFullSource.normalized_normal_norm
#print axioms CarryFullSource.normalized_normal_mass_lower
#print axioms CarryFullSource.normalized_normal_ne_zero
#print axioms CarryFullSource.normalized_normal_tangent_pair
#print axioms CarryFullSource.normalComponent
#print axioms CarryFullSource.normalComponentEnergy
#print axioms CarryFullSource.normal_component_orthogonal_remainder
#print axioms CarryFullSource.normal_center_inner_zero
#print axioms CarryFullSource.normal_component_invariant_along_center
#print axioms CarryFullSource.normal_component_mem_normal_line
#print axioms CarryFullSource.normal_component_energy_exact
#print axioms CarryFullSource.normal_component_energy_upper
#print axioms CarryFullSource.full_state_native_mass_gap
#print axioms CarryFullSource.normal_component_strict_small
#print axioms CarryFullSource.normal_component_not_native_mass
#print axioms CarryFullSource.isometric_transport_not_native_mass
#print axioms CarryFullSource.value_preserving_operation_native_gap
#print axioms CarryFullSource.orthogonal_extension_not_native_mass
#print axioms CarryFullSource.native_mass_value_readout_gain

#audit_completed_pairing 0
  CarryFullSource.FullCarrier
  CarryFullSource.originalNormalizedState
  CarryFullSource.sourceNormalization
  CarryFullSource.original_state_eq_scaled
  CarryFullSource.original_state_zero
  CarryFullSource.three_value_coordinates
  CarryFullSource.forced_value_norm_sq
  CarryFullSource.full_state_mass_exact
  CarryFullSource.full_state_mass_lower
  CarryFullSource.center_mass_lower
  CarryFullSource.value_preserving_mass_lower
  CarryFullSource.source_normalization_cancels_collision
  CarryFullSource.normalizedNormal
  CarryFullSource.normalizedPhysicalTangent
  CarryFullSource.normalized_normal_eq_scaled
  CarryFullSource.normalized_normal_norm
  CarryFullSource.normalized_normal_mass_lower
  CarryFullSource.normalized_normal_ne_zero
  CarryFullSource.normalComponent
  CarryFullSource.normalComponentEnergy
  CarryFullSource.normal_component_orthogonal_remainder
  CarryFullSource.normal_center_inner_zero
  CarryFullSource.normal_component_invariant_along_center
  CarryFullSource.normal_component_mem_normal_line

#audit_completed_pairing 1
  CarryFullSource.normalized_normal_tangent_pair
  CarryFullSource.normal_component_energy_exact
  CarryFullSource.normal_component_energy_upper

#audit_completed_pairing 2
  CarryFullSource.full_state_native_mass_gap
  CarryFullSource.normal_component_strict_small
  CarryFullSource.normal_component_not_native_mass
  CarryFullSource.isometric_transport_not_native_mass
  CarryFullSource.value_preserving_operation_native_gap
  CarryFullSource.orthogonal_extension_not_native_mass
  CarryFullSource.native_mass_value_readout_gain

#audit_completed_pairing 3
  CarryFullSource.FullCarrier
  CarryFullSource.originalNormalizedState
  CarryFullSource.sourceNormalization
  CarryFullSource.original_state_eq_scaled
  CarryFullSource.original_state_zero
  CarryFullSource.three_value_coordinates
  CarryFullSource.forced_value_norm_sq
  CarryFullSource.full_state_mass_exact
  CarryFullSource.full_state_mass_lower
  CarryFullSource.center_mass_lower
  CarryFullSource.value_preserving_mass_lower
  CarryFullSource.source_normalization_cancels_collision
  CarryFullSource.normalizedNormal
  CarryFullSource.normalizedPhysicalTangent
  CarryFullSource.normalized_normal_eq_scaled
  CarryFullSource.normalized_normal_norm
  CarryFullSource.normalized_normal_mass_lower
  CarryFullSource.normalized_normal_ne_zero
  CarryFullSource.normalized_normal_tangent_pair
  CarryFullSource.normalComponent
  CarryFullSource.normalComponentEnergy
  CarryFullSource.normal_component_orthogonal_remainder
  CarryFullSource.normal_center_inner_zero
  CarryFullSource.normal_component_invariant_along_center
  CarryFullSource.normal_component_mem_normal_line
  CarryFullSource.normal_component_energy_exact
  CarryFullSource.normal_component_energy_upper
  CarryFullSource.full_state_native_mass_gap
  CarryFullSource.normal_component_strict_small
  CarryFullSource.normal_component_not_native_mass
  CarryFullSource.isometric_transport_not_native_mass
  CarryFullSource.value_preserving_operation_native_gap
  CarryFullSource.orthogonal_extension_not_native_mass
  CarryFullSource.native_mass_value_readout_gain
