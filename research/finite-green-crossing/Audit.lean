import C2Compensation
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
  logInfo m!"Native finite Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryFiniteGreen.greenPort
#print axioms CarryFiniteGreen.greenPortProfile
#print axioms CarryFiniteGreen.green_port_toLp
#print axioms CarryFiniteGreen.green_port_profile_apply
#print axioms CarryFiniteGreen.green_port_inner
#print axioms CarryFiniteGreen.initialInput
#print axioms CarryFiniteGreen.initial_shift
#print axioms CarryFiniteGreen.initial_bulk
#print axioms CarryFiniteGreen.completed_residual_smul
#print axioms CarryFiniteGreen.residual_numerator_initial
#print axioms CarryFiniteGreen.native_advance_radial
#print axioms CarryFiniteGreen.normalized_positive_response
#print axioms CarryFiniteGreen.responseIncrement
#print axioms CarryFiniteGreen.residualScale
#print axioms CarryFiniteGreen.initial_regular
#print axioms CarryFiniteGreen.residual_initial_first
#print axioms CarryFiniteGreen.residual_initial_pair
#print axioms CarryFiniteGreen.pair_power_zero
#print axioms CarryFiniteGreen.reconstructed_residual_initial
#print axioms CarryFiniteGreen.chiralRadialScale
#print axioms CarryFiniteGreen.residual_scale_eq
#print axioms CarryFiniteGreen.chiral_scale_norm_product
#print axioms CarryFiniteGreen.chiral_scaled_inner
#print axioms CarryFiniteGreen.initial_source
#print axioms CarryFiniteGreen.initial_mean
#print axioms CarryFiniteGreen.initial_contrast
#print axioms CarryFiniteGreen.initial_source_energy
#print axioms CarryFiniteGreen.physical_form_equal_right
#print axioms CarryFiniteGreen.initial_green_split
#print axioms CarryFiniteGreen.initial_residual_self
#print axioms CarryFiniteGreen.initial_source_residual_pairing
#print axioms CarryFiniteGreen.initial_mixed_pairing
#print axioms CarryFiniteGreen.initial_mixed_real
#print axioms CarryFiniteGreen.initial_bulk_real
#print axioms CarryFiniteGreen.adjacent_points_difference
#print axioms CarryFiniteGreen.radial_point_scaled
#print axioms CarryFiniteGreen.scaled_increment_dslope
#print axioms CarryFiniteGreen.scaled_response_dslope
#print axioms CarryFiniteGreen.native_derivative_zero
#print axioms CarryFiniteGreen.scaled_increment_limit
#print axioms CarryFiniteGreen.scaled_response_limit
#print axioms CarryFiniteGreen.increment_ruler_limit
#print axioms CarryFiniteGreen.incident_ruler_limit
#print axioms CarryFiniteGreen.mixed_energy_limit
#print axioms CarryFiniteGreen.bulk_energy_limit
#print axioms CarryFiniteGreen.source_energy_limit
#print axioms CarryFiniteGreen.c2_weight_pos
#print axioms CarryFiniteGreen.c2_weight_lt_one
#print axioms CarryFiniteGreen.c2_mixed_limit_pos
#print axioms CarryFiniteGreen.c2_bulk_limit_neg
#print axioms CarryFiniteGreen.c2_eventually_mixed_positive
#print axioms CarryFiniteGreen.c2_eventually_bulk_negative
#print axioms CarryFiniteGreen.c2_eventually_compensates
#print axioms CarryFiniteGreen.c2_canonical_eventually_compensates

#audit_completed_pairing 0
  CarryFiniteGreen.greenPort
  CarryFiniteGreen.greenPortProfile
  CarryFiniteGreen.green_port_toLp
  CarryFiniteGreen.green_port_profile_apply
  CarryFiniteGreen.green_port_inner
  CarryFiniteGreen.initialInput
  CarryFiniteGreen.initial_shift
  CarryFiniteGreen.initial_bulk
  CarryFiniteGreen.completed_residual_smul
  CarryFiniteGreen.residual_numerator_initial
  CarryFiniteGreen.native_advance_radial
  CarryFiniteGreen.normalized_positive_response
  CarryFiniteGreen.responseIncrement
  CarryFiniteGreen.residualScale
  CarryFiniteGreen.initial_regular
  CarryFiniteGreen.residual_initial_first
  CarryFiniteGreen.residual_initial_pair
  CarryFiniteGreen.pair_power_zero
  CarryFiniteGreen.reconstructed_residual_initial
  CarryFiniteGreen.chiralRadialScale
  CarryFiniteGreen.residual_scale_eq
  CarryFiniteGreen.chiral_scale_norm_product
  CarryFiniteGreen.chiral_scaled_inner
  CarryFiniteGreen.initial_source
  CarryFiniteGreen.initial_mean
  CarryFiniteGreen.initial_contrast
  CarryFiniteGreen.initial_source_energy
  CarryFiniteGreen.physical_form_equal_right
  CarryFiniteGreen.initial_green_split
  CarryFiniteGreen.initial_residual_self
  CarryFiniteGreen.initial_source_residual_pairing
  CarryFiniteGreen.initial_mixed_pairing
  CarryFiniteGreen.initial_mixed_real
  CarryFiniteGreen.initial_bulk_real

#audit_completed_pairing 1
  CarryFiniteGreen.adjacent_points_difference
  CarryFiniteGreen.radial_point_scaled
  CarryFiniteGreen.scaled_increment_dslope
  CarryFiniteGreen.scaled_response_dslope
  CarryFiniteGreen.native_derivative_zero
  CarryFiniteGreen.scaled_increment_limit
  CarryFiniteGreen.scaled_response_limit
  CarryFiniteGreen.increment_ruler_limit
  CarryFiniteGreen.incident_ruler_limit
  CarryFiniteGreen.mixed_energy_limit
  CarryFiniteGreen.bulk_energy_limit
  CarryFiniteGreen.source_energy_limit

#audit_completed_pairing 2
  CarryFiniteGreen.c2_weight_pos
  CarryFiniteGreen.c2_weight_lt_one
  CarryFiniteGreen.c2_mixed_limit_pos
  CarryFiniteGreen.c2_bulk_limit_neg
  CarryFiniteGreen.c2_eventually_mixed_positive
  CarryFiniteGreen.c2_eventually_bulk_negative
  CarryFiniteGreen.c2_eventually_compensates
  CarryFiniteGreen.c2_canonical_eventually_compensates

#audit_completed_pairing 2
  CarryFiniteGreen.greenPort
  CarryFiniteGreen.greenPortProfile
  CarryFiniteGreen.green_port_toLp
  CarryFiniteGreen.green_port_profile_apply
  CarryFiniteGreen.green_port_inner
  CarryFiniteGreen.initialInput
  CarryFiniteGreen.initial_shift
  CarryFiniteGreen.initial_bulk
  CarryFiniteGreen.completed_residual_smul
  CarryFiniteGreen.residual_numerator_initial
  CarryFiniteGreen.native_advance_radial
  CarryFiniteGreen.normalized_positive_response
  CarryFiniteGreen.responseIncrement
  CarryFiniteGreen.residualScale
  CarryFiniteGreen.initial_regular
  CarryFiniteGreen.residual_initial_first
  CarryFiniteGreen.residual_initial_pair
  CarryFiniteGreen.pair_power_zero
  CarryFiniteGreen.reconstructed_residual_initial
  CarryFiniteGreen.chiralRadialScale
  CarryFiniteGreen.residual_scale_eq
  CarryFiniteGreen.chiral_scale_norm_product
  CarryFiniteGreen.chiral_scaled_inner
  CarryFiniteGreen.initial_source
  CarryFiniteGreen.initial_mean
  CarryFiniteGreen.initial_contrast
  CarryFiniteGreen.initial_source_energy
  CarryFiniteGreen.physical_form_equal_right
  CarryFiniteGreen.initial_green_split
  CarryFiniteGreen.initial_residual_self
  CarryFiniteGreen.initial_source_residual_pairing
  CarryFiniteGreen.initial_mixed_pairing
  CarryFiniteGreen.initial_mixed_real
  CarryFiniteGreen.initial_bulk_real
  CarryFiniteGreen.adjacent_points_difference
  CarryFiniteGreen.radial_point_scaled
  CarryFiniteGreen.scaled_increment_dslope
  CarryFiniteGreen.scaled_response_dslope
  CarryFiniteGreen.native_derivative_zero
  CarryFiniteGreen.scaled_increment_limit
  CarryFiniteGreen.scaled_response_limit
  CarryFiniteGreen.increment_ruler_limit
  CarryFiniteGreen.incident_ruler_limit
  CarryFiniteGreen.mixed_energy_limit
  CarryFiniteGreen.bulk_energy_limit
  CarryFiniteGreen.source_energy_limit
  CarryFiniteGreen.c2_weight_pos
  CarryFiniteGreen.c2_weight_lt_one
  CarryFiniteGreen.c2_mixed_limit_pos
  CarryFiniteGreen.c2_bulk_limit_neg
  CarryFiniteGreen.c2_eventually_mixed_positive
  CarryFiniteGreen.c2_eventually_bulk_negative
  CarryFiniteGreen.c2_eventually_compensates
  CarryFiniteGreen.c2_canonical_eventually_compensates
