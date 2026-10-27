import CriticalOddDefect
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
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
  logInfo m!"Cubic odd physical Green defect {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryCubicOdd.odd_weighted_input
#print axioms CarryCubicOdd.odd_weight_commutator
#print axioms CarryCubicOdd.odd_weight_bulk
#print axioms CarryCubicOdd.odd_weight_boundary
#print axioms CarryCubicOdd.odd_weight_residual
#print axioms CarryCubicOdd.odd_weight_complete
#print axioms CarryCubicOdd.odd_weight_two_defects
#print axioms CarryCubicOdd.cubic_odd_profile
#print axioms CarryCubicOdd.cubic_bulk_coefficients
#print axioms CarryCubicOdd.cubic_weighted_input
#print axioms CarryCubicOdd.cubic_commutator_coefficients
#print axioms CarryCubicOdd.cubic_bulk_vector
#print axioms CarryCubicOdd.cubic_boundary_vector
#print axioms CarryCubicOdd.cubic_residual_vector
#print axioms CarryCubicOdd.cubic_bulk_residual_cancellation
#print axioms CarryCubicOdd.cubic_complete_vector
#print axioms CarryCubicOdd.part_field_add_input
#print axioms CarryCubicOdd.completed_part_add_input
#print axioms CarryCubicOdd.criticalOddSource
#print axioms CarryCubicOdd.trialCoeff
#print axioms CarryCubicOdd.critical_source_as_finite
#print axioms CarryCubicOdd.critical_source_profiles
#print axioms CarryCubicOdd.critical_field_vectors
#print axioms CarryCubicOdd.critical_completed_parts
#print axioms CarryCubicOdd.critical_bilinear
#print axioms CarryCubicOdd.critical_green_tendsto
#print axioms CarryCubicOdd.critical_signed_tendsto
#print axioms CarryCubicOdd.critical_old_cross_tendsto
#print axioms CarryCubicOdd.critical_old_cross_zero
#print axioms CarryCubicOdd.critical_schur_tendsto
#print axioms CarryCubicOdd.criticalBeta
#print axioms CarryCubicOdd.critical_source_atoms
#print axioms CarryCubicOdd.kernel_four_atoms
#print axioms CarryCubicOdd.criticalSampleReadout
#print axioms CarryCubicOdd.critical_kernel_readout
#print axioms CarryCubicOdd.critical_signed_readout_exact
#print axioms CarryCubicOdd.critical_green_readout_exact
#print axioms CarryCubicOdd.cubic_halo_fields
#print axioms CarryCubicOdd.critical_cauchy_row
#print axioms CarryCubicOdd.criticalRho
#print axioms CarryCubicOdd.critical_readout_four_samples
#print axioms CarryCubicOdd.critical_rho_alternating
#print axioms CarryCubicOdd.critical_diagonal_four_samples_exact
#print axioms CarryCubicOdd.positive_address_weight_negative
#print axioms CarryCubicOdd.positive_address_weight_positive
#print axioms CarryCubicOdd.no_sign_from_nonnegative_address_weights

#audit_odd_green construction
  CarryCubicOdd.odd_weighted_input
  CarryCubicOdd.odd_weight_commutator
  CarryCubicOdd.odd_weight_bulk
  CarryCubicOdd.odd_weight_boundary
  CarryCubicOdd.odd_weight_residual
  CarryCubicOdd.odd_weight_complete
  CarryCubicOdd.odd_weight_two_defects
  CarryCubicOdd.cubic_odd_profile
  CarryCubicOdd.cubic_bulk_coefficients
  CarryCubicOdd.cubic_weighted_input
  CarryCubicOdd.cubic_commutator_coefficients
  CarryCubicOdd.cubic_bulk_vector
  CarryCubicOdd.cubic_boundary_vector
  CarryCubicOdd.cubic_residual_vector
  CarryCubicOdd.cubic_bulk_residual_cancellation
  CarryCubicOdd.cubic_complete_vector
  CarryCubicOdd.part_field_add_input
  CarryCubicOdd.completed_part_add_input
  CarryCubicOdd.criticalOddSource
  CarryCubicOdd.trialCoeff
  CarryCubicOdd.critical_source_as_finite
  CarryCubicOdd.critical_source_profiles
  CarryCubicOdd.critical_field_vectors
  CarryCubicOdd.critical_completed_parts
  CarryCubicOdd.criticalBeta
  CarryCubicOdd.critical_source_atoms
  CarryCubicOdd.kernel_four_atoms
  CarryCubicOdd.criticalSampleReadout
  CarryCubicOdd.critical_kernel_readout
  CarryCubicOdd.critical_signed_readout_exact
  CarryCubicOdd.critical_green_readout_exact
  CarryCubicOdd.cubic_halo_fields
  CarryCubicOdd.critical_cauchy_row
  CarryCubicOdd.criticalRho
  CarryCubicOdd.critical_readout_four_samples
  CarryCubicOdd.critical_rho_alternating
  CarryCubicOdd.critical_diagonal_four_samples_exact
  CarryCubicOdd.positive_address_weight_negative
  CarryCubicOdd.positive_address_weight_positive
  CarryCubicOdd.no_sign_from_nonnegative_address_weights


#audit_odd_green provenance
  CarryCubicOdd.critical_bilinear
  CarryCubicOdd.critical_green_tendsto
  CarryCubicOdd.critical_signed_tendsto
  CarryCubicOdd.critical_old_cross_tendsto
  CarryCubicOdd.critical_old_cross_zero
  CarryCubicOdd.critical_schur_tendsto
