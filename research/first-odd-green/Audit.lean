import OddSigns
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
  logInfo m!"First odd Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryFirstOddGreen.basisInput
#print axioms CarryFirstOddGreen.increment
#print axioms CarryFirstOddGreen.basis_shift
#print axioms CarryFirstOddGreen.source_basis
#print axioms CarryFirstOddGreen.residual_add
#print axioms CarryFirstOddGreen.successor_bulk
#print axioms CarryFirstOddGreen.successor_residual_numerator
#print axioms CarryFirstOddGreen.basis_regular
#print axioms CarryFirstOddGreen.residual_basis_pair
#print axioms CarryFirstOddGreen.successorPort
#print axioms CarryFirstOddGreen.reconstructed_successor
#print axioms CarryFirstOddGreen.basis_contrast
#print axioms CarryFirstOddGreen.nodeRegular
#print axioms CarryFirstOddGreen.basisPort
#print axioms CarryFirstOddGreen.residual_two_ports
#print axioms CarryFirstOddGreen.residual_ordered_zero
#print axioms CarryFirstOddGreen.form_add_left
#print axioms CarryFirstOddGreen.form_sub_sub
#print axioms CarryFirstOddGreen.ordered_mixed_pairing
#print axioms CarryFirstOddGreen.oddInput
#print axioms CarryFirstOddGreen.oddBulk
#print axioms CarryFirstOddGreen.oddResidual
#print axioms CarryFirstOddGreen.bulk_smul_sub
#print axioms CarryFirstOddGreen.residual_smul_sub
#print axioms CarryFirstOddGreen.numerator_smul_sub
#print axioms CarryFirstOddGreen.odd_residual_original
#print axioms CarryFirstOddGreen.odd_source_original
#print axioms CarryFirstOddGreen.first_odd_jet_difference
#print axioms CarryFirstOddGreen.odd_vector_split
#print axioms CarryFirstOddGreen.odd_bulk_original
#print axioms CarryFirstOddGreen.odd_residual_pair
#print axioms CarryFirstOddGreen.odd_residual_self_zero
#print axioms CarryFirstOddGreen.inverse_step_product
#print axioms CarryFirstOddGreen.odd_mixed_four_crossings
#print axioms CarryFirstOddGreen.portOverlap
#print axioms CarryFirstOddGreen.odd_mixed_exact
#print axioms CarryFirstOddGreen.odd_energy_three_sectors
#print axioms CarryFirstOddGreen.successorProfile
#print axioms CarryFirstOddGreen.successor_port_toLp
#print axioms CarryFirstOddGreen.successor_profile_apply
#print axioms CarryFirstOddGreen.oddDensity
#print axioms CarryFirstOddGreen.oddCoefficient
#print axioms CarryFirstOddGreen.odd_port_overlap
#print axioms CarryFirstOddGreen.overlap_difference
#print axioms CarryFirstOddGreen.odd_density_continuousOn
#print axioms CarryFirstOddGreen.odd_density_lower
#print axioms CarryFirstOddGreen.odd_coefficient_lower
#print axioms CarryFirstOddGreen.odd_coefficient_pos
#print axioms CarryFirstOddGreen.node_regular_eventually
#print axioms CarryFirstOddGreen.adjacent_increment_step
#print axioms CarryFirstOddGreen.scaled_increment_basis
#print axioms CarryFirstOddGreen.increment_basis_limit
#print axioms CarryFirstOddGreen.odd_mixed_scaled_exact
#print axioms CarryFirstOddGreen.odd_mixed_scaled_complex_limit
#print axioms CarryFirstOddGreen.complex_real_div
#print axioms CarryFirstOddGreen.odd_mixed_scaled_limit
#print axioms CarryFirstOddGreen.form_same_power
#print axioms CarryFirstOddGreen.odd_source_complex_limit
#print axioms CarryFirstOddGreen.odd_source_limit
#print axioms CarryFirstOddGreen.inverse_radial_mass_limit
#print axioms CarryFirstOddGreen.odd_source_scaled_limit
#print axioms CarryFirstOddGreen.odd_bulk_scaled_limit
#print axioms CarryFirstOddGreen.odd_eventual_mixed_positive
#print axioms CarryFirstOddGreen.odd_eventual_bulk_negative
#print axioms CarryFirstOddGreen.odd_mixed_no_finite_limit
#print axioms CarryFirstOddGreen.odd_bulk_no_finite_limit
#print axioms CarryFirstOddGreen.odd_eventual_compensation
#print axioms CarryFirstOddGreen.canonical_odd_channel_signs

#audit_completed_pairing 0
  CarryFirstOddGreen.basisInput
  CarryFirstOddGreen.increment
  CarryFirstOddGreen.basis_shift
  CarryFirstOddGreen.source_basis
  CarryFirstOddGreen.residual_add
  CarryFirstOddGreen.successor_bulk
  CarryFirstOddGreen.successor_residual_numerator
  CarryFirstOddGreen.basis_regular
  CarryFirstOddGreen.residual_basis_pair
  CarryFirstOddGreen.successorPort
  CarryFirstOddGreen.reconstructed_successor
  CarryFirstOddGreen.basis_contrast
  CarryFirstOddGreen.nodeRegular
  CarryFirstOddGreen.basisPort
  CarryFirstOddGreen.residual_two_ports
  CarryFirstOddGreen.residual_ordered_zero
  CarryFirstOddGreen.form_add_left
  CarryFirstOddGreen.form_sub_sub
  CarryFirstOddGreen.ordered_mixed_pairing
  CarryFirstOddGreen.oddInput
  CarryFirstOddGreen.oddBulk
  CarryFirstOddGreen.oddResidual
  CarryFirstOddGreen.bulk_smul_sub
  CarryFirstOddGreen.residual_smul_sub
  CarryFirstOddGreen.numerator_smul_sub
  CarryFirstOddGreen.odd_residual_original
  CarryFirstOddGreen.odd_source_original
  CarryFirstOddGreen.first_odd_jet_difference
  CarryFirstOddGreen.odd_vector_split
  CarryFirstOddGreen.odd_bulk_original
  CarryFirstOddGreen.odd_residual_pair
  CarryFirstOddGreen.odd_residual_self_zero
  CarryFirstOddGreen.inverse_step_product
  CarryFirstOddGreen.odd_mixed_four_crossings
  CarryFirstOddGreen.portOverlap
  CarryFirstOddGreen.odd_mixed_exact
  CarryFirstOddGreen.odd_energy_three_sectors
  CarryFirstOddGreen.successorProfile
  CarryFirstOddGreen.successor_port_toLp
  CarryFirstOddGreen.successor_profile_apply
  CarryFirstOddGreen.oddDensity
  CarryFirstOddGreen.oddCoefficient
  CarryFirstOddGreen.odd_port_overlap
  CarryFirstOddGreen.overlap_difference
  CarryFirstOddGreen.odd_density_continuousOn
  CarryFirstOddGreen.odd_density_lower
  CarryFirstOddGreen.odd_coefficient_lower
  CarryFirstOddGreen.odd_coefficient_pos

#audit_completed_pairing 1
  CarryFirstOddGreen.node_regular_eventually
  CarryFirstOddGreen.adjacent_increment_step
  CarryFirstOddGreen.scaled_increment_basis
  CarryFirstOddGreen.increment_basis_limit
  CarryFirstOddGreen.odd_mixed_scaled_exact
  CarryFirstOddGreen.odd_mixed_scaled_complex_limit
  CarryFirstOddGreen.complex_real_div
  CarryFirstOddGreen.odd_mixed_scaled_limit
  CarryFirstOddGreen.form_same_power
  CarryFirstOddGreen.odd_source_complex_limit
  CarryFirstOddGreen.odd_source_limit
  CarryFirstOddGreen.inverse_radial_mass_limit
  CarryFirstOddGreen.odd_source_scaled_limit
  CarryFirstOddGreen.odd_bulk_scaled_limit

#audit_completed_pairing 2
  CarryFirstOddGreen.odd_eventual_mixed_positive
  CarryFirstOddGreen.odd_eventual_bulk_negative
  CarryFirstOddGreen.odd_mixed_no_finite_limit
  CarryFirstOddGreen.odd_bulk_no_finite_limit
  CarryFirstOddGreen.odd_eventual_compensation
  CarryFirstOddGreen.canonical_odd_channel_signs

#audit_completed_pairing 2
  CarryFirstOddGreen.basisInput
  CarryFirstOddGreen.increment
  CarryFirstOddGreen.basis_shift
  CarryFirstOddGreen.source_basis
  CarryFirstOddGreen.residual_add
  CarryFirstOddGreen.successor_bulk
  CarryFirstOddGreen.successor_residual_numerator
  CarryFirstOddGreen.basis_regular
  CarryFirstOddGreen.residual_basis_pair
  CarryFirstOddGreen.successorPort
  CarryFirstOddGreen.reconstructed_successor
  CarryFirstOddGreen.basis_contrast
  CarryFirstOddGreen.nodeRegular
  CarryFirstOddGreen.basisPort
  CarryFirstOddGreen.residual_two_ports
  CarryFirstOddGreen.residual_ordered_zero
  CarryFirstOddGreen.form_add_left
  CarryFirstOddGreen.form_sub_sub
  CarryFirstOddGreen.ordered_mixed_pairing
  CarryFirstOddGreen.oddInput
  CarryFirstOddGreen.oddBulk
  CarryFirstOddGreen.oddResidual
  CarryFirstOddGreen.bulk_smul_sub
  CarryFirstOddGreen.residual_smul_sub
  CarryFirstOddGreen.numerator_smul_sub
  CarryFirstOddGreen.odd_residual_original
  CarryFirstOddGreen.odd_source_original
  CarryFirstOddGreen.first_odd_jet_difference
  CarryFirstOddGreen.odd_vector_split
  CarryFirstOddGreen.odd_bulk_original
  CarryFirstOddGreen.odd_residual_pair
  CarryFirstOddGreen.odd_residual_self_zero
  CarryFirstOddGreen.inverse_step_product
  CarryFirstOddGreen.odd_mixed_four_crossings
  CarryFirstOddGreen.portOverlap
  CarryFirstOddGreen.odd_mixed_exact
  CarryFirstOddGreen.odd_energy_three_sectors
  CarryFirstOddGreen.successorProfile
  CarryFirstOddGreen.successor_port_toLp
  CarryFirstOddGreen.successor_profile_apply
  CarryFirstOddGreen.oddDensity
  CarryFirstOddGreen.oddCoefficient
  CarryFirstOddGreen.odd_port_overlap
  CarryFirstOddGreen.overlap_difference
  CarryFirstOddGreen.odd_density_continuousOn
  CarryFirstOddGreen.odd_density_lower
  CarryFirstOddGreen.odd_coefficient_lower
  CarryFirstOddGreen.odd_coefficient_pos
  CarryFirstOddGreen.node_regular_eventually
  CarryFirstOddGreen.adjacent_increment_step
  CarryFirstOddGreen.scaled_increment_basis
  CarryFirstOddGreen.increment_basis_limit
  CarryFirstOddGreen.odd_mixed_scaled_exact
  CarryFirstOddGreen.odd_mixed_scaled_complex_limit
  CarryFirstOddGreen.complex_real_div
  CarryFirstOddGreen.odd_mixed_scaled_limit
  CarryFirstOddGreen.form_same_power
  CarryFirstOddGreen.odd_source_complex_limit
  CarryFirstOddGreen.odd_source_limit
  CarryFirstOddGreen.inverse_radial_mass_limit
  CarryFirstOddGreen.odd_source_scaled_limit
  CarryFirstOddGreen.odd_bulk_scaled_limit
  CarryFirstOddGreen.odd_eventual_mixed_positive
  CarryFirstOddGreen.odd_eventual_bulk_negative
  CarryFirstOddGreen.odd_mixed_no_finite_limit
  CarryFirstOddGreen.odd_bulk_no_finite_limit
  CarryFirstOddGreen.odd_eventual_compensation
  CarryFirstOddGreen.canonical_odd_channel_signs
