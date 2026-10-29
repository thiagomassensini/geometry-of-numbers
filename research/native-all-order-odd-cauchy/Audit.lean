import AllOrderGreenFilters
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryCubicOdd.critical_cauchy_row,
    `CarryCubicOdd.critical_kernel_readout,
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
  logInfo m!"All-order original odd Cauchy filter {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryOddCauchy.complementRow
#print axioms CarryOddCauchy.complement_vector_succ
#print axioms CarryOddCauchy.complement_row_succ
#print axioms CarryOddCauchy.complement_row_zero
#print axioms CarryOddCauchy.factorial_row_zero
#print axioms CarryOddCauchy.factorial_row_difference
#print axioms CarryOddCauchy.complement_row_factorial
#print axioms CarryOddCauchy.nativeOddBeta
#print axioms CarryOddCauchy.odd_exponent_sign
#print axioms CarryOddCauchy.odd_stencil_sign
#print axioms CarryOddCauchy.native_odd_coefficient
#print axioms CarryOddCauchy.native_odd_vector
#print axioms CarryOddCauchy.native_odd_cauchy_row
#print axioms CarryOddCauchy.native_odd_atoms
#print axioms CarryOddCauchy.native_odd_cauchy_reverse
#print axioms CarryOddCauchy.oddFilterMagnitude
#print axioms CarryOddCauchy.oddFilterCoefficient
#print axioms CarryOddCauchy.oddFilter
#print axioms CarryOddCauchy.weighted_native_odd_vector
#print axioms CarryOddCauchy.native_odd_kernel_filter
#print axioms CarryOddCauchy.odd_filter_coefficient_factorization
#print axioms CarryOddCauchy.odd_filter_magnitude_pos
#print axioms CarryOddCauchy.odd_filter_even_pos
#print axioms CarryOddCauchy.odd_filter_odd_neg
#print axioms CarryOddCauchy.odd_filter_outside_support
#print axioms CarryOddCauchy.native_odd_kernel_forward_difference
#print axioms CarryOddCauchy.native_odd_ordered_filters
#print axioms CarryOddCauchy.completed_odd_part_calibration
#print axioms CarryOddCauchy.completed_odd_source_calibration
#print axioms CarryOddCauchy.native_odd_nine_field_reconstruction
#print axioms CarryOddCauchy.native_odd_nine_fields_filter
#print axioms CarryOddCauchy.normalized_odd_filter_exact
#print axioms CarryOddCauchy.radial_odd_signed_filter_exact
#print axioms CarryOddCauchy.completed_odd_green_filter_exact
#print axioms CarryOddCauchy.finite_odd_signed_filters_exact
#print axioms CarryOddCauchy.finite_odd_green_filters_exact
#print axioms CarryOddCauchy.completed_odd_filter_tendsto
#print axioms CarryOddCauchy.completed_odd_green_filter_tendsto
#print axioms CarryOddCauchy.native_odd_row_regressions
#print axioms CarryOddCauchy.odd_filter_regressions

#audit_odd_green construction
  CarryOddCauchy.complementRow
  CarryOddCauchy.complement_vector_succ
  CarryOddCauchy.complement_row_succ
  CarryOddCauchy.complement_row_zero
  CarryOddCauchy.factorial_row_zero
  CarryOddCauchy.factorial_row_difference
  CarryOddCauchy.complement_row_factorial
  CarryOddCauchy.nativeOddBeta
  CarryOddCauchy.odd_exponent_sign
  CarryOddCauchy.odd_stencil_sign
  CarryOddCauchy.native_odd_coefficient
  CarryOddCauchy.native_odd_vector
  CarryOddCauchy.native_odd_cauchy_row
  CarryOddCauchy.native_odd_atoms
  CarryOddCauchy.native_odd_cauchy_reverse
  CarryOddCauchy.oddFilterMagnitude
  CarryOddCauchy.oddFilterCoefficient
  CarryOddCauchy.oddFilter
  CarryOddCauchy.weighted_native_odd_vector
  CarryOddCauchy.native_odd_kernel_filter
  CarryOddCauchy.odd_filter_coefficient_factorization
  CarryOddCauchy.odd_filter_magnitude_pos
  CarryOddCauchy.odd_filter_even_pos
  CarryOddCauchy.odd_filter_odd_neg
  CarryOddCauchy.odd_filter_outside_support
  CarryOddCauchy.native_odd_kernel_forward_difference
  CarryOddCauchy.native_odd_ordered_filters
  CarryOddCauchy.completed_odd_part_calibration
  CarryOddCauchy.completed_odd_source_calibration
  CarryOddCauchy.native_odd_nine_field_reconstruction
  CarryOddCauchy.native_odd_nine_fields_filter
  CarryOddCauchy.normalized_odd_filter_exact
  CarryOddCauchy.radial_odd_signed_filter_exact
  CarryOddCauchy.completed_odd_green_filter_exact
  CarryOddCauchy.finite_odd_signed_filters_exact
  CarryOddCauchy.finite_odd_green_filters_exact
  CarryOddCauchy.native_odd_row_regressions
  CarryOddCauchy.odd_filter_regressions


#audit_odd_green provenance
  CarryOddCauchy.completed_odd_filter_tendsto
  CarryOddCauchy.completed_odd_green_filter_tendsto
