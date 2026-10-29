import OddRegressions
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
  logInfo m!"Odd native Green compensation {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryOddGreen.greenColumn
#print axioms CarryOddGreen.traceColumn
#print axioms CarryOddGreen.odd_profile_radial_jet
#print axioms CarryOddGreen.odd_bulk_coefficients
#print axioms CarryOddGreen.odd_weighted_coefficients
#print axioms CarryOddGreen.odd_commutator_coefficients
#print axioms CarryOddGreen.odd_bulk_vector
#print axioms CarryOddGreen.odd_boundary_vector
#print axioms CarryOddGreen.odd_residual_vector
#print axioms CarryOddGreen.odd_bulk_residual_cancellation
#print axioms CarryOddGreen.odd_complete_vector_reconstruction
#print axioms CarryOddGreen.odd_three_vector_identity
#print axioms CarryOddGreen.odd_physical_jet_calibration
#print axioms CarryOddGreen.kernel_imaginary_imaginary
#print axioms CarryOddGreen.oddPairing
#print axioms CarryOddGreen.odd_ordered_kernel_sum
#print axioms CarryOddGreen.odd_pairing_exact
#print axioms CarryOddGreen.normalized_odd_pair_tendsto
#print axioms CarryOddGreen.oddBilinear
#print axioms CarryOddGreen.odd_pairing_tendsto
#print axioms CarryOddGreen.odd_green_pairing_tendsto
#print axioms CarryOddGreen.odd_linear_residual
#print axioms CarryOddGreen.odd_cubic_residual
#print axioms CarryOddGreen.shifted_hankel_eq_source
#print axioms CarryOddGreen.odd_matrix_entry_tendsto
#print axioms CarryOddGreen.odd_matrix_green_entry_tendsto
#print axioms CarryOddGreen.odd_matrix_entry_real_tendsto
#print axioms CarryOddGreen.odd_bilinear_eq_matrix
#print axioms CarryOddGreen.odd_matrix_bilinear_tendsto
#print axioms CarryOddGreen.odd_matrix_green_bilinear_tendsto
#print axioms CarryOddGreen.odd_bilinear_diagonal_eq

#audit_odd_green construction
  CarryOddGreen.greenColumn
  CarryOddGreen.traceColumn
  CarryOddGreen.odd_profile_radial_jet
  CarryOddGreen.odd_bulk_coefficients
  CarryOddGreen.odd_weighted_coefficients
  CarryOddGreen.odd_commutator_coefficients
  CarryOddGreen.odd_bulk_vector
  CarryOddGreen.odd_boundary_vector
  CarryOddGreen.odd_residual_vector
  CarryOddGreen.odd_bulk_residual_cancellation
  CarryOddGreen.odd_complete_vector_reconstruction
  CarryOddGreen.odd_three_vector_identity
  CarryOddGreen.odd_physical_jet_calibration
  CarryOddGreen.kernel_imaginary_imaginary
  CarryOddGreen.oddPairing
  CarryOddGreen.odd_ordered_kernel_sum
  CarryOddGreen.odd_pairing_exact
  CarryOddGreen.odd_linear_residual
  CarryOddGreen.odd_cubic_residual


#audit_odd_green provenance
  CarryOddGreen.normalized_odd_pair_tendsto
  CarryOddGreen.oddBilinear
  CarryOddGreen.odd_pairing_tendsto
  CarryOddGreen.odd_green_pairing_tendsto
  CarryOddGreen.shifted_hankel_eq_source
  CarryOddGreen.odd_matrix_entry_tendsto
  CarryOddGreen.odd_matrix_green_entry_tendsto
  CarryOddGreen.odd_matrix_entry_real_tendsto
  CarryOddGreen.odd_bilinear_eq_matrix
  CarryOddGreen.odd_matrix_bilinear_tendsto
  CarryOddGreen.odd_matrix_green_bilinear_tendsto
  CarryOddGreen.odd_bilinear_diagonal_eq
