import SchurTransport
import PrefixRegression
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
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
    `CarryCriticalMixed.source_nonlinear_margin_pos,
    `CarryCriticalMixed.source_correction_numerator_pos]
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
  logInfo m!"Polarized jet-four audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryPolarizedFour.jetInput
#print axioms CarryPolarizedFour.jet_input_source
#print axioms CarryPolarizedFour.evenPolynomialInput
#print axioms CarryPolarizedFour.even_polynomial_source
#print axioms CarryPolarizedFour.quarticInput
#print axioms CarryPolarizedFour.quartic_source_original
#print axioms CarryPolarizedFour.fourthScale
#print axioms CarryPolarizedFour.fourth_scale_real
#print axioms CarryPolarizedFour.fiveWeight
#print axioms CarryPolarizedFour.quartic_input_five
#print axioms CarryPolarizedFour.fiveRegular
#print axioms CarryPolarizedFour.five_regular_eventually
#print axioms CarryPolarizedFour.five_basis_residual
#print axioms CarryPolarizedFour.quarticBulk
#print axioms CarryPolarizedFour.quarticResidual
#print axioms CarryPolarizedFour.quartic_bulk_five
#print axioms CarryPolarizedFour.quartic_residual_five
#print axioms CarryPolarizedFour.quartic_vector_split
#print axioms CarryPolarizedFour.quartic_full_green
#print axioms CarryPolarizedFour.quartic_residual_cross_zero
#print axioms CarryPolarizedFour.quartic_mixed_twenty_five
#print axioms CarryPolarizedFour.crosses
#print axioms CarryPolarizedFour.sampleMass
#print axioms CarryPolarizedFour.quarticBalance
#print axioms CarryPolarizedFour.quartic_balance_source
#print axioms CarryPolarizedFour.quartic_balance_twenty_five
#print axioms CarryPolarizedFour.quartic_balance_five_samples
#print axioms CarryPolarizedFour.momentPairing
#print axioms CarryPolarizedFour.finiteTerm
#print axioms CarryPolarizedFour.correctionTerm
#print axioms CarryPolarizedFour.fourthTerm
#print axioms CarryPolarizedFour.higherPolynomial
#print axioms CarryPolarizedFour.normalizedMass
#print axioms CarryPolarizedFour.errorReadout
#print axioms CarryPolarizedFour.readout_fifteenth_remainder
#print axioms CarryPolarizedFour.quartic_exact_expansion
#print axioms CarryPolarizedFour.error_readout_continuousAt
#print axioms CarryPolarizedFour.quartic_finite_limit
#print axioms CarryPolarizedFour.quartic_correction_limit
#print axioms CarryPolarizedFour.quartic_fourth_limit
#print axioms CarryPolarizedFour.quartic_sixth_error_bound
#print axioms CarryPolarizedFour.moment_pairing_original_functional
#print axioms CarryPolarizedFour.moment_pairing_quadratic
#print axioms CarryPolarizedFour.inverseCoefficients
#print axioms CarryPolarizedFour.criticalPolynomial
#print axioms CarryPolarizedFour.critical_polynomial_snoc
#print axioms CarryPolarizedFour.critical_coefficients_solve
#print axioms CarryPolarizedFour.critical_moment_pairing
#print axioms CarryPolarizedFour.critical_old_pairing_zero
#print axioms CarryPolarizedFour.inverse_schur_source_original
#print axioms CarryPolarizedFour.critical_green_limit
#print axioms CarryPolarizedFour.critical_green_old_limit_zero
#print axioms CarryPolarizedFour.critical_green_correction_limit
#print axioms CarryPolarizedFour.quartic_prefix_input
#print axioms CarryPolarizedFour.quartic_prefix_balance
#print axioms CarryPolarizedFour.quartic_prefix_finite
#print axioms CarryPolarizedFour.quartic_prefix_correction
#print axioms CarryPolarizedFour.quartic_prefix_fourth
#print axioms NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit

#audit_completed_pairing 0
  CarryPolarizedFour.jetInput
  CarryPolarizedFour.jet_input_source
  CarryPolarizedFour.evenPolynomialInput
  CarryPolarizedFour.even_polynomial_source
  CarryPolarizedFour.quarticInput
  CarryPolarizedFour.quartic_source_original
  CarryPolarizedFour.fourthScale
  CarryPolarizedFour.fourth_scale_real
  CarryPolarizedFour.fiveWeight
  CarryPolarizedFour.quartic_input_five
  CarryPolarizedFour.fiveRegular
  CarryPolarizedFour.five_regular_eventually
  CarryPolarizedFour.five_basis_residual
  CarryPolarizedFour.quarticBulk
  CarryPolarizedFour.quarticResidual
  CarryPolarizedFour.quartic_bulk_five
  CarryPolarizedFour.quartic_residual_five
  CarryPolarizedFour.quartic_vector_split
  CarryPolarizedFour.quartic_full_green
  CarryPolarizedFour.quartic_residual_cross_zero
  CarryPolarizedFour.quartic_mixed_twenty_five
  CarryPolarizedFour.crosses
  CarryPolarizedFour.sampleMass
  CarryPolarizedFour.quarticBalance
  CarryPolarizedFour.quartic_balance_source
  CarryPolarizedFour.quartic_balance_twenty_five
  CarryPolarizedFour.quartic_balance_five_samples

#audit_completed_pairing 1
  CarryPolarizedFour.momentPairing
  CarryPolarizedFour.finiteTerm
  CarryPolarizedFour.correctionTerm
  CarryPolarizedFour.fourthTerm
  CarryPolarizedFour.higherPolynomial
  CarryPolarizedFour.normalizedMass
  CarryPolarizedFour.errorReadout
  CarryPolarizedFour.readout_fifteenth_remainder
  CarryPolarizedFour.quartic_exact_expansion
  CarryPolarizedFour.error_readout_continuousAt
  CarryPolarizedFour.quartic_finite_limit
  CarryPolarizedFour.quartic_correction_limit
  CarryPolarizedFour.quartic_fourth_limit
  CarryPolarizedFour.quartic_sixth_error_bound
  CarryPolarizedFour.moment_pairing_original_functional
  CarryPolarizedFour.moment_pairing_quadratic
  CarryPolarizedFour.inverseCoefficients
  CarryPolarizedFour.criticalPolynomial
  CarryPolarizedFour.critical_polynomial_snoc
  CarryPolarizedFour.critical_coefficients_solve
  CarryPolarizedFour.critical_moment_pairing
  CarryPolarizedFour.critical_old_pairing_zero
  CarryPolarizedFour.inverse_schur_source_original
  CarryPolarizedFour.critical_green_limit
  CarryPolarizedFour.critical_green_old_limit_zero
  CarryPolarizedFour.critical_green_correction_limit
  CarryPolarizedFour.quartic_prefix_input
  CarryPolarizedFour.quartic_prefix_balance
  CarryPolarizedFour.quartic_prefix_finite
  CarryPolarizedFour.quartic_prefix_correction
  CarryPolarizedFour.quartic_prefix_fourth

#audit_completed_pairing 1
  CarryPolarizedFour.jetInput
  CarryPolarizedFour.jet_input_source
  CarryPolarizedFour.evenPolynomialInput
  CarryPolarizedFour.even_polynomial_source
  CarryPolarizedFour.quarticInput
  CarryPolarizedFour.quartic_source_original
  CarryPolarizedFour.fourthScale
  CarryPolarizedFour.fourth_scale_real
  CarryPolarizedFour.fiveWeight
  CarryPolarizedFour.quartic_input_five
  CarryPolarizedFour.fiveRegular
  CarryPolarizedFour.five_regular_eventually
  CarryPolarizedFour.five_basis_residual
  CarryPolarizedFour.quarticBulk
  CarryPolarizedFour.quarticResidual
  CarryPolarizedFour.quartic_bulk_five
  CarryPolarizedFour.quartic_residual_five
  CarryPolarizedFour.quartic_vector_split
  CarryPolarizedFour.quartic_full_green
  CarryPolarizedFour.quartic_residual_cross_zero
  CarryPolarizedFour.quartic_mixed_twenty_five
  CarryPolarizedFour.crosses
  CarryPolarizedFour.sampleMass
  CarryPolarizedFour.quarticBalance
  CarryPolarizedFour.quartic_balance_source
  CarryPolarizedFour.quartic_balance_twenty_five
  CarryPolarizedFour.quartic_balance_five_samples
  CarryPolarizedFour.momentPairing
  CarryPolarizedFour.finiteTerm
  CarryPolarizedFour.correctionTerm
  CarryPolarizedFour.fourthTerm
  CarryPolarizedFour.higherPolynomial
  CarryPolarizedFour.normalizedMass
  CarryPolarizedFour.errorReadout
  CarryPolarizedFour.readout_fifteenth_remainder
  CarryPolarizedFour.quartic_exact_expansion
  CarryPolarizedFour.error_readout_continuousAt
  CarryPolarizedFour.quartic_finite_limit
  CarryPolarizedFour.quartic_correction_limit
  CarryPolarizedFour.quartic_fourth_limit
  CarryPolarizedFour.quartic_sixth_error_bound
  CarryPolarizedFour.moment_pairing_original_functional
  CarryPolarizedFour.moment_pairing_quadratic
  CarryPolarizedFour.inverseCoefficients
  CarryPolarizedFour.criticalPolynomial
  CarryPolarizedFour.critical_polynomial_snoc
  CarryPolarizedFour.critical_coefficients_solve
  CarryPolarizedFour.critical_moment_pairing
  CarryPolarizedFour.critical_old_pairing_zero
  CarryPolarizedFour.inverse_schur_source_original
  CarryPolarizedFour.critical_green_limit
  CarryPolarizedFour.critical_green_old_limit_zero
  CarryPolarizedFour.critical_green_correction_limit
  CarryPolarizedFour.quartic_prefix_input
  CarryPolarizedFour.quartic_prefix_balance
  CarryPolarizedFour.quartic_prefix_finite
  CarryPolarizedFour.quartic_prefix_correction
  CarryPolarizedFour.quartic_prefix_fourth
