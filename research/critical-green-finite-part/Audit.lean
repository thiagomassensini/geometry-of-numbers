import CertifiedDirection
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
  logInfo m!"Green finite-part audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryGreenFinitePart.imaginaryReadout
#print axioms CarryGreenFinitePart.readoutCoefficient
#print axioms CarryGreenFinitePart.readout_analytic
#print axioms CarryGreenFinitePart.readout_coefficient_derivative
#print axioms CarryGreenFinitePart.readout_coefficient_even
#print axioms CarryGreenFinitePart.readout_coefficient_odd
#print axioms CarryGreenFinitePart.readout_exact_remainder
#print axioms CarryGreenFinitePart.readout_real
#print axioms CarryGreenFinitePart.radialStep
#print axioms CarryGreenFinitePart.radial_step_limit
#print axioms CarryGreenFinitePart.radial_node_readout
#print axioms CarryGreenFinitePart.greenBalance
#print axioms CarryGreenFinitePart.green_balance_source
#print axioms CarryGreenFinitePart.basis_mean
#print axioms CarryGreenFinitePart.source_basis_real
#print axioms CarryGreenFinitePart.second_scale_real
#print axioms CarryGreenFinitePart.realWeight
#print axioms CarryGreenFinitePart.critical_weight_real
#print axioms CarryGreenFinitePart.real_weighted_form
#print axioms CarryGreenFinitePart.source_energy_three_samples
#print axioms CarryGreenFinitePart.green_balance_three_samples
#print axioms CarryGreenFinitePart.finiteTerm
#print axioms CarryGreenFinitePart.correctionTerm
#print axioms CarryGreenFinitePart.fourthPolynomial
#print axioms CarryGreenFinitePart.remainderReadout
#print axioms CarryGreenFinitePart.errorReadout
#print axioms CarryGreenFinitePart.green_balance_exact_expansion
#print axioms CarryGreenFinitePart.criticalParameter
#print axioms CarryGreenFinitePart.finite_term_critical
#print axioms CarryGreenFinitePart.critical_correction_formula
#print axioms CarryGreenFinitePart.error_readout_continuousAt
#print axioms CarryGreenFinitePart.radial_mass_step
#print axioms CarryGreenFinitePart.green_finite_term_limit
#print axioms CarryGreenFinitePart.green_correction_limit
#print axioms CarryGreenFinitePart.green_fourth_correction_limit
#print axioms CarryGreenFinitePart.green_sixth_order_error_bound
#print axioms CarryGreenFinitePart.critical_correction_negative
#print axioms CarryGreenFinitePart.critical_finite_term_positive
#print axioms CarryGreenFinitePart.critical_green_scaled_correction
#print axioms CarryGreenFinitePart.critical_green_eventually_between

#audit_completed_pairing 0
  CarryGreenFinitePart.greenBalance
  CarryGreenFinitePart.green_balance_source
  CarryGreenFinitePart.basis_mean
  CarryGreenFinitePart.source_basis_real
  CarryGreenFinitePart.second_scale_real
  CarryGreenFinitePart.realWeight
  CarryGreenFinitePart.critical_weight_real
  CarryGreenFinitePart.real_weighted_form
  CarryGreenFinitePart.source_energy_three_samples
  CarryGreenFinitePart.green_balance_three_samples

#audit_completed_pairing 1
  CarryGreenFinitePart.imaginaryReadout
  CarryGreenFinitePart.readoutCoefficient
  CarryGreenFinitePart.readout_analytic
  CarryGreenFinitePart.readout_coefficient_derivative
  CarryGreenFinitePart.readout_coefficient_even
  CarryGreenFinitePart.readout_coefficient_odd
  CarryGreenFinitePart.readout_exact_remainder
  CarryGreenFinitePart.readout_real
  CarryGreenFinitePart.radialStep
  CarryGreenFinitePart.radial_step_limit
  CarryGreenFinitePart.radial_node_readout
  CarryGreenFinitePart.finiteTerm
  CarryGreenFinitePart.correctionTerm
  CarryGreenFinitePart.fourthPolynomial
  CarryGreenFinitePart.remainderReadout
  CarryGreenFinitePart.errorReadout
  CarryGreenFinitePart.green_balance_exact_expansion
  CarryGreenFinitePart.criticalParameter
  CarryGreenFinitePart.finite_term_critical
  CarryGreenFinitePart.critical_correction_formula
  CarryGreenFinitePart.error_readout_continuousAt
  CarryGreenFinitePart.radial_mass_step
  CarryGreenFinitePart.green_finite_term_limit
  CarryGreenFinitePart.green_correction_limit
  CarryGreenFinitePart.green_fourth_correction_limit
  CarryGreenFinitePart.green_sixth_order_error_bound

#audit_completed_pairing 2
  CarryGreenFinitePart.critical_correction_negative
  CarryGreenFinitePart.critical_finite_term_positive
  CarryGreenFinitePart.critical_green_scaled_correction
  CarryGreenFinitePart.critical_green_eventually_between

#audit_completed_pairing 2
  CarryGreenFinitePart.imaginaryReadout
  CarryGreenFinitePart.readoutCoefficient
  CarryGreenFinitePart.readout_analytic
  CarryGreenFinitePart.readout_coefficient_derivative
  CarryGreenFinitePart.readout_coefficient_even
  CarryGreenFinitePart.readout_coefficient_odd
  CarryGreenFinitePart.readout_exact_remainder
  CarryGreenFinitePart.readout_real
  CarryGreenFinitePart.radialStep
  CarryGreenFinitePart.radial_step_limit
  CarryGreenFinitePart.radial_node_readout
  CarryGreenFinitePart.greenBalance
  CarryGreenFinitePart.green_balance_source
  CarryGreenFinitePart.basis_mean
  CarryGreenFinitePart.source_basis_real
  CarryGreenFinitePart.second_scale_real
  CarryGreenFinitePart.realWeight
  CarryGreenFinitePart.critical_weight_real
  CarryGreenFinitePart.real_weighted_form
  CarryGreenFinitePart.source_energy_three_samples
  CarryGreenFinitePart.green_balance_three_samples
  CarryGreenFinitePart.finiteTerm
  CarryGreenFinitePart.correctionTerm
  CarryGreenFinitePart.fourthPolynomial
  CarryGreenFinitePart.remainderReadout
  CarryGreenFinitePart.errorReadout
  CarryGreenFinitePart.green_balance_exact_expansion
  CarryGreenFinitePart.criticalParameter
  CarryGreenFinitePart.finite_term_critical
  CarryGreenFinitePart.critical_correction_formula
  CarryGreenFinitePart.error_readout_continuousAt
  CarryGreenFinitePart.radial_mass_step
  CarryGreenFinitePart.green_finite_term_limit
  CarryGreenFinitePart.green_correction_limit
  CarryGreenFinitePart.green_fourth_correction_limit
  CarryGreenFinitePart.green_sixth_order_error_bound
  CarryGreenFinitePart.critical_correction_negative
  CarryGreenFinitePart.critical_finite_term_positive
  CarryGreenFinitePart.critical_green_scaled_correction
  CarryGreenFinitePart.critical_green_eventually_between
