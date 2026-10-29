import IntegratedNormTest
import Lean

open Lean Elab Command
elab "#audit_theta_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
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
      if forbidden.contains name then
        throwError "Forbidden canonical-sign consumer: {name}"
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
  logInfo m!"Theta transport audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical-sign consumers absent"

#print axioms CarryThetaPolarized.green_product_defect
#print axioms CarryThetaPolarized.green_flux_product
#print axioms CarryThetaPolarized.green_product_integral
#print axioms CarryThetaPolarized.thetaBilinearPolynomial
#print axioms CarryThetaPolarized.thetaBilinearPolynomial_integral
#print axioms CarryThetaPolarized.thetaBilinearPolynomial_center_traces
#print axioms CarryThetaPolarized.native_bilinear_eq_green_integral
#print axioms CarryThetaPolarized.thetaInputPolynomial
#print axioms CarryThetaPolarized.thetaInputPolynomial_succ
#print axioms CarryThetaPolarized.moment_top_coefficient_ne_zero
#print axioms CarryThetaPolarized.thetaInputPolynomial_coeff_last
#print axioms CarryThetaPolarized.thetaInputPolynomial_zero_iff
#print axioms CarryThetaPolarized.thetaInputPolynomial_injective
#print axioms CarryThetaPolarized.greenPolynomial_zero_iff
#print axioms CarryThetaPolarized.greenPolynomial_injective
#print axioms CarryThetaPolarized.thetaGreenInput_injective
#print axioms CarryThetaPolarized.moment_zero_eval
#print axioms CarryThetaPolarized.moment_one_eval
#print axioms CarryThetaPolarized.moment_two_eval
#print axioms CarryThetaPolarized.thetaDensityDeterminant
#print axioms CarryThetaPolarized.thetaDensityDeterminant_formula
#print axioms CarryThetaPolarized.thetaDensityDeterminant_coeff_eight
#print axioms CarryThetaPolarized.thetaDensityDeterminant_coeff_eight_neg
#print axioms CarryThetaPolarized.thetaDensityDeterminant_natDegree
#print axioms CarryThetaPolarized.thetaDensityDeterminant_tendsto_atBot
#print axioms CarryThetaPolarized.thetaDensityDeterminant_eventually_neg
#print axioms CarryThetaPolarized.thetaDensityDeterminant_not_ae_nonneg
#print axioms CarryThetaPolarized.no_pointwise_theta_density_gram
#print axioms CarryThetaPolarized.no_ae_weighted_theta_density_gram
#print axioms CarryThetaPolarized.even_density_diagonals_pos_but_determinant_neg
#print axioms CarryThetaPolarized.momentPolynomial_center_traces
#print axioms CarryThetaPolarized.thetaProductResidual
#print axioms CarryThetaPolarized.thetaProductResidual_center_traces
#print axioms CarryThetaPolarized.thetaProductResidual_green_formula
#print axioms CarryThetaPolarized.canonical_pairing_eq_theta_product_add_green_residual
#print axioms CarryThetaPolarized.theta_polynomial_square_integral_nonneg
#print axioms CarryThetaPolarized.thetaProductResidual_flux_zero_at_center
#print axioms CarryThetaPolarized.theta_first_polynomial_square_integral
#print axioms CarryThetaPolarized.xi_fourth_moment_lt_twice_mass_second
#print axioms CarryThetaPolarized.theta_first_polynomial_square_integral_lt_native
#print axioms CarryThetaPolarized.theta_product_residual_zero_zero_integral_pos

#audit_theta_transport
  CarryThetaPolarized.green_product_defect
  CarryThetaPolarized.green_flux_product
  CarryThetaPolarized.green_product_integral
  CarryThetaPolarized.thetaBilinearPolynomial
  CarryThetaPolarized.thetaBilinearPolynomial_integral
  CarryThetaPolarized.thetaBilinearPolynomial_center_traces
  CarryThetaPolarized.native_bilinear_eq_green_integral
  CarryThetaPolarized.thetaInputPolynomial
  CarryThetaPolarized.thetaInputPolynomial_succ
  CarryThetaPolarized.moment_top_coefficient_ne_zero
  CarryThetaPolarized.thetaInputPolynomial_coeff_last
  CarryThetaPolarized.thetaInputPolynomial_zero_iff
  CarryThetaPolarized.thetaInputPolynomial_injective
  CarryThetaPolarized.greenPolynomial_zero_iff
  CarryThetaPolarized.greenPolynomial_injective
  CarryThetaPolarized.thetaGreenInput_injective
  CarryThetaPolarized.moment_zero_eval
  CarryThetaPolarized.moment_one_eval
  CarryThetaPolarized.moment_two_eval
  CarryThetaPolarized.thetaDensityDeterminant
  CarryThetaPolarized.thetaDensityDeterminant_formula
  CarryThetaPolarized.thetaDensityDeterminant_coeff_eight
  CarryThetaPolarized.thetaDensityDeterminant_coeff_eight_neg
  CarryThetaPolarized.thetaDensityDeterminant_natDegree
  CarryThetaPolarized.thetaDensityDeterminant_tendsto_atBot
  CarryThetaPolarized.thetaDensityDeterminant_eventually_neg
  CarryThetaPolarized.thetaDensityDeterminant_not_ae_nonneg
  CarryThetaPolarized.no_pointwise_theta_density_gram
  CarryThetaPolarized.no_ae_weighted_theta_density_gram
  CarryThetaPolarized.even_density_diagonals_pos_but_determinant_neg
  CarryThetaPolarized.momentPolynomial_center_traces
  CarryThetaPolarized.thetaProductResidual
  CarryThetaPolarized.thetaProductResidual_center_traces
  CarryThetaPolarized.thetaProductResidual_green_formula
  CarryThetaPolarized.canonical_pairing_eq_theta_product_add_green_residual
  CarryThetaPolarized.theta_polynomial_square_integral_nonneg
  CarryThetaPolarized.thetaProductResidual_flux_zero_at_center
  CarryThetaPolarized.theta_first_polynomial_square_integral
  CarryThetaPolarized.xi_fourth_moment_lt_twice_mass_second
  CarryThetaPolarized.theta_first_polynomial_square_integral_lt_native
  CarryThetaPolarized.theta_product_residual_zero_zero_integral_pos
