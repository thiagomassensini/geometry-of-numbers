import Regression
import Lean

open Lean Elab Command
elab "#audit_c3_gamma " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
  let forbidden := if mode.getId == `orientation then forbidden else forbidden ++ #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"C3 original Gamma audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryC3Gamma.expHead
#print axioms CarryC3Gamma.gammaHeadIntegral
#print axioms CarryC3Gamma.exp_head_error
#print axioms CarryC3Gamma.gamma_tail_bound
#print axioms CarryC3Gamma.gamma_compact_error
#print axioms CarryC3Gamma.gamma_integral_approx_error
#print axioms CarryC3Gamma.gammaFinite
#print axioms CarryC3Gamma.euler_term
#print axioms CarryC3Gamma.gamma_head_integral_formula
#print axioms CarryC3Gamma.gamma_finite_error
#print axioms CarryC3Gamma.exp_neg_eighty_one_bound
#print axioms CarryC3Gamma.gamma_finite_512_error
#print axioms CarryC3Gamma.nativeGamma
#print axioms CarryC3Gamma.finiteNativeGamma
#print axioms CarryC3Gamma.native_gamma_argument
#print axioms CarryC3Gamma.native_gamma_uniform_error
#print axioms CarryC3Gamma.finite_gamma_analytic
#print axioms CarryC3Gamma.native_gamma_analytic
#print axioms CarryC3Gamma.native_gamma_jet_error
#print axioms CarryC3Gamma.jet_mul
#print axioms CarryC3Gamma.jet_inv_affine
#print axioms CarryC3Gamma.jet_exp_linear
#print axioms CarryC3Gamma.jet_sum
#print axioms CarryC3Gamma.jet_const_mul
#print axioms CarryC3Gamma.native_gamma_power_formula
#print axioms CarryC3Gamma.rationalCoefficient
#print axioms CarryC3Gamma.gammaCoefficient
#print axioms CarryC3Gamma.finite_native_gamma_formula
#print axioms CarryC3Gamma.finite_native_gamma_coefficient
#print axioms CarryC3Gamma.coefficientReference
#print axioms CarryC3Gamma.rational_coefficient_boxes
#print axioms CarryC3Gamma.logApprox
#print axioms CarryC3Gamma.logReference
#print axioms CarryC3Gamma.log_rational_box
#print axioms CarryC3Gamma.rat_abs_cast_le
#print axioms CarryC3Gamma.log_three_box
#print axioms CarryC3Gamma.gammaRealReference
#print axioms CarryC3Gamma.gammaRationalPolynomial
#print axioms CarryC3Gamma.gamma_rational_boxes
#print axioms CarryC3Gamma.coefficient_reference_bound
#print axioms CarryC3Gamma.realGammaPolynomial
#print axioms CarryC3Gamma.real_gamma_polynomial_error
#print axioms CarryC3Gamma.gammaReference
#print axioms CarryC3Gamma.gamma_coefficient_real
#print axioms CarryC3Gamma.native_gamma_seven_boxes
#print axioms CarryC3Gamma.xiBeforeGamma
#print axioms CarryC3Gamma.native_xi_gamma_factorization
#print axioms CarryC3Gamma.c3_value_multiplier_gamma_factorization

#audit_c3_gamma euler_integral
  CarryC3Gamma.expHead
  CarryC3Gamma.gammaHeadIntegral
  CarryC3Gamma.exp_head_error
  CarryC3Gamma.gamma_tail_bound
  CarryC3Gamma.gamma_compact_error
  CarryC3Gamma.gamma_integral_approx_error

#audit_c3_gamma finite_evaluator
  CarryC3Gamma.gammaFinite
  CarryC3Gamma.euler_term
  CarryC3Gamma.gamma_head_integral_formula
  CarryC3Gamma.gamma_finite_error

#audit_c3_gamma native_jets
  CarryC3Gamma.exp_neg_eighty_one_bound
  CarryC3Gamma.gamma_finite_512_error
  CarryC3Gamma.nativeGamma
  CarryC3Gamma.finiteNativeGamma
  CarryC3Gamma.native_gamma_argument
  CarryC3Gamma.native_gamma_uniform_error
  CarryC3Gamma.finite_gamma_analytic
  CarryC3Gamma.native_gamma_analytic
  CarryC3Gamma.native_gamma_jet_error

#audit_c3_gamma coefficient_formula
  CarryC3Gamma.jet_mul
  CarryC3Gamma.jet_inv_affine
  CarryC3Gamma.jet_exp_linear
  CarryC3Gamma.jet_sum
  CarryC3Gamma.jet_const_mul
  CarryC3Gamma.native_gamma_power_formula
  CarryC3Gamma.rationalCoefficient
  CarryC3Gamma.gammaCoefficient
  CarryC3Gamma.finite_native_gamma_formula
  CarryC3Gamma.finite_native_gamma_coefficient

#audit_c3_gamma exact_rational_sums
  CarryC3Gamma.coefficientReference
  CarryC3Gamma.rational_coefficient_boxes

#audit_c3_gamma log_and_references
  CarryC3Gamma.logApprox
  CarryC3Gamma.logReference
  CarryC3Gamma.log_rational_box
  CarryC3Gamma.rat_abs_cast_le
  CarryC3Gamma.log_three_box
  CarryC3Gamma.gammaRealReference
  CarryC3Gamma.gammaRationalPolynomial
  CarryC3Gamma.gamma_rational_boxes
  CarryC3Gamma.coefficient_reference_bound

#audit_c3_gamma seven_value_boxes
  CarryC3Gamma.realGammaPolynomial
  CarryC3Gamma.real_gamma_polynomial_error
  CarryC3Gamma.gammaReference
  CarryC3Gamma.gamma_coefficient_real
  CarryC3Gamma.native_gamma_seven_boxes

#audit_c3_gamma original_source
  CarryC3Gamma.xiBeforeGamma
  CarryC3Gamma.native_xi_gamma_factorization
  CarryC3Gamma.c3_value_multiplier_gamma_factorization
