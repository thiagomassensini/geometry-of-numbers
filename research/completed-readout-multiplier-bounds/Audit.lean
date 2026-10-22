import Canary
import Lean

open Lean Elab Command
elab "#audit_readout_bounds " mode:ident ids:ident+ : command => do
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
  logInfo m!"Readout multiplier audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryReadoutBounds.real_gamma_le_inverse
#print axioms CarryReadoutBounds.complex_gamma_norm_le_real
#print axioms CarryReadoutBounds.complex_gamma_norm_le
#print axioms CarryReadoutBounds.complex_sin_norm_le_exp
#print axioms CarryReadoutBounds.exp_two_le_nine
#print axioms CarryReadoutBounds.gammaFactor
#print axioms CarryReadoutBounds.gamma_argument_bounds
#print axioms CarryReadoutBounds.gamma_factor_bound
#print axioms CarryReadoutBounds.inverse_gamma_factor_bound
#print axioms CarryReadoutBounds.complexSignal
#print axioms CarryReadoutBounds.reciprocal_cells_summable
#print axioms CarryReadoutBounds.reciprocal_cells_bound
#print axioms CarryReadoutBounds.signal_deviation_bound
#print axioms CarryReadoutBounds.signal_norm_lower
#print axioms CarryReadoutBounds.signal_nonzero
#print axioms CarryReadoutBounds.inverse_signal_bound
#print axioms CarryReadoutBounds.complex_signal_differentiableOn
#print axioms CarryReadoutBounds.complex_signal_real
#print axioms CarryReadoutBounds.normalized_cauchy
#print axioms CarryReadoutBounds.log_two_bounds
#print axioms CarryReadoutBounds.power_two_lower
#print axioms CarryReadoutBounds.camera_power_bounds
#print axioms CarryReadoutBounds.camera_inverse_factors
#print axioms CarryReadoutBounds.camera_complex_nonzero
#print axioms CarryReadoutBounds.camera_complex_bound
#print axioms CarryReadoutBounds.camera_complex_inverse_bound
#print axioms CarryReadoutBounds.polynomialFactor
#print axioms CarryReadoutBounds.exponentialFactor
#print axioms CarryReadoutBounds.complexDressing
#print axioms CarryReadoutBounds.parameter_analytic
#print axioms CarryReadoutBounds.polynomial_analytic
#print axioms CarryReadoutBounds.exponential_analytic
#print axioms CarryReadoutBounds.gamma_factor_analytic
#print axioms CarryReadoutBounds.polynomial_factor_bounds
#print axioms CarryReadoutBounds.log_pi_bounds
#print axioms CarryReadoutBounds.exponential_factor_bounds
#print axioms CarryReadoutBounds.derivative_eighth_bound
#print axioms CarryReadoutBounds.complex_dressing_formula
#print axioms CarryReadoutBounds.complex_dressing_analytic
#print axioms CarryReadoutBounds.complex_dressing_nonzero
#print axioms CarryReadoutBounds.dressing_log_split
#print axioms CarryReadoutBounds.dressing_log_bound
#print axioms CarryReadoutBounds.complexOrdinaryMultiplier
#print axioms CarryReadoutBounds.complexClockMultiplier
#print axioms CarryReadoutBounds.complex_signal_analytic
#print axioms CarryReadoutBounds.complex_ordinary_multiplier_analytic
#print axioms CarryReadoutBounds.complex_clock_multiplier_analytic
#print axioms CarryReadoutBounds.complex_ordinary_multiplier_bound
#print axioms CarryReadoutBounds.complex_clock_multiplier_bound
#print axioms CarryReadoutBounds.complex_dressing_real
#print axioms CarryReadoutBounds.dressing_deriv_real
#print axioms CarryReadoutBounds.clock_multiplier_real
#print axioms CarryReadoutBounds.ordinary_multiplier_real
#print axioms CarryReadoutBounds.ordinary_multiplier_jet_bound
#print axioms CarryReadoutBounds.clock_multiplier_jet_bound
#print axioms CarryReadoutBounds.explicitResponseConstant
#print axioms CarryReadoutBounds.response_constant_le
#print axioms CarryReadoutBounds.explicit_moment_error
#print axioms CarryReadoutBounds.explicitBilinearConstant
#print axioms CarryReadoutBounds.bilinear_constant_le
#print axioms CarryReadoutBounds.explicit_bilinear_error
#print axioms CarryReadoutBounds.explicit_critical_error
#print axioms CarryReadoutBounds.secondEvenResidual
#print axioms CarryReadoutBounds.secondEvenObservation
#print axioms CarryReadoutBounds.second_even_residual_error
#print axioms CarryReadoutBounds.response_constants_odd
#print axioms CarryReadoutBounds.second_even_error_at_100000
#print axioms CarryReadoutBounds.first_six_multiplier_bounds
#print axioms CarryReadoutBounds.second_even_residual_eq_pivot
#print axioms CarryReadoutBounds.second_even_critical_error_at_100000

#audit_readout_bounds gamma
  CarryReadoutBounds.real_gamma_le_inverse
  CarryReadoutBounds.complex_gamma_norm_le_real
  CarryReadoutBounds.complex_gamma_norm_le
  CarryReadoutBounds.complex_sin_norm_le_exp
  CarryReadoutBounds.exp_two_le_nine
  CarryReadoutBounds.gammaFactor
  CarryReadoutBounds.gamma_argument_bounds
  CarryReadoutBounds.gamma_factor_bound
  CarryReadoutBounds.inverse_gamma_factor_bound

#audit_readout_bounds signal
  CarryReadoutBounds.complexSignal
  CarryReadoutBounds.reciprocal_cells_summable
  CarryReadoutBounds.reciprocal_cells_bound
  CarryReadoutBounds.signal_deviation_bound
  CarryReadoutBounds.signal_norm_lower
  CarryReadoutBounds.signal_nonzero
  CarryReadoutBounds.inverse_signal_bound
  CarryReadoutBounds.complex_signal_differentiableOn
  CarryReadoutBounds.complex_signal_real
  CarryReadoutBounds.normalized_cauchy

#audit_readout_bounds camera
  CarryReadoutBounds.log_two_bounds
  CarryReadoutBounds.power_two_lower
  CarryReadoutBounds.camera_power_bounds
  CarryReadoutBounds.camera_inverse_factors
  CarryReadoutBounds.camera_complex_nonzero
  CarryReadoutBounds.camera_complex_bound
  CarryReadoutBounds.camera_complex_inverse_bound

#audit_readout_bounds dressing
  CarryReadoutBounds.polynomialFactor
  CarryReadoutBounds.exponentialFactor
  CarryReadoutBounds.complexDressing
  CarryReadoutBounds.parameter_analytic
  CarryReadoutBounds.polynomial_analytic
  CarryReadoutBounds.exponential_analytic
  CarryReadoutBounds.gamma_factor_analytic
  CarryReadoutBounds.polynomial_factor_bounds
  CarryReadoutBounds.log_pi_bounds
  CarryReadoutBounds.exponential_factor_bounds
  CarryReadoutBounds.derivative_eighth_bound
  CarryReadoutBounds.complex_dressing_formula
  CarryReadoutBounds.complex_dressing_analytic
  CarryReadoutBounds.complex_dressing_nonzero
  CarryReadoutBounds.dressing_log_split
  CarryReadoutBounds.dressing_log_bound

#audit_readout_bounds multipliers
  CarryReadoutBounds.complexOrdinaryMultiplier
  CarryReadoutBounds.complexClockMultiplier
  CarryReadoutBounds.complex_signal_analytic
  CarryReadoutBounds.complex_ordinary_multiplier_analytic
  CarryReadoutBounds.complex_clock_multiplier_analytic
  CarryReadoutBounds.complex_ordinary_multiplier_bound
  CarryReadoutBounds.complex_clock_multiplier_bound
  CarryReadoutBounds.complex_dressing_real
  CarryReadoutBounds.dressing_deriv_real
  CarryReadoutBounds.clock_multiplier_real
  CarryReadoutBounds.ordinary_multiplier_real
  CarryReadoutBounds.ordinary_multiplier_jet_bound
  CarryReadoutBounds.clock_multiplier_jet_bound

#audit_readout_bounds budgets
  CarryReadoutBounds.explicitResponseConstant
  CarryReadoutBounds.response_constant_le
  CarryReadoutBounds.explicit_moment_error
  CarryReadoutBounds.explicitBilinearConstant
  CarryReadoutBounds.bilinear_constant_le
  CarryReadoutBounds.explicit_bilinear_error
  CarryReadoutBounds.explicit_critical_error
  CarryReadoutBounds.secondEvenResidual
  CarryReadoutBounds.secondEvenObservation
  CarryReadoutBounds.second_even_residual_error

#audit_readout_bounds canary
  CarryReadoutBounds.response_constants_odd
  CarryReadoutBounds.second_even_error_at_100000
  CarryReadoutBounds.first_six_multiplier_bounds
  CarryReadoutBounds.second_even_residual_eq_pivot
  CarryReadoutBounds.second_even_critical_error_at_100000
