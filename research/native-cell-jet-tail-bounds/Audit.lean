import TailAcceleration
import Lean

open Lean Elab Command
elab "#audit_cell_tail " mode:ident ids:ident+ : command => do
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
  let forbidden := if mode.getId != `boundary then forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner] else forbidden
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
  logInfo m!"Cell tail audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryCellTail.complexCell
#print axioms CarryCellTail.complex_cell_real
#print axioms CarryCellTail.complex_cell_entire
#print axioms CarryCellTail.complex_cell_bound
#print axioms CarryCellTail.complexJet
#print axioms CarryCellTail.complex_jet_bound
#print axioms CarryCellTail.cshift
#print axioms CarryCellTail.cshift_analytic
#print axioms CarryCellTail.cshift_coefficient
#print axioms CarryCellTail.real_dslope_germ
#print axioms CarryCellTail.real_jet_complex
#print axioms CarryCellTail.cell_jet_coefficient
#print axioms CarryCellTail.cell_jet_bound
#print axioms CarryCellTail.reciprocal_step
#print axioms CarryCellTail.reciprocal_cell_tail
#print axioms CarryCellTail.return_jet_quantitative
#print axioms CarryCellTail.clockCell
#print axioms CarryCellTail.clock_cell_real_derivative
#print axioms CarryCellTail.complex_clock_real
#print axioms CarryCellTail.complex_jet_derivative
#print axioms CarryCellTail.clock_jet_coefficient
#print axioms CarryCellTail.clock_cell_jet_bound
#print axioms CarryCellTail.clock_return_jet_quantitative
#print axioms CarryCellTail.rJet
#print axioms CarryCellTail.rJet_derivative
#print axioms CarryCellTail.rJet_add
#print axioms CarryCellTail.rJet_sub
#print axioms CarryCellTail.rJet_mul
#print axioms CarryCellTail.rJet_mul_bound
#print axioms CarryCellTail.rJet_sum
#print axioms CarryCellTail.ordinaryHead
#print axioms CarryCellTail.clockHead
#print axioms CarryCellTail.ordinaryTail
#print axioms CarryCellTail.clockTail
#print axioms CarryCellTail.cell_real_analytic
#print axioms CarryCellTail.clock_cell_real_analytic
#print axioms CarryCellTail.beta_real_analytic
#print axioms CarryCellTail.kappa_real_analytic
#print axioms CarryCellTail.ordinary_head_analytic
#print axioms CarryCellTail.clock_head_analytic
#print axioms CarryCellTail.ordinary_tail_analytic
#print axioms CarryCellTail.clock_tail_analytic
#print axioms CarryCellTail.ordinaryBudget
#print axioms CarryCellTail.clockBudget
#print axioms CarryCellTail.ordinary_tail_jet_bound
#print axioms CarryCellTail.clock_tail_jet_bound
#print axioms CarryCellTail.original_response_center_ne
#print axioms CarryCellTail.ordinaryMultiplier
#print axioms CarryCellTail.clockMultiplier
#print axioms CarryCellTail.ordinary_multiplier_analytic
#print axioms CarryCellTail.clock_multiplier_analytic
#print axioms CarryCellTail.responseObservation
#print axioms CarryCellTail.response_observation_analytic
#print axioms CarryCellTail.normalized_response_channels
#print axioms CarryCellTail.response_tail_exact
#print axioms CarryCellTail.responseBudget
#print axioms CarryCellTail.response_jet_error
#print axioms CarryCellTail.observedMoment
#print axioms CarryCellTail.native_moment_jet
#print axioms CarryCellTail.native_moment_error
#print axioms CarryCellTail.criticalObservation
#print axioms CarryCellTail.criticalErrorBudget
#print axioms CarryCellTail.critical_pivot_coefficients
#print axioms CarryCellTail.exact_critical_error
#print axioms CarryCellTail.responseErrorConstant
#print axioms CarryCellTail.response_budget_rate
#print axioms CarryCellTail.criticalErrorConstant
#print axioms CarryCellTail.critical_budget_rate
#print axioms CarryCellTail.critical_cutoff_suffices
#print axioms CarryCellTail.second_even_error
#print axioms CarryCellTail.reciprocal_cell_summable
#print axioms CarryCellTail.bounded_cell_series_tail
#print axioms CarryCellTail.clock_cell_point_bound
#print axioms CarryCellTail.ordinary_tail_point_bound
#print axioms CarryCellTail.clock_tail_point_bound
#print axioms CarryCellTail.pairMagnitude
#print axioms CarryCellTail.balanceMagnitude
#print axioms CarryCellTail.reduced_form_norm_bound
#print axioms CarryCellTail.pairTailBudget
#print axioms CarryCellTail.native_tail_pair_exact
#print axioms CarryCellTail.native_tail_pair_bound
#print axioms CarryCellTail.full_green_tail_budget
#print axioms CarryCellTail.delta2
#print axioms CarryCellTail.delta4
#print axioms CarryCellTail.tailBoundary
#print axioms CarryCellTail.tailRemainder
#print axioms CarryCellTail.tail_acceleration_cell
#print axioms CarryCellTail.tail_acceleration_finite
#print axioms CarryCellTail.native_cell_delta2
#print axioms CarryCellTail.native_tail_window_acceleration

#audit_cell_tail cells
  CarryCellTail.complexCell
  CarryCellTail.complex_cell_real
  CarryCellTail.complex_cell_entire
  CarryCellTail.complex_cell_bound
  CarryCellTail.complexJet
  CarryCellTail.complex_jet_bound
  CarryCellTail.cshift
  CarryCellTail.cshift_analytic
  CarryCellTail.cshift_coefficient
  CarryCellTail.real_dslope_germ
  CarryCellTail.real_jet_complex
  CarryCellTail.cell_jet_coefficient
  CarryCellTail.cell_jet_bound
  CarryCellTail.reciprocal_step
  CarryCellTail.reciprocal_cell_tail
  CarryCellTail.return_jet_quantitative

#audit_cell_tail clock
  CarryCellTail.clockCell
  CarryCellTail.clock_cell_real_derivative
  CarryCellTail.complex_clock_real
  CarryCellTail.complex_jet_derivative
  CarryCellTail.clock_jet_coefficient
  CarryCellTail.clock_cell_jet_bound
  CarryCellTail.clock_return_jet_quantitative

#audit_cell_tail calculus
  CarryCellTail.rJet
  CarryCellTail.rJet_derivative
  CarryCellTail.rJet_add
  CarryCellTail.rJet_sub
  CarryCellTail.rJet_mul
  CarryCellTail.rJet_mul_bound
  CarryCellTail.rJet_sum

#audit_cell_tail response
  CarryCellTail.ordinaryHead
  CarryCellTail.clockHead
  CarryCellTail.ordinaryTail
  CarryCellTail.clockTail
  CarryCellTail.cell_real_analytic
  CarryCellTail.clock_cell_real_analytic
  CarryCellTail.beta_real_analytic
  CarryCellTail.kappa_real_analytic
  CarryCellTail.ordinary_head_analytic
  CarryCellTail.clock_head_analytic
  CarryCellTail.ordinary_tail_analytic
  CarryCellTail.clock_tail_analytic
  CarryCellTail.ordinaryBudget
  CarryCellTail.clockBudget
  CarryCellTail.ordinary_tail_jet_bound
  CarryCellTail.clock_tail_jet_bound
  CarryCellTail.original_response_center_ne
  CarryCellTail.ordinaryMultiplier
  CarryCellTail.clockMultiplier
  CarryCellTail.ordinary_multiplier_analytic
  CarryCellTail.clock_multiplier_analytic
  CarryCellTail.responseObservation
  CarryCellTail.response_observation_analytic
  CarryCellTail.normalized_response_channels
  CarryCellTail.response_tail_exact
  CarryCellTail.responseBudget
  CarryCellTail.response_jet_error
  CarryCellTail.observedMoment
  CarryCellTail.native_moment_jet
  CarryCellTail.native_moment_error

#audit_cell_tail critical
  CarryCellTail.criticalObservation
  CarryCellTail.criticalErrorBudget
  CarryCellTail.critical_pivot_coefficients
  CarryCellTail.exact_critical_error
  CarryCellTail.responseErrorConstant
  CarryCellTail.response_budget_rate
  CarryCellTail.criticalErrorConstant
  CarryCellTail.critical_budget_rate
  CarryCellTail.critical_cutoff_suffices
  CarryCellTail.second_even_error

#audit_cell_tail boundary
  CarryCellTail.reciprocal_cell_summable
  CarryCellTail.bounded_cell_series_tail
  CarryCellTail.clock_cell_point_bound
  CarryCellTail.ordinary_tail_point_bound
  CarryCellTail.clock_tail_point_bound
  CarryCellTail.pairMagnitude
  CarryCellTail.balanceMagnitude
  CarryCellTail.reduced_form_norm_bound
  CarryCellTail.pairTailBudget
  CarryCellTail.native_tail_pair_exact
  CarryCellTail.native_tail_pair_bound
  CarryCellTail.full_green_tail_budget

#audit_cell_tail acceleration
  CarryCellTail.delta2
  CarryCellTail.delta4
  CarryCellTail.tailBoundary
  CarryCellTail.tailRemainder
  CarryCellTail.tail_acceleration_cell
  CarryCellTail.tail_acceleration_finite
  CarryCellTail.native_cell_delta2
  CarryCellTail.native_tail_window_acceleration
