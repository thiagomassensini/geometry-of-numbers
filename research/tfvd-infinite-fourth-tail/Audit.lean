import Canary
import Lean

open Lean Elab Command
elab "#audit_fourth_tail " mode:ident ids:ident+ : command => do
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
  logInfo m!"Fourth tail audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryFourthTail.cpow_spatial_derivative
#print axioms CarryFourthTail.fourth_difference_norm_le
#print axioms CarryFourthTail.complexSample
#print axioms CarryFourthTail.complex_sample_real
#print axioms CarryFourthTail.complex_sample_entire
#print axioms CarryFourthTail.complexFourth
#print axioms CarryFourthTail.complexBoundary
#print axioms CarryFourthTail.complexRemainder
#print axioms CarryFourthTail.complex_fourth_entire
#print axioms CarryFourthTail.exponent_closed_half
#print axioms CarryFourthTail.complex_fourth_bound
#print axioms CarryFourthTail.complex_first_bound
#print axioms CarryFourthTail.complex_boundary_entire
#print axioms CarryFourthTail.complex_remainder_entire
#print axioms CarryFourthTail.complex_boundary_bound
#print axioms CarryFourthTail.complex_remainder_bound
#print axioms CarryFourthTail.normalized_cauchy_half
#print axioms CarryFourthTail.nativeBoundary
#print axioms CarryFourthTail.nativeRemainder
#print axioms CarryFourthTail.nativeFourth
#print axioms CarryFourthTail.complex_fourth_real
#print axioms CarryFourthTail.complex_boundary_real
#print axioms CarryFourthTail.complex_remainder_real
#print axioms CarryFourthTail.native_boundary_analytic
#print axioms CarryFourthTail.native_remainder_analytic
#print axioms CarryFourthTail.fourthJet
#print axioms CarryFourthTail.boundaryJet
#print axioms CarryFourthTail.remainderJet
#print axioms CarryFourthTail.fourth_jet_bound
#print axioms CarryFourthTail.boundary_jet_bound
#print axioms CarryFourthTail.remainder_jet_bound
#print axioms CarryFourthTail.quartic_reciprocal_step
#print axioms CarryFourthTail.quartic_cell_summable
#print axioms CarryFourthTail.quartic_cell_tail
#print axioms CarryFourthTail.native_jet_window
#print axioms CarryFourthTail.boundary_jet_vanishes
#print axioms CarryFourthTail.remainder_jets_summable
#print axioms CarryFourthTail.remainder_series_bound
#print axioms CarryFourthTail.infinite_jet_acceleration
#print axioms CarryFourthTail.acceleratedOrdinaryHead
#print axioms CarryFourthTail.acceleratedOrdinaryTail
#print axioms CarryFourthTail.accelerated_ordinary_head_analytic
#print axioms CarryFourthTail.accelerated_ordinary_tail_analytic
#print axioms CarryFourthTail.accelerated_ordinary_jet_exact
#print axioms CarryFourthTail.acceleratedOrdinaryBudget
#print axioms CarryFourthTail.accelerated_ordinary_jet_bound
#print axioms CarryFourthTail.nativeClockBoundary
#print axioms CarryFourthTail.boundary_hasDerivAt_clock
#print axioms CarryFourthTail.boundary_clock_derivative
#print axioms CarryFourthTail.native_clock_boundary_analytic
#print axioms CarryFourthTail.boundary_clock_jet
#print axioms CarryFourthTail.return_clock_jet
#print axioms CarryFourthTail.finite_clock_jet
#print axioms CarryFourthTail.acceleratedClockHead
#print axioms CarryFourthTail.acceleratedClockTail
#print axioms CarryFourthTail.accelerated_clock_head_analytic
#print axioms CarryFourthTail.accelerated_clock_tail_analytic
#print axioms CarryFourthTail.accelerated_clock_jet_exact
#print axioms CarryFourthTail.accelerated_clock_jet_series
#print axioms CarryFourthTail.acceleratedClockBudget
#print axioms CarryFourthTail.accelerated_clock_jet_bound
#print axioms CarryFourthTail.acceleratedResponseObservation
#print axioms CarryFourthTail.accelerated_response_analytic
#print axioms CarryFourthTail.accelerated_response_tail_exact
#print axioms CarryFourthTail.acceleratedResponseBudget
#print axioms CarryFourthTail.accelerated_response_jet_error
#print axioms CarryFourthTail.accelerated_response_budget_rate
#print axioms CarryFourthTail.acceleratedObservedMoment
#print axioms CarryFourthTail.accelerated_native_moment_error
#print axioms CarryFourthTail.observedBilinear
#print axioms CarryFourthTail.bilinearErrorConstant
#print axioms CarryFourthTail.accelerated_bilinear_error
#print axioms CarryFourthTail.acceleratedCriticalObservation
#print axioms CarryFourthTail.accelerated_critical_error
#print axioms CarryFourthTail.critical_budget_improvement
#print axioms CarryFourthTail.accelerated_critical_cutoff_suffices
#print axioms CarryFourthTail.rJet_left_constant
#print axioms CarryFourthTail.native_sample_analytic
#print axioms CarryFourthTail.sampleJet
#print axioms CarryFourthTail.fourthWeights
#print axioms CarryFourthTail.boundaryWeights
#print axioms CarryFourthTail.fourth_weight_stencil
#print axioms CarryFourthTail.boundary_weight_stencil
#print axioms CarryFourthTail.fourth_jet_stencil
#print axioms CarryFourthTail.boundary_jet_stencil
#print axioms CarryFourthTail.normalized_material_fourth_bound
#print axioms CarryFourthTail.acceleratedPairHead
#print axioms CarryFourthTail.acceleratedPairTail
#print axioms CarryFourthTail.accelerated_pair_head_tail
#print axioms CarryFourthTail.accelerated_green_tail_ledger
#print axioms CarryFourthTail.dressedValueJetBudget
#print axioms CarryFourthTail.dressedCompanionJetBudget
#print axioms CarryFourthTail.accelerated_value_tail_jet_bound
#print axioms CarryFourthTail.accelerated_companion_tail_jet_bound
#print axioms CarryFourthTail.ordinary_fifth_501_error_lt
#print axioms CarryFourthTail.clock_fifth_1145_error_lt
#print axioms CarryFourthTail.critical_budget_gain_at_16

#audit_fourth_tail fourth
  CarryFourthTail.cpow_spatial_derivative
  CarryFourthTail.fourth_difference_norm_le
  CarryFourthTail.complexSample
  CarryFourthTail.complex_sample_real
  CarryFourthTail.complex_sample_entire
  CarryFourthTail.complexFourth
  CarryFourthTail.complexBoundary
  CarryFourthTail.complexRemainder
  CarryFourthTail.complex_fourth_entire
  CarryFourthTail.exponent_closed_half
  CarryFourthTail.complex_fourth_bound

#audit_fourth_tail jets
  CarryFourthTail.complex_first_bound
  CarryFourthTail.complex_boundary_entire
  CarryFourthTail.complex_remainder_entire
  CarryFourthTail.complex_boundary_bound
  CarryFourthTail.complex_remainder_bound
  CarryFourthTail.normalized_cauchy_half
  CarryFourthTail.nativeBoundary
  CarryFourthTail.nativeRemainder
  CarryFourthTail.nativeFourth
  CarryFourthTail.complex_fourth_real
  CarryFourthTail.complex_boundary_real
  CarryFourthTail.complex_remainder_real
  CarryFourthTail.native_boundary_analytic
  CarryFourthTail.native_remainder_analytic
  CarryFourthTail.fourthJet
  CarryFourthTail.boundaryJet
  CarryFourthTail.remainderJet
  CarryFourthTail.fourth_jet_bound
  CarryFourthTail.boundary_jet_bound
  CarryFourthTail.remainder_jet_bound

#audit_fourth_tail envelope
  CarryFourthTail.quartic_reciprocal_step
  CarryFourthTail.quartic_cell_summable
  CarryFourthTail.quartic_cell_tail

#audit_fourth_tail infinite
  CarryFourthTail.native_jet_window
  CarryFourthTail.boundary_jet_vanishes
  CarryFourthTail.remainder_jets_summable
  CarryFourthTail.remainder_series_bound
  CarryFourthTail.infinite_jet_acceleration
  CarryFourthTail.acceleratedOrdinaryHead
  CarryFourthTail.acceleratedOrdinaryTail
  CarryFourthTail.accelerated_ordinary_head_analytic
  CarryFourthTail.accelerated_ordinary_tail_analytic
  CarryFourthTail.accelerated_ordinary_jet_exact
  CarryFourthTail.acceleratedOrdinaryBudget
  CarryFourthTail.accelerated_ordinary_jet_bound

#audit_fourth_tail clock
  CarryFourthTail.nativeClockBoundary
  CarryFourthTail.boundary_hasDerivAt_clock
  CarryFourthTail.boundary_clock_derivative
  CarryFourthTail.native_clock_boundary_analytic
  CarryFourthTail.boundary_clock_jet
  CarryFourthTail.return_clock_jet
  CarryFourthTail.finite_clock_jet
  CarryFourthTail.acceleratedClockHead
  CarryFourthTail.acceleratedClockTail
  CarryFourthTail.accelerated_clock_head_analytic
  CarryFourthTail.accelerated_clock_tail_analytic
  CarryFourthTail.accelerated_clock_jet_exact
  CarryFourthTail.accelerated_clock_jet_series
  CarryFourthTail.acceleratedClockBudget
  CarryFourthTail.accelerated_clock_jet_bound

#audit_fourth_tail critical
  CarryFourthTail.acceleratedResponseObservation
  CarryFourthTail.accelerated_response_analytic
  CarryFourthTail.accelerated_response_tail_exact
  CarryFourthTail.acceleratedResponseBudget
  CarryFourthTail.accelerated_response_jet_error
  CarryFourthTail.accelerated_response_budget_rate
  CarryFourthTail.acceleratedObservedMoment
  CarryFourthTail.accelerated_native_moment_error
  CarryFourthTail.observedBilinear
  CarryFourthTail.bilinearErrorConstant
  CarryFourthTail.accelerated_bilinear_error
  CarryFourthTail.acceleratedCriticalObservation
  CarryFourthTail.accelerated_critical_error
  CarryFourthTail.critical_budget_improvement
  CarryFourthTail.accelerated_critical_cutoff_suffices

#audit_fourth_tail stencils
  CarryFourthTail.rJet_left_constant
  CarryFourthTail.native_sample_analytic
  CarryFourthTail.sampleJet
  CarryFourthTail.fourthWeights
  CarryFourthTail.boundaryWeights
  CarryFourthTail.fourth_weight_stencil
  CarryFourthTail.boundary_weight_stencil
  CarryFourthTail.fourth_jet_stencil
  CarryFourthTail.boundary_jet_stencil
  CarryFourthTail.normalized_material_fourth_bound

#audit_fourth_tail boundary
  CarryFourthTail.acceleratedPairHead
  CarryFourthTail.acceleratedPairTail
  CarryFourthTail.accelerated_pair_head_tail
  CarryFourthTail.accelerated_green_tail_ledger
  CarryFourthTail.dressedValueJetBudget
  CarryFourthTail.dressedCompanionJetBudget
  CarryFourthTail.accelerated_value_tail_jet_bound
  CarryFourthTail.accelerated_companion_tail_jet_bound

#audit_fourth_tail canary
  CarryFourthTail.ordinary_fifth_501_error_lt
  CarryFourthTail.clock_fifth_1145_error_lt
  CarryFourthTail.critical_budget_gain_at_16
