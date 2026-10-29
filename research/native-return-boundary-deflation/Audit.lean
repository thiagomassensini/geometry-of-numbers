import Controls
import ExactSeventh
import Lean

open Lean Elab Command
elab "#audit_return_deflation " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ if mode.getId == `prefix_test then #[] else #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos]
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
  logInfo m!"Return deflation audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryReturnDeflation.balance
#print axioms CarryReturnDeflation.deficit
#print axioms CarryReturnDeflation.feedbackIn
#print axioms CarryReturnDeflation.feedbackOut
#print axioms CarryReturnDeflation.feedback_balance
#print axioms CarryReturnDeflation.projection_split
#print axioms CarryReturnDeflation.feedback_projection_split
#print axioms CarryReturnDeflation.feedback_anchor_in
#print axioms CarryReturnDeflation.feedback_anchor_out
#print axioms CarryReturnDeflation.feedback_reconstruct_incident
#print axioms CarryReturnDeflation.feedback_reconstruct_returned
#print axioms CarryReturnDeflation.projected_reconstruct_incident
#print axioms CarryReturnDeflation.feedback_anchor_complement
#print axioms CarryReturnDeflation.singleton_projection
#print axioms CarryReturnDeflation.singleton_projection_pair
#print axioms CarryReturnDeflation.anchorCross
#print axioms CarryReturnDeflation.anchorCross_eq_balance
#print axioms CarryReturnDeflation.feedback_anchor_pair
#print axioms CarryReturnDeflation.projected_feedback_pair
#print axioms CarryReturnDeflation.physical_schur_remainder
#print axioms CarryReturnDeflation.eraseHead
#print axioms CarryReturnDeflation.source_head_decomposition
#print axioms CarryReturnDeflation.linearMap_eraseHead
#print axioms CarryReturnDeflation.scaled_anchor_schur
#print axioms CarryReturnDeflation.ControlSpace
#print axioms CarryReturnDeflation.controlAnchor
#print axioms CarryReturnDeflation.controlIncident
#print axioms CarryReturnDeflation.controlReturned
#print axioms CarryReturnDeflation.control_anchor_deficit_pos
#print axioms CarryReturnDeflation.control_feedback_incident_zero
#print axioms CarryReturnDeflation.control_original_negative
#print axioms CarryReturnDeflation.control_remainder_negative
#print axioms CarryReturnDeflation.control_anchor_incident_independent
#print axioms CarryReturnDeflation.Physical
#print axioms CarryReturnDeflation.nativeAnchor
#print axioms CarryReturnDeflation.anchorMass
#print axioms CarryReturnDeflation.nativeBoundarySpan
#print axioms CarryReturnDeflation.nativeBoundarySpan_projection
#print axioms CarryReturnDeflation.nativeBoundaryProjection
#print axioms CarryReturnDeflation.anchorMass_pos
#print axioms CarryReturnDeflation.nativeAnchor_inner
#print axioms CarryReturnDeflation.nativeBoundaryProjection_anchor
#print axioms CarryReturnDeflation.nativeIn
#print axioms CarryReturnDeflation.nativeOut
#print axioms CarryReturnDeflation.boundaryChannel
#print axioms CarryReturnDeflation.remainingIncident
#print axioms CarryReturnDeflation.remainingPair
#print axioms CarryReturnDeflation.nativeBalance
#print axioms CarryReturnDeflation.native_deficit
#print axioms CarryReturnDeflation.native_balance_split
#print axioms CarryReturnDeflation.native_boundary_formula
#print axioms CarryReturnDeflation.native_schur_remainder
#print axioms CarryReturnDeflation.native_incident_head
#print axioms CarryReturnDeflation.native_returned_head
#print axioms CarryReturnDeflation.nativeIn_head
#print axioms CarryReturnDeflation.nativeOut_head
#print axioms CarryReturnDeflation.remainingIncident_head
#print axioms CarryReturnDeflation.remainingPair_head_left
#print axioms CarryReturnDeflation.remainingPair_head_right
#print axioms CarryReturnDeflation.remainingPair_eraseHead
#print axioms CarryReturnDeflation.native_reconstruct_incident
#print axioms CarryReturnDeflation.native_reconstruct_returned
#print axioms CarryReturnDeflation.channels_separate_source
#print axioms CarryReturnDeflation.nativeIn_mem_original_span
#print axioms CarryReturnDeflation.nativeOut_mem_original_span
#print axioms CarryReturnDeflation.boundaryChannel_mem_original_span
#print axioms CarryReturnDeflation.remainingIncident_mem_original_span
#print axioms CarryReturnDeflation.physical_inner_self_re
#print axioms CarryReturnDeflation.native_storage_balance
#print axioms CarryReturnDeflation.native_energy_split
#print axioms CarryReturnDeflation.oneDeficit_eventually_pos
#print axioms CarryReturnDeflation.boundary_energy_eventually_nonnegative
#print axioms CarryReturnDeflation.jetBoundaryChannel
#print axioms CarryReturnDeflation.jetRemainingPair
#print axioms CarryReturnDeflation.jet_deflation_balance
#print axioms CarryReturnDeflation.deflatedJetEnergy
#print axioms CarryReturnDeflation.deflatedJetEnergy_eventually_storage
#print axioms CarryReturnDeflation.deflatedJetEnergy_tendsto
#print axioms CarryReturnDeflation.pr41_deflatedJetEnergy_tendsto
#print axioms CarryReturnDeflation.exact_seventh_residual_test
#print axioms CarryReturnDeflation.canonicalBoundaryPair
#print axioms CarryReturnDeflation.jetNativeBalance
#print axioms CarryReturnDeflation.jetNativeBalance_eq_form
#print axioms CarryReturnDeflation.jetNativeBalance_tendsto
#print axioms CarryReturnDeflation.headBoundary
#print axioms CarryReturnDeflation.headBoundary_eq_single
#print axioms CarryReturnDeflation.headAmplitude
#print axioms CarryReturnDeflation.head_jet_input
#print axioms CarryReturnDeflation.head_jet_incident
#print axioms CarryReturnDeflation.head_jet_returned
#print axioms CarryReturnDeflation.head_canonical_pair_self
#print axioms CarryReturnDeflation.head_amplitude_eventually_ne_zero
#print axioms CarryReturnDeflation.jetSchurRemainder
#print axioms CarryReturnDeflation.jet_remaining_schur_eventually
#print axioms CarryReturnDeflation.jet_remaining_schur_tendsto
#print axioms CarryReturnDeflation.canonical_even_real
#print axioms CarryReturnDeflation.constant_coefficientPolynomial
#print axioms CarryReturnDeflation.pr41_even_head_cross_zero
#print axioms CarryReturnDeflation.pr41_odd_head_cross_zero
#print axioms CarryReturnDeflation.head_orthogonal_remainder_tendsto
#print axioms CarryReturnDeflation.projectedJetPair
#print axioms CarryReturnDeflation.projectedJetPair_eq_difference
#print axioms CarryReturnDeflation.head_orthogonal_projected_tendsto_zero
#print axioms CarryReturnDeflation.pr41_even_projected_tendsto_zero
#print axioms CarryReturnDeflation.pr41_odd_projected_tendsto_zero
#print axioms CarryReturnDeflation.deflatedJetEnergy_eq_parts
#print axioms CarryReturnDeflation.residual_energy_tendsto_of_projected_zero
#print axioms CarryReturnDeflation.pr41_even_remaining_energy_tendsto
#print axioms CarryReturnDeflation.pr41_odd_remaining_energy_tendsto
#print axioms CarryReturnDeflation.exact_seventh_head_cross_zero
#print axioms CarryReturnDeflation.exact_seventh_projected_tendsto_zero
#print axioms CarryReturnDeflation.exact_seventh_remaining_energy_tendsto

#audit_return_deflation algebra
  CarryReturnDeflation.balance
  CarryReturnDeflation.deficit
  CarryReturnDeflation.feedbackIn
  CarryReturnDeflation.feedbackOut
  CarryReturnDeflation.feedback_balance
  CarryReturnDeflation.projection_split
  CarryReturnDeflation.feedback_projection_split
  CarryReturnDeflation.feedback_anchor_in
  CarryReturnDeflation.feedback_anchor_out
  CarryReturnDeflation.feedback_reconstruct_incident
  CarryReturnDeflation.feedback_reconstruct_returned
  CarryReturnDeflation.projected_reconstruct_incident
  CarryReturnDeflation.feedback_anchor_complement
  CarryReturnDeflation.singleton_projection
  CarryReturnDeflation.singleton_projection_pair
  CarryReturnDeflation.anchorCross
  CarryReturnDeflation.anchorCross_eq_balance
  CarryReturnDeflation.feedback_anchor_pair
  CarryReturnDeflation.projected_feedback_pair
  CarryReturnDeflation.physical_schur_remainder
  CarryReturnDeflation.eraseHead
  CarryReturnDeflation.source_head_decomposition
  CarryReturnDeflation.linearMap_eraseHead
  CarryReturnDeflation.scaled_anchor_schur
  CarryReturnDeflation.ControlSpace
  CarryReturnDeflation.controlAnchor
  CarryReturnDeflation.controlIncident
  CarryReturnDeflation.controlReturned
  CarryReturnDeflation.control_anchor_deficit_pos
  CarryReturnDeflation.control_feedback_incident_zero
  CarryReturnDeflation.control_original_negative
  CarryReturnDeflation.control_remainder_negative
  CarryReturnDeflation.control_anchor_incident_independent

#audit_return_deflation native
  CarryReturnDeflation.Physical
  CarryReturnDeflation.nativeAnchor
  CarryReturnDeflation.anchorMass
  CarryReturnDeflation.nativeBoundarySpan
  CarryReturnDeflation.nativeBoundarySpan_projection
  CarryReturnDeflation.nativeBoundaryProjection
  CarryReturnDeflation.anchorMass_pos
  CarryReturnDeflation.nativeAnchor_inner
  CarryReturnDeflation.nativeBoundaryProjection_anchor
  CarryReturnDeflation.nativeIn
  CarryReturnDeflation.nativeOut
  CarryReturnDeflation.boundaryChannel
  CarryReturnDeflation.remainingIncident
  CarryReturnDeflation.remainingPair
  CarryReturnDeflation.nativeBalance
  CarryReturnDeflation.native_deficit
  CarryReturnDeflation.native_balance_split
  CarryReturnDeflation.native_boundary_formula
  CarryReturnDeflation.native_schur_remainder
  CarryReturnDeflation.native_incident_head
  CarryReturnDeflation.native_returned_head
  CarryReturnDeflation.nativeIn_head
  CarryReturnDeflation.nativeOut_head
  CarryReturnDeflation.remainingIncident_head
  CarryReturnDeflation.remainingPair_head_left
  CarryReturnDeflation.remainingPair_head_right
  CarryReturnDeflation.remainingPair_eraseHead
  CarryReturnDeflation.native_reconstruct_incident
  CarryReturnDeflation.native_reconstruct_returned
  CarryReturnDeflation.channels_separate_source
  CarryReturnDeflation.nativeIn_mem_original_span
  CarryReturnDeflation.nativeOut_mem_original_span
  CarryReturnDeflation.boundaryChannel_mem_original_span
  CarryReturnDeflation.remainingIncident_mem_original_span
  CarryReturnDeflation.physical_inner_self_re
  CarryReturnDeflation.native_storage_balance
  CarryReturnDeflation.native_energy_split
  CarryReturnDeflation.oneDeficit_eventually_pos
  CarryReturnDeflation.boundary_energy_eventually_nonnegative
  CarryReturnDeflation.jetBoundaryChannel
  CarryReturnDeflation.jetRemainingPair
  CarryReturnDeflation.jet_deflation_balance
  CarryReturnDeflation.deflatedJetEnergy
  CarryReturnDeflation.deflatedJetEnergy_eventually_storage
  CarryReturnDeflation.deflatedJetEnergy_tendsto
  CarryReturnDeflation.pr41_deflatedJetEnergy_tendsto
  CarryReturnDeflation.exact_seventh_residual_test
  CarryReturnDeflation.canonicalBoundaryPair
  CarryReturnDeflation.jetNativeBalance
  CarryReturnDeflation.jetNativeBalance_eq_form
  CarryReturnDeflation.jetNativeBalance_tendsto
  CarryReturnDeflation.headBoundary
  CarryReturnDeflation.headBoundary_eq_single
  CarryReturnDeflation.headAmplitude
  CarryReturnDeflation.head_jet_input
  CarryReturnDeflation.head_jet_incident
  CarryReturnDeflation.head_jet_returned
  CarryReturnDeflation.head_canonical_pair_self
  CarryReturnDeflation.head_amplitude_eventually_ne_zero
  CarryReturnDeflation.jetSchurRemainder
  CarryReturnDeflation.jet_remaining_schur_eventually
  CarryReturnDeflation.jet_remaining_schur_tendsto
  CarryReturnDeflation.canonical_even_real
  CarryReturnDeflation.constant_coefficientPolynomial
  CarryReturnDeflation.pr41_even_head_cross_zero
  CarryReturnDeflation.pr41_odd_head_cross_zero
  CarryReturnDeflation.head_orthogonal_remainder_tendsto
  CarryReturnDeflation.projectedJetPair
  CarryReturnDeflation.projectedJetPair_eq_difference
  CarryReturnDeflation.head_orthogonal_projected_tendsto_zero
  CarryReturnDeflation.pr41_even_projected_tendsto_zero
  CarryReturnDeflation.pr41_odd_projected_tendsto_zero
  CarryReturnDeflation.deflatedJetEnergy_eq_parts
  CarryReturnDeflation.residual_energy_tendsto_of_projected_zero
  CarryReturnDeflation.pr41_even_remaining_energy_tendsto
  CarryReturnDeflation.pr41_odd_remaining_energy_tendsto

#audit_return_deflation prefix_test
  CarryReturnDeflation.exact_seventh_head_cross_zero
  CarryReturnDeflation.exact_seventh_projected_tendsto_zero
  CarryReturnDeflation.exact_seventh_remaining_energy_tendsto
