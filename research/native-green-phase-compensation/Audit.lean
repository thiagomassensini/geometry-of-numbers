import ConfluentKernel
import Lean

open Lean Elab Command
elab "#audit_native_phase " mode:ident ids:ident+ : command => do
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
  let forbidden := if mode.getId == `orbit || mode.getId == `phase then forbidden ++ #[
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
  logInfo m!"Native phase audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryNativePhase.material_gradient_analytic
#print axioms CarryNativePhase.material_boundary_analytic
#print axioms CarryNativePhase.material_state_analytic
#print axioms CarryNativePhase.sourceCenter
#print axioms CarryNativePhase.sourceOverlap
#print axioms CarryNativePhase.source_center_analytic
#print axioms CarryNativePhase.source_overlap_analytic
#print axioms CarryNativePhase.source_center_origin
#print axioms CarryNativePhase.source_overlap_origin
#print axioms CarryNativePhase.source_overlap_derivative
#print axioms CarryNativePhase.native_ratio_analytic
#print axioms CarryNativePhase.forcing_scalar_analytic
#print axioms CarryNativePhase.dressed_state_analytic
#print axioms CarryNativePhase.companion_first_analytic
#print axioms CarryNativePhase.compressed_first_analytic
#print axioms CarryNativePhase.companion_probe_analytic
#print axioms CarryNativePhase.materialJetTwo
#print axioms CarryNativePhase.secondCorrection
#print axioms CarryNativePhase.phaseCoefficient
#print axioms CarryNativePhase.source_center_derivative
#print axioms CarryNativePhase.scalar_second_expansion
#print axioms CarryNativePhase.source_center_expansion
#print axioms CarryNativePhase.second_correction_analytic
#print axioms CarryNativePhase.native_quadratic_expansion
#print axioms CarryNativePhase.second_coefficient_physical
#print axioms CarryNativePhase.phase_coefficient_im_physical
#print axioms CarryNativePhase.phase_quadratic_tendsto
#print axioms CarryNativePhase.phase_coefficient_is_native_jet
#print axioms CarryNativePhase.retainedWeight
#print axioms CarryNativePhase.phaseNumerator
#print axioms CarryNativePhase.confluentRetained
#print axioms CarryNativePhase.compensatedGreen
#print axioms CarryNativePhase.compensatedCoefficient
#print axioms CarryNativePhase.mixed_confluent_numerator
#print axioms CarryNativePhase.compensated_source_factor
#print axioms CarryNativePhase.compensated_source_regular
#print axioms CarryNativePhase.native_phase_diagonal_compensation
#print axioms CarryNativePhase.phase_residue_fourth_order
#print axioms CarryNativePhase.analytic_conjugate
#print axioms CarryNativePhase.source_normalized_analytic
#print axioms CarryNativePhase.source_reduced_analytic
#print axioms CarryNativePhase.source_remainder_row_analytic
#print axioms CarryNativePhase.confluent_retained_row_analytic
#print axioms CarryNativePhase.companion_row_analytic
#print axioms CarryNativePhase.compensated_row_analytic
#print axioms CarryNativePhase.compensated_diagonal_confluence
#print axioms CarryNativePhase.native_ratio_kernel_jet
#print axioms CarryNativePhase.native_ratio_two_offdiagonal_jets
#print axioms CarryNativePhase.phase_obstructs_isolated_hermitian
#print axioms CarryNativePhase.confluent_retained_centered
#print axioms CarryNativePhase.centered_confluent_balance
#print axioms CarryNativePhase.canonical_confluent_pullback

#audit_native_phase orbit
  CarryNativePhase.material_gradient_analytic
  CarryNativePhase.material_boundary_analytic
  CarryNativePhase.material_state_analytic
  CarryNativePhase.sourceCenter
  CarryNativePhase.sourceOverlap
  CarryNativePhase.source_center_analytic
  CarryNativePhase.source_overlap_analytic
  CarryNativePhase.source_center_origin
  CarryNativePhase.source_overlap_origin
  CarryNativePhase.source_overlap_derivative
  CarryNativePhase.native_ratio_analytic
  CarryNativePhase.forcing_scalar_analytic
  CarryNativePhase.dressed_state_analytic
  CarryNativePhase.companion_first_analytic
  CarryNativePhase.compressed_first_analytic
  CarryNativePhase.companion_probe_analytic

#audit_native_phase phase
  CarryNativePhase.materialJetTwo
  CarryNativePhase.secondCorrection
  CarryNativePhase.phaseCoefficient
  CarryNativePhase.source_center_derivative
  CarryNativePhase.scalar_second_expansion
  CarryNativePhase.source_center_expansion
  CarryNativePhase.second_correction_analytic
  CarryNativePhase.native_quadratic_expansion
  CarryNativePhase.second_coefficient_physical
  CarryNativePhase.phase_coefficient_im_physical
  CarryNativePhase.phase_quadratic_tendsto
  CarryNativePhase.phase_coefficient_is_native_jet

#audit_native_phase ledger
  CarryNativePhase.retainedWeight
  CarryNativePhase.phaseNumerator
  CarryNativePhase.confluentRetained
  CarryNativePhase.compensatedGreen
  CarryNativePhase.compensatedCoefficient
  CarryNativePhase.mixed_confluent_numerator
  CarryNativePhase.compensated_source_factor
  CarryNativePhase.compensated_source_regular
  CarryNativePhase.native_phase_diagonal_compensation
  CarryNativePhase.phase_residue_fourth_order

#audit_native_phase confluence
  CarryNativePhase.analytic_conjugate
  CarryNativePhase.source_normalized_analytic
  CarryNativePhase.source_reduced_analytic
  CarryNativePhase.source_remainder_row_analytic
  CarryNativePhase.confluent_retained_row_analytic
  CarryNativePhase.companion_row_analytic
  CarryNativePhase.compensated_row_analytic
  CarryNativePhase.compensated_diagonal_confluence
  CarryNativePhase.native_ratio_kernel_jet
  CarryNativePhase.native_ratio_two_offdiagonal_jets
  CarryNativePhase.phase_obstructs_isolated_hermitian
  CarryNativePhase.confluent_retained_centered
  CarryNativePhase.centered_confluent_balance
  CarryNativePhase.canonical_confluent_pullback
