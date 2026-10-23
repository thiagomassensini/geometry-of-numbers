import Regression
import Lean

open Lean Elab Command
elab "#audit_two_even " mode:ident ids:ident+ : command => do
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
  logInfo m!"Two-even-jet audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryTwoEvenJets.polarizedQuartic
#print axioms CarryTwoEvenJets.quartic
#print axioms CarryTwoEvenJets.nativeEvenJets
#print axioms CarryTwoEvenJets.native_three_convolutions
#print axioms CarryTwoEvenJets.determinant_clear_of_convolutions
#print axioms CarryTwoEvenJets.native_two_even_determinant_clear
#print axioms CarryTwoEvenJets.response_two_even_determinant
#print axioms CarryTwoEvenJets.tracePiece
#print axioms CarryTwoEvenJets.headTrace
#print axioms CarryTwoEvenJets.tailTrace
#print axioms CarryTwoEvenJets.tracePiece_add
#print axioms CarryTwoEvenJets.stateTrace_head_tail
#print axioms CarryTwoEvenJets.completedTrace_head_tail
#print axioms CarryTwoEvenJets.valueMultiplier
#print axioms CarryTwoEvenJets.completedCell
#print axioms CarryTwoEvenJets.head_value_formula
#print axioms CarryTwoEvenJets.head_value_seed_cells
#print axioms CarryTwoEvenJets.head_value_succ
#print axioms CarryTwoEvenJets.valueMultiplier_analytic
#print axioms CarryTwoEvenJets.head_value_analytic
#print axioms CarryTwoEvenJets.completedCell_analytic
#print axioms CarryTwoEvenJets.full_value_eventually_head_tail
#print axioms CarryTwoEvenJets.tail_value_analytic
#print axioms CarryTwoEvenJets.sourceJet
#print axioms CarryTwoEvenJets.headEvenJets
#print axioms CarryTwoEvenJets.tailEvenJets
#print axioms CarryTwoEvenJets.cellEvenJets
#print axioms CarryTwoEvenJets.sourceJet_add
#print axioms CarryTwoEvenJets.full_even_jets_head_tail
#print axioms CarryTwoEvenJets.odd_jets_head_tail_cancel
#print axioms CarryTwoEvenJets.head_even_jets_succ
#print axioms CarryTwoEvenJets.polarizedQuartic_add_four
#print axioms CarryTwoEvenJets.quarticFlux
#print axioms CarryTwoEvenJets.quartic_add_flux
#print axioms CarryTwoEvenJets.quartic_prefix_flux
#print axioms CarryTwoEvenJets.determinantTail
#print axioms CarryTwoEvenJets.native_prefix_flux
#print axioms CarryTwoEvenJets.native_two_even_tfvd_ledger
#print axioms CarryTwoEvenJets.determinantTail_step
#print axioms CarryTwoEvenJets.native_two_even_residual
#print axioms CarryTwoEvenJets.native_two_even_critical_residual
#print axioms CarryTwoEvenJets.native_center_real
#print axioms CarryTwoEvenJets.native_center_eq_ofReal
#print axioms CarryTwoEvenJets.native_center_re_ne_zero
#print axioms CarryTwoEvenJets.native_center_fourth_pos
#print axioms CarryTwoEvenJets.native_real_determinant
#print axioms CarryTwoEvenJets.native_real_tfvd_ledger
#print axioms CarryTwoEvenJets.polarizedQuartic_norm_le
#print axioms CarryTwoEvenJets.quartic_difference
#print axioms CarryTwoEvenJets.quartic_unit_error
#print axioms CarryTwoEvenJets.reference
#print axioms CarryTwoEvenJets.fourJetTolerance
#print axioms CarryTwoEvenJets.reference_norm
#print axioms CarryTwoEvenJets.reference_quartic_lower
#print axioms CarryTwoEvenJets.four_jet_error_suffices
#print axioms CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes

#audit_two_even invariant
  CarryTwoEvenJets.polarizedQuartic
  CarryTwoEvenJets.quartic
  CarryTwoEvenJets.nativeEvenJets
  CarryTwoEvenJets.native_three_convolutions
  CarryTwoEvenJets.determinant_clear_of_convolutions
  CarryTwoEvenJets.native_two_even_determinant_clear
  CarryTwoEvenJets.response_two_even_determinant

#audit_two_even complete_trace
  CarryTwoEvenJets.tracePiece
  CarryTwoEvenJets.headTrace
  CarryTwoEvenJets.tailTrace
  CarryTwoEvenJets.tracePiece_add
  CarryTwoEvenJets.stateTrace_head_tail
  CarryTwoEvenJets.completedTrace_head_tail
  CarryTwoEvenJets.valueMultiplier
  CarryTwoEvenJets.completedCell
  CarryTwoEvenJets.head_value_formula
  CarryTwoEvenJets.head_value_seed_cells
  CarryTwoEvenJets.head_value_succ
  CarryTwoEvenJets.valueMultiplier_analytic
  CarryTwoEvenJets.head_value_analytic
  CarryTwoEvenJets.completedCell_analytic
  CarryTwoEvenJets.full_value_eventually_head_tail
  CarryTwoEvenJets.tail_value_analytic
  CarryTwoEvenJets.sourceJet
  CarryTwoEvenJets.headEvenJets
  CarryTwoEvenJets.tailEvenJets
  CarryTwoEvenJets.cellEvenJets
  CarryTwoEvenJets.sourceJet_add
  CarryTwoEvenJets.full_even_jets_head_tail
  CarryTwoEvenJets.odd_jets_head_tail_cancel
  CarryTwoEvenJets.head_even_jets_succ

#audit_two_even cutoff_flux
  CarryTwoEvenJets.polarizedQuartic_add_four
  CarryTwoEvenJets.quarticFlux
  CarryTwoEvenJets.quartic_add_flux
  CarryTwoEvenJets.quartic_prefix_flux
  CarryTwoEvenJets.determinantTail
  CarryTwoEvenJets.native_prefix_flux
  CarryTwoEvenJets.native_two_even_tfvd_ledger
  CarryTwoEvenJets.determinantTail_step
  CarryTwoEvenJets.native_two_even_residual
  CarryTwoEvenJets.native_two_even_critical_residual

#audit_two_even real_ledger
  CarryTwoEvenJets.native_center_real
  CarryTwoEvenJets.native_center_eq_ofReal
  CarryTwoEvenJets.native_center_re_ne_zero
  CarryTwoEvenJets.native_center_fourth_pos
  CarryTwoEvenJets.native_real_determinant
  CarryTwoEvenJets.native_real_tfvd_ledger

#audit_two_even error
  CarryTwoEvenJets.polarizedQuartic_norm_le
  CarryTwoEvenJets.quartic_difference
  CarryTwoEvenJets.quartic_unit_error

#audit_two_even rational_sufficiency
  CarryTwoEvenJets.reference
  CarryTwoEvenJets.fourJetTolerance
  CarryTwoEvenJets.reference_norm
  CarryTwoEvenJets.reference_quartic_lower
  CarryTwoEvenJets.four_jet_error_suffices
  CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes
