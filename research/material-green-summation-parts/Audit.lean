import ClockReturnJets
import Lean

open Lean Elab Command
elab "#audit_material_parts " mode:ident ids:ident+ : command => do
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
  logInfo m!"Material parts audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryMaterialParts.endpointFlux
#print axioms CarryMaterialParts.curvatureBulk
#print axioms CarryMaterialParts.polarized_summation_parts
#print axioms CarryMaterialParts.ordinarySamples
#print axioms CarryMaterialParts.clockSamples
#print axioms CarryMaterialParts.ordinary_difference
#print axioms CarryMaterialParts.clock_difference
#print axioms CarryMaterialParts.ordinary_clock_parts
#print axioms CarryMaterialParts.clock_ordinary_parts
#print axioms CarryMaterialParts.MaterialPair
#print axioms CarryMaterialParts.interiorTerm
#print axioms CarryMaterialParts.boundaryGreen
#print axioms CarryMaterialParts.prefixGreen
#print axioms CarryMaterialParts.tailGreen
#print axioms CarryMaterialParts.interior_summable
#print axioms CarryMaterialParts.full_green_series
#print axioms CarryMaterialParts.full_green_head_tail
#print axioms CarryMaterialParts.hidden_interior_exact
#print axioms CarryMaterialParts.hidden_tail_exact
#print axioms CarryMaterialParts.finite_hidden_cancellation
#print axioms CarryMaterialParts.full_hidden_equals_finite
#print axioms CarryMaterialParts.boundary_readout_exact
#print axioms CarryMaterialParts.companionSamples
#print axioms CarryMaterialParts.valueSamples
#print axioms CarryMaterialParts.reducedFirstSamples
#print axioms CarryMaterialParts.reducedSecondSamples
#print axioms CarryMaterialParts.companion_difference
#print axioms CarryMaterialParts.value_difference
#print axioms CarryMaterialParts.reduced_first_difference
#print axioms CarryMaterialParts.reduced_second_difference
#print axioms CarryMaterialParts.nativeFluxBulk
#print axioms CarryMaterialParts.native_interior_parts
#print axioms CarryMaterialParts.native_prefix_parts
#print axioms CarryMaterialParts.native_hidden_prefix_parts
#print axioms CarryMaterialParts.native_tfvd_ledger
#print axioms CarryMaterialParts.native_cutoff_boundary_exact
#print axioms CarryMaterialParts.reducedCellForm
#print axioms CarryMaterialParts.reduced_cell_four_terms
#print axioms CarryMaterialParts.reduced_return_cell_form
#print axioms CarryMaterialParts.reduced_prefix_cell_form
#print axioms CarryMaterialParts.reduced_return_four_cells
#print axioms CarryMaterialParts.reduced_return_tail_defect
#print axioms CarryMaterialParts.nativeBalancedPrefix
#print axioms CarryMaterialParts.native_material_cell_balance
#print axioms CarryMaterialParts.native_balanced_cutoff_independent
#print axioms CarryMaterialParts.native_numerator_jets_cutoff
#print axioms CarryMaterialParts.native_cutoff_canonical_factor
#print axioms CarryMaterialParts.native_cutoff_canonical_regular
#print axioms CarryMaterialParts.material_l1_analytic
#print axioms CarryMaterialParts.l1JetShift
#print axioms CarryMaterialParts.l1JetShift_succ
#print axioms CarryMaterialParts.l1JetShift_analytic
#print axioms CarryMaterialParts.map_l1_jets
#print axioms CarryMaterialParts.cellReturnReadout
#print axioms CarryMaterialParts.cellReturnReadout_apply
#print axioms CarryMaterialParts.cellReturnReadout_source
#print axioms CarryMaterialParts.materialL1Jet
#print axioms CarryMaterialParts.cellJet
#print axioms CarryMaterialParts.return_jet_readout
#print axioms CarryMaterialParts.cell_jet_norm_summable
#print axioms CarryMaterialParts.return_jet_cells
#print axioms CarryMaterialParts.cellJetCoordinate
#print axioms CarryMaterialParts.cell_jet_source
#print axioms CarryMaterialParts.return_jet_head_tail
#print axioms CarryMaterialParts.return_jet_tail_bound
#print axioms CarryMaterialParts.return_jet_tail_tendsto
#print axioms CarryMaterialParts.return_jet_norm_tail_tendsto
#print axioms CarryMaterialParts.material_clock_l1_analytic
#print axioms CarryMaterialParts.cellReturnReadout_clock_source
#print axioms CarryMaterialParts.materialClockL1Jet
#print axioms CarryMaterialParts.clockCellJet
#print axioms CarryMaterialParts.clock_return_jet_readout
#print axioms CarryMaterialParts.clock_cell_jet_norm_summable
#print axioms CarryMaterialParts.clock_return_jet_cells
#print axioms CarryMaterialParts.clock_cell_jet_source
#print axioms CarryMaterialParts.clock_return_jet_head_tail
#print axioms CarryMaterialParts.clock_return_jet_tail_bound
#print axioms CarryMaterialParts.clock_return_jet_tail_tendsto
#print axioms CarryMaterialParts.clock_return_jet_norm_tail_tendsto

#audit_material_parts parts
  CarryMaterialParts.endpointFlux
  CarryMaterialParts.curvatureBulk
  CarryMaterialParts.polarized_summation_parts
  CarryMaterialParts.ordinarySamples
  CarryMaterialParts.clockSamples
  CarryMaterialParts.ordinary_difference
  CarryMaterialParts.clock_difference
  CarryMaterialParts.ordinary_clock_parts
  CarryMaterialParts.clock_ordinary_parts

#audit_material_parts ledger
  CarryMaterialParts.MaterialPair
  CarryMaterialParts.interiorTerm
  CarryMaterialParts.boundaryGreen
  CarryMaterialParts.prefixGreen
  CarryMaterialParts.tailGreen
  CarryMaterialParts.interior_summable
  CarryMaterialParts.full_green_series
  CarryMaterialParts.full_green_head_tail
  CarryMaterialParts.hidden_interior_exact
  CarryMaterialParts.hidden_tail_exact
  CarryMaterialParts.finite_hidden_cancellation
  CarryMaterialParts.full_hidden_equals_finite
  CarryMaterialParts.boundary_readout_exact

#audit_material_parts native
  CarryMaterialParts.companionSamples
  CarryMaterialParts.valueSamples
  CarryMaterialParts.reducedFirstSamples
  CarryMaterialParts.reducedSecondSamples
  CarryMaterialParts.companion_difference
  CarryMaterialParts.value_difference
  CarryMaterialParts.reduced_first_difference
  CarryMaterialParts.reduced_second_difference
  CarryMaterialParts.nativeFluxBulk
  CarryMaterialParts.native_interior_parts
  CarryMaterialParts.native_prefix_parts
  CarryMaterialParts.native_hidden_prefix_parts
  CarryMaterialParts.native_tfvd_ledger
  CarryMaterialParts.native_cutoff_boundary_exact

#audit_material_parts boundary
  CarryMaterialParts.reducedCellForm
  CarryMaterialParts.reduced_cell_four_terms
  CarryMaterialParts.reduced_return_cell_form
  CarryMaterialParts.reduced_prefix_cell_form
  CarryMaterialParts.reduced_return_four_cells
  CarryMaterialParts.reduced_return_tail_defect
  CarryMaterialParts.nativeBalancedPrefix
  CarryMaterialParts.native_material_cell_balance
  CarryMaterialParts.native_balanced_cutoff_independent
  CarryMaterialParts.native_numerator_jets_cutoff
  CarryMaterialParts.native_cutoff_canonical_factor
  CarryMaterialParts.native_cutoff_canonical_regular

#audit_material_parts jets
  CarryMaterialParts.material_l1_analytic
  CarryMaterialParts.l1JetShift
  CarryMaterialParts.l1JetShift_succ
  CarryMaterialParts.l1JetShift_analytic
  CarryMaterialParts.map_l1_jets
  CarryMaterialParts.cellReturnReadout
  CarryMaterialParts.cellReturnReadout_apply
  CarryMaterialParts.cellReturnReadout_source
  CarryMaterialParts.materialL1Jet
  CarryMaterialParts.cellJet
  CarryMaterialParts.return_jet_readout
  CarryMaterialParts.cell_jet_norm_summable
  CarryMaterialParts.return_jet_cells
  CarryMaterialParts.cellJetCoordinate
  CarryMaterialParts.cell_jet_source
  CarryMaterialParts.return_jet_head_tail
  CarryMaterialParts.return_jet_tail_bound
  CarryMaterialParts.return_jet_tail_tendsto
  CarryMaterialParts.return_jet_norm_tail_tendsto

#audit_material_parts clockjets
  CarryMaterialParts.material_clock_l1_analytic
  CarryMaterialParts.cellReturnReadout_clock_source
  CarryMaterialParts.materialClockL1Jet
  CarryMaterialParts.clockCellJet
  CarryMaterialParts.clock_return_jet_readout
  CarryMaterialParts.clock_cell_jet_norm_summable
  CarryMaterialParts.clock_return_jet_cells
  CarryMaterialParts.clock_cell_jet_source
  CarryMaterialParts.clock_return_jet_head_tail
  CarryMaterialParts.clock_return_jet_tail_bound
  CarryMaterialParts.clock_return_jet_tail_tendsto
  CarryMaterialParts.clock_return_jet_norm_tail_tendsto
