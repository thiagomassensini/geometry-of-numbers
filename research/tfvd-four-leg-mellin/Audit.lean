import C2CellStep
import Lean

open Lean Elab Command
elab "#audit_theta_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden moment-derived or sign consumer: {name}"
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
  logInfo m!"TFVD four-leg Mellin audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment-derived constructions and sign consumers absent"

#print axioms CarryFourLeg.heatEdge
#print axioms CarryFourLeg.heat_edge_continuous
#print axioms CarryFourLeg.heat_edge_norm_le
#print axioms CarryFourLeg.heat_edge_mellin
#print axioms CarryFourLeg.native_gradient_hasDerivAt
#print axioms CarryFourLeg.heat_edge_trace_calibration
#print axioms CarryFourLeg.materialEdgeTrace
#print axioms CarryFourLeg.material_edge_trace_eq
#print axioms CarryFourLeg.mixed_value_decode
#print axioms CarryFourLeg.mixed_log_decode
#print axioms CarryFourLeg.addressedGradientLegs
#print axioms CarryFourLeg.original_mixed_legs_addresses
#print axioms CarryFourLeg.heatMixedLegs
#print axioms CarryFourLeg.heat_mixed_legs_calibration
#print axioms CarryFourLeg.original_four_legs_mellin
#print axioms CarryFourLeg.middle_value_edge_shared
#print axioms CarryFourLeg.middle_log_edge_shared
#print axioms CarryFourLeg.materialHeadTrace
#print axioms CarryFourLeg.material_head_trace_eq
#print axioms CarryFourLeg.heatReadoutResiduals
#print axioms CarryFourLeg.originalReadoutResiduals
#print axioms CarryFourLeg.four_readout_residuals_mellin
#print axioms CarryFourLeg.heatReadoutCorrection
#print axioms CarryFourLeg.heat_readout_eq_original_ledger
#print axioms CarryFourLeg.heat_crosses_eq_original_ledger
#print axioms CarryFourLeg.native_ledger_with_mellin_readout
#print axioms CarryFourLeg.bracket_variable_rotation_defect
#print axioms CarryFourLeg.trace_variable_rotation_defect
#print axioms CarryFourLeg.scalar_bracket_multiplier_defect
#print axioms CarryFourLeg.scalar_trace_multiplier_defect
#print axioms CarryFourLeg.multiplier_tfvd_reconstruction
#print axioms CarryFourLeg.c2_material_wave_step
#print axioms CarryFourLeg.c2_material_correction_norm
#print axioms CarryFourLeg.c2_phase_correction_hasDerivAt
#print axioms CarryFourLeg.c2_material_amplitude_factor
#print axioms CarryFourLeg.one_block_value_legs
#print axioms CarryFourLeg.one_block_log_legs
#print axioms CarryFourLeg.one_block_right_residual
#print axioms CarryFourLeg.nat_term_at_real
#print axioms CarryFourLeg.one_block_right_residual_at_center
#print axioms CarryFourLeg.one_block_right_residual_center_gt_one
#print axioms CarryFourLeg.one_block_right_residual_center_ne_zero
#print axioms CarryFourLeg.zero_time_leg_phase
#print axioms CarryFourLeg.dilated_middle_addresses_distinct
#print axioms CarryFourLeg.c2LegLogIncrement
#print axioms CarryFourLeg.c2LegWaveFactor
#print axioms CarryFourLeg.c2LegJet
#print axioms CarryFourLeg.c2LegTransfer
#print axioms CarryFourLeg.c2_leg_jet_step
#print axioms CarryFourLeg.c2_two_leg_green_defect
#print axioms CarryFourLeg.nativePointJet
#print axioms CarryFourLeg.nativeGradientJet
#print axioms CarryFourLeg.native_gradient_jet_eq
#print axioms CarryFourLeg.transportedC2Cell
#print axioms CarryFourLeg.transported_c2_cell_eq
#print axioms CarryFourLeg.one_block_c2_cells_before_step
#print axioms CarryFourLeg.one_block_c2_cells_after_step
#print axioms CarryFourLeg.one_block_middle_splits_at_one

#audit_theta_transport
  CarryFourLeg.heatEdge
  CarryFourLeg.heat_edge_continuous
  CarryFourLeg.heat_edge_norm_le
  CarryFourLeg.heat_edge_mellin
  CarryFourLeg.native_gradient_hasDerivAt
  CarryFourLeg.heat_edge_trace_calibration
  CarryFourLeg.materialEdgeTrace
  CarryFourLeg.material_edge_trace_eq
  CarryFourLeg.mixed_value_decode
  CarryFourLeg.mixed_log_decode
  CarryFourLeg.addressedGradientLegs
  CarryFourLeg.original_mixed_legs_addresses
  CarryFourLeg.heatMixedLegs
  CarryFourLeg.heat_mixed_legs_calibration
  CarryFourLeg.original_four_legs_mellin
  CarryFourLeg.middle_value_edge_shared
  CarryFourLeg.middle_log_edge_shared
  CarryFourLeg.materialHeadTrace
  CarryFourLeg.material_head_trace_eq
  CarryFourLeg.heatReadoutResiduals
  CarryFourLeg.originalReadoutResiduals
  CarryFourLeg.four_readout_residuals_mellin
  CarryFourLeg.heatReadoutCorrection
  CarryFourLeg.heat_readout_eq_original_ledger
  CarryFourLeg.heat_crosses_eq_original_ledger
  CarryFourLeg.native_ledger_with_mellin_readout
  CarryFourLeg.bracket_variable_rotation_defect
  CarryFourLeg.trace_variable_rotation_defect
  CarryFourLeg.scalar_bracket_multiplier_defect
  CarryFourLeg.scalar_trace_multiplier_defect
  CarryFourLeg.multiplier_tfvd_reconstruction
  CarryFourLeg.c2_material_wave_step
  CarryFourLeg.c2_material_correction_norm
  CarryFourLeg.c2_phase_correction_hasDerivAt
  CarryFourLeg.c2_material_amplitude_factor
  CarryFourLeg.one_block_value_legs
  CarryFourLeg.one_block_log_legs
  CarryFourLeg.one_block_right_residual
  CarryFourLeg.nat_term_at_real
  CarryFourLeg.one_block_right_residual_at_center
  CarryFourLeg.one_block_right_residual_center_gt_one
  CarryFourLeg.one_block_right_residual_center_ne_zero
  CarryFourLeg.zero_time_leg_phase
  CarryFourLeg.dilated_middle_addresses_distinct
  CarryFourLeg.c2LegLogIncrement
  CarryFourLeg.c2LegWaveFactor
  CarryFourLeg.c2LegJet
  CarryFourLeg.c2LegTransfer
  CarryFourLeg.c2_leg_jet_step
  CarryFourLeg.c2_two_leg_green_defect
  CarryFourLeg.nativePointJet
  CarryFourLeg.nativeGradientJet
  CarryFourLeg.native_gradient_jet_eq
  CarryFourLeg.transportedC2Cell
  CarryFourLeg.transported_c2_cell_eq
  CarryFourLeg.one_block_c2_cells_before_step
  CarryFourLeg.one_block_c2_cells_after_step
  CarryFourLeg.one_block_middle_splits_at_one
