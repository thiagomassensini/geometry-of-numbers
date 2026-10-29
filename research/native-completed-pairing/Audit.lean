import LowOrderControls
import Lean

open Lean Elab Command
elab "#audit_completed_pairing " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let signs := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial]
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
        throwError "Forbidden downstream sign consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-defined construction: {name}"
      if tier.getNat <= 1 && signs.contains name then
        throwError "Finite sign or theta-moment dependency outside canary: {name}"
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
  logInfo m!"Completed pairing audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryCompletedPairing.valueGain
#print axioms CarryCompletedPairing.jetGain
#print axioms CarryCompletedPairing.companionShear
#print axioms CarryCompletedPairing.native_completion_matrix
#print axioms CarryCompletedPairing.jet_gain_height_factor
#print axioms CarryCompletedPairing.integral_completion_matrix
#print axioms CarryCompletedPairing.CompletionPairingChannels
#print axioms CarryCompletedPairing.CompletionPairingChannels.mk
#print axioms CarryCompletedPairing.CompletionPairingChannels.jetTransport
#print axioms CarryCompletedPairing.CompletionPairingChannels.companionTransport
#print axioms CarryCompletedPairing.CompletionPairingChannels.total
#print axioms CarryCompletedPairing.completionPairingChannels
#print axioms CarryCompletedPairing.native_completion_pairing
#print axioms CarryCompletedPairing.completion_jet_transport_exact
#print axioms CarryCompletedPairing.native_completion_pairing_expanded
#print axioms CarryCompletedPairing.completedIntegralCells
#print axioms CarryCompletedPairing.completedNativeCells
#print axioms CarryCompletedPairing.completed_cells_mellin
#print axioms CarryCompletedPairing.completed_cells_two_inputs
#print axioms CarryCompletedPairing.completed_cell_pairing
#print axioms CarryCompletedPairing.integralMaterialTrace
#print axioms CarryCompletedPairing.integral_material_trace_eq
#print axioms CarryCompletedPairing.integral_material_trace_eq_raw
#print axioms CarryCompletedPairing.completedIntegralTrace
#print axioms CarryCompletedPairing.completed_trace_mellin
#print axioms CarryCompletedPairing.completedIntegralPairing
#print axioms CarryCompletedPairing.completed_pairing_mellin
#print axioms CarryCompletedPairing.completed_pairing_eq_original
#print axioms CarryCompletedPairing.integralHeightReadout
#print axioms CarryCompletedPairing.height_readout_mellin
#print axioms CarryCompletedPairing.integralHeightTail
#print axioms CarryCompletedPairing.height_tail_mellin
#print axioms CarryCompletedPairing.integralArchimedeanChannel
#print axioms CarryCompletedPairing.archimedean_channel_mellin
#print axioms CarryCompletedPairing.integralCompletedChannels
#print axioms CarryCompletedPairing.completed_channels_mellin
#print axioms CarryCompletedPairing.completed_channels_pairing
#print axioms CarryCompletedPairing.mellinResponse
#print axioms CarryCompletedPairing.mellin_response_eventuallyEq
#print axioms CarryCompletedPairing.mellin_response_analyticAt
#print axioms CarryCompletedPairing.mellinMomentKernel
#print axioms CarryCompletedPairing.completed_pairing_normalized
#print axioms CarryCompletedPairing.mellin_response_on_domain
#print axioms CarryCompletedPairing.moment_kernel_from_completed_pairing
#print axioms CarryCompletedPairing.mellin_mixed_jets
#print axioms CarryCompletedPairing.mellin_even_jets
#print axioms CarryCompletedPairing.mellin_shifted_jets
#print axioms CarryCompletedPairing.mellin_even_odd_jets_zero
#print axioms CarryCompletedPairing.mellin_jet_00
#print axioms CarryCompletedPairing.mellin_jet_01
#print axioms CarryCompletedPairing.mellin_jet_11
#print axioms CarryCompletedPairing.value_gain_ne_zero
#print axioms CarryCompletedPairing.completion_preserves_value_distinction
#print axioms CarryCompletedPairing.completion_basis_defect
#print axioms CarryCompletedPairing.completion_basis_defect_ne_zero
#print axioms CarryCompletedPairing.height_readout_defect
#print axioms CarryCompletedPairing.integral_height_readout_defect
#print axioms CarryCompletedPairing.integral_pairing_full_operator
#print axioms CarryCompletedPairing.integral_pairing_chiral_difference
#print axioms CarryCompletedPairing.mellin_response_signed_germ
#print axioms CarryCompletedPairing.normalizedScalarTrace
#print axioms CarryCompletedPairing.normalized_scalar_trace_germ
#print axioms CarryCompletedPairing.projectedEvenJet
#print axioms CarryCompletedPairing.projected_even_jet_exact
#print axioms CarryCompletedPairing.projected_even_gram_00
#print axioms CarryCompletedPairing.projected_even_gram_01
#print axioms CarryCompletedPairing.projected_even_gram_11
#print axioms CarryCompletedPairing.projected_gram_three_defects
#print axioms CarryCompletedPairing.projected_gram_zero_ne_canonical
#print axioms CarryCompletedPairing.projected_gram_cross_ne_canonical
#print axioms CarryCompletedPairing.not_projected_even_gram_representation

#audit_completed_pairing 0
  CarryCompletedPairing.valueGain
  CarryCompletedPairing.jetGain
  CarryCompletedPairing.companionShear
  CarryCompletedPairing.native_completion_matrix
  CarryCompletedPairing.jet_gain_height_factor
  CarryCompletedPairing.integral_completion_matrix
  CarryCompletedPairing.CompletionPairingChannels
  CarryCompletedPairing.CompletionPairingChannels.mk
  CarryCompletedPairing.CompletionPairingChannels.jetTransport
  CarryCompletedPairing.CompletionPairingChannels.companionTransport
  CarryCompletedPairing.CompletionPairingChannels.total
  CarryCompletedPairing.completionPairingChannels
  CarryCompletedPairing.native_completion_pairing
  CarryCompletedPairing.completion_jet_transport_exact
  CarryCompletedPairing.native_completion_pairing_expanded
  CarryCompletedPairing.completedIntegralCells
  CarryCompletedPairing.completedNativeCells
  CarryCompletedPairing.completed_cells_mellin
  CarryCompletedPairing.completed_cells_two_inputs
  CarryCompletedPairing.completed_cell_pairing
  CarryCompletedPairing.integralMaterialTrace
  CarryCompletedPairing.integral_material_trace_eq
  CarryCompletedPairing.integral_material_trace_eq_raw
  CarryCompletedPairing.completedIntegralTrace
  CarryCompletedPairing.completed_trace_mellin
  CarryCompletedPairing.completedIntegralPairing
  CarryCompletedPairing.completed_pairing_mellin
  CarryCompletedPairing.completed_pairing_eq_original
  CarryCompletedPairing.integralHeightReadout
  CarryCompletedPairing.height_readout_mellin
  CarryCompletedPairing.integralHeightTail
  CarryCompletedPairing.height_tail_mellin
  CarryCompletedPairing.integralArchimedeanChannel
  CarryCompletedPairing.archimedean_channel_mellin
  CarryCompletedPairing.integralCompletedChannels
  CarryCompletedPairing.completed_channels_mellin
  CarryCompletedPairing.completed_channels_pairing
  CarryCompletedPairing.mellinResponse
  CarryCompletedPairing.mellinMomentKernel
  CarryCompletedPairing.value_gain_ne_zero
  CarryCompletedPairing.completion_preserves_value_distinction
  CarryCompletedPairing.completion_basis_defect
  CarryCompletedPairing.completion_basis_defect_ne_zero
  CarryCompletedPairing.height_readout_defect
  CarryCompletedPairing.integral_height_readout_defect
  CarryCompletedPairing.normalizedScalarTrace
  CarryCompletedPairing.projectedEvenJet

#audit_completed_pairing 1
  CarryCompletedPairing.mellin_response_eventuallyEq
  CarryCompletedPairing.mellin_response_analyticAt
  CarryCompletedPairing.completed_pairing_normalized
  CarryCompletedPairing.mellin_response_on_domain
  CarryCompletedPairing.moment_kernel_from_completed_pairing
  CarryCompletedPairing.mellin_mixed_jets
  CarryCompletedPairing.mellin_even_jets
  CarryCompletedPairing.mellin_shifted_jets
  CarryCompletedPairing.mellin_even_odd_jets_zero
  CarryCompletedPairing.mellin_jet_00
  CarryCompletedPairing.mellin_jet_01
  CarryCompletedPairing.mellin_jet_11
  CarryCompletedPairing.integral_pairing_full_operator
  CarryCompletedPairing.integral_pairing_chiral_difference
  CarryCompletedPairing.mellin_response_signed_germ
  CarryCompletedPairing.normalized_scalar_trace_germ
  CarryCompletedPairing.projected_even_jet_exact
  CarryCompletedPairing.projected_even_gram_00
  CarryCompletedPairing.projected_even_gram_01
  CarryCompletedPairing.projected_even_gram_11
  CarryCompletedPairing.projected_gram_three_defects

#audit_completed_pairing 2
  CarryCompletedPairing.projected_gram_zero_ne_canonical
  CarryCompletedPairing.projected_gram_cross_ne_canonical
  CarryCompletedPairing.not_projected_even_gram_representation

#audit_completed_pairing 3
  CarryCompletedPairing.valueGain
  CarryCompletedPairing.jetGain
  CarryCompletedPairing.companionShear
  CarryCompletedPairing.native_completion_matrix
  CarryCompletedPairing.jet_gain_height_factor
  CarryCompletedPairing.integral_completion_matrix
  CarryCompletedPairing.CompletionPairingChannels
  CarryCompletedPairing.CompletionPairingChannels.mk
  CarryCompletedPairing.CompletionPairingChannels.jetTransport
  CarryCompletedPairing.CompletionPairingChannels.companionTransport
  CarryCompletedPairing.CompletionPairingChannels.total
  CarryCompletedPairing.completionPairingChannels
  CarryCompletedPairing.native_completion_pairing
  CarryCompletedPairing.completion_jet_transport_exact
  CarryCompletedPairing.native_completion_pairing_expanded
  CarryCompletedPairing.completedIntegralCells
  CarryCompletedPairing.completedNativeCells
  CarryCompletedPairing.completed_cells_mellin
  CarryCompletedPairing.completed_cells_two_inputs
  CarryCompletedPairing.completed_cell_pairing
  CarryCompletedPairing.integralMaterialTrace
  CarryCompletedPairing.integral_material_trace_eq
  CarryCompletedPairing.integral_material_trace_eq_raw
  CarryCompletedPairing.completedIntegralTrace
  CarryCompletedPairing.completed_trace_mellin
  CarryCompletedPairing.completedIntegralPairing
  CarryCompletedPairing.completed_pairing_mellin
  CarryCompletedPairing.completed_pairing_eq_original
  CarryCompletedPairing.integralHeightReadout
  CarryCompletedPairing.height_readout_mellin
  CarryCompletedPairing.integralHeightTail
  CarryCompletedPairing.height_tail_mellin
  CarryCompletedPairing.integralArchimedeanChannel
  CarryCompletedPairing.archimedean_channel_mellin
  CarryCompletedPairing.integralCompletedChannels
  CarryCompletedPairing.completed_channels_mellin
  CarryCompletedPairing.completed_channels_pairing
  CarryCompletedPairing.mellinResponse
  CarryCompletedPairing.mellin_response_eventuallyEq
  CarryCompletedPairing.mellin_response_analyticAt
  CarryCompletedPairing.mellinMomentKernel
  CarryCompletedPairing.completed_pairing_normalized
  CarryCompletedPairing.mellin_response_on_domain
  CarryCompletedPairing.moment_kernel_from_completed_pairing
  CarryCompletedPairing.mellin_mixed_jets
  CarryCompletedPairing.mellin_even_jets
  CarryCompletedPairing.mellin_shifted_jets
  CarryCompletedPairing.mellin_even_odd_jets_zero
  CarryCompletedPairing.mellin_jet_00
  CarryCompletedPairing.mellin_jet_01
  CarryCompletedPairing.mellin_jet_11
  CarryCompletedPairing.value_gain_ne_zero
  CarryCompletedPairing.completion_preserves_value_distinction
  CarryCompletedPairing.completion_basis_defect
  CarryCompletedPairing.completion_basis_defect_ne_zero
  CarryCompletedPairing.height_readout_defect
  CarryCompletedPairing.integral_height_readout_defect
  CarryCompletedPairing.integral_pairing_full_operator
  CarryCompletedPairing.integral_pairing_chiral_difference
  CarryCompletedPairing.mellin_response_signed_germ
  CarryCompletedPairing.normalizedScalarTrace
  CarryCompletedPairing.normalized_scalar_trace_germ
  CarryCompletedPairing.projectedEvenJet
  CarryCompletedPairing.projected_even_jet_exact
  CarryCompletedPairing.projected_even_gram_00
  CarryCompletedPairing.projected_even_gram_01
  CarryCompletedPairing.projected_even_gram_11
  CarryCompletedPairing.projected_gram_three_defects
  CarryCompletedPairing.projected_gram_zero_ne_canonical
  CarryCompletedPairing.projected_gram_cross_ne_canonical
  CarryCompletedPairing.not_projected_even_gram_representation
