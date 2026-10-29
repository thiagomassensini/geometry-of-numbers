import GreenTransport
import DiscreteSign
import Lean

open Lean Elab Command
elab "#audit_complete_tfvd " mode:ident ids:ident+ : command => do
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
  let forbidden := if mode.getId != `ledger then forbidden ++ #[
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
  logInfo m!"Complete TFVD audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryCompleteTfvd.MaterialTfvdData
#print axioms CarryCompleteTfvd.materialAnalysis
#print axioms CarryCompleteTfvd.materialAnalysis_injective
#print axioms CarryCompleteTfvd.materialCoordinates
#print axioms CarryCompleteTfvd.materialEncode
#print axioms CarryCompleteTfvd.materialDecode
#print axioms CarryCompleteTfvd.material_roundtrip
#print axioms CarryCompleteTfvd.material_data_roundtrip
#print axioms CarryCompleteTfvd.source_data
#print axioms CarryCompleteTfvd.greenOnData
#print axioms CarryCompleteTfvd.pairEncode
#print axioms CarryCompleteTfvd.green_roundtrip
#print axioms CarryCompleteTfvd.original_readout_roundtrip
#print axioms CarryCompleteTfvd.original_pair_reduction_roundtrip
#print axioms CarryCompleteTfvd.verticalGreen
#print axioms CarryCompleteTfvd.verticalReturn
#print axioms CarryCompleteTfvd.vertical_reconstruct
#print axioms CarryCompleteTfvd.vertical_return_idempotent
#print axioms CarryCompleteTfvd.vertical_green_return_zero
#print axioms CarryCompleteTfvd.vertical_return_green_zero
#print axioms CarryCompleteTfvd.vertical_green_idempotent
#print axioms CarryCompleteTfvd.vertical_pairing
#print axioms CarryCompleteTfvd.vertical_energy
#print axioms CarryCompleteTfvd.vertical_green_single_two
#print axioms CarryCompleteTfvd.vertical_mixed_witness
#print axioms CarryCompleteTfvd.vertical_not_orthogonal
#print axioms CarryCompleteTfvd.critical_two_mixed_witness
#print axioms CarryCompleteTfvd.vertical_shift_norm
#print axioms CarryCompleteTfvd.weighted_core_energy
#print axioms CarryCompleteTfvd.plateauEighteen
#print axioms CarryCompleteTfvd.plateau_apply
#print axioms CarryCompleteTfvd.plateau_trace_zero
#print axioms CarryCompleteTfvd.plateau_curvature_energy
#print axioms CarryCompleteTfvd.critical_plateau_negative_laplacian
#print axioms CarryCompleteTfvd.weighted_centered_energy
#print axioms CarryCompleteTfvd.weighted_negative_bulk
#print axioms CarryCompleteTfvd.critical_no_tracezero_laplacian_positive
#print axioms CarryCompleteTfvd.tfvdCompensatedGreen
#print axioms CarryCompleteTfvd.tfvd_compensated_exact
#print axioms CarryCompleteTfvd.tfvd_compensated_confluence
#print axioms CarryCompleteTfvd.tfvdMixedGreen
#print axioms CarryCompleteTfvd.tfvd_mixed_exact
#print axioms CarryCompleteTfvd.tfvdWholeGreen
#print axioms CarryCompleteTfvd.tfvd_whole_factor
#print axioms CarryCompleteTfvd.tfvd_native_residual_regular

#audit_complete_tfvd coordinates
  CarryCompleteTfvd.MaterialTfvdData
  CarryCompleteTfvd.materialAnalysis
  CarryCompleteTfvd.materialAnalysis_injective
  CarryCompleteTfvd.materialCoordinates
  CarryCompleteTfvd.materialEncode
  CarryCompleteTfvd.materialDecode
  CarryCompleteTfvd.material_roundtrip
  CarryCompleteTfvd.material_data_roundtrip
  CarryCompleteTfvd.source_data
  CarryCompleteTfvd.greenOnData
  CarryCompleteTfvd.pairEncode
  CarryCompleteTfvd.green_roundtrip
  CarryCompleteTfvd.original_readout_roundtrip
  CarryCompleteTfvd.original_pair_reduction_roundtrip

#audit_complete_tfvd oblique
  CarryCompleteTfvd.verticalGreen
  CarryCompleteTfvd.verticalReturn
  CarryCompleteTfvd.vertical_reconstruct
  CarryCompleteTfvd.vertical_return_idempotent
  CarryCompleteTfvd.vertical_green_return_zero
  CarryCompleteTfvd.vertical_return_green_zero
  CarryCompleteTfvd.vertical_green_idempotent
  CarryCompleteTfvd.vertical_pairing
  CarryCompleteTfvd.vertical_energy
  CarryCompleteTfvd.vertical_green_single_two
  CarryCompleteTfvd.vertical_mixed_witness
  CarryCompleteTfvd.vertical_not_orthogonal
  CarryCompleteTfvd.critical_two_mixed_witness

#audit_complete_tfvd discrete
  CarryCompleteTfvd.vertical_shift_norm
  CarryCompleteTfvd.weighted_core_energy
  CarryCompleteTfvd.plateauEighteen
  CarryCompleteTfvd.plateau_apply
  CarryCompleteTfvd.plateau_trace_zero
  CarryCompleteTfvd.plateau_curvature_energy
  CarryCompleteTfvd.critical_plateau_negative_laplacian
  CarryCompleteTfvd.weighted_centered_energy
  CarryCompleteTfvd.weighted_negative_bulk
  CarryCompleteTfvd.critical_no_tracezero_laplacian_positive

#audit_complete_tfvd ledger
  CarryCompleteTfvd.tfvdCompensatedGreen
  CarryCompleteTfvd.tfvd_compensated_exact
  CarryCompleteTfvd.tfvd_compensated_confluence
  CarryCompleteTfvd.tfvdMixedGreen
  CarryCompleteTfvd.tfvd_mixed_exact
  CarryCompleteTfvd.tfvdWholeGreen
  CarryCompleteTfvd.tfvd_whole_factor
  CarryCompleteTfvd.tfvd_native_residual_regular
