import DampedCamera
import StencilObstruction
import PR41Bridge
import CentralResidual
import Lean

open Lean Elab Command
elab "#audit_jet_overlap " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := if mode.getId == `structural then #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one]
    else #[]
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
        throwError "Unexpected finite sign dependency: {name}"
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
  logInfo m!"Jet overlap audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryJetOverlap.observedCauchy
#print axioms CarryJetOverlap.observedCauchy_eq
#print axioms CarryJetOverlap.radialOverlap_independent
#print axioms CarryJetOverlap.radialOverlap_closed
#print axioms CarryJetOverlap.observedSynthesis
#print axioms CarryJetOverlap.observedSynthesis_pairing
#print axioms CarryJetOverlap.complement_pairing
#print axioms CarryJetOverlap.complement_zero_sum
#print axioms CarryJetOverlap.complement_zero_sum_nonpos
#print axioms CarryJetOverlap.radialOverlap_zero_one
#print axioms CarryJetOverlap.first_stencil_complement
#print axioms CarryJetOverlap.first_stencil_complement_neg
#print axioms CarryJetOverlap.strip
#print axioms CarryJetOverlap.sourceWeight
#print axioms CarryJetOverlap.variableDefect
#print axioms CarryJetOverlap.overlapCorrection
#print axioms CarryJetOverlap.four_channel_split
#print axioms CarryJetOverlap.source_balance_budget
#print axioms CarryJetOverlap.jet_pairing_source_balance
#print axioms CarryJetOverlap.jetBudget
#print axioms CarryJetOverlap.jetBudget_eq_original_pairing
#print axioms CarryJetOverlap.jetBudget_energy
#print axioms CarryJetOverlap.jetBudget_eventually_close
#print axioms CarryJetOverlap.jetBudget_eventually_energy_control
#print axioms CarryJetOverlap.ambientMatrix
#print axioms CarryJetOverlap.ambientMatrix_eq_kernel
#print axioms CarryJetOverlap.overlapMatrix
#print axioms CarryJetOverlap.overlapMatrix_eq_gram
#print axioms CarryJetOverlap.overlapMatrix_posSemidef
#print axioms CarryJetOverlap.ambientMatrix_posSemidef
#print axioms CarryJetOverlap.dampedCameraMatrix
#print axioms CarryJetOverlap.dampedCameraMatrix_posSemidef
#print axioms CarryJetOverlap.dampedCameraBalance
#print axioms CarryJetOverlap.ambientMatrix_eq_camera
#print axioms CarryJetOverlap.camera_pairing_eq_ambient_sum
#print axioms CarryJetOverlap.camera_sub_overlap_eq_damped
#print axioms CarryJetOverlap.jetBudget_eq_damped_add_defect
#print axioms CarryJetOverlap.dampedCameraBalance_self_nonneg
#print axioms CarryJetOverlap.observedSynthesis_eq_zero_iff
#print axioms CarryJetOverlap.complement_zero_sum_strict
#print axioms CarryJetOverlap.forwardStencil
#print axioms CarryJetOverlap.forwardStencil_sum_zero
#print axioms CarryJetOverlap.forwardStencil_ne_zero
#print axioms CarryJetOverlap.forwardStencil_complement_strict
#print axioms CarryJetOverlap.pr41_residual_exact_budget
#print axioms CarryJetOverlap.pr41_residual_budget_eventually_close
#print axioms CarryJetOverlap.pr41_inverseSchur_budget_eventually_close
#print axioms CarryJetOverlap.centralIndex
#print axioms CarryJetOverlap.centralIndex_tendsto
#print axioms CarryJetOverlap.central_point_eq
#print axioms CarryJetOverlap.centralStrip
#print axioms CarryJetOverlap.centralCoefficients
#print axioms CarryJetOverlap.centralResidual
#print axioms CarryJetOverlap.centralResidual_eventually_eq_negative_old_defect
#print axioms CarryJetOverlap.centralResidual_tendsto_negative_excess
#print axioms CarryJetOverlap.centralResidual_eventually_negative

#audit_jet_overlap structural
  CarryJetOverlap.observedCauchy
  CarryJetOverlap.observedCauchy_eq
  CarryJetOverlap.radialOverlap_independent
  CarryJetOverlap.radialOverlap_closed
  CarryJetOverlap.observedSynthesis
  CarryJetOverlap.observedSynthesis_pairing
  CarryJetOverlap.complement_pairing
  CarryJetOverlap.complement_zero_sum
  CarryJetOverlap.complement_zero_sum_nonpos
  CarryJetOverlap.radialOverlap_zero_one
  CarryJetOverlap.first_stencil_complement
  CarryJetOverlap.first_stencil_complement_neg
  CarryJetOverlap.strip
  CarryJetOverlap.sourceWeight
  CarryJetOverlap.variableDefect
  CarryJetOverlap.overlapCorrection
  CarryJetOverlap.four_channel_split
  CarryJetOverlap.source_balance_budget
  CarryJetOverlap.jet_pairing_source_balance
  CarryJetOverlap.jetBudget
  CarryJetOverlap.jetBudget_eq_original_pairing
  CarryJetOverlap.jetBudget_energy
  CarryJetOverlap.jetBudget_eventually_close
  CarryJetOverlap.jetBudget_eventually_energy_control
  CarryJetOverlap.ambientMatrix
  CarryJetOverlap.ambientMatrix_eq_kernel
  CarryJetOverlap.overlapMatrix
  CarryJetOverlap.overlapMatrix_eq_gram
  CarryJetOverlap.overlapMatrix_posSemidef
  CarryJetOverlap.ambientMatrix_posSemidef
  CarryJetOverlap.dampedCameraMatrix
  CarryJetOverlap.dampedCameraMatrix_posSemidef
  CarryJetOverlap.dampedCameraBalance
  CarryJetOverlap.ambientMatrix_eq_camera
  CarryJetOverlap.camera_pairing_eq_ambient_sum
  CarryJetOverlap.camera_sub_overlap_eq_damped
  CarryJetOverlap.jetBudget_eq_damped_add_defect
  CarryJetOverlap.dampedCameraBalance_self_nonneg
  CarryJetOverlap.observedSynthesis_eq_zero_iff
  CarryJetOverlap.complement_zero_sum_strict
  CarryJetOverlap.forwardStencil
  CarryJetOverlap.forwardStencil_sum_zero
  CarryJetOverlap.forwardStencil_ne_zero
  CarryJetOverlap.forwardStencil_complement_strict
  CarryJetOverlap.pr41_residual_exact_budget
  CarryJetOverlap.pr41_residual_budget_eventually_close
  CarryJetOverlap.pr41_inverseSchur_budget_eventually_close

#audit_jet_overlap central
  CarryJetOverlap.centralIndex
  CarryJetOverlap.centralIndex_tendsto
  CarryJetOverlap.central_point_eq
  CarryJetOverlap.centralStrip
  CarryJetOverlap.centralCoefficients
  CarryJetOverlap.centralResidual
  CarryJetOverlap.centralResidual_eventually_eq_negative_old_defect
  CarryJetOverlap.centralResidual_tendsto_negative_excess
  CarryJetOverlap.centralResidual_eventually_negative
