import NativeCompletion
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
  logInfo m!"Native camera tail Mellin audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment-derived constructions and sign consumers absent"

#print axioms CarryCameraTail.heat
#print axioms CarryCameraTail.cameraHeatBlock
#print axioms CarryCameraTail.cameraHeatTail
#print axioms CarryCameraTail.cameraHeatPrefix
#print axioms CarryCameraTail.heat_antitone
#print axioms CarryCameraTail.summable_heat
#print axioms CarryCameraTail.summable_camera_blocks
#print axioms CarryCameraTail.camera_block_norm_le
#print axioms CarryCameraTail.camera_prefix_norm_le
#print axioms CarryCameraTail.camera_prefix_tendsto
#print axioms CarryCameraTail.camera_tail_norm_le
#print axioms CarryCameraTail.camera_prefix_continuous
#print axioms CarryCameraTail.camera_tail_measurable
#print axioms CarryCameraTail.heat_mellin_convergent
#print axioms CarryCameraTail.camera_block_mellin_convergent
#print axioms CarryCameraTail.camera_block_mellin
#print axioms CarryCameraTail.camera_prefix_mellin_convergent
#print axioms CarryCameraTail.camera_prefix_mellin
#print axioms CarryCameraTail.mellin_heat_bound_integrable
#print axioms CarryCameraTail.camera_prefix_mellin_tendsto
#print axioms CarryCameraTail.camera_tail_mellin
#print axioms CarryCameraTail.camera_tail_mellin_convergent
#print axioms CarryCameraTail.bounded_heat_mellin_hasDerivAt
#print axioms CarryCameraTail.tail_log_mellin_hasDerivAt
#print axioms CarryCameraTail.tail_native_mellin_hasDerivAt
#print axioms CarryCameraTail.camera_tail_log_mellin
#print axioms CarryCameraTail.heatTailTrace
#print axioms CarryCameraTail.heat_tail_trace_calibration
#print axioms CarryCameraTail.original_stored_tail_trace
#print axioms CarryCameraTail.cameraHeatHead
#print axioms CarryCameraTail.heatTrace
#print axioms CarryCameraTail.nativeHeadTrace
#print axioms CarryCameraTail.nativeTailTrace
#print axioms CarryCameraTail.camera_head_norm_le
#print axioms CarryCameraTail.camera_head_continuous
#print axioms CarryCameraTail.camera_head_mellin_convergent
#print axioms CarryCameraTail.camera_head_mellin
#print axioms CarryCameraTail.camera_head_trace_calibration
#print axioms CarryCameraTail.camera_heat_head_tail
#print axioms CarryCameraTail.original_record_projections_mellin
#print axioms CarryCameraTail.gammaDress_add
#print axioms CarryCameraTail.completed_heat_trace_calibration
#print axioms CarryCameraTail.completed_heat_green_four_crosses
#print axioms CarryCameraTail.completed_heat_green_gamma_defect
#print axioms CarryCameraTail.camera_tail_tendsto_zero
#print axioms CarryCameraTail.tailErrorIntegrand
#print axioms CarryCameraTail.heatErrorMajorant
#print axioms CarryCameraTail.heat_error_majorant_integrable
#print axioms CarryCameraTail.tail_error_integrand_eq_weight
#print axioms CarryCameraTail.tail_error_integrand_le
#print axioms CarryCameraTail.weighted_camera_tail_error_tendsto_zero
#print axioms CarryCameraTail.gammaUndress
#print axioms CarryCameraTail.gammaUndress_gammaDress
#print axioms CarryCameraTail.gammaDress_gammaUndress
#print axioms CarryCameraTail.gammaUndress_add
#print axioms CarryCameraTail.native_head_from_heat
#print axioms CarryCameraTail.native_tail_from_heat
#print axioms CarryCameraTail.mellinCompletionDefect
#print axioms CarryCameraTail.mellin_completion_eq_original_ledger
#print axioms CarryCameraTail.native_ledger_with_mellin_completion
#print axioms CarryCameraTail.nativeCompletionTrace
#print axioms CarryCameraTail.native_completed_trace_from_mellin
#print axioms CarryCameraTail.nativeCompletionTrace_add
#print axioms CarryCameraTail.completedHeatHead
#print axioms CarryCameraTail.completedHeatTail
#print axioms CarryCameraTail.original_completed_trace_head_tail
#print axioms CarryCameraTail.completed_native_green_four_crosses

#audit_theta_transport
  CarryCameraTail.heat
  CarryCameraTail.cameraHeatBlock
  CarryCameraTail.cameraHeatTail
  CarryCameraTail.cameraHeatPrefix
  CarryCameraTail.heat_antitone
  CarryCameraTail.summable_heat
  CarryCameraTail.summable_camera_blocks
  CarryCameraTail.camera_block_norm_le
  CarryCameraTail.camera_prefix_norm_le
  CarryCameraTail.camera_prefix_tendsto
  CarryCameraTail.camera_tail_norm_le
  CarryCameraTail.camera_prefix_continuous
  CarryCameraTail.camera_tail_measurable
  CarryCameraTail.heat_mellin_convergent
  CarryCameraTail.camera_block_mellin_convergent
  CarryCameraTail.camera_block_mellin
  CarryCameraTail.camera_prefix_mellin_convergent
  CarryCameraTail.camera_prefix_mellin
  CarryCameraTail.mellin_heat_bound_integrable
  CarryCameraTail.camera_prefix_mellin_tendsto
  CarryCameraTail.camera_tail_mellin
  CarryCameraTail.camera_tail_mellin_convergent
  CarryCameraTail.bounded_heat_mellin_hasDerivAt
  CarryCameraTail.tail_log_mellin_hasDerivAt
  CarryCameraTail.tail_native_mellin_hasDerivAt
  CarryCameraTail.camera_tail_log_mellin
  CarryCameraTail.heatTailTrace
  CarryCameraTail.heat_tail_trace_calibration
  CarryCameraTail.original_stored_tail_trace
  CarryCameraTail.cameraHeatHead
  CarryCameraTail.heatTrace
  CarryCameraTail.nativeHeadTrace
  CarryCameraTail.nativeTailTrace
  CarryCameraTail.camera_head_norm_le
  CarryCameraTail.camera_head_continuous
  CarryCameraTail.camera_head_mellin_convergent
  CarryCameraTail.camera_head_mellin
  CarryCameraTail.camera_head_trace_calibration
  CarryCameraTail.camera_heat_head_tail
  CarryCameraTail.original_record_projections_mellin
  CarryCameraTail.gammaDress_add
  CarryCameraTail.completed_heat_trace_calibration
  CarryCameraTail.completed_heat_green_four_crosses
  CarryCameraTail.completed_heat_green_gamma_defect
  CarryCameraTail.camera_tail_tendsto_zero
  CarryCameraTail.tailErrorIntegrand
  CarryCameraTail.heatErrorMajorant
  CarryCameraTail.heat_error_majorant_integrable
  CarryCameraTail.tail_error_integrand_eq_weight
  CarryCameraTail.tail_error_integrand_le
  CarryCameraTail.weighted_camera_tail_error_tendsto_zero
  CarryCameraTail.gammaUndress
  CarryCameraTail.gammaUndress_gammaDress
  CarryCameraTail.gammaDress_gammaUndress
  CarryCameraTail.gammaUndress_add
  CarryCameraTail.native_head_from_heat
  CarryCameraTail.native_tail_from_heat
  CarryCameraTail.mellinCompletionDefect
  CarryCameraTail.mellin_completion_eq_original_ledger
  CarryCameraTail.native_ledger_with_mellin_completion
  CarryCameraTail.nativeCompletionTrace
  CarryCameraTail.native_completed_trace_from_mellin
  CarryCameraTail.nativeCompletionTrace_add
  CarryCameraTail.completedHeatHead
  CarryCameraTail.completedHeatTail
  CarryCameraTail.original_completed_trace_head_tail
  CarryCameraTail.completed_native_green_four_crosses
