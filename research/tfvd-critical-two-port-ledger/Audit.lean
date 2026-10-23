import Regression
import Lean

open Lean Elab Command
elab "#audit_tfvd_critical " mode:ident ids:ident+ : command => do
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
  logInfo m!"TFVD critical flux audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryTfvdCritical.cauchy_pairing_swap
#print axioms CarryTfvdCritical.secondPort_pairing_change
#print axioms CarryTfvdCritical.portFlux
#print axioms CarryTfvdCritical.twoPort_real_self
#print axioms CarryTfvdCritical.portFlux_add
#print axioms CarryTfvdCritical.twoPort_real_change
#print axioms CarryTfvdCritical.tfvd_head_cross_residual
#print axioms CarryTfvdCritical.fixedMaterial
#print axioms CarryTfvdCritical.canonicalStates
#print axioms CarryTfvdCritical.fullSecond
#print axioms CarryTfvdCritical.headSecond
#print axioms CarryTfvdCritical.errorSecond
#print axioms CarryTfvdCritical.fullSource
#print axioms CarryTfvdCritical.headSource
#print axioms CarryTfvdCritical.headFlux
#print axioms CarryTfvdCritical.correctionFlux
#print axioms CarryTfvdCritical.head_plus_error
#print axioms CarryTfvdCritical.fullSource_eq_original
#print axioms CarryTfvdCritical.fullSource_eventually_eq_original
#print axioms CarryTfvdCritical.full_head_polarized_ledger
#print axioms CarryTfvdCritical.full_head_real_ledger
#print axioms CarryTfvdCritical.errorSecond_determinant
#print axioms CarryTfvdCritical.exact_ratio_denominators_eventually
#print axioms CarryTfvdCritical.jet_form_re_eq_excess
#print axioms CarryTfvdCritical.original_flux_ledger_eventually
#print axioms CarryTfvdCritical.total_flux_tendsto
#print axioms CarryTfvdCritical.critical_total_flux_tendsto
#print axioms CarryTfvdCritical.correctionFlux_abs_bound
#print axioms CarryTfvdCritical.canonicalHeadResponse
#print axioms CarryTfvdCritical.first_even_material
#print axioms CarryTfvdCritical.first_even_head_formula
#print axioms CarryTfvdCritical.first_even_head_normalized
#print axioms CarryTfvdCritical.first_even_head_scaled_tendsto
#print axioms CarryTfvdCritical.convergent_div_radial_scale
#print axioms CarryTfvdCritical.first_even_correction_scaled_tendsto
#print axioms CarryTfvdCritical.fixed_head_no_finite_limit
#print axioms CarryTfvdCritical.fixed_correction_no_finite_limit

#audit_tfvd_critical two_port
  CarryTfvdCritical.cauchy_pairing_swap
  CarryTfvdCritical.secondPort_pairing_change
  CarryTfvdCritical.portFlux
  CarryTfvdCritical.twoPort_real_self
  CarryTfvdCritical.portFlux_add
  CarryTfvdCritical.twoPort_real_change
  CarryTfvdCritical.tfvd_head_cross_residual

#audit_tfvd_critical producer
  CarryTfvdCritical.fixedMaterial
  CarryTfvdCritical.canonicalStates
  CarryTfvdCritical.fullSecond
  CarryTfvdCritical.headSecond
  CarryTfvdCritical.errorSecond
  CarryTfvdCritical.fullSource
  CarryTfvdCritical.headSource
  CarryTfvdCritical.headFlux
  CarryTfvdCritical.correctionFlux
  CarryTfvdCritical.head_plus_error
  CarryTfvdCritical.fullSource_eq_original
  CarryTfvdCritical.fullSource_eventually_eq_original
  CarryTfvdCritical.full_head_polarized_ledger
  CarryTfvdCritical.full_head_real_ledger
  CarryTfvdCritical.errorSecond_determinant
  CarryTfvdCritical.exact_ratio_denominators_eventually

#audit_tfvd_critical critical
  CarryTfvdCritical.jet_form_re_eq_excess
  CarryTfvdCritical.original_flux_ledger_eventually
  CarryTfvdCritical.total_flux_tendsto
  CarryTfvdCritical.critical_total_flux_tendsto
  CarryTfvdCritical.correctionFlux_abs_bound

#audit_tfvd_critical cancellation
  CarryTfvdCritical.canonicalHeadResponse
  CarryTfvdCritical.first_even_material
  CarryTfvdCritical.first_even_head_formula
  CarryTfvdCritical.first_even_head_normalized
  CarryTfvdCritical.first_even_head_scaled_tendsto
  CarryTfvdCritical.convergent_div_radial_scale
  CarryTfvdCritical.first_even_correction_scaled_tendsto
  CarryTfvdCritical.fixed_head_no_finite_limit
  CarryTfvdCritical.fixed_correction_no_finite_limit
