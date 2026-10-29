import Regression
import Lean

open Lean Elab Command
elab "#audit_conservative_transport " mode:ident ids:ident+ : command => do
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
  logInfo m!"Native negative direction audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryNegativeDirection.incident_chart_eventually_bijective
#print axioms CarryNegativeDirection.incident_jet_eventually_injective
#print axioms CarryNegativeDirection.invisible_incidence_cannot_return
#print axioms CarryNegativeDirection.source_quadratic_smul
#print axioms CarryNegativeDirection.nullCouplingWitness
#print axioms CarryNegativeDirection.null_coupling_witness_energy
#print axioms CarryNegativeDirection.null_coupling_witness_negative
#print axioms CarryNegativeDirection.psd_extension_annihilates_old_null_crossings
#print axioms CarryNegativeDirection.source_sewing_of_solution
#print axioms CarryNegativeDirection.solution_witness_energy
#print axioms CarryNegativeDirection.solution_residual_independent
#print axioms CarryNegativeDirection.psd_extension_iff_solution_residual
#print axioms CarryNegativeDirection.returnExcess
#print axioms CarryNegativeDirection.returnExcess_tendsto
#print axioms CarryNegativeDirection.negative_boundary_iff_persistent_excess
#print axioms CarryNegativeDirection.returnExcess_eq_neg_storage
#print axioms CarryNegativeDirection.finite_amplification_iff_jet_excess
#print axioms CarryNegativeDirection.negative_boundary_eventually_amplifies
#print axioms CarryNegativeDirection.negative_boundary_regular_witness
#print axioms CarryNegativeDirection.negative_schur_iff_persistent_excess
#print axioms CarryNegativeDirection.canonical_null_crossing_forces_persistent_return
#print axioms CarryNegativeDirection.canonical_solution_residual_forces_persistent_return

#audit_conservative_transport chart
  CarryNegativeDirection.incident_chart_eventually_bijective
  CarryNegativeDirection.incident_jet_eventually_injective
  CarryNegativeDirection.invisible_incidence_cannot_return

#audit_conservative_transport singular
  CarryNegativeDirection.source_quadratic_smul
  CarryNegativeDirection.nullCouplingWitness
  CarryNegativeDirection.null_coupling_witness_energy
  CarryNegativeDirection.null_coupling_witness_negative
  CarryNegativeDirection.psd_extension_annihilates_old_null_crossings
  CarryNegativeDirection.source_sewing_of_solution
  CarryNegativeDirection.solution_witness_energy
  CarryNegativeDirection.solution_residual_independent
  CarryNegativeDirection.psd_extension_iff_solution_residual

#audit_conservative_transport negative_transport
  CarryNegativeDirection.returnExcess
  CarryNegativeDirection.returnExcess_tendsto
  CarryNegativeDirection.negative_boundary_iff_persistent_excess
  CarryNegativeDirection.returnExcess_eq_neg_storage
  CarryNegativeDirection.finite_amplification_iff_jet_excess
  CarryNegativeDirection.negative_boundary_eventually_amplifies
  CarryNegativeDirection.negative_boundary_regular_witness
  CarryNegativeDirection.negative_schur_iff_persistent_excess
  CarryNegativeDirection.canonical_null_crossing_forces_persistent_return
  CarryNegativeDirection.canonical_solution_residual_forces_persistent_return
