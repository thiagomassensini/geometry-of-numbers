import TwelveNative
import Lean
open Lean Elab Command
elab "#audit_flow " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySixthOdd.sixth_odd_pivot_pos,
    `CarrySixthOdd.sixth_ordered_odd_pivot_pos,
    `CarrySixthOdd.sixth_odd_sourceRemainder_pos,
    `CarrySixthOdd.sixth_odd_literal_theta_gate,
    `CarrySixthOdd.sixth_odd_integral_gate,
    `CarrySixthOdd.both_six_source_sectors_posDef,
    `CarrySixthOdd.twelve_boundary_margin,
    `CarrySixthOdd.correctedGreen_twelve_physical_realization,
    `CarrySixthOdd.canonical_twelve_physical_realization,
    `CarrySixthOdd.sixth_odd_eventually_above_pivot,
    `CarrySixthOdd.trial_sixth_lower_check,
    `CarrySixthOdd.trial_six_rectangle_check,
    `CarrySixthOdd.trial_sixth_pivot_bounds,
    `CarrySixthOdd.trial_six_pivots_pos,
    `CarrySixthOdd.trial_six_posDef,
    `CarrySixthOdd.sixth_odd_criticalMargin,
    `CarrySixthOdd.sixth_odd_sourceThetaGap_pos,
    `CarrySixthOdd.sixth_odd_theta_integral_certificate,
    `CarrySixthOdd.twelve_boundary_positive,
    `CarrySixthOdd.twelve_return_eventually_contractive,
    `CarryEffectiveRadial.six_effective_anchor_positive,
    `CarryEffectiveRadial.six_boundary_positive_from_effective_budget,
    `CarryMaterialVariation.six_critical_correction_positive,
    `CarryMaterialVariation.six_energy_eventually_above,
    `CarryMaterialVariation.six_original_eventually_above,
    `CarryBoundaryReconstruction.six_physical_eventually_decreasing,
    `CarryBoundaryReconstruction.six_boundary_tail,
    `CarryBoundaryReconstruction.six_accumulated_tail_scale,
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarryIntegralCertificate.material_fourth_pivot_bounds_integral,
    `CarryIntegralCertificate.material_fourth_pivot_pos_integral,
    `CarryIntegralCertificate.material_fourth_block_posDef_integral,
    `CarryIntegralCertificate.material_fourth_critical_positive_integral,
    `CarryIntegralCertificate.material_fourth_theta_integral_gate,
    `CarryIntegralCertificate.material_fourth_cholesky_integral]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for a in (← collectAxioms decl) do
      unless allowed.contains a do throwError "Unexpected axiom in {decl}: {a}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden finite positivity/equivalence dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing declaration: {name}"
  for required in #[`CarrySixthOdd.mem_thetaTwentyFourBox,
      `CarrySixthOdd.mem_trialPairingBox,
      `CarryThetaPattern.odd_source_five_posDef,
      `CarrySixthRelative.transformed_old_coercive,
      `CarrySixthRelative.congruence_inverse_residual,
      `CarryDirectAnchor.finite_energy_direct_error,
      `CarryExplicitBudget.finite_odd_critical_anchor_of_relative_budget,
      `CarryVariationalSchur.sourceTrialEnergy_eq_schur_add_residual_of_isUnit,
      `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; sixth-pivot positivity forbidden, old prefix allowed"

#print axioms CarrySixthRelative.twelve_coeff_last
#print axioms CarrySixthRelative.twelve_old_isUnit
#print axioms CarrySixthRelative.twelve_trialFin_coeff
#print axioms CarrySixthRelative.twelve_pairing_eq_original_form
#print axioms CarrySixthRelative.twelve_pairing_lower
#print axioms CarrySixthRelative.twelve_trial_form_lower
#print axioms CarrySixthRelative.oldCoordinate_upper
#print axioms CarrySixthRelative.oldCoordinate_isUnit
#print axioms CarrySixthRelative.oldCoordinate_mulVec_injective
#print axioms CarrySixthRelative.transformedOld_posDef
#print axioms CarrySixthRelative.old_trial_last_row_zero
#print axioms CarrySixthRelative.trialPairing_old_truncated
#print axioms CarrySixthRelative.transformedOld_entry
#print axioms CarrySixthRelative.transformed_diag_lower
#print axioms CarrySixthRelative.transformed_offdiag_abs
#print axioms CarrySixthRelative.mixed_entry_lower
#print axioms CarrySixthRelative.transformed_old_coercive
#print axioms CarrySixthRelative.congruence_inverse_residual
#print axioms CarrySixthRelative.twelve_residual_component
#print axioms CarrySixthRelative.twelve_trial_cross_expand
#print axioms CarrySixthRelative.transformed_residual_entry
#print axioms CarrySixthRelative.trial_cross_bounded
#print axioms CarrySixthRelative.transformed_residual_bounded
#print axioms CarrySixthRelative.transformed_residual_square_bound
#print axioms CarrySixthRelative.original_inverse_correction_upper
#print axioms CarrySixthRelative.twelve_trial_form_identity
#print axioms CarrySixthRelative.twelve_trial_physical_eventually_lower
#print axioms CarrySixthRelative.twelve_relative_budget_eventually
#print axioms CarrySixthRelative.twelve_critical_anchor_eventually
#print axioms CarrySixthRelative.twelve_critical_anchor_exists
#print axioms CarrySixthRelative.twelve_critical_anchor_exists_after_grid
#print axioms CarrySixthRelative.twelve_critical_form_positive_from_anchor
#print axioms CarrySixthRelative.sixth_odd_schur_positive_via_relative_source
#print axioms CarrySixthRelative.twelve_original_boundary_positive_via_relative_source

#audit_flow
  CarrySixthRelative.twelve_trial_form_lower
  CarrySixthRelative.transformed_old_coercive
  CarrySixthRelative.original_inverse_correction_upper
  CarrySixthRelative.twelve_relative_budget_eventually
  CarrySixthRelative.twelve_critical_anchor_eventually
  CarrySixthRelative.sixth_odd_schur_positive_via_relative_source
  CarrySixthRelative.twelve_original_boundary_positive_via_relative_source
