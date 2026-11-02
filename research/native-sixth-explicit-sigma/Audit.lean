import TwelveNative
import RadialCutoff
import SigmaQuadratic
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
      `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy,
      `CarrySigmaSource.displaced_log_jet_eq_green,
      `CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
      `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; sixth-pivot positivity forbidden, old prefix allowed"

#print axioms CarrySixthExplicit.congruence_inverse_apply
#print axioms CarrySixthExplicit.transformed_solve_norm_bound
#print axioms CarrySixthExplicit.transformed_solve_component_bound
#print axioms CarrySixthExplicit.old_coordinate_entry_bound
#print axioms CarrySixthExplicit.original_solve_correction_bound
#print axioms CarrySixthExplicit.twelve_trial_coefficient_bound
#print axioms CarrySixthExplicit.critical_old_coefficient_identity
#print axioms CarrySixthExplicit.critical_coefficient_bound
#print axioms CarrySixthExplicit.pair_constant_symmetric
#print axioms CarrySixthExplicit.sixth_pair_constants_bounded
#print axioms CarrySixthExplicit.twelve_pair_constants_bounded
#print axioms CarrySixthExplicit.explicit_radial_grid_cutoff
#print axioms CarrySixthExplicit.explicit_radial_step
#print axioms CarrySixthExplicit.trial_family_budget_bound
#print axioms CarrySixthExplicit.critical_family_budget_bound
#print axioms CarrySixthExplicit.trial_error_identity
#print axioms CarrySixthExplicit.trial_error_after_cutoff
#print axioms CarrySixthExplicit.critical_error_after_cutoff
#print axioms CarrySixthExplicit.trial_source_lower_after_cutoff
#print axioms CarrySixthExplicit.relative_budget_after_cutoff
#print axioms CarrySixthExplicit.critical_anchor_after_cutoff
#print axioms CarrySixthExplicit.critical_source_lower_after_cutoff
#print axioms CarrySixthExplicit.critical_anchor_at_cutoff
#print axioms CarrySigmaSource.displacedHeight_parameter
#print axioms CarrySigmaSource.displacedHeight_strip
#print axioms CarrySigmaSource.sigma_response_central_axis
#print axioms CarrySigmaSource.sigma_density_center
#print axioms CarrySigmaSource.sigma_log_jet_center_formula
#print axioms CarrySigmaSource.sigma_response_conjugate
#print axioms CarrySigmaSource.sigma_density_even
#print axioms CarrySigmaSource.sigma_log_jet_even
#print axioms CarrySigmaSource.sigma_log_jet_deriv_zero
#print axioms CarrySigmaSource.completed_source_eventually_ne_zero
#print axioms CarrySigmaSource.center_real_source_hasDerivAt
#print axioms CarrySigmaSource.center_real_source_deriv
#print axioms CarrySigmaSource.center_real_source_ne_zero
#print axioms CarrySigmaSource.center_real_source_deriv_zero
#print axioms CarrySigmaSource.center_real_source_second_deriv
#print axioms CarrySigmaSource.center_log_second_deriv
#print axioms CarrySigmaSource.sigma_log_jet_zero_eq_canonical
#print axioms CarrySigmaSource.center_response_real_iteratedDeriv_eventually
#print axioms CarrySigmaSource.center_log_deriv_eventually
#print axioms CarrySigmaSource.sigma_log_jet_center_eq_canonical
#print axioms CarrySigmaSource.sigma_green_center_eq_canonical
#print axioms CarrySigmaSource.sigma_path_real_hasDerivAt
#print axioms CarrySigmaSource.sigma_green_raw_second_deriv
#print axioms CarrySigmaSource.sigma_green_curvature_at_center
#print axioms CarrySigmaSource.log_density_hasDerivAt
#print axioms CarrySigmaSource.analytic_real_iteratedDeriv_at_zero
#print axioms CarrySigmaSource.displaced_green_response_analytic
#print axioms CarrySigmaSource.displaced_log_deriv_eventually
#print axioms CarrySigmaSource.displaced_log_jet_eq_green
#print axioms CarrySigmaSource.sigma_green_raw_second_deriv_at
#print axioms CarrySigmaSource.sigma_green_curvature_at
#print axioms CarrySigmaSource.sigma_log_green_eventuallyEq_at
#print axioms CarrySigmaSource.sigma_log_jet_curvature_at
#print axioms CarrySigmaSource.sigma_log_jet_curvature_center
#print axioms CarrySigmaSource.sigma_green_moment_analytic_center
#print axioms CarrySigmaSource.sigma_log_jet_analytic_center
#print axioms CarrySigmaSource.sigma_moment_form_center
#print axioms CarrySigmaSource.sigma_moment_form_curvature_center
#print axioms CarrySigmaSource.sigma_critical_form_curvature_center
#print axioms CarrySigmaSource.sigma_log_jet_deriv_center
#print axioms CarrySigmaSource.sigma_critical_form_center_eq_schur

#audit_flow
  CarrySixthRelative.twelve_original_boundary_positive_via_relative_source
  CarrySixthExplicit.critical_anchor_at_cutoff
  CarrySixthExplicit.critical_source_lower_after_cutoff
  CarrySixthExplicit.relative_budget_after_cutoff
  CarrySigmaSource.sigma_log_jet_even
  CarrySigmaSource.sigma_log_jet_center_eq_canonical
  CarrySigmaSource.sigma_log_jet_curvature_at
  CarrySigmaSource.sigma_log_jet_curvature_center
  CarrySigmaSource.sigma_moment_form_curvature_center
  CarrySigmaSource.sigma_critical_form_center_eq_schur
