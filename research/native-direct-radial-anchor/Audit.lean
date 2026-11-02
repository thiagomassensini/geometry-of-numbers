import TenNativeBoundary
import Lean
open Lean Elab Command
elab "#audit_flow " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryEffectiveRadial.six_effective_anchor_positive,
    `CarryEffectiveRadial.six_boundary_positive_from_effective_budget,
    `CarryThetaPattern.odd_five_pivots_pos,
    `CarryThetaPattern.fifth_odd_pivot_pos,
    `CarryMaterialVariation.six_critical_correction_positive,
    `CarryMaterialVariation.six_energy_eventually_above,
    `CarryMaterialVariation.six_original_eventually_above,
    `CarryBoundaryReconstruction.six_physical_eventually_decreasing,
    `CarryBoundaryReconstruction.six_boundary_tail,
    `CarryBoundaryReconstruction.six_accumulated_tail_scale,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
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
  for required in #[`CarryIntegralCertificate.material_theta_integral_input,
      `CarryThetaPattern.mem_thetaTwentyBox,
      `NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit,
      `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy,
      `CarryVariationalSchur.sourceTrialEnergy_eq_schur_add_residual_of_isUnit,
      `CarryDirectAnchor.scaled_inverse_residual,
      `CarryDirectAnchor.scaled_inverse_correction_upper,
      `CarryDirectAnchor.finite_energy_direct_error] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#print axioms CarryDirectAnchor.pair_value_error
#print axioms CarryDirectAnchor.finite_energy_direct_error
#print axioms CarryDirectAnchor.diagonal_isUnit
#print axioms CarryDirectAnchor.scaled_old_isUnit
#print axioms CarryDirectAnchor.scaled_inverse_residual
#print axioms CarryDirectAnchor.ten_old_block_isUnit
#print axioms CarryDirectAnchor.ten_original_inverse_correction_upper
#print axioms CarryDirectAnchor.trial_fin_coeff_on_range
#print axioms CarryDirectAnchor.trial_fin_source_equal
#print axioms CarryDirectAnchor.trial_fin_error_equal
#print axioms CarryDirectAnchor.ten_critical_anchor_of_small
#print axioms CarryDirectAnchor.ten_critical_anchor_eventually
#print axioms CarryDirectAnchor.ten_critical_anchor_exists
#print axioms CarryDirectAnchor.ten_pair_constants_bounded
#print axioms CarryDirectAnchor.ten_trial_coefficient_bounded
#print axioms CarryDirectAnchor.ten_trial_budget_bounded
#print axioms CarryDirectAnchor.ten_anchor_step
#print axioms CarryDirectAnchor.ten_anchor_cutoff
#print axioms CarryDirectAnchor.ten_trial_finite_source_lower
#print axioms CarryDirectAnchor.ten_trial_tail_budget
#print axioms CarryDirectAnchor.ten_trial_anchor_dominates_tail
#print axioms CarryDirectAnchor.ten_critical_budget_small_of_cutoff
#print axioms CarryDirectAnchor.ten_critical_anchor_at_explicit_cutoff
#print axioms CarryDirectAnchor.ten_critical_form_positive_from_finite_source
#print axioms CarryDirectAnchor.fifth_odd_schur_positive_via_direct_source
#print axioms CarryDirectAnchor.ten_original_boundary_positive_via_direct_source
#print axioms CarryDirectAnchor.scaled_det_box_mem
#print axioms CarryDirectAnchor.numerator_box_mem
#print axioms CarryDirectAnchor.scaled_det_positive
#print axioms CarryDirectAnchor.numerator_eq_dot
#print axioms CarryDirectAnchor.correction_box_mem
#print axioms CarryDirectAnchor.scaled_inverse_correction_upper
#print axioms CarryDirectAnchor.scale_ne_zero
#print axioms CarryDirectAnchor.entry_box_mem
#print axioms CarryDirectAnchor.residual_box_mem
#print axioms CarryDirectAnchor.minor_box_mem
#print axioms CarryDirectAnchor.adj_box_mem
#print axioms CarryDirectAnchor.source_tenth_box_mem
#print axioms CarryDirectAnchor.source_ninth_box_mem
#print axioms CarryDirectAnchor.moment_box_8_mem
#print axioms CarryDirectAnchor.moment_box_9_mem
#print axioms CarryDirectAnchor.trial_coefficient_box_mem
#print axioms CarryDirectAnchor.ten_moment_box_mem
#print axioms CarryDirectAnchor.trial_head_box_mem
#print axioms CarryDirectAnchor.rational_trial_head_lower
#print axioms CarryDirectAnchor.ten_step_after_anchor
#print axioms CarryDirectAnchor.ten_trial_source_lower_after_anchor
#print axioms CarryDirectAnchor.ten_trial_tail_budget_after_anchor
#print axioms CarryDirectAnchor.finite_odd_form_eq_quadratic
#print axioms CarryDirectAnchor.finite_source_error
#print axioms CarryDirectAnchor.finite_critical_transfer

#audit_flow
  CarryDirectAnchor.ten_critical_anchor_at_explicit_cutoff
  CarryDirectAnchor.fifth_odd_schur_positive_via_direct_source
  CarryDirectAnchor.ten_original_boundary_positive_via_direct_source
  CarryDirectAnchor.ten_trial_finite_source_lower
