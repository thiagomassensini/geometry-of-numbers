import EightNative
import EightQuantitative
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
      `CarrySummableRadial.family_increment_budget,
      `NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit,
      `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#print axioms CarryCriticalRadialMargin.det3_box_mem
#print axioms CarryCriticalRadialMargin.old_det_box_mem
#print axioms CarryCriticalRadialMargin.old_det_box_positive
#print axioms CarryCriticalRadialMargin.old_det_positive
#print axioms CarryCriticalRadialMargin.num0_box_mem
#print axioms CarryCriticalRadialMargin.num1_box_mem
#print axioms CarryCriticalRadialMargin.num2_box_mem
#print axioms CarryCriticalRadialMargin.critical0_box_mem
#print axioms CarryCriticalRadialMargin.critical1_box_mem
#print axioms CarryCriticalRadialMargin.critical2_box_mem
#print axioms CarryCriticalRadialMargin.eight_critical_old_rows
#print axioms CarryCriticalRadialMargin.eight_coeff_box_mem
#print axioms CarryCriticalRadialMargin.eight_moment_box_mem
#print axioms CarryCriticalRadialMargin.eight_head_box_mem
#print axioms CarryCriticalRadialMargin.eight_head_strict_lower
#print axioms CarryCriticalRadialMargin.moment_box_1_mem
#print axioms CarryCriticalRadialMargin.moment_box_2_mem
#print axioms CarryCriticalRadialMargin.moment_box_3_mem
#print axioms CarryCriticalRadialMargin.moment_box_4_mem
#print axioms CarryCriticalRadialMargin.moment_box_5_mem
#print axioms CarryCriticalRadialMargin.moment_box_6_mem
#print axioms CarryCriticalRadialMargin.moment_box_7_mem
#print axioms CarryCriticalRadialMargin.eight_pair_constants_bounded
#print axioms CarryCriticalRadialMargin.eight_coefficient_bounded
#print axioms CarryCriticalRadialMargin.eight_family_constant_bounded
#print axioms CarryCriticalRadialMargin.eight_anchor_error
#print axioms CarryCriticalRadialMargin.eight_anchor_beats_general_tail
#print axioms CarryCriticalRadialMargin.fourth_odd_original_boundary_positive
#print axioms CarryCriticalRadialMargin.eight_general_tail_explicit
#print axioms CarryCriticalRadialMargin.eight_anchor_explicit_lower
#print axioms CarryCriticalRadialMargin.eight_old_matrix_det
#print axioms CarryCriticalRadialMargin.eight_old_matrix_isUnit
#print axioms CarryCriticalRadialMargin.eight_critical_vector_equation
#print axioms CarryCriticalRadialMargin.eight_critical_vector_eq_inverse
#print axioms CarryCriticalRadialMargin.eight_form_eq_source_quadratic
#print axioms CarryCriticalRadialMargin.eight_form_eq_original_schur
#print axioms CarryCriticalRadialMargin.eight_boundary_positive_via_general_tail
#print axioms CarryCriticalRadialMargin.fourth_odd_schur_positive_via_source_anchor
#print axioms CarryCriticalRadialMargin.finite_odd_boundary_positive_of_anchor
#print axioms CarryCriticalRadialMargin.six_boundary_positive_via_general_tail
#print axioms CarryCriticalRadialMargin.six_canonical_form_eq_half_limit
#print axioms CarryCriticalRadialMargin.six_residual_positive_via_general_tail
#print axioms CarryCriticalRadialMargin.six_pair_constants_bounded
#print axioms CarryCriticalRadialMargin.six_coefficient_bounded
#print axioms CarryCriticalRadialMargin.six_family_constant_bounded
#print axioms CarryCriticalRadialMargin.six_anchor_beats_general_tail

#audit_flow
  CarryCriticalRadialMargin.eight_anchor_beats_general_tail
  CarryCriticalRadialMargin.eight_general_tail_explicit
  CarryCriticalRadialMargin.eight_anchor_explicit_lower
  CarryCriticalRadialMargin.fourth_odd_original_boundary_positive
