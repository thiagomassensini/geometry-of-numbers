import RelativeCertificate
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
      `CarryDirectAnchor.finite_energy_direct_error,
      `CarryVariationalSchur.sourceTrialResidual_inverse_of_isUnit,
      `CarryExplicitBudget.scaled_inverse_apply,
      `CarryExplicitBudget.finite_family_budget_bound,
      `CarryExplicitBudget.finite_odd_critical_anchor_of_relative_budget] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#print axioms CarryExplicitBudget.finite_family_budget_bound
#print axioms CarryExplicitBudget.finite_family_direct_budget_bound
#print axioms CarryExplicitBudget.scaled_inverse_apply
#print axioms CarryExplicitBudget.correction_numerator_box_mem
#print axioms CarryExplicitBudget.correction_box_mem
#print axioms CarryExplicitBudget.correction_bounded
#print axioms CarryExplicitBudget.critical_old_coefficient_identity
#print axioms CarryExplicitBudget.critical_coefficient_bounded
#print axioms CarryExplicitBudget.critical_family_budget_rational
#print axioms CarryExplicitBudget.critical_error_at_numeric_cutoff
#print axioms CarryExplicitBudget.critical_anchor_after_numeric_cutoff
#print axioms CarryExplicitBudget.critical_energy_lower_after_numeric_cutoff
#print axioms CarryExplicitBudget.critical_anchor_at_numeric_cutoff
#print axioms CarryExplicitBudget.finite_odd_critical_anchor_of_relative_budget
#print axioms CarryExplicitBudget.ten_relative_budget_after_numeric_cutoff
#print axioms CarryExplicitBudget.ten_anchor_via_relative_budget

#audit_flow
  CarryExplicitBudget.finite_family_direct_budget_bound
  CarryExplicitBudget.critical_anchor_after_numeric_cutoff
  CarryExplicitBudget.critical_energy_lower_after_numeric_cutoff
  CarryExplicitBudget.ten_relative_budget_after_numeric_cutoff
  CarryExplicitBudget.ten_anchor_via_relative_budget
  CarryDirectAnchor.ten_original_boundary_positive_via_direct_source
