import LocalPositivity
import FiniteNeighborhood
import ThetaCurvatureBridge
import NativeBoundaryBalance
import SourceSignRegression
import SignControl
import Lean
open Lean Elab Command
elab "#audit_flow " mode:str ids:ident+ : command => do
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
      if (mode.getString == "general" && (name == `CarryCriticalMixed.source_correction_numerator_pos || name == `CarryCriticalMixed.source_nonlinear_margin_pos)) || (forbidden.contains name && mode.getString != "finite-certified") ||
          (mode.getString == "finite-certified" && (name == `CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes || name == `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier)) ||
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
  let required := if mode.getString == "general" then
    #[`CarryLocalPositivity.sigmaSchur_differentiable_center,
      `CarryMovingSigma.sigma_schur_center,
      `CarrySelfAdjointOperator.sourceMomentMatrix_succ_posDef_iff,
      `CarrySigmaSource.sigma_log_jet_even]
    else if mode.getString == "finite-source" then #[`CarryCriticalMixed.source_correction_numerator_pos,
      `CarryCriticalMixed.source_nonlinear_margin_pos,
      `CarryMovingSigma.moving_schur_curvature_expanded]
    else if mode.getString == "finite-certified" then #[`CarrySixthEven.even_source_six_posDef,
      `CarrySixthOdd.odd_source_six_posDef, `CarryLocalPositivity.sigmaMatrix_finite_eventually_posDef]
    else #[]
  for name in required do
    unless seen.contains name do throwError "Missing provenance bridge: {name}"
  let note := if mode.getString == "finite-certified" then
    "sixth-order certificates explicitly required"
    else "sixth-order certificates forbidden; old prefix allowed"
  logInfo m!"Transitive source audit ({mode.getString}): {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; {note}"

#audit_flow "general" CarryLocalPositivity.sigmaMatrix_finite_eventually_posDef CarryLocalPositivity.sigmaSchur_deriv_center
#audit_flow "finite-source" CarryLocalPositivity.second_even_positive_local_max
#audit_flow "finite-certified" CarryLocalPositivity.both_six_sigmaMatrices_eventually_posDef CarryLocalPositivity.exists_positive_noncentral_six_sections
