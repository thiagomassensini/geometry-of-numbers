import SectorRegression
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
  for required in #[`MomentosHankel.pivot_second_deriv_hankel_local,
      `MomentosHankel.pivot_second_deriv_local,
      `MomentosHankel.schurVector_differentiableAt,
      `CarryMovingSigma.euclideanCLM_hasDerivAt_of_entries,
      `CarryMovingSigma.exists_sigma_prefix_neighborhood,
      `CarrySigmaSource.sigma_log_jet_analytic_center,
      `CarrySigmaSource.sigma_log_jet_curvature_center,
      `CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical] do
    unless seen.contains required do throwError "Missing provenance bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; sixth-pivot positivity forbidden, old prefix allowed"

#print axioms MomentosHankel.pivot_second_deriv_local
#print axioms MomentosHankel.pivot_second_deriv_matrix_local
#print axioms MomentosHankel.pivot_second_deriv_hankel_local
#print axioms MomentosHankel.pivot_second_deriv_hankel_local_fixed_form
#print axioms MomentosHankel.matrixInverse_differentiableAt
#print axioms MomentosHankel.mulVec_differentiableAt
#print axioms MomentosHankel.schurVector_differentiableAt
#print axioms MomentosHankel.pivot_second_deriv
#print axioms MomentosHankel.pivot_second_deriv_matrix
#print axioms MomentosHankel.schurVector_pivot
#print axioms MomentosHankel.schurVector_curvature
#print axioms MomentosHankel.schurRelation
#print axioms MomentosHankel.schurVector_mulVec
#print axioms MomentosHankel.schurVector_pivot_eq
#print axioms MomentosHankel.inner_eLast_schurVector
#print axioms MomentosHankel.toEuclideanCLM_schurVector
#print axioms CarryMovingSigma.euclideanCLM_basis_expansion
#print axioms CarryMovingSigma.euclideanCLM_hasDerivAt_of_entries
#print axioms CarryMovingSigma.sigma_matrix_center
#print axioms CarryMovingSigma.sigma_matrix_continuous_center
#print axioms CarryMovingSigma.sigma_matrix_first_center
#print axioms CarryMovingSigma.sigma_matrix_symm
#print axioms CarryMovingSigma.exists_sigma_prefix_neighborhood
#print axioms CarryMovingSigma.sigma_matrix_operator_first
#print axioms CarryMovingSigma.sigma_matrix_operator_second_center
#print axioms CarryMovingSigma.sigma_schur_center
#print axioms CarryMovingSigma.central_schur_vector
#print axioms CarryMovingSigma.moving_schur_curvature
#print axioms CarryMovingSigma.moving_schur_curvature_expanded
#print axioms CarryMovingSigma.moving_schur_eq_fixed_form_curvature
#print axioms CarryMovingSigma.even_moving_schur_curvature
#print axioms CarryMovingSigma.odd_moving_schur_curvature
#print axioms CarryMovingSigma.first_even_pivot_curvature
#print axioms CarryMovingSigma.first_odd_pivot_curvature

#audit_flow
  CarryMovingSigma.moving_schur_curvature_expanded
  CarryMovingSigma.moving_schur_eq_fixed_form_curvature
  CarryMovingSigma.even_moving_schur_curvature
  CarryMovingSigma.odd_moving_schur_curvature
  CarryMovingSigma.first_even_pivot_curvature
  CarryMovingSigma.first_odd_pivot_curvature
