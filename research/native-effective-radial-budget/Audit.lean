import EffectiveSixBudget
import Lean
open Lean Elab Command
elab "#audit_flow " group:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
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
      if group.getId == `algebra &&
          (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
           name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic ||
           name == `CarrySelfAdjointOperator.completedNativeOperatorLogDerivative) then
        throwError "Source-dependent algebra root: {name}"
      if group.getId != `certificate && name == `CarryIntegralCertificate.material_theta_integral_input then
        throwError "Unexpected interval certificate in sign-free group: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing declaration: {name}"
  if group.getId == `source then
    for required in #[`CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_sharp_decay,
      `CarryEffectiveRadial.source_response_product_on_disc,
      `CarryEffectiveRadial.source_remainder_deriv_bound,
      `CarryEffectiveRadial.six_expansion_on_disc,
      `CarryEffectiveRadial.six_physical_at_explicit_step] do
      unless seen.contains required do throwError "Missing actual source/physical bridge: {required}"
  if group.getId == `certificate then
    for required in #[`CarryIntegralCertificate.material_theta_integral_input,
      `CarryIntegralCertificate.mem_logMomentBox,
      `CarryEffectiveRadial.six_effective_increment_budget,
      `CarryEffectiveRadial.six_effective_anchor_positive,
      `CarryEffectiveRadial.native_response_exact_remainder,
      `CarryEffectiveRadial.six_effective_remainder_deriv_bound,
      `CarryEffectiveRadial.six_physical_at_explicit_step] do
      unless seen.contains required do throwError "Missing effective full-source budget link: {required}"
  logInfo m!"Effective budget audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
#print axioms CarryEffectiveRadial.sourceSeries
#print axioms CarryEffectiveRadial.source_coefficient_bound
#print axioms CarryEffectiveRadial.source_series_radius
#print axioms CarryEffectiveRadial.source_series_positive_radius
#print axioms CarryEffectiveRadial.source_series_mem
#print axioms CarryEffectiveRadial.source_series_analytic
#print axioms CarryEffectiveRadial.source_series_hasSum
#print axioms CarryEffectiveRadial.source_series_local_eq
#print axioms CarryEffectiveRadial.sourceResponse
#print axioms CarryEffectiveRadial.source_response_analytic
#print axioms CarryEffectiveRadial.source_response_local_eq
#print axioms CarryEffectiveRadial.quarter_disc_in_domain
#print axioms CarryEffectiveRadial.source_response_product_on_disc
#print axioms CarryEffectiveRadial.source_response_eq_native
#print axioms CarryEffectiveRadial.native_response_hasSum_on_disc
#print axioms CarryEffectiveRadial.imaginary_characteristic_ne_zero
#print axioms CarryEffectiveRadial.source_tail_term
#print axioms CarryEffectiveRadial.source_tail_norm
#print axioms CarryEffectiveRadial.native_response_prefix_error
#print axioms CarryEffectiveRadial.shiftedSeries
#print axioms CarryEffectiveRadial.shifted_coefficient_bound
#print axioms CarryEffectiveRadial.shifted_series_radius
#print axioms CarryEffectiveRadial.shifted_series_mem
#print axioms CarryEffectiveRadial.shifted_series_hasSum
#print axioms CarryEffectiveRadial.sourceRemainder
#print axioms CarryEffectiveRadial.native_response_exact_remainder
#print axioms CarryEffectiveRadial.source_remainder_analytic
#print axioms CarryEffectiveRadial.source_remainder_norm_le_one
#print axioms CarryEffectiveRadial.source_remainder_deriv_bound
#print axioms CarryEffectiveRadial.sixHigherPolynomial
#print axioms CarryEffectiveRadial.sixEffectiveRemainder
#print axioms CarryEffectiveRadial.radial_node_norm
#print axioms CarryEffectiveRadial.six_effective_remainder_analytic
#print axioms CarryEffectiveRadial.canonical_moment_norm_le_one
#print axioms CarryEffectiveRadial.six_expansion_on_disc
#print axioms CarryEffectiveRadial.finite_norm_budget
#print axioms CarryEffectiveRadial.nodeMonomials
#print axioms CarryEffectiveRadial.nodeCoefficients
#print axioms CarryEffectiveRadial.node_coefficients_exact
#print axioms CarryEffectiveRadial.six_node_weight_bound
#print axioms CarryEffectiveRadial.higherMonomials
#print axioms CarryEffectiveRadial.higherCoefficients
#print axioms CarryEffectiveRadial.six_higher_polynomial_bound
#print axioms CarryEffectiveRadial.six_effective_remainder_bound
#print axioms CarryEffectiveRadial.six_effective_remainder_deriv_bound
#print axioms CarryEffectiveRadial.native_response_norm_bound
#print axioms CarryEffectiveRadial.native_positive_coordinate_ne_zero
#print axioms CarryEffectiveRadial.imaginary_radial_regular
#print axioms CarryEffectiveRadial.six_radial_regular
#print axioms CarryEffectiveRadial.six_physical_at_explicit_step
#print axioms CarryEffectiveRadial.squared_step_budget
#print axioms CarryEffectiveRadial.radial_budget_hasSum
#print axioms CarryEffectiveRadial.budgetStep
#print axioms CarryEffectiveRadial.budgetIndex
#print axioms CarryEffectiveRadial.budget_step_positive
#print axioms CarryEffectiveRadial.budget_step_small
#print axioms CarryEffectiveRadial.unitBox
#print axioms CarryEffectiveRadial.smallCorrectionBox
#print axioms CarryEffectiveRadial.critical_sizes
#print axioms CarryEffectiveRadial.sixLimitBox
#print axioms CarryEffectiveRadial.stepBox
#print axioms CarryEffectiveRadial.anchorHeadBox
#print axioms CarryEffectiveRadial.anchor_head_membership
#print axioms CarryEffectiveRadial.anchor_head_lower
#print axioms CarryEffectiveRadial.criticalCurve
#print axioms CarryEffectiveRadial.critical_curve_hasDerivAt
#print axioms CarryEffectiveRadial.critical_curve_derivative_budget
#print axioms CarryEffectiveRadial.critical_curve_grid
#print axioms CarryEffectiveRadial.step_at_budget_index
#print axioms CarryEffectiveRadial.step_after_budget_index
#print axioms CarryEffectiveRadial.six_effective_increment_budget
#print axioms CarryEffectiveRadial.six_effective_anchor_positive
#print axioms CarryEffectiveRadial.six_boundary_positive_from_effective_budget
#print axioms CarryEffectiveRadial.six_effective_absolute_tail
#print axioms CarryEffectiveRadial.third_odd_residual_pos_via_effective_budget

#audit_flow algebra
  CarryEffectiveRadial.radial_node_norm
  CarryEffectiveRadial.finite_norm_budget
  CarryEffectiveRadial.nodeMonomials
  CarryEffectiveRadial.nodeCoefficients
  CarryEffectiveRadial.node_coefficients_exact
  CarryEffectiveRadial.six_node_weight_bound
  CarryEffectiveRadial.squared_step_budget
  CarryEffectiveRadial.radial_budget_hasSum
  CarryEffectiveRadial.budgetStep
  CarryEffectiveRadial.budgetIndex
  CarryEffectiveRadial.budget_step_positive
  CarryEffectiveRadial.budget_step_small
  CarryEffectiveRadial.unitBox
  CarryEffectiveRadial.smallCorrectionBox
  CarryEffectiveRadial.stepBox
  CarryEffectiveRadial.step_at_budget_index
  CarryEffectiveRadial.step_after_budget_index

#audit_flow source
  CarryEffectiveRadial.sourceSeries
  CarryEffectiveRadial.source_coefficient_bound
  CarryEffectiveRadial.source_series_radius
  CarryEffectiveRadial.source_series_positive_radius
  CarryEffectiveRadial.source_series_mem
  CarryEffectiveRadial.source_series_analytic
  CarryEffectiveRadial.source_series_hasSum
  CarryEffectiveRadial.source_series_local_eq
  CarryEffectiveRadial.sourceResponse
  CarryEffectiveRadial.source_response_analytic
  CarryEffectiveRadial.source_response_local_eq
  CarryEffectiveRadial.quarter_disc_in_domain
  CarryEffectiveRadial.source_response_product_on_disc
  CarryEffectiveRadial.source_response_eq_native
  CarryEffectiveRadial.native_response_hasSum_on_disc
  CarryEffectiveRadial.imaginary_characteristic_ne_zero
  CarryEffectiveRadial.source_tail_term
  CarryEffectiveRadial.source_tail_norm
  CarryEffectiveRadial.native_response_prefix_error
  CarryEffectiveRadial.shiftedSeries
  CarryEffectiveRadial.shifted_coefficient_bound
  CarryEffectiveRadial.shifted_series_radius
  CarryEffectiveRadial.shifted_series_mem
  CarryEffectiveRadial.shifted_series_hasSum
  CarryEffectiveRadial.sourceRemainder
  CarryEffectiveRadial.native_response_exact_remainder
  CarryEffectiveRadial.source_remainder_analytic
  CarryEffectiveRadial.source_remainder_norm_le_one
  CarryEffectiveRadial.source_remainder_deriv_bound
  CarryEffectiveRadial.sixHigherPolynomial
  CarryEffectiveRadial.sixEffectiveRemainder
  CarryEffectiveRadial.six_effective_remainder_analytic
  CarryEffectiveRadial.canonical_moment_norm_le_one
  CarryEffectiveRadial.six_expansion_on_disc
  CarryEffectiveRadial.higherMonomials
  CarryEffectiveRadial.higherCoefficients
  CarryEffectiveRadial.six_higher_polynomial_bound
  CarryEffectiveRadial.six_effective_remainder_bound
  CarryEffectiveRadial.six_effective_remainder_deriv_bound
  CarryEffectiveRadial.native_response_norm_bound
  CarryEffectiveRadial.native_positive_coordinate_ne_zero
  CarryEffectiveRadial.imaginary_radial_regular
  CarryEffectiveRadial.six_radial_regular
  CarryEffectiveRadial.six_physical_at_explicit_step
  CarryEffectiveRadial.criticalCurve
  CarryEffectiveRadial.critical_curve_hasDerivAt
  CarryEffectiveRadial.critical_curve_grid

#audit_flow certificate
  CarryEffectiveRadial.critical_sizes
  CarryEffectiveRadial.sixLimitBox
  CarryEffectiveRadial.anchorHeadBox
  CarryEffectiveRadial.anchor_head_membership
  CarryEffectiveRadial.anchor_head_lower
  CarryEffectiveRadial.critical_curve_derivative_budget
  CarryEffectiveRadial.six_effective_increment_budget
  CarryEffectiveRadial.six_effective_anchor_positive
  CarryEffectiveRadial.six_boundary_positive_from_effective_budget
  CarryEffectiveRadial.six_effective_absolute_tail
  CarryEffectiveRadial.third_odd_residual_pos_via_effective_budget
