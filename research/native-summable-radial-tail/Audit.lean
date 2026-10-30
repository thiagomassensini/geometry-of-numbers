import Examples
import Lean
open Lean Elab Command
elab "#audit_flow " ids:ident+ : command => do
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
      if name == `CarryIntegralCertificate.material_theta_integral_input then
        throwError "Unexpected finite interval certificate: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing declaration: {name}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#print axioms CarrySummableRadial.effective_response_samples
#print axioms CarrySummableRadial.odd_filter_affine
#print axioms CarrySummableRadial.odd_pair_effective_expansion
#print axioms CarrySummableRadial.normalized_odd_pair_effective_at_regular
#print axioms CarrySummableRadial.odd_filter_budget_nonneg
#print axioms CarrySummableRadial.odd_filter_effective_tail_bound
#print axioms CarrySummableRadial.odd_pair_effective_tail_bound
#print axioms CarrySummableRadial.odd_filter_tail_hasDerivAt
#print axioms CarrySummableRadial.odd_filter_tail_derivative_bound
#print axioms CarrySummableRadial.odd_pair_tail_hasDerivAt
#print axioms CarrySummableRadial.odd_pair_tail_derivative_bound
#print axioms CarrySummableRadial.effective_remainder_norm
#print axioms CarrySummableRadial.effective_remainder_analytic
#print axioms CarrySummableRadial.effective_response_expansion
#print axioms CarrySummableRadial.effective_remainder_deriv_bound
#print axioms CarrySummableRadial.six_grid_cutoff_value
#print axioms CarrySummableRadial.first_pair_constant_value
#print axioms CarrySummableRadial.odd_grid_size_pos
#print axioms CarrySummableRadial.odd_grid_cutoff_regular
#print axioms CarrySummableRadial.finite_odd_energy_pairing_at_regular
#print axioms CarrySummableRadial.finite_odd_energy_pairing_at_cutoff
#print axioms CarrySummableRadial.family_constant_nonneg
#print axioms CarrySummableRadial.family_curve_grid
#print axioms CarrySummableRadial.family_pair_disc
#print axioms CarrySummableRadial.family_curve_differentiable
#print axioms CarrySummableRadial.family_curve_derivative_bound
#print axioms CarrySummableRadial.pair_constant_nonneg
#print axioms CarrySummableRadial.pair_curve_hasDerivAt
#print axioms CarrySummableRadial.pair_curve_derivative_bound
#print axioms CarrySummableRadial.squared_step_scaled
#print axioms CarrySummableRadial.six_input_eq_finite_odd
#print axioms CarrySummableRadial.six_physical_eq_twice_finite_energy
#print axioms CarrySummableRadial.six_original_absolute_tail_regression
#print axioms CarrySummableRadial.six_anchor_tail_regression
#print axioms CarrySummableRadial.family_curve_zero
#print axioms CarrySummableRadial.family_energy_tendsto
#print axioms CarrySummableRadial.family_increment_budget
#print axioms CarrySummableRadial.finite_odd_energy_absolute_tail
#print axioms CarrySummableRadial.family_budget_tendsto_zero

#audit_flow
  CarrySummableRadial.finite_odd_energy_absolute_tail
  CarrySummableRadial.family_budget_tendsto_zero
