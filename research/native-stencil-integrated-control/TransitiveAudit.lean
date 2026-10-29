import OriginalSourceTransport
import BudgetContinuity
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
  for required in #[`CarryOddCauchy.complement_row_factorial,
      `CarrySpatialCorrection.difference_power_stirling,
      `CarryOddEnergy.normalized_odd_pair_expansion,
      `CarryOddEnergy.finite_odd_energy_correction_tendsto,
      `CarryJetVariationBudget.physical_derivative_explicit_budget,
      `CarryMaterialVariation.radial_jet_hasDerivAt] do
    unless seen.contains required do throwError "Missing physical/source bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#audit_flow
  CarryCenteredStirling.stirling_second_diagonal_two
  CarryCenteredStirling.centered_coefficient_polynomial
  CarryCenteredStirling.stirling_coefficient_eq_lambda
  CarryCenteredStirling.physical_stencil_cauchy_beta
  CarryCenteredStirling.centeredDifference
  CarryCenteredStirling.centered_difference_sum
  CarryCenteredStirling.centered_difference_stirling
  CarryCenteredStirling.centered_difference_two_above
  CarryCenteredStirling.centered_difference_two_above_closed
  CarryCenteredStirling.centered_correction_eq_lambda
  CarryCenteredStirling.stencilPair
  CarryCenteredStirling.stencil_pair_physical_reduction
  CarryCenteredStirling.shifted_factorial_binomial
  CarryCenteredStirling.centered_sum_split_generic
  CarryCenteredStirling.centered_odd_split
  CarryCenteredStirling.odd_beta_term_to_centered
  CarryCenteredStirling.odd_stencil_pair_eq_centered
  CarryCenteredStirling.odd_stencil_correction_all_order
  CarryCenteredStirling.lambdaCoefficient
  CarryCenteredStirling.existing_spatial_coefficient_eq_lambda
  CarryCenteredStirling.original_odd_pair_expansion_lambda
  CarryCenteredStirling.original_finite_odd_energy_correction_lambda
  CarryCenteredStirling.original_stencil_coefficient_eq_lambda
  CarryCenteredStirling.lambdaReal
  CarryCenteredStirling.lambda_real_positive
  CarryCenteredStirling.lambda_complex_eq_real
  CarryCenteredStirling.lambda_crossing_negative
  CarryIntegratedControl.physicalCurve
  CarryIntegratedControl.prefixCurve
  CarryIntegratedControl.pointBudget
  CarryIntegratedControl.physical_curve_hasDerivAt
  CarryIntegratedControl.prefix_curve_hasDerivAt
  CarryIntegratedControl.source_error_hasDerivAt_and_bound
  CarryIntegratedControl.integrated_source_error
  CarryIntegratedControl.jetCombination
  CarryIntegratedControl.jet_combination_differentiable
  CarryIntegratedControl.integrated_original_jet_combinations
  CarryIntegratedControl.physical_curve_exact_prefix_and_tail
  CarryIntegratedControl.integrated_source_error_integral
  CarryIntegratedControl.integrated_original_jets_integral
  CarryIntegratedControl.integrated_native_grid_jets
  CarryIntegratedControl.jetCombinationVelocity
  CarryIntegratedControl.jet_combination_velocity
  CarryIntegratedControl.jet_combination_continuous
  CarryIntegratedControl.jet_velocity_continuous
  CarryIntegratedControl.address_budget_continuous
  CarryIntegratedControl.family_budget_continuous
  CarryIntegratedControl.velocity_budget_continuous
  CarryIntegratedControl.size_continuous
  CarryIntegratedControl.explicitJetBudget
  CarryIntegratedControl.explicit_jet_budget_eq
  CarryIntegratedControl.explicit_jet_budget_continuous
  CarryIntegratedControl.point_jet_budget_continuous
  CarryIntegratedControl.native_jet_budget_interval_integrable
  CarryIntegratedControl.integrated_native_grid_jets_unconditional
