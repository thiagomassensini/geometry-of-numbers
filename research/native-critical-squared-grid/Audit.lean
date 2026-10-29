import GridSignObstruction
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryCubicOdd.critical_cauchy_row,
    `CarryCubicOdd.critical_readout_four_samples,
    `CarryCubicOdd.critical_rho_alternating,
    `CarryCubicOdd.critical_diagonal_four_samples_exact,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarryOddEnergy.finite_odd_source_pairing,
    `CarryOddEnergy.finite_odd_energy_pairing,
    `CarryOddEnergy.finite_odd_energy_correction_tendsto,
    `CarryOddEnergy.finite_odd_green_correction_tendsto,
    `CarryCrossRadial.first_cross_exact,
    `CarryCrossRadial.doubled_first_exact,
    `CarryCrossRadial.doubled_scaled_tendsto,
    `CarryCrossRadial.doubled_scaled_expansion,
    `CarryCrossRadial.doubled_unscaled_expansion,
    `CarryCrossRadial.doubled_next_tendsto,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {decl}: {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name ||
          (construction && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden canonical/sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  logInfo m!"Native critical squared-grid mechanism {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryCriticalGrid.squaredNode
#print axioms CarryCriticalGrid.gridFirst
#print axioms CarryCriticalGrid.gridSecond
#print axioms CarryCriticalGrid.gridSecondRight
#print axioms CarryCriticalGrid.gridThird
#print axioms CarryCriticalGrid.grid_third_barycentric
#print axioms CarryCriticalGrid.squared_grid_reconstruction
#print axioms CarryCriticalGrid.squared_grid_data_injective
#print axioms CarryCriticalGrid.grid_third_mul_node
#print axioms CarryCriticalGrid.grid_third_top_factors
#print axioms CarryCriticalGrid.grid_constant_cancellation
#print axioms CarryCriticalGrid.criticalGridPolynomial
#print axioms CarryCriticalGrid.critical_polynomial_limit_product
#print axioms CarryCriticalGrid.critical_polynomial_shifted_product
#print axioms CarryCriticalGrid.gridBalance
#print axioms CarryCriticalGrid.critical_grid_curvatures
#print axioms CarryCriticalGrid.grid_mixed_from_pairs
#print axioms CarryCriticalGrid.grid_first_from_pairs
#print axioms CarryCriticalGrid.critical_grid_constant
#print axioms CarryCriticalGrid.critical_grid_product_defect
#print axioms CarryCriticalGrid.squaredScale
#print axioms CarryCriticalGrid.normalizedFourSamples
#print axioms CarryCriticalGrid.nativeFourSamples
#print axioms CarryCriticalGrid.squared_scale_nonzero
#print axioms CarryCriticalGrid.squared_scale_real_positive
#print axioms CarryCriticalGrid.native_four_samples_real
#print axioms CarryCriticalGrid.normalized_four_samples_recover
#print axioms CarryCriticalGrid.critical_readout_squared_grid
#print axioms CarryCriticalGrid.native_critical_grid_exact
#print axioms CarryCriticalGrid.native_critical_curvatures_exact
#print axioms CarryCriticalGrid.native_critical_product_defect_exact
#print axioms CarryCriticalGrid.native_critical_grid_tendsto
#print axioms CarryCriticalGrid.native_critical_grid_schur_tendsto
#print axioms CarryCriticalGrid.squared_scale_tendsto_zero
#print axioms CarryCriticalGrid.native_grid_third_tendsto
#print axioms CarryCriticalGrid.native_grid_mixed_tendsto
#print axioms CarryCriticalGrid.native_grid_first_tendsto
#print axioms CarryCriticalGrid.native_grid_second_tendsto
#print axioms CarryCriticalGrid.native_grid_node_third_tendsto
#print axioms CarryCriticalGrid.nativeGridDefect
#print axioms CarryCriticalGrid.native_grid_defect_scaled_tendsto
#print axioms CarryCriticalGrid.native_grid_defect_tendsto_zero
#print axioms CarryCriticalGrid.native_four_sample_tendsto
#print axioms CarryCriticalGrid.native_newton_data_tendsto
#print axioms CarryCriticalGrid.diagnosticSamples
#print axioms CarryCriticalGrid.diagnostic_samples_positive_real
#print axioms CarryCriticalGrid.diagnostic_three_curvature_signs
#print axioms CarryCriticalGrid.diagnostic_positive_entries
#print axioms CarryCriticalGrid.diagnostic_critical_negative
#print axioms CarryCriticalGrid.no_sign_from_three_curvatures

#audit_odd_green construction
  CarryCriticalGrid.squaredNode
  CarryCriticalGrid.gridFirst
  CarryCriticalGrid.gridSecond
  CarryCriticalGrid.gridSecondRight
  CarryCriticalGrid.gridThird
  CarryCriticalGrid.grid_third_barycentric
  CarryCriticalGrid.squared_grid_reconstruction
  CarryCriticalGrid.squared_grid_data_injective
  CarryCriticalGrid.grid_third_mul_node
  CarryCriticalGrid.grid_third_top_factors
  CarryCriticalGrid.grid_constant_cancellation
  CarryCriticalGrid.criticalGridPolynomial
  CarryCriticalGrid.critical_polynomial_limit_product
  CarryCriticalGrid.critical_polynomial_shifted_product
  CarryCriticalGrid.gridBalance
  CarryCriticalGrid.critical_grid_curvatures
  CarryCriticalGrid.grid_mixed_from_pairs
  CarryCriticalGrid.grid_first_from_pairs
  CarryCriticalGrid.critical_grid_constant
  CarryCriticalGrid.critical_grid_product_defect
  CarryCriticalGrid.squaredScale
  CarryCriticalGrid.normalizedFourSamples
  CarryCriticalGrid.nativeFourSamples
  CarryCriticalGrid.squared_scale_nonzero
  CarryCriticalGrid.squared_scale_real_positive
  CarryCriticalGrid.native_four_samples_real
  CarryCriticalGrid.normalized_four_samples_recover
  CarryCriticalGrid.critical_readout_squared_grid
  CarryCriticalGrid.native_critical_grid_exact
  CarryCriticalGrid.native_critical_curvatures_exact
  CarryCriticalGrid.native_critical_product_defect_exact
  CarryCriticalGrid.squared_scale_tendsto_zero
  CarryCriticalGrid.nativeGridDefect
  CarryCriticalGrid.diagnosticSamples
  CarryCriticalGrid.diagnostic_samples_positive_real
  CarryCriticalGrid.diagnostic_three_curvature_signs
  CarryCriticalGrid.diagnostic_positive_entries
  CarryCriticalGrid.diagnostic_critical_negative
  CarryCriticalGrid.no_sign_from_three_curvatures


#audit_odd_green provenance
  CarryCriticalGrid.native_critical_grid_tendsto
  CarryCriticalGrid.native_critical_grid_schur_tendsto
  CarryCriticalGrid.native_grid_third_tendsto
  CarryCriticalGrid.native_grid_mixed_tendsto
  CarryCriticalGrid.native_grid_first_tendsto
  CarryCriticalGrid.native_grid_second_tendsto
  CarryCriticalGrid.native_grid_node_third_tendsto
  CarryCriticalGrid.native_grid_defect_scaled_tendsto
  CarryCriticalGrid.native_grid_defect_tendsto_zero
  CarryCriticalGrid.native_four_sample_tendsto
  CarryCriticalGrid.native_newton_data_tendsto
