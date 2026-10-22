import Orientation
import Lean

open Lean Elab Command
elab "#audit_conservative_transport " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
  let forbidden := if mode.getId == `orientation then forbidden else forbidden ++ #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
      if forbidden.contains name then
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"Radial conservative source audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryRadialConservative.radialSymbol
#print axioms CarryRadialConservative.radialPortCoefficient
#print axioms CarryRadialConservative.radial_den_pos
#print axioms CarryRadialConservative.radial_symbol_shift
#print axioms CarryRadialConservative.radial_symbol_scaled_address
#print axioms CarryRadialConservative.scalar_conservation
#print axioms CarryRadialConservative.conservativeSynthesis
#print axioms CarryRadialConservative.conservativePort
#print axioms CarryRadialConservative.polarized_conservation
#print axioms CarryRadialConservative.conservative_energy
#print axioms CarryRadialConservative.conservativeTransfer
#print axioms CarryRadialConservative.conservativeTransfer_exact
#print axioms CarryRadialConservative.conservativeTransfer_contractive
#print axioms CarryRadialConservative.conservativeSynthesis_snoc_zero
#print axioms CarryRadialConservative.conservativePort_snoc_zero
#print axioms CarryRadialConservative.nativeDefect
#print axioms CarryRadialConservative.native_defect_columns
#print axioms CarryRadialConservative.native_polarized_ledger
#print axioms CarryRadialConservative.native_energy_ledger
#print axioms CarryRadialConservative.jetCoefficients
#print axioms CarryRadialConservative.exact_native_transfer_jet
#print axioms CarryRadialConservative.finite_eventually_admissible
#print axioms CarryRadialConservative.realRadialStep
#print axioms CarryRadialConservative.real_radial_step_tendsto
#print axioms CarryRadialConservative.radial_symbol_in_step
#print axioms CarryRadialConservative.radial_port_in_step
#print axioms CarryRadialConservative.radial_symbol_tendsto
#print axioms CarryRadialConservative.radial_port_tendsto
#print axioms CarryRadialConservative.radial_symbol_tangent
#print axioms CarryRadialConservative.native_symbol_tangent
#print axioms CarryRadialConservative.native_symbol_defect_tangent
#print axioms CarryRadialConservative.scaled_comparator_tendsto
#print axioms CarryRadialConservative.scaled_native_defect_tendsto_zero
#print axioms CarryRadialConservative.cayley_difference
#print axioms CarryRadialConservative.radial_symbol_cayley
#print axioms CarryRadialConservative.native_response_defect_on_grid
#print axioms CarryRadialConservative.first_even_coefficients
#print axioms CarryRadialConservative.first_odd_coefficients
#print axioms CarryRadialConservative.first_odd_scaled_defect_tendsto_zero
#print axioms CarryRadialConservative.first_even_port
#print axioms CarryRadialConservative.first_even_defect
#print axioms CarryRadialConservative.first_even_port_energy_tendsto
#print axioms CarryRadialConservative.first_even_balance_tendsto
#print axioms CarryRadialConservative.inverse_radial_sqrt_tendsto
#print axioms CarryRadialConservative.first_even_defect_factor
#print axioms CarryRadialConservative.first_even_defect_tendsto_zero
#print axioms CarryRadialConservative.first_even_mixed_cross_tendsto
#print axioms CarryRadialConservative.first_even_mixed_cross_eventually_pos
#print axioms CarryRadialConservative.native_symbol_defect_tangent_ne
#print axioms CarryRadialConservative.native_symbol_eventually_ne

#audit_conservative_transport conservative
  CarryRadialConservative.radialSymbol
  CarryRadialConservative.radialPortCoefficient
  CarryRadialConservative.radial_den_pos
  CarryRadialConservative.radial_symbol_shift
  CarryRadialConservative.radial_symbol_scaled_address
  CarryRadialConservative.scalar_conservation
  CarryRadialConservative.conservativeSynthesis
  CarryRadialConservative.conservativePort
  CarryRadialConservative.polarized_conservation
  CarryRadialConservative.conservative_energy
  CarryRadialConservative.conservativeTransfer
  CarryRadialConservative.conservativeTransfer_exact
  CarryRadialConservative.conservativeTransfer_contractive
  CarryRadialConservative.conservativeSynthesis_snoc_zero
  CarryRadialConservative.conservativePort_snoc_zero

#audit_conservative_transport native
  CarryRadialConservative.nativeDefect
  CarryRadialConservative.native_defect_columns
  CarryRadialConservative.native_polarized_ledger
  CarryRadialConservative.native_energy_ledger
  CarryRadialConservative.jetCoefficients
  CarryRadialConservative.exact_native_transfer_jet
  CarryRadialConservative.finite_eventually_admissible

#audit_conservative_transport radial_limits
  CarryRadialConservative.realRadialStep
  CarryRadialConservative.real_radial_step_tendsto
  CarryRadialConservative.radial_symbol_in_step
  CarryRadialConservative.radial_port_in_step
  CarryRadialConservative.radial_symbol_tendsto
  CarryRadialConservative.radial_port_tendsto
  CarryRadialConservative.radial_symbol_tangent
  CarryRadialConservative.native_symbol_tangent
  CarryRadialConservative.native_symbol_defect_tangent
  CarryRadialConservative.scaled_comparator_tendsto
  CarryRadialConservative.scaled_native_defect_tendsto_zero
  CarryRadialConservative.cayley_difference
  CarryRadialConservative.radial_symbol_cayley
  CarryRadialConservative.native_response_defect_on_grid

#audit_conservative_transport even_jet
  CarryRadialConservative.first_even_coefficients
  CarryRadialConservative.first_odd_coefficients
  CarryRadialConservative.first_odd_scaled_defect_tendsto_zero
  CarryRadialConservative.first_even_port
  CarryRadialConservative.first_even_defect
  CarryRadialConservative.first_even_port_energy_tendsto
  CarryRadialConservative.first_even_balance_tendsto
  CarryRadialConservative.inverse_radial_sqrt_tendsto
  CarryRadialConservative.first_even_defect_factor
  CarryRadialConservative.first_even_defect_tendsto_zero
  CarryRadialConservative.first_even_mixed_cross_tendsto

#audit_conservative_transport orientation
  CarryRadialConservative.first_even_mixed_cross_eventually_pos
  CarryRadialConservative.native_symbol_defect_tangent_ne
  CarryRadialConservative.native_symbol_eventually_ne
