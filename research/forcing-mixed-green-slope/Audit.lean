import CenteredMixed
import SlopeControls
import Lean

open Lean Elab Command
elab "#audit_mixed_green " mode:ident ids:ident+ : command => do
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
  let forbidden := if mode.getId == `slope then forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner] else forbidden
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
  logInfo m!"Mixed Green audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryMixedGreen.companionProbe
#print axioms CarryMixedGreen.valueProbe
#print axioms CarryMixedGreen.mixedForcingGreen
#print axioms CarryMixedGreen.hiddenGreen
#print axioms CarryMixedGreen.mixedHiddenGreen
#print axioms CarryMixedGreen.mixed_forcing_exact
#print axioms CarryMixedGreen.mixed_hidden_regular
#print axioms CarryMixedGreen.valueRatio
#print axioms CarryMixedGreen.retained_cross_ratio
#print axioms CarryMixedGreen.retained_cross_phase_split
#print axioms CarryMixedGreen.complete_mixed_hidden_factor
#print axioms CarryMixedGreen.diagonal_compensation
#print axioms CarryMixedGreen.companionCoefficient
#print axioms CarryMixedGreen.retainedCoefficient
#print axioms CarryMixedGreen.mixed_regular_split
#print axioms CarryMixedGreen.scalar_forcing_centered
#print axioms CarryMixedGreen.companion_bilinear
#print axioms CarryMixedGreen.companion_centered_bilinear
#print axioms CarryMixedGreen.retained_centered_bilinear
#print axioms CarryMixedGreen.centered_mixed_coefficient
#print axioms CarryMixedGreen.retained_regular_ratio
#print axioms CarryMixedGreen.mixed_regular_anchor
#print axioms CarryMixedGreen.value_probe_origin
#print axioms CarryMixedGreen.compressed_value_origin_derivative
#print axioms CarryMixedGreen.value_probe_origin_derivative
#print axioms CarryMixedGreen.forcing_scalar_differentiable
#print axioms CarryMixedGreen.value_ratio_origin
#print axioms CarryMixedGreen.value_ratio_undressed
#print axioms CarryMixedGreen.value_ratio_origin_derivative
#print axioms CarryMixedGreen.forcing_slope_pos
#print axioms CarryMixedGreen.forcing_slope_material_lower
#print axioms CarryMixedGreen.value_ratio_slope_tendsto
#print axioms CarryMixedGreen.value_ratio_positive_near
#print axioms CarryMixedGreen.value_ratio_phase_first_order_zero
#print axioms CarryMixedGreen.retained_two_ray_tendsto
#print axioms CarryMixedGreen.controlResponse
#print axioms CarryMixedGreen.controlLoewner
#print axioms CarryMixedGreen.control_regular
#print axioms CarryMixedGreen.control_response_derivative
#print axioms CarryMixedGreen.control_same_native_first_jet
#print axioms CarryMixedGreen.control_quadratic
#print axioms CarryMixedGreen.control_negative_direction
#print axioms CarryMixedGreen.control_positive_diagonals

#audit_mixed_green mixed
  CarryMixedGreen.companionProbe
  CarryMixedGreen.valueProbe
  CarryMixedGreen.mixedForcingGreen
  CarryMixedGreen.hiddenGreen
  CarryMixedGreen.mixedHiddenGreen
  CarryMixedGreen.mixed_forcing_exact
  CarryMixedGreen.mixed_hidden_regular
  CarryMixedGreen.valueRatio
  CarryMixedGreen.retained_cross_ratio
  CarryMixedGreen.retained_cross_phase_split
  CarryMixedGreen.complete_mixed_hidden_factor
  CarryMixedGreen.diagonal_compensation

#audit_mixed_green centered
  CarryMixedGreen.companionCoefficient
  CarryMixedGreen.retainedCoefficient
  CarryMixedGreen.mixed_regular_split
  CarryMixedGreen.scalar_forcing_centered
  CarryMixedGreen.companion_bilinear
  CarryMixedGreen.companion_centered_bilinear
  CarryMixedGreen.retained_centered_bilinear
  CarryMixedGreen.centered_mixed_coefficient
  CarryMixedGreen.retained_regular_ratio
  CarryMixedGreen.mixed_regular_anchor

#audit_mixed_green slope
  CarryMixedGreen.value_probe_origin
  CarryMixedGreen.compressed_value_origin_derivative
  CarryMixedGreen.value_probe_origin_derivative
  CarryMixedGreen.forcing_scalar_differentiable
  CarryMixedGreen.value_ratio_origin
  CarryMixedGreen.value_ratio_undressed
  CarryMixedGreen.value_ratio_origin_derivative
  CarryMixedGreen.forcing_slope_pos
  CarryMixedGreen.forcing_slope_material_lower
  CarryMixedGreen.value_ratio_slope_tendsto
  CarryMixedGreen.value_ratio_positive_near
  CarryMixedGreen.value_ratio_phase_first_order_zero
  CarryMixedGreen.retained_two_ray_tendsto

#audit_mixed_green controls
  CarryMixedGreen.controlResponse
  CarryMixedGreen.controlLoewner
  CarryMixedGreen.control_regular
  CarryMixedGreen.control_response_derivative
  CarryMixedGreen.control_same_native_first_jet
  CarryMixedGreen.control_quadratic
  CarryMixedGreen.control_negative_direction
  CarryMixedGreen.control_positive_diagonals
