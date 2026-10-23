import NativePortCalibration
import Lean

open Lean Elab Command
elab "#audit_theta_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden moment-derived or sign consumer: {name}"
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
  logInfo m!"Material theta TFVD audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment-derived constructions and sign consumers absent"

#print axioms CarryMaterialTheta.addressMode
#print axioms CarryMaterialTheta.addressModeFirst
#print axioms CarryMaterialTheta.addressMode_succ
#print axioms CarryMaterialTheta.addressModeFirst_succ
#print axioms CarryMaterialTheta.addressMode_pos
#print axioms CarryMaterialTheta.addressMode_hasDerivAt
#print axioms CarryMaterialTheta.carry_amplitude_eq_exp
#print axioms CarryMaterialTheta.exp_double_shift
#print axioms CarryMaterialTheta.addressMode_dilation
#print axioms CarryMaterialTheta.addressModeFirst_dilation
#print axioms CarryMaterialTheta.MaterialThetaPort
#print axioms CarryMaterialTheta.materialThetaMode
#print axioms CarryMaterialTheta.dilationShear
#print axioms CarryMaterialTheta.materialThetaMode_dilation
#print axioms CarryMaterialTheta.materialThetaMode_injective
#print axioms CarryMaterialTheta.resolvedThetaLift
#print axioms CarryMaterialTheta.thetaLift
#print axioms CarryMaterialTheta.resolvedThetaLift_injective
#print axioms CarryMaterialTheta.resolvedLabeledThetaLift
#print axioms CarryMaterialTheta.resolvedLabeledThetaLift_injective
#print axioms CarryMaterialTheta.thetaLiftLinear
#print axioms CarryMaterialTheta.portFirstDifference
#print axioms CarryMaterialTheta.portSecondDifference
#print axioms CarryMaterialTheta.portReturn
#print axioms CarryMaterialTheta.portGreen
#print axioms CarryMaterialTheta.port_tfvd
#print axioms CarryMaterialTheta.thetaLift_firstDifference
#print axioms CarryMaterialTheta.thetaLift_secondDifference
#print axioms CarryMaterialTheta.thetaLift_return
#print axioms CarryMaterialTheta.thetaLift_green
#print axioms CarryMaterialTheta.logPort
#print axioms CarryMaterialTheta.derivativePort
#print axioms CarryMaterialTheta.tfvd_log_green_four_crosses
#print axioms CarryMaterialTheta.real_shear_preserves_green
#print axioms CarryMaterialTheta.theta_mode_log_green_dilation
#print axioms CarryMaterialTheta.finiteHeatSynthesis
#print axioms CarryMaterialTheta.heat_to_theta_value
#print axioms CarryMaterialTheta.finite_heat_mellin
#print axioms CarryMaterialTheta.finite_heat_mellin_native
#print axioms CarryMaterialTheta.integerThetaPort
#print axioms CarryMaterialTheta.odd_camera_port_normal_form
#print axioms CarryMaterialTheta.odd_atlas_port_cross_identity
#print axioms CarryMaterialTheta.theta_lift_green_all_crosses
#print axioms CarryMaterialTheta.summable_square_address_mode
#print axioms CarryMaterialTheta.summable_material_log_mode
#print axioms CarryMaterialTheta.addressed_port_hasSum
#print axioms CarryMaterialTheta.addressed_port_summable
#print axioms CarryMaterialTheta.completedThetaPort
#print axioms CarryMaterialTheta.completedThetaPort_components
#print axioms CarryMaterialTheta.thetaPortHead
#print axioms CarryMaterialTheta.thetaPortTail
#print axioms CarryMaterialTheta.completedThetaPort_head_tail
#print axioms CarryMaterialTheta.logPortLinear
#print axioms CarryMaterialTheta.derivativePortLinear
#print axioms CarryMaterialTheta.completed_theta_green_four_crosses
#print axioms CarryMaterialTheta.dilationShearLinear
#print axioms CarryMaterialTheta.dilatedThetaPort
#print axioms CarryMaterialTheta.dilated_port_hasSum
#print axioms CarryMaterialTheta.dilatedThetaPort_eq_shift_shear
#print axioms CarryMaterialTheta.completedCameraThetaPort
#print axioms CarryMaterialTheta.completed_camera_shift_formula
#print axioms CarryMaterialTheta.dilatedThetaHead
#print axioms CarryMaterialTheta.dilatedThetaTail
#print axioms CarryMaterialTheta.dilatedThetaPort_head_tail
#print axioms CarryMaterialTheta.completed_camera_head_tail
#print axioms CarryMaterialTheta.addressTowerPort
#print axioms CarryMaterialTheta.address_tower_step
#print axioms CarryMaterialTheta.address_tower_tfvd
#print axioms CarryMaterialTheta.raw_critical_material_sum_not_summable
#print axioms CarryMaterialTheta.material_log_green_modes
#print axioms CarryMaterialTheta.theta_derivative_green_modes
#print axioms CarryMaterialTheta.raw_modal_fluxes_have_opposite_sign
#print axioms CarryMaterialTheta.nonzero_mode_with_zero_self_green
#print axioms CarryMaterialTheta.finiteMaterialValue
#print axioms CarryMaterialTheta.finiteMaterialLog
#print axioms CarryMaterialTheta.finiteMaterialValue_hasDerivAt
#print axioms CarryMaterialTheta.heat_mellin_material_value
#print axioms CarryMaterialTheta.heat_mellin_material_log
#print axioms CarryMaterialTheta.native_completion_eq_gammaR
#print axioms CarryMaterialTheta.original_completed_finite_value_mellin
#print axioms CarryMaterialTheta.gammaR_differentiableAt
#print axioms CarryMaterialTheta.finite_heat_mellin_hasDerivAt
#print axioms CarryMaterialTheta.gammaDress
#print axioms CarryMaterialTheta.gammaDress_eq_mellin_trace
#print axioms CarryMaterialTheta.native_height_mellin_hasDerivAt
#print axioms CarryMaterialTheta.native_height_gamma_trace
#print axioms CarryMaterialTheta.gammaDress_green_defect
#print axioms CarryMaterialTheta.heatSample
#print axioms CarryMaterialTheta.finite_address_mellin
#print axioms CarryMaterialTheta.heat_difference_mellin
#print axioms CarryMaterialTheta.nativeHeatGreenPort
#print axioms CarryMaterialTheta.cellwiseMellinPort
#print axioms CarryMaterialTheta.native_green_port_mellin
#print axioms CarryMaterialTheta.native_green_mellin_two_inputs
#print axioms CarryMaterialTheta.original_tfvd_green_projection_mellin
#print axioms CarryMaterialTheta.weightGreenPort
#print axioms CarryMaterialTheta.cellwise_mellin_weights
#print axioms CarryMaterialTheta.weighted_native_port_mellin
#print axioms CarryMaterialTheta.weighted_native_two_input_green

#audit_theta_transport
  CarryMaterialTheta.addressMode
  CarryMaterialTheta.addressModeFirst
  CarryMaterialTheta.addressMode_succ
  CarryMaterialTheta.addressModeFirst_succ
  CarryMaterialTheta.addressMode_pos
  CarryMaterialTheta.addressMode_hasDerivAt
  CarryMaterialTheta.carry_amplitude_eq_exp
  CarryMaterialTheta.exp_double_shift
  CarryMaterialTheta.addressMode_dilation
  CarryMaterialTheta.addressModeFirst_dilation
  CarryMaterialTheta.MaterialThetaPort
  CarryMaterialTheta.materialThetaMode
  CarryMaterialTheta.dilationShear
  CarryMaterialTheta.materialThetaMode_dilation
  CarryMaterialTheta.materialThetaMode_injective
  CarryMaterialTheta.resolvedThetaLift
  CarryMaterialTheta.thetaLift
  CarryMaterialTheta.resolvedThetaLift_injective
  CarryMaterialTheta.resolvedLabeledThetaLift
  CarryMaterialTheta.resolvedLabeledThetaLift_injective
  CarryMaterialTheta.thetaLiftLinear
  CarryMaterialTheta.portFirstDifference
  CarryMaterialTheta.portSecondDifference
  CarryMaterialTheta.portReturn
  CarryMaterialTheta.portGreen
  CarryMaterialTheta.port_tfvd
  CarryMaterialTheta.thetaLift_firstDifference
  CarryMaterialTheta.thetaLift_secondDifference
  CarryMaterialTheta.thetaLift_return
  CarryMaterialTheta.thetaLift_green
  CarryMaterialTheta.logPort
  CarryMaterialTheta.derivativePort
  CarryMaterialTheta.tfvd_log_green_four_crosses
  CarryMaterialTheta.real_shear_preserves_green
  CarryMaterialTheta.theta_mode_log_green_dilation
  CarryMaterialTheta.finiteHeatSynthesis
  CarryMaterialTheta.heat_to_theta_value
  CarryMaterialTheta.finite_heat_mellin
  CarryMaterialTheta.finite_heat_mellin_native
  CarryMaterialTheta.integerThetaPort
  CarryMaterialTheta.odd_camera_port_normal_form
  CarryMaterialTheta.odd_atlas_port_cross_identity
  CarryMaterialTheta.theta_lift_green_all_crosses
  CarryMaterialTheta.summable_square_address_mode
  CarryMaterialTheta.summable_material_log_mode
  CarryMaterialTheta.addressed_port_hasSum
  CarryMaterialTheta.addressed_port_summable
  CarryMaterialTheta.completedThetaPort
  CarryMaterialTheta.completedThetaPort_components
  CarryMaterialTheta.thetaPortHead
  CarryMaterialTheta.thetaPortTail
  CarryMaterialTheta.completedThetaPort_head_tail
  CarryMaterialTheta.logPortLinear
  CarryMaterialTheta.derivativePortLinear
  CarryMaterialTheta.completed_theta_green_four_crosses
  CarryMaterialTheta.dilationShearLinear
  CarryMaterialTheta.dilatedThetaPort
  CarryMaterialTheta.dilated_port_hasSum
  CarryMaterialTheta.dilatedThetaPort_eq_shift_shear
  CarryMaterialTheta.completedCameraThetaPort
  CarryMaterialTheta.completed_camera_shift_formula
  CarryMaterialTheta.dilatedThetaHead
  CarryMaterialTheta.dilatedThetaTail
  CarryMaterialTheta.dilatedThetaPort_head_tail
  CarryMaterialTheta.completed_camera_head_tail
  CarryMaterialTheta.addressTowerPort
  CarryMaterialTheta.address_tower_step
  CarryMaterialTheta.address_tower_tfvd
  CarryMaterialTheta.raw_critical_material_sum_not_summable
  CarryMaterialTheta.material_log_green_modes
  CarryMaterialTheta.theta_derivative_green_modes
  CarryMaterialTheta.raw_modal_fluxes_have_opposite_sign
  CarryMaterialTheta.nonzero_mode_with_zero_self_green
  CarryMaterialTheta.finiteMaterialValue
  CarryMaterialTheta.finiteMaterialLog
  CarryMaterialTheta.finiteMaterialValue_hasDerivAt
  CarryMaterialTheta.heat_mellin_material_value
  CarryMaterialTheta.heat_mellin_material_log
  CarryMaterialTheta.native_completion_eq_gammaR
  CarryMaterialTheta.original_completed_finite_value_mellin
  CarryMaterialTheta.gammaR_differentiableAt
  CarryMaterialTheta.finite_heat_mellin_hasDerivAt
  CarryMaterialTheta.gammaDress
  CarryMaterialTheta.gammaDress_eq_mellin_trace
  CarryMaterialTheta.native_height_mellin_hasDerivAt
  CarryMaterialTheta.native_height_gamma_trace
  CarryMaterialTheta.gammaDress_green_defect
  CarryMaterialTheta.heatSample
  CarryMaterialTheta.finite_address_mellin
  CarryMaterialTheta.heat_difference_mellin
  CarryMaterialTheta.nativeHeatGreenPort
  CarryMaterialTheta.cellwiseMellinPort
  CarryMaterialTheta.native_green_port_mellin
  CarryMaterialTheta.native_green_mellin_two_inputs
  CarryMaterialTheta.original_tfvd_green_projection_mellin
  CarryMaterialTheta.weightGreenPort
  CarryMaterialTheta.cellwise_mellin_weights
  CarryMaterialTheta.weighted_native_port_mellin
  CarryMaterialTheta.weighted_native_two_input_green
