import CriticalEnergyTransport
import Lean
open Lean Elab Command
elab "#audit_flow " group:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
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
  if group.getId == `certificate then
    for required in #[`CarryIntegralCertificate.material_theta_integral_input,
      `CarryIntegralCertificate.mem_logMomentBox,
      `CarryMovingRadial.critical_exact_remainder,
      `CarryMovingRadial.critical_physical_energy] do
      unless seen.contains required do throwError "Missing actual full physical source/certificate link: {required}"
  logInfo m!"Moving radial audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
#print axioms CarryMovingRadial.point
#print axioms CarryMovingRadial.scale
#print axioms CarryMovingRadial.curveState
#print axioms CarryMovingRadial.point_at_grid
#print axioms CarryMovingRadial.scale_at_grid
#print axioms CarryMovingRadial.curve_at_grid
#print axioms CarryMovingRadial.curve_eq_original
#print axioms CarryMovingRadial.finite_coefficients_support
#print axioms CarryMovingRadial.curve_euler_newton
#print axioms CarryMovingRadial.fixedSynthesis
#print axioms CarryMovingRadial.curveCoefficients
#print axioms CarryMovingRadial.curveQuotient
#print axioms CarryMovingRadial.curve_legs
#print axioms CarryMovingRadial.original_amplitude
#print axioms CarryMovingRadial.original_returned_amplitude
#print axioms CarryMovingRadial.fullPair
#print axioms CarryMovingRadial.fixedSynthesis_pairing
#print axioms CarryMovingRadial.curve_full_pair
#print axioms CarryMovingRadial.curve_norm_balance
#print axioms CarryMovingRadial.original_norm_balance
#print axioms CarryMovingRadial.amplitude_defect
#print axioms CarryMovingRadial.rho
#print axioms CarryMovingRadial.rho_real
#print axioms CarryMovingRadial.radial_amplitude_defect
#print axioms CarryMovingRadial.scale_product
#print axioms CarryMovingRadial.responsePair
#print axioms CarryMovingRadial.fullPair_eq_response
#print axioms CarryMovingRadial.physical_response_pair
#print axioms CarryMovingRadial.returnVariation
#print axioms CarryMovingRadial.fullPair_hasDerivAt
#print axioms CarryMovingRadial.fullPair_derivative
#print axioms CarryMovingRadial.amplitude_analytic
#print axioms CarryMovingRadial.quotient_analytic
#print axioms CarryMovingRadial.radial_differentiable
#print axioms CarryMovingRadial.scale_differentiable
#print axioms CarryMovingRadial.curve_differentiable
#print axioms CarryMovingRadial.coefficientVelocity
#print axioms CarryMovingRadial.returnVelocity
#print axioms CarryMovingRadial.physical_moving_derivative
#print axioms CarryMovingRadial.criticalWeight
#print axioms CarryMovingRadial.criticalNodeWeight
#print axioms CarryMovingRadial.criticalKernel
#print axioms CarryMovingRadial.criticalEnergy
#print axioms CarryMovingRadial.criticalLimit
#print axioms CarryMovingRadial.criticalCorrection
#print axioms CarryMovingRadial.critical_kernel_reduction
#print axioms CarryMovingRadial.source_taylor_ten
#print axioms CarryMovingRadial.critical_exact_remainder
#print axioms CarryMovingRadial.critical_correction_tendsto
#print axioms CarryMovingRadial.criticalRaw
#print axioms CarryMovingRadial.critical_raw_at_grid
#print axioms CarryMovingRadial.finite_coefficients_restrict
#print axioms CarryMovingRadial.critical_curve_eq_original
#print axioms CarryMovingRadial.critical_raw_differentiable
#print axioms CarryMovingRadial.curve_regular_eventually
#print axioms CarryMovingRadial.critical_physical_derivative
#print axioms CarryMovingRadial.orientationPolynomial
#print axioms CarryMovingRadial.orientationBox
#print axioms CarryMovingRadial.orientation_box_positive
#print axioms CarryMovingRadial.h1_box_positive
#print axioms CarryMovingRadial.source_orientation_positive
#print axioms CarryMovingRadial.criticalParameter
#print axioms CarryMovingRadial.critical_correction_positive
#print axioms CarryMovingRadial.critical_energy_eventually_above
#print axioms CarryMovingRadial.critical_weight_real
#print axioms CarryMovingRadial.critical_raw_product
#print axioms CarryMovingRadial.critical_response_energy
#print axioms CarryMovingRadial.critical_physical_energy
#print axioms CarryMovingRadial.critical_original_eventually_above
#print axioms CarryMovingRadial.critical_original_correction_tendsto

#audit_flow algebra
  CarryMovingRadial.point
  CarryMovingRadial.scale
  CarryMovingRadial.point_at_grid
  CarryMovingRadial.scale_at_grid
  CarryMovingRadial.finite_coefficients_support
  CarryMovingRadial.fixedSynthesis
  CarryMovingRadial.fullPair
  CarryMovingRadial.fixedSynthesis_pairing
  CarryMovingRadial.returnVariation
  CarryMovingRadial.fullPair_hasDerivAt
  CarryMovingRadial.fullPair_derivative
  CarryMovingRadial.criticalWeight
  CarryMovingRadial.criticalNodeWeight
  CarryMovingRadial.criticalRaw
  CarryMovingRadial.finite_coefficients_restrict
  CarryMovingRadial.critical_raw_differentiable
  CarryMovingRadial.orientationPolynomial
  CarryMovingRadial.critical_weight_real
  CarryMovingRadial.critical_raw_product

#audit_flow source
  CarryMovingRadial.curveState
  CarryMovingRadial.curve_at_grid
  CarryMovingRadial.curve_eq_original
  CarryMovingRadial.curve_euler_newton
  CarryMovingRadial.curveCoefficients
  CarryMovingRadial.curveQuotient
  CarryMovingRadial.curve_legs
  CarryMovingRadial.original_amplitude
  CarryMovingRadial.original_returned_amplitude
  CarryMovingRadial.curve_full_pair
  CarryMovingRadial.curve_norm_balance
  CarryMovingRadial.original_norm_balance
  CarryMovingRadial.amplitude_defect
  CarryMovingRadial.rho
  CarryMovingRadial.rho_real
  CarryMovingRadial.radial_amplitude_defect
  CarryMovingRadial.scale_product
  CarryMovingRadial.responsePair
  CarryMovingRadial.fullPair_eq_response
  CarryMovingRadial.physical_response_pair
  CarryMovingRadial.amplitude_analytic
  CarryMovingRadial.quotient_analytic
  CarryMovingRadial.radial_differentiable
  CarryMovingRadial.scale_differentiable
  CarryMovingRadial.curve_differentiable
  CarryMovingRadial.coefficientVelocity
  CarryMovingRadial.returnVelocity
  CarryMovingRadial.physical_moving_derivative
  CarryMovingRadial.criticalKernel
  CarryMovingRadial.criticalEnergy
  CarryMovingRadial.criticalLimit
  CarryMovingRadial.criticalCorrection
  CarryMovingRadial.critical_kernel_reduction
  CarryMovingRadial.source_taylor_ten
  CarryMovingRadial.critical_exact_remainder
  CarryMovingRadial.critical_correction_tendsto
  CarryMovingRadial.critical_raw_at_grid
  CarryMovingRadial.critical_curve_eq_original
  CarryMovingRadial.curve_regular_eventually
  CarryMovingRadial.critical_physical_derivative
  CarryMovingRadial.criticalParameter
  CarryMovingRadial.critical_response_energy
  CarryMovingRadial.critical_physical_energy
  CarryMovingRadial.critical_original_correction_tendsto

#audit_flow certificate
  CarryMovingRadial.orientationBox
  CarryMovingRadial.orientation_box_positive
  CarryMovingRadial.h1_box_positive
  CarryMovingRadial.source_orientation_positive
  CarryMovingRadial.critical_correction_positive
  CarryMovingRadial.critical_energy_eventually_above
  CarryMovingRadial.critical_original_eventually_above
