import SixEnergyTransport
import JetEulerVariation
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
      `CarryMaterialVariation.six_exact_remainder,
      `CarryMaterialVariation.six_physical_energy] do
      unless seen.contains required do throwError "Missing actual full physical source/certificate link: {required}"
  logInfo m!"Material variation audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
#print axioms CarryMaterialVariation.materialPair
#print axioms CarryMaterialVariation.materialVariation
#print axioms CarryMaterialVariation.materialPair_affine
#print axioms CarryMaterialVariation.materialPair_hasDerivAt
#print axioms CarryMaterialVariation.scaled_material_hasDerivAt
#print axioms CarryMaterialVariation.rho_differentiable
#print axioms CarryMaterialVariation.source_regular_local
#print axioms CarryMaterialVariation.rawVelocity
#print axioms CarryMaterialVariation.rhoVelocity
#print axioms CarryMaterialVariation.physical_material_derivative
#print axioms CarryMaterialVariation.radialJetVector
#print axioms CarryMaterialVariation.radial_jet_vector_at_grid
#print axioms CarryMaterialVariation.radial_jet_prefix_support
#print axioms CarryMaterialVariation.radial_jet_curve_original
#print axioms CarryMaterialVariation.radial_jet_curve_complete_jet
#print axioms CarryMaterialVariation.radial_jet_hasDerivAt
#print axioms CarryMaterialVariation.materialPair_scale_inputs
#print axioms CarryMaterialVariation.materialPair_linear_readout
#print axioms CarryMaterialVariation.jet_material_variation
#print axioms CarryMaterialVariation.jet_kernel_monomial
#print axioms CarryMaterialVariation.canonical_layer_annihilated
#print axioms CarryMaterialVariation.physical_jet_material_derivative
#print axioms CarryMaterialVariation.sixInput
#print axioms CarryMaterialVariation.sixWeight
#print axioms CarryMaterialVariation.sixRaw
#print axioms CarryMaterialVariation.six_input_outside
#print axioms CarryMaterialVariation.six_input_support
#print axioms CarryMaterialVariation.six_raw_at_grid
#print axioms CarryMaterialVariation.six_curve_eq_original
#print axioms CarryMaterialVariation.six_raw_differentiable
#print axioms CarryMaterialVariation.six_closed_material_derivative
#print axioms CarryMaterialVariation.sixNodeWeight
#print axioms CarryMaterialVariation.sixKernel
#print axioms CarryMaterialVariation.sixEnergy
#print axioms CarryMaterialVariation.sixLimit
#print axioms CarryMaterialVariation.sixCorrection
#print axioms CarryMaterialVariation.six_kernel_reduction
#print axioms CarryMaterialVariation.source_taylor_fourteen
#print axioms CarryMaterialVariation.six_exact_remainder
#print axioms CarryMaterialVariation.six_correction_tendsto
#print axioms CarryMaterialVariation.prefixDelta
#print axioms CarryMaterialVariation.uNumerator
#print axioms CarryMaterialVariation.vNumerator
#print axioms CarryMaterialVariation.sixU
#print axioms CarryMaterialVariation.sixV
#print axioms CarryMaterialVariation.deltaBox
#print axioms CarryMaterialVariation.uNumeratorBox
#print axioms CarryMaterialVariation.vNumeratorBox
#print axioms CarryMaterialVariation.sixUBox
#print axioms CarryMaterialVariation.sixVBox
#print axioms CarryMaterialVariation.sixCorrectionBox
#print axioms CarryMaterialVariation.delta_box_positive
#print axioms CarryMaterialVariation.six_correction_box_positive
#print axioms CarryMaterialVariation.source_box_membership
#print axioms CarryMaterialVariation.prefix_delta_positive
#print axioms CarryMaterialVariation.six_critical_old_rows
#print axioms CarryMaterialVariation.six_critical_limit_residual
#print axioms CarryMaterialVariation.six_critical_correction_positive
#print axioms CarryMaterialVariation.six_energy_eventually_above
#print axioms CarryMaterialVariation.six_weight_real
#print axioms CarryMaterialVariation.six_raw_product
#print axioms CarryMaterialVariation.six_response_energy
#print axioms CarryMaterialVariation.six_physical_energy
#print axioms CarryMaterialVariation.six_original_eventually_above
#print axioms CarryMaterialVariation.six_original_correction_tendsto

#audit_flow algebra
  CarryMaterialVariation.materialPair
  CarryMaterialVariation.materialVariation
  CarryMaterialVariation.materialPair_affine
  CarryMaterialVariation.materialPair_hasDerivAt
  CarryMaterialVariation.scaled_material_hasDerivAt
  CarryMaterialVariation.radialJetVector
  CarryMaterialVariation.radial_jet_vector_at_grid
  CarryMaterialVariation.radial_jet_prefix_support
  CarryMaterialVariation.radial_jet_hasDerivAt
  CarryMaterialVariation.materialPair_scale_inputs
  CarryMaterialVariation.materialPair_linear_readout
  CarryMaterialVariation.jet_material_variation
  CarryMaterialVariation.jet_kernel_monomial
  CarryMaterialVariation.canonical_layer_annihilated
  CarryMaterialVariation.sixInput
  CarryMaterialVariation.sixWeight
  CarryMaterialVariation.sixRaw
  CarryMaterialVariation.six_input_outside
  CarryMaterialVariation.six_input_support
  CarryMaterialVariation.six_raw_at_grid
  CarryMaterialVariation.six_raw_differentiable
  CarryMaterialVariation.sixNodeWeight
  CarryMaterialVariation.six_weight_real
  CarryMaterialVariation.six_raw_product

#audit_flow source
  CarryMaterialVariation.rho_differentiable
  CarryMaterialVariation.source_regular_local
  CarryMaterialVariation.rawVelocity
  CarryMaterialVariation.rhoVelocity
  CarryMaterialVariation.physical_material_derivative
  CarryMaterialVariation.radial_jet_curve_original
  CarryMaterialVariation.radial_jet_curve_complete_jet
  CarryMaterialVariation.physical_jet_material_derivative
  CarryMaterialVariation.six_curve_eq_original
  CarryMaterialVariation.six_closed_material_derivative
  CarryMaterialVariation.sixKernel
  CarryMaterialVariation.sixEnergy
  CarryMaterialVariation.sixLimit
  CarryMaterialVariation.sixCorrection
  CarryMaterialVariation.six_kernel_reduction
  CarryMaterialVariation.source_taylor_fourteen
  CarryMaterialVariation.six_exact_remainder
  CarryMaterialVariation.six_correction_tendsto
  CarryMaterialVariation.prefixDelta
  CarryMaterialVariation.uNumerator
  CarryMaterialVariation.vNumerator
  CarryMaterialVariation.sixU
  CarryMaterialVariation.sixV
  CarryMaterialVariation.six_response_energy
  CarryMaterialVariation.six_physical_energy
  CarryMaterialVariation.six_original_correction_tendsto

#audit_flow certificate
  CarryMaterialVariation.deltaBox
  CarryMaterialVariation.uNumeratorBox
  CarryMaterialVariation.vNumeratorBox
  CarryMaterialVariation.sixUBox
  CarryMaterialVariation.sixVBox
  CarryMaterialVariation.sixCorrectionBox
  CarryMaterialVariation.delta_box_positive
  CarryMaterialVariation.six_correction_box_positive
  CarryMaterialVariation.source_box_membership
  CarryMaterialVariation.prefix_delta_positive
  CarryMaterialVariation.six_critical_old_rows
  CarryMaterialVariation.six_critical_limit_residual
  CarryMaterialVariation.six_critical_correction_positive
  CarryMaterialVariation.six_energy_eventually_above
  CarryMaterialVariation.six_original_eventually_above
