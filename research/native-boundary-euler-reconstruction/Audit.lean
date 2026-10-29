import TailControls
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
  if group.getId == `source then
    for required in #[`CarryMaterialVariation.six_exact_remainder,
      `CarryMaterialVariation.six_physical_energy,
      `CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto] do
      unless seen.contains required do throwError "Missing original source reconstruction: {required}"
  if group.getId == `certificate then
    for required in #[`CarryIntegralCertificate.material_theta_integral_input,
      `CarryIntegralCertificate.mem_logMomentBox,
      `CarryMaterialVariation.six_exact_remainder,
      `CarryMaterialVariation.six_physical_energy] do
      unless seen.contains required do throwError "Missing actual full physical source/certificate link: {required}"
  logInfo m!"Boundary reconstruction audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
#print axioms CarryBoundaryReconstruction.radial_partial_sum
#print axioms CarryBoundaryReconstruction.radial_partial_sum_tendsto
#print axioms CarryBoundaryReconstruction.radial_drop_hasSum
#print axioms CarryBoundaryReconstruction.completePair
#print axioms CarryBoundaryReconstruction.complete_pair_boundary_reconstruction
#print axioms CarryBoundaryReconstruction.quadraticExtension
#print axioms CarryBoundaryReconstruction.quadratic_extension_derivative
#print axioms CarryBoundaryReconstruction.quadratic_extension_strictMono
#print axioms CarryBoundaryReconstruction.quadratic_extension_tendsto
#print axioms CarryBoundaryReconstruction.sixPhysical
#print axioms CarryBoundaryReconstruction.radial_step_positive
#print axioms CarryBoundaryReconstruction.radial_step_decreasing
#print axioms CarryBoundaryReconstruction.radial_step_tendsto
#print axioms CarryBoundaryReconstruction.six_physical_analytic_extension
#print axioms CarryBoundaryReconstruction.six_physical_tendsto
#print axioms CarryBoundaryReconstruction.six_physical_eventually_decreasing
#print axioms CarryBoundaryReconstruction.six_boundary_tail
#print axioms CarryBoundaryReconstruction.six_accumulated_tail_scale
#print axioms CarryBoundaryReconstruction.boundary_error_of_increment_budget
#print axioms CarryBoundaryReconstruction.positive_boundary_of_increment_budget
#print axioms CarryBoundaryReconstruction.increments_ignore_constant
#print axioms CarryBoundaryReconstruction.positive_decreasing_zero_boundary

#audit_flow algebra
  CarryBoundaryReconstruction.radial_partial_sum
  CarryBoundaryReconstruction.radial_partial_sum_tendsto
  CarryBoundaryReconstruction.radial_drop_hasSum
  CarryBoundaryReconstruction.quadraticExtension
  CarryBoundaryReconstruction.quadratic_extension_derivative
  CarryBoundaryReconstruction.quadratic_extension_strictMono
  CarryBoundaryReconstruction.quadratic_extension_tendsto
  CarryBoundaryReconstruction.radial_step_positive
  CarryBoundaryReconstruction.radial_step_decreasing
  CarryBoundaryReconstruction.radial_step_tendsto
  CarryBoundaryReconstruction.boundary_error_of_increment_budget
  CarryBoundaryReconstruction.positive_boundary_of_increment_budget
  CarryBoundaryReconstruction.increments_ignore_constant
  CarryBoundaryReconstruction.positive_decreasing_zero_boundary

#audit_flow source
  CarryBoundaryReconstruction.completePair
  CarryBoundaryReconstruction.complete_pair_boundary_reconstruction
  CarryBoundaryReconstruction.sixPhysical
  CarryBoundaryReconstruction.six_physical_analytic_extension
  CarryBoundaryReconstruction.six_physical_tendsto

#audit_flow certificate
  CarryBoundaryReconstruction.six_physical_eventually_decreasing
  CarryBoundaryReconstruction.six_boundary_tail
  CarryBoundaryReconstruction.six_accumulated_tail_scale
