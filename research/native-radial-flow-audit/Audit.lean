import RadialDefect
import RadialReality
import KernelSign
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
           name == `CarryRadialFlow.flowResponse) then
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
      `CarryRadialFlow.flow_first_eight,
      `CarryRadialFlow.fourFlowKernel_exact_remainder] do
      unless seen.contains required do throwError "Missing actual source/certificate link: {required}"
  logInfo m!"Radial flow audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
#print axioms CarryRadialFlow.tc
#print axioms CarryRadialFlow.tc_mul
#print axioms CarryRadialFlow.tc_add
#print axioms CarryRadialFlow.tc_deriv
#print axioms CarryRadialFlow.tc_id
#print axioms CarryRadialFlow.source_normalized_response
#print axioms CarryRadialFlow.source_tc_odd
#print axioms CarryRadialFlow.source_tc_even
#print axioms CarryRadialFlow.flowResponse
#print axioms CarryRadialFlow.source_zero
#print axioms CarryRadialFlow.flow_analytic
#print axioms CarryRadialFlow.flow_equation
#print axioms CarryRadialFlow.flow_tc_recurrence
#print axioms CarryRadialFlow.flowJetPolynomial
#print axioms CarryRadialFlow.flow_first_eight
#print axioms CarryRadialFlow.cayleyResponse
#print axioms CarryRadialFlow.original_quotient_analytic
#print axioms CarryRadialFlow.original_quotient_eq_cayley
#print axioms CarryRadialFlow.cayley_flow_equation
#print axioms CarryRadialFlow.original_quotient_flow_equation
#print axioms CarryRadialFlow.original_rotated_response
#print axioms CarryRadialFlow.original_quotient_radial_real
#print axioms CarryRadialFlow.mu
#print axioms CarryRadialFlow.flowJetWitness
#print axioms CarryRadialFlow.radialWeight
#print axioms CarryRadialFlow.address
#print axioms CarryRadialFlow.fourFlowKernel
#print axioms CarryRadialFlow.nodeWeight
#print axioms CarryRadialFlow.fourFlowKernel_reduction
#print axioms CarryRadialFlow.flow_taylor_polynomial
#print axioms CarryRadialFlow.fourFlowKernel_exact_remainder
#print axioms CarryRadialFlow.fourFlowKernel_normalized_tendsto
#print axioms CarryRadialFlow.radialQuotient
#print axioms CarryRadialFlow.radialDefectEntry
#print axioms CarryRadialFlow.address_sum_ne_zero
#print axioms CarryRadialFlow.radial_defect_flow
#print axioms CarryRadialFlow.flowWitness
#print axioms CarryRadialFlow.slopeBox
#print axioms CarryRadialFlow.firstFlowBox
#print axioms CarryRadialFlow.secondFlowBox
#print axioms CarryRadialFlow.thirdFlowBox
#print axioms CarryRadialFlow.flowWitnessBox
#print axioms CarryRadialFlow.flowWitnessBox_negative
#print axioms CarryRadialFlow.source_flow_witness_neg
#print axioms CarryRadialFlow.actual_flow_jet_witness_neg
#print axioms CarryRadialFlow.flowJetWitness_re_neg
#print axioms CarryRadialFlow.fourFlowKernel_normalized_eventually_neg
#print axioms CarryRadialFlow.fourFlowKernel_eventually_neg
#print axioms CarryRadialFlow.radialWeightReal
#print axioms CarryRadialFlow.radialWeight_ofReal
#print axioms CarryRadialFlow.realFlowMatrix
#print axioms CarryRadialFlow.fourFlowKernel_real_form
#print axioms CarryRadialFlow.fourFlowMatrix_eventually_not_nonnegative

#audit_flow algebra
  CarryRadialFlow.tc
  CarryRadialFlow.tc_mul
  CarryRadialFlow.tc_add
  CarryRadialFlow.tc_deriv
  CarryRadialFlow.tc_id
  CarryRadialFlow.flowJetPolynomial
  CarryRadialFlow.radialWeight
  CarryRadialFlow.address
  CarryRadialFlow.nodeWeight
  CarryRadialFlow.flowWitness
  CarryRadialFlow.radialWeightReal

#audit_flow source
  CarryRadialFlow.source_normalized_response
  CarryRadialFlow.source_tc_odd
  CarryRadialFlow.source_tc_even
  CarryRadialFlow.flowResponse
  CarryRadialFlow.source_zero
  CarryRadialFlow.flow_analytic
  CarryRadialFlow.flow_equation
  CarryRadialFlow.flow_tc_recurrence
  CarryRadialFlow.flow_first_eight
  CarryRadialFlow.cayleyResponse
  CarryRadialFlow.original_quotient_analytic
  CarryRadialFlow.original_quotient_eq_cayley
  CarryRadialFlow.cayley_flow_equation
  CarryRadialFlow.original_quotient_flow_equation
  CarryRadialFlow.original_rotated_response
  CarryRadialFlow.original_quotient_radial_real
  CarryRadialFlow.mu
  CarryRadialFlow.flowJetWitness
  CarryRadialFlow.fourFlowKernel
  CarryRadialFlow.fourFlowKernel_reduction
  CarryRadialFlow.flow_taylor_polynomial
  CarryRadialFlow.fourFlowKernel_exact_remainder
  CarryRadialFlow.fourFlowKernel_normalized_tendsto
  CarryRadialFlow.radialQuotient
  CarryRadialFlow.radialDefectEntry
  CarryRadialFlow.address_sum_ne_zero
  CarryRadialFlow.radial_defect_flow

#audit_flow certificate
  CarryRadialFlow.slopeBox
  CarryRadialFlow.firstFlowBox
  CarryRadialFlow.secondFlowBox
  CarryRadialFlow.thirdFlowBox
  CarryRadialFlow.flowWitnessBox
  CarryRadialFlow.flowWitnessBox_negative
  CarryRadialFlow.source_flow_witness_neg
  CarryRadialFlow.actual_flow_jet_witness_neg
  CarryRadialFlow.flowJetWitness_re_neg
  CarryRadialFlow.fourFlowKernel_normalized_eventually_neg
  CarryRadialFlow.fourFlowKernel_eventually_neg
  CarryRadialFlow.radialWeight_ofReal
  CarryRadialFlow.realFlowMatrix
  CarryRadialFlow.fourFlowKernel_real_form
  CarryRadialFlow.fourFlowMatrix_eventually_not_nonnegative
