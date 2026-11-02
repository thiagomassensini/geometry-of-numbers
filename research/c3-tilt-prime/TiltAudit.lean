import TransverseLedger
import MixedPrime
import Lean

open Lean Elab Command
elab "#audit_tilt_source " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryIntegralCertificate.material_theta_integral_input,
    `CarryIntegralCertificate.mem_logMomentBox,
    `CarryIntegralCertificate.mem_characteristicBox,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarryMaterialSourceFactorComparison.material_even_pivots_three_pos,
    `CarryMaterialSourceFactorComparison.material_even_three_posDef,
    `CarryC3DimensionThree.pivot_positive_from_certified_boxes,
    `CarryC3DimensionThree.sourcePair_gt_six,
    `CarryC3DimensionThree.sourceHead_gt_three]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do throwError "Unexpected axiom in {decl}: {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then throwError "Forbidden theta-box or sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unexpected axiom: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing dependency: {name}"
  let required := #[
    `CPFormal.Analytic.Cp.finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder,
    `CarryC3Tail.native_c3_head_tail,
    `CarryC3Tail.characteristic_c3_formula,
    `CarrySourceDimensionThree.native_even_gate,
    `CarrySourceDimensionThree.native_odd_gate,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse,
    `CarrySelfAdjointOperator.deriv_finiteCanonicalRealCriticalWeightedTiltTrace_zero_pos,
    `CarrySelfAdjointOperator.completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder,
    `CarrySelfAdjointOperator.canonicalRealCriticalWeightedTiltTotalSensitivity_pos,
    `CarrySelfAdjointOperator.hasDerivAt_cpTilt_three_zero,
    `CarrySelfAdjointOperator.primeDepthLogLedger_eq_log,
    `CarrySelfAdjointOperator.carryTiltThreeFirstSensitivity_le_two_div_sq]
  for name in required do
    unless seen.contains name do throwError "Missing declared provenance: {name}"
  logInfo m!"Tilt and prime-depth audit: roots {ids.size}; closure {seen.size}; standard axioms only; specified theta/sign consumers absent; source, C3 tail, prime-depth, transverse sensitivity and Schur transport present"

#audit_tilt_source CarryTiltSlice.finite_tilt_vertical_jets_zero CarryTiltSlice.transverse_sensitivity_positive CarryTiltSlice.native_even_coefficient_carrier_boundary_tail CarryTiltSlice.even_pivot_gate_carrier CarryTiltSlice.odd_pivot_gate_carrier CarryTiltSlice.prime_depth_carrier_recurrence CarryTiltSlice.height_jets_zero_transverse_sensitivity_pos CarryTiltSlice.transverse_global_ledger CarryTiltSlice.finite_mixed_tilt_identity CarryTiltSlice.finite_mixed_tilt_positive CarryTiltSlice.mixedTiltTerm_summable CarryTiltSlice.primeDepthMixedTiltTerm_tsum_pos CarryTiltSlice.finite_mixed_prime_depth_tendsto_positive
