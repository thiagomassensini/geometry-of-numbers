import NativeEvenCertificate
import NativeOddCertificate
import C3Regression
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

/-- Checks the recorded declaration closure, including theorem bodies, for the
allowed axioms and the specified alternative sign routes. -/
elab "#audit_c3_certificate " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryC3DimensionThree.pivot_positive_from_certified_boxes,
    `CarryIntegralCertificate.material_theta_integral_input,
    `CarryIntegralCertificate.mem_logMomentBox,
    `CarryIntegralCertificate.mem_characteristicBox,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    `CarrySelfAdjointOperator.completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    `CarryMaterialSourceFactorComparison.material_even_pivots_three_pos,
    `CarryMaterialSourceFactorComparison.material_even_three_posDef,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos]
  let forbiddenModules := #[`PivotBoxes, `CanonicalPivotCertificate]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for axiomName in (← collectAxioms decl) do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {decl}: {axiomName}"
  let mathModules := #[
    `C3Acceleration48, `C3Power26Step, `C3Power26Tail, `C3Power26Series,
    `C3Boundary48Finite, `C3Boundary48Infinity, `C3Boundary48Stencil,
    `C3CompletionTail48, `C3Head48Jet, `C3Head48Boxes, `GeneralCofactorIdentity,
    `ChiralOrder11, `CofactorIdentity, `SchurGate, `IntervalGate, `C3Regression,
    `GammaThirteen, `CompletedBoxes48, `GammaHeadCrosswalk, `SourceGate,
    `CorrelationGate, `ChartReciprocal, `BaseCoefficient, `CompletedCoefficient,
    `CorrelationInterval, `LeftJetMagnitudeLow, `LeftJetMagnitudeHigh, `LeftJetMagnitude,
    `BoundaryTransport, `FiniteReferenceTable, `SourceCoefficientGreen,
    `CofactorTransport, `NativeOddCertificate, `NativeEvenCertificate]
  for moduleName in mathModules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Missing mission module: {moduleName}"
  let mut audited : Nat := 0
  for idx in [:env.header.moduleNames.size] do
    if mathModules.contains env.header.moduleNames[idx]! then
      for info in env.header.moduleData[idx]!.constants do
        match info with
        | .thmInfo _ =>
          todo := info.name :: todo
          audited := audited + 1
        | .axiomInfo _ => throwError "Mission module declared an axiom: {info.name}"
        | _ => pure ()
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then
        throwError "Unexpected sign or theta-box dependency: {name}"
      if let some idx := env.getModuleIdxFor? name then
        if let some moduleName := env.header.moduleNames[idx.toNat]? then
          if forbiddenModules.contains moduleName then
            throwError "Unexpected declaration from {moduleName}: {name}"
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing dependency: {name}"
      if let .axiomInfo _ := info then
        unless allowed.contains name do
          throwError "Unexpected axiom: {name}"
      todo := info.type.getUsedConstants.toList ++ todo
      if let some value := info.value? (allowOpaque := true) then
        todo := value.getUsedConstants.toList ++ todo
  let required := #[
    `C3CofactorCorrelation.native_even_coefficient_candidate_contains,
    `C3CofactorCorrelation.completed_native_jet_reference_error48_tight,
    `CarryC3Tail.completed_native_head_tail48,
    `CarryOddHeadSource.odd_prefix_isUnit_from_completed_c3,
    `CarrySourceBezout.native_source_bezout_posDef_iff,
    `CarrySourceBezout.sourceSchur_eq_scaled,
    `CarryCriticalRelative.critical_scaled_relative_deficit]
  for name in required do
    unless seen.contains name do throwError "Missing expected provenance: {name}"
  logInfo m!"C3 certificate audit: {ids.size} result roots, {audited} mission theorems, {seen.size} dependencies. Only standard axioms, specified alternative sign routes excluded"

#audit_c3_certificate
  CarryC3Tail.c3_acceleration48_polynomial
  C3GeneralCofactor.transportedCofactor_eq_criticalVector
  C3GeneralCofactor.transportedCofactor_last
  C3GeneralCofactor.transportedCofactor_properties_of_ne_zero
  C3GeneralCofactor.hankel_mulVec_transportedCofactor
  C3GeneralCofactor.hankel_transportedCofactor_energy
  C3GeneralCofactor.sourceMomentSchur_pos_of_block_posDef
  C3CofactorChiral.c3_odd_third_cofactor_polynomial_positive
  C3CofactorChiral.c3_odd_third_bezout_det_positive
  C3CofactorChiral.c3_odd_third_source_schur_positive
  C3CofactorChiral.c3_odd_third_native_pivot_positive
  C3CofactorChiral.c3_odd_cofactor_eq_criticalCoefficients
  C3CofactorChiral.c3_odd_third_gap_coefficient_positive
  C3CofactorChiral.c3_odd_third_scaled_relative_deficit_positive_limit
  C3CofactorChiral.c3_odd_third_relative_gap_positive
  C3CofactorChiral.c3_even_third_bezout_det_lower
  C3CofactorChiral.c3_even_third_native_pivot_positive
