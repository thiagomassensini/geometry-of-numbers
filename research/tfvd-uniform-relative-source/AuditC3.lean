import C3UniformRegression
import C3OrderRate
import Lean

open Lean Elab Command
elab "#audit_source_transport " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySourceBezout.native_second_even_pivot_pos_from_original_split,
    `CarrySourceBezout.native_second_even_remainder_pos_from_original_split,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg,
    `CarryC3Boxes.canonical_two_even_determinant_pos_from_c3,
    `CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes]
  let forbidden := if mode.getId == `NativeRepartition64 then forbidden ++ #[
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    `CarrySelfAdjointOperator.completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    `CarrySelfAdjointOperator.completedNativeThetaTailMoment_zero_le_calibration]
    else forbidden
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
        throwError "Circular/later sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency in imported environment: {name}"

  let required := #[`CarryC3Boxes.canonical_four_source_boxes,
    `CarryC3Tail.completed_tail_jet_error,
    `CarryUniformSource.critical_positive_of_repartition_head,
    `CarrySourceBezout.native_even_one_isUnit_from_source]
  for name in required do
    unless seen.contains name do throwError "Missing source provenance: {name}"
  let extra := if mode.getId == `NativeRepartition64 then "; C3 split excludes theta calibration" else ""
  logInfo m!"Source residual audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; standard axioms only; forbidden sign dependencies absent{extra}"

#audit_source_transport NativeRepartition64 CarryUniformSource.c3_second_pivot_pos_via_uniform_budget CarryUniformSource.c3_second_scaled_margin_via_uniform_budget CarryUniformSource.c3_critical_explicit_order_rate
