import SourceGateIndependence
import Lean

open Lean Elab Command
elab "#audit_source_orientation " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryIntegralCertificate.material_theta_integral_input,
    `CarryIntegralCertificate.mem_logMomentBox,
    `CarryIntegralCertificate.mem_characteristicBox,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    `CarrySelfAdjointOperator.completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    `CarrySelfAdjointOperator.completedNativeThetaTailMoment_zero_le_calibration,
    `CarryMaterialSourceFactorComparison.material_even_pivots_three_pos,
    `CarryMaterialSourceFactorComparison.material_even_three_posDef,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySourceBezout.native_second_even_pivot_pos_from_original_split,
    `CarrySourceBezout.native_second_even_remainder_pos_from_original_split]
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
  let required := #[`CarryC3Boxes.canonical_four_source_boxes,
    `CarrySourceBezout.sourceSchur_eq_scaled,
    `CarrySourceBezout.native_source_recurrence]
  for name in required do
    unless seen.contains name do throwError "Missing declared provenance: {name}"
  logInfo m!"Source orientation audit: roots {ids.size}; closure {seen.size}; standard axioms only; specified theta-box and sign dependencies absent; PR #70 source boxes and Schur transport present"

#audit_source_orientation CarrySourceDimensionThree.native_even_gate CarrySourceDimensionThree.native_odd_gate CarrySourceDimensionThree.even_schur_data_insufficient CarrySourceDimensionThree.odd_schur_data_insufficient CarrySourceDimensionThree.even_ceiling_unchanged CarrySourceDimensionThree.odd_ceiling_unchanged
