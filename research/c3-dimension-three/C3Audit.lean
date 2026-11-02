import PivotBoxes
import Lean

open Lean Elab Command
elab "#audit_c3_dimension_three " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryMaterialSourceFactorComparison.material_even_pivots_three_pos,
    `CarryMaterialSourceFactorComparison.material_even_three_posDef,
    `CarrySourceBezout.native_second_even_pivot_pos_from_original_split,
    `CarrySourceBezout.native_second_even_remainder_pos_from_original_split,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg,
    `CarryC3Boxes.canonical_two_even_determinant_pos_from_c3,
    `CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes]
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
      if forbidden.contains name then throwError "Forbidden sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unexpected axiom: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing dependency: {name}"
  let required := #[`CarryC3Tail.accelerated_c3_tail_bound,
    `CarryIntegralCertificate.material_theta_integral_input,
    `CarrySourceBezout.criticalVector_mulVec,
    `CarryUniformSource.repartition_explicit_order_bound]
  for name in required do
    unless seen.contains name do throwError "Missing declared provenance: {name}"
  logInfo m!"C3 dimension three audit: roots {ids.size}; type/body closure {seen.size}; standard axioms only; specified sign dependencies absent; original tail and theta boxes present"

#audit_c3_dimension_three CarryC3DimensionThree.c3_256_critical_error_unconditional CarryC3DimensionThree.c3_256_positive_from_head CarryC3DimensionThree.sourcePair_gt_six CarryC3DimensionThree.sourceHead_gt_three CarryC3DimensionThree.pivot_positive_from_certified_boxes
