import CubicRecomposition
import Lean

open Lean Elab Command
elab "#audit_green_cubic " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarryCrossRadial.first_cross_exact,
    `CarryCrossRadial.doubled_first_exact,
    `CarryCrossRadial.doubled_scaled_tendsto,
    `CarryCrossRadial.doubled_scaled_expansion,
    `CarryCrossRadial.doubled_unscaled_expansion,
    `CarryCrossRadial.doubled_next_tendsto,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
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
      if forbidden.contains name ||
          (construction && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden canonical/sign dependency: {name}"
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
  logInfo m!"Vector Green cubic coefficient {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryGreenCubic.part_field_sum_weight
#print axioms CarryGreenCubic.part_full_taylor_expansion
#print axioms CarryGreenCubic.part_full_remainder_continuous
#print axioms CarryGreenCubic.cubicProfile
#print axioms CarryGreenCubic.seed_address_compensation
#print axioms CarryGreenCubic.seed_cubic_compensation
#print axioms CarryGreenCubic.seed_cubic_residual_ne_zero
#print axioms CarryGreenCubic.cubicPart
#print axioms CarryGreenCubic.cubic_part_expansion
#print axioms CarryGreenCubic.cubic_part_tendsto
#print axioms CarryGreenCubic.doubled_cubic_vector_identity
#print axioms CarryGreenCubic.cubic_crossing_identity
#print axioms CarryGreenCubic.cubicCoefficient
#print axioms CarryGreenCubic.cubic_crossing_tendsto
#print axioms CarryGreenCubic.cubic_residual_residual_zero
#print axioms CarryGreenCubic.cubic_residual_row
#print axioms CarryGreenCubic.cubic_residual_column
#print axioms CarryGreenCubic.sum_cubic_pairings
#print axioms CarryGreenCubic.sum_cubic_eq
#print axioms CarryGreenCubic.recomposed_cubic_tendsto
#print axioms CarryGreenCubic.recomposed_green_cubic_tendsto

#audit_green_cubic construction
  CarryGreenCubic.part_field_sum_weight
  CarryGreenCubic.seed_address_compensation
  CarryGreenCubic.cubicProfile
  CarryGreenCubic.seed_cubic_compensation
  CarryGreenCubic.seed_cubic_residual_ne_zero
  CarryGreenCubic.sum_cubic_pairings


#audit_green_cubic provenance
  CarryGreenCubic.part_full_taylor_expansion
  CarryGreenCubic.part_full_remainder_continuous
  CarryGreenCubic.cubicPart
  CarryGreenCubic.cubic_part_expansion
  CarryGreenCubic.cubic_part_tendsto
  CarryGreenCubic.doubled_cubic_vector_identity
  CarryGreenCubic.cubic_crossing_identity
  CarryGreenCubic.cubicCoefficient
  CarryGreenCubic.cubic_crossing_tendsto
  CarryGreenCubic.cubic_residual_residual_zero
  CarryGreenCubic.cubic_residual_row
  CarryGreenCubic.cubic_residual_column
  CarryGreenCubic.sum_cubic_eq
  CarryGreenCubic.recomposed_cubic_tendsto
  CarryGreenCubic.recomposed_green_cubic_tendsto
