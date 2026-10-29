import GreenRegression
import Lean

open Lean Elab Command
elab "#audit_green_leading " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
  logInfo m!"Vector Green leading coefficient {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

#print axioms CarryGreenLeading.partField
#print axioms CarryGreenLeading.part_field_reconstruction
#print axioms CarryGreenLeading.part_field_add_weight
#print axioms CarryGreenLeading.part_field_scale_weight
#print axioms CarryGreenLeading.part_field_scale_input
#print axioms CarryGreenLeading.part_field_finite_locality
#print axioms CarryGreenLeading.completed_part_as_fields
#print axioms CarryGreenLeading.completed_part_scale_input
#print axioms CarryGreenLeading.part_constant_residual_zero
#print axioms CarryGreenLeading.constantPart
#print axioms CarryGreenLeading.linearPart
#print axioms CarryGreenLeading.native_part_coordinates
#print axioms CarryGreenLeading.native_part_contrast_mean
#print axioms CarryGreenLeading.part_response_expansion
#print axioms CarryGreenLeading.part_field_continuous
#print axioms CarryGreenLeading.part_remainder_continuous
#print axioms CarryGreenLeading.normalizedPart
#print axioms CarryGreenLeading.normalized_part_expansion
#print axioms CarryGreenLeading.normalized_part_tendsto
#print axioms CarryGreenLeading.chiral_difference_square
#print axioms CarryGreenLeading.native_parts_pair
#print axioms CarryGreenLeading.partCross
#print axioms CarryGreenLeading.part_cross_exact
#print axioms CarryGreenLeading.part_cross_scaled_identity
#print axioms CarryGreenLeading.leadingCoefficient
#print axioms CarryGreenLeading.part_cross_scaled_tendsto
#print axioms CarryGreenLeading.double_inner_sum
#print axioms CarryGreenLeading.sum_cross_coefficients
#print axioms CarryGreenLeading.sum_leading_eq
#print axioms CarryGreenLeading.part_cross_sum
#print axioms CarryGreenLeading.recomposed_leading_tendsto
#print axioms CarryGreenLeading.leading_residual_residual_zero
#print axioms CarryGreenLeading.leading_residual_row
#print axioms CarryGreenLeading.leading_residual_column
#print axioms CarryGreenLeading.linear_even_residual
#print axioms CarryGreenLeading.even_vector_compensation
#print axioms CarryGreenLeading.linear_even_residual_ne_zero

#audit_green_leading construction
  CarryGreenLeading.partField
  CarryGreenLeading.part_field_reconstruction
  CarryGreenLeading.part_field_add_weight
  CarryGreenLeading.part_field_scale_weight
  CarryGreenLeading.part_field_scale_input
  CarryGreenLeading.part_field_finite_locality
  CarryGreenLeading.completed_part_as_fields
  CarryGreenLeading.completed_part_scale_input
  CarryGreenLeading.part_constant_residual_zero
  CarryGreenLeading.constantPart
  CarryGreenLeading.linearPart
  CarryGreenLeading.native_part_coordinates
  CarryGreenLeading.native_part_contrast_mean
  CarryGreenLeading.part_field_continuous
  CarryGreenLeading.normalizedPart
  CarryGreenLeading.chiral_difference_square
  CarryGreenLeading.native_parts_pair
  CarryGreenLeading.partCross
  CarryGreenLeading.part_cross_exact
  CarryGreenLeading.part_cross_scaled_identity
  CarryGreenLeading.double_inner_sum
  CarryGreenLeading.sum_cross_coefficients
  CarryGreenLeading.part_cross_sum
  CarryGreenLeading.linear_even_residual
  CarryGreenLeading.linear_even_residual_ne_zero
  CarryGreenLeading.even_vector_compensation


#audit_green_leading provenance
  CarryGreenLeading.part_response_expansion
  CarryGreenLeading.part_remainder_continuous
  CarryGreenLeading.normalized_part_expansion
  CarryGreenLeading.normalized_part_tendsto
  CarryGreenLeading.leadingCoefficient
  CarryGreenLeading.part_cross_scaled_tendsto
  CarryGreenLeading.sum_leading_eq
  CarryGreenLeading.recomposed_leading_tendsto
  CarryGreenLeading.leading_residual_residual_zero
  CarryGreenLeading.leading_residual_row
  CarryGreenLeading.leading_residual_column
