import ImaginaryRegression
import Lean

open Lean Elab Command
elab "#audit_mixed_imaginary " group:ident ids:ident+ : command => do
  let spatial := group.getId == `spatial
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
          (spatial && (name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic ||
            name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment)) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Canonical or downstream sign dependency in spatial proof: {name}"
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
  logInfo m!"All-order mixed imaginary law {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryMixedImaginary.divided_one_above
#print axioms CarryMixedImaginary.mixedSlope
#print axioms CarryMixedImaginary.mixedStaticPair
#print axioms CarryMixedImaginary.mixed_static_divided
#print axioms CarryMixedImaginary.mixed_static_below
#print axioms CarryMixedImaginary.mixed_static_leading
#print axioms CarryMixedImaginary.mixed_profile_phase
#print axioms CarryMixedImaginary.mixedOrderWeight
#print axioms CarryMixedImaginary.mixed_slope_eq_weight
#print axioms CarryMixedImaginary.mixed_weight_pos
#print axioms CarryMixedImaginary.mixed_weight_neg
#print axioms CarryMixedImaginary.mixed_taylor_sum
#print axioms CarryMixedImaginary.mixed_taylor_cancellation
#print axioms CarryMixedImaginary.mixed_response_expansion
#print axioms CarryMixedImaginary.remainder_samples_continuous
#print axioms CarryMixedImaginary.mixed_remainder_continuous
#print axioms CarryMixedImaginary.normalizedMixedRay
#print axioms CarryMixedImaginary.mixed_phase_leading
#print axioms CarryMixedImaginary.normalized_mixed_expansion
#print axioms CarryMixedImaginary.normalized_mixed_tendsto
#print axioms CarryMixedImaginary.finite_mixed_kernel_pairing
#print axioms CarryMixedImaginary.finite_mixed_pairing
#print axioms CarryMixedImaginary.imaginaryCoefficient
#print axioms CarryMixedImaginary.finite_mixed_scaled_tendsto
#print axioms CarryMixedImaginary.finite_mixed_imaginary_tendsto
#print axioms CarryMixedImaginary.mixedGreenPair
#print axioms CarryMixedImaginary.finite_mixed_green_scaled_tendsto
#print axioms CarryMixedImaginary.mixed_weights_low_order
#print axioms CarryMixedImaginary.mixed_weight_ne_zero
#print axioms CarryMixedImaginary.not_all_mixed_weights_nonnegative
#print axioms CarryMixedImaginary.first_mixed_from_all_order
#print axioms CarryMixedImaginary.mixed_jet_scaled_tendsto
#print axioms CarryMixedImaginary.imaginary_coefficient_two_ordered_terms
#print axioms CarryMixedImaginary.mixed_orthogonality_forces_coefficient_zero

#audit_mixed_imaginary spatial
  CarryMixedImaginary.divided_one_above
  CarryMixedImaginary.mixedSlope
  CarryMixedImaginary.mixedStaticPair
  CarryMixedImaginary.mixed_static_divided
  CarryMixedImaginary.mixed_static_below
  CarryMixedImaginary.mixed_static_leading
  CarryMixedImaginary.mixed_profile_phase
  CarryMixedImaginary.mixedOrderWeight
  CarryMixedImaginary.mixed_slope_eq_weight
  CarryMixedImaginary.mixed_weight_pos
  CarryMixedImaginary.mixed_weight_neg
  CarryMixedImaginary.mixed_weights_low_order
  CarryMixedImaginary.mixed_weight_ne_zero
  CarryMixedImaginary.not_all_mixed_weights_nonnegative

#audit_mixed_imaginary provenance
  CarryMixedImaginary.mixed_taylor_sum
  CarryMixedImaginary.mixed_taylor_cancellation
  CarryMixedImaginary.mixed_response_expansion
  CarryMixedImaginary.remainder_samples_continuous
  CarryMixedImaginary.mixed_remainder_continuous
  CarryMixedImaginary.normalizedMixedRay
  CarryMixedImaginary.mixed_phase_leading
  CarryMixedImaginary.normalized_mixed_expansion
  CarryMixedImaginary.normalized_mixed_tendsto
  CarryMixedImaginary.finite_mixed_kernel_pairing
  CarryMixedImaginary.finite_mixed_pairing
  CarryMixedImaginary.imaginaryCoefficient
  CarryMixedImaginary.finite_mixed_scaled_tendsto
  CarryMixedImaginary.finite_mixed_imaginary_tendsto
  CarryMixedImaginary.mixedGreenPair
  CarryMixedImaginary.finite_mixed_green_scaled_tendsto
  CarryMixedImaginary.first_mixed_from_all_order
  CarryMixedImaginary.mixed_jet_scaled_tendsto
  CarryMixedImaginary.imaginary_coefficient_two_ordered_terms
  CarryMixedImaginary.mixed_orthogonality_forces_coefficient_zero
