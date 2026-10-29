import QuarticFlux
import Lean

open Lean Elab Command
elab "#audit_quartic_taylor " group:ident ids:ident+ : command => do
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
  logInfo m!"Quartic Taylor {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryQuarticTaylor.response_eleventh_remainder
#print axioms CarryQuarticTaylor.remainderWeight11
#print axioms CarryQuarticTaylor.taylorWeight9
#print axioms CarryQuarticTaylor.response_weight_taylor11_prefix
#print axioms CarryQuarticTaylor.response_weight_taylor11_six
#print axioms CarryQuarticTaylor.remainder_weight11_continuous
#print axioms CarryQuarticTaylor.five
#print axioms CarryQuarticTaylor.quarticProfile
#print axioms CarryQuarticTaylor.profile_five
#print axioms CarryQuarticTaylor.weight_five
#print axioms CarryQuarticTaylor.profile_support
#print axioms CarryQuarticTaylor.commutator_five
#print axioms CarryQuarticTaylor.full_five_pairing
#print axioms CarryQuarticTaylor.kernel_three_input_expansion
#print axioms CarryQuarticTaylor.full_profile_weights
#print axioms CarryQuarticTaylor.quarticQuadratic
#print axioms CarryQuarticTaylor.quarticPolynomialError
#print axioms CarryQuarticTaylor.full_weight_cancellation
#print axioms CarryQuarticTaylor.radial_leading_two
#print axioms CarryQuarticTaylor.radial_leading_four
#print axioms CarryQuarticTaylor.critical_family_profile
#print axioms CarryQuarticTaylor.kernel_scale_both
#print axioms CarryQuarticTaylor.field_congr_prefix
#print axioms CarryQuarticTaylor.response_field_kernel_taylor11
#print axioms CarryQuarticTaylor.remainder_five_field_continuous
#print axioms CarryQuarticTaylor.remainder_profile_field_continuous
#print axioms CarryQuarticTaylor.remainder_profile_kernel_continuous
#print axioms CarryQuarticTaylor.remainder_profile_second_order
#print axioms CarryQuarticTaylor.canonicalQuarticQuadratic
#print axioms CarryQuarticTaylor.quarticFullError
#print axioms CarryQuarticTaylor.quarticLeadingFlux
#print axioms CarryQuarticTaylor.kernel_taylor9_real
#print axioms CarryQuarticTaylor.full_profile_taylor_cancellation
#print axioms CarryQuarticTaylor.quartic_sector_taylor_expansion
#print axioms CarryQuarticTaylor.quartic_full_flux_exact
#print axioms CarryQuarticTaylor.quartic_full_error_continuous
#print axioms CarryQuarticTaylor.quartic_complete_expansion
#print axioms CarryQuarticTaylor.quartic_full_energy_limit
#print axioms CarryQuarticTaylor.quartic_full_second_order_bound
#print axioms CarryQuarticTaylor.full_energy_norm_difference
#print axioms CarryQuarticTaylor.quartic_norm_difference_limit

#audit_quartic_taylor spatial
  CarryQuarticTaylor.five
  CarryQuarticTaylor.quarticProfile
  CarryQuarticTaylor.profile_five
  CarryQuarticTaylor.weight_five
  CarryQuarticTaylor.profile_support
  CarryQuarticTaylor.commutator_five
  CarryQuarticTaylor.full_five_pairing
  CarryQuarticTaylor.kernel_three_input_expansion
  CarryQuarticTaylor.full_profile_weights
  CarryQuarticTaylor.quarticQuadratic
  CarryQuarticTaylor.quarticPolynomialError
  CarryQuarticTaylor.full_weight_cancellation
  CarryQuarticTaylor.radial_leading_two
  CarryQuarticTaylor.radial_leading_four
  CarryQuarticTaylor.critical_family_profile
  CarryQuarticTaylor.kernel_scale_both

#audit_quartic_taylor provenance
  CarryQuarticTaylor.response_eleventh_remainder
  CarryQuarticTaylor.remainderWeight11
  CarryQuarticTaylor.taylorWeight9
  CarryQuarticTaylor.response_weight_taylor11_prefix
  CarryQuarticTaylor.response_weight_taylor11_six
  CarryQuarticTaylor.remainder_weight11_continuous
  CarryQuarticTaylor.field_congr_prefix
  CarryQuarticTaylor.response_field_kernel_taylor11
  CarryQuarticTaylor.remainder_five_field_continuous
  CarryQuarticTaylor.remainder_profile_field_continuous
  CarryQuarticTaylor.remainder_profile_kernel_continuous
  CarryQuarticTaylor.remainder_profile_second_order
  CarryQuarticTaylor.canonicalQuarticQuadratic
  CarryQuarticTaylor.quarticFullError
  CarryQuarticTaylor.quarticLeadingFlux
  CarryQuarticTaylor.kernel_taylor9_real
  CarryQuarticTaylor.full_profile_taylor_cancellation
  CarryQuarticTaylor.quartic_sector_taylor_expansion
  CarryQuarticTaylor.quartic_full_flux_exact
  CarryQuarticTaylor.quartic_full_error_continuous
  CarryQuarticTaylor.quartic_complete_expansion
  CarryQuarticTaylor.quartic_full_energy_limit
  CarryQuarticTaylor.quartic_full_second_order_bound
  CarryQuarticTaylor.full_energy_norm_difference
  CarryQuarticTaylor.quartic_norm_difference_limit
