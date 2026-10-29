import CriticalSchur
import Lean

open Lean Elab Command
elab "#audit_quartic_correction " group:ident ids:ident+ : command => do
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
  logInfo m!"Quartic correction {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryQuarticCorrection.response_remainder11_with_value
#print axioms CarryQuarticCorrection.nativeRemainder11
#print axioms CarryQuarticCorrection.native_remainder_analytic
#print axioms CarryQuarticCorrection.native_remainder_value
#print axioms CarryQuarticCorrection.native_response_taylor11
#print axioms CarryQuarticCorrection.native_response_weight_prefix
#print axioms CarryQuarticCorrection.remainder_value_of_response_identity
#print axioms CarryQuarticCorrection.full_quartic_weight11_complex
#print axioms CarryQuarticCorrection.full_quartic_weight11_real
#print axioms CarryQuarticCorrection.zero_remainder_kernel
#print axioms CarryQuarticCorrection.quarticCorrection
#print axioms CarryQuarticCorrection.native_response_field_kernel_prefix
#print axioms CarryQuarticCorrection.native_sector_expansion
#print axioms CarryQuarticCorrection.native_complete_expansion
#print axioms CarryQuarticCorrection.native_full_error_zero
#print axioms CarryQuarticCorrection.native_scaled_error_limit
#print axioms CarryQuarticCorrection.native_scaled_norm_difference_limit
#print axioms CarryQuarticCorrection.native_eventually_below
#print axioms CarryQuarticCorrection.native_eventually_above
#print axioms CarryQuarticCorrection.oldBlockSolution
#print axioms CarryQuarticCorrection.quartic_schur_identity
#print axioms CarryQuarticCorrection.criticalQuarticA
#print axioms CarryQuarticCorrection.criticalQuarticB
#print axioms CarryQuarticCorrection.critical_quartic_schur
#print axioms CarryQuarticCorrection.critical_scaled_error_limit
#print axioms CarryQuarticCorrection.critical_scaled_norm_difference_limit
#print axioms CarryQuarticCorrection.critical_full_energy_limit

#audit_quartic_correction spatial
  CarryQuarticCorrection.full_quartic_weight11_complex
  CarryQuarticCorrection.full_quartic_weight11_real
  CarryQuarticCorrection.zero_remainder_kernel
  CarryQuarticCorrection.oldBlockSolution
  CarryQuarticCorrection.quartic_schur_identity

#audit_quartic_correction provenance
  CarryQuarticCorrection.response_remainder11_with_value
  CarryQuarticCorrection.nativeRemainder11
  CarryQuarticCorrection.native_remainder_analytic
  CarryQuarticCorrection.native_remainder_value
  CarryQuarticCorrection.native_response_taylor11
  CarryQuarticCorrection.native_response_weight_prefix
  CarryQuarticCorrection.remainder_value_of_response_identity
  CarryQuarticCorrection.quarticCorrection
  CarryQuarticCorrection.native_response_field_kernel_prefix
  CarryQuarticCorrection.native_sector_expansion
  CarryQuarticCorrection.native_complete_expansion
  CarryQuarticCorrection.native_full_error_zero
  CarryQuarticCorrection.native_scaled_error_limit
  CarryQuarticCorrection.native_scaled_norm_difference_limit
  CarryQuarticCorrection.native_eventually_below
  CarryQuarticCorrection.native_eventually_above
  CarryQuarticCorrection.criticalQuarticA
  CarryQuarticCorrection.criticalQuarticB
  CarryQuarticCorrection.critical_quartic_schur
  CarryQuarticCorrection.critical_scaled_error_limit
  CarryQuarticCorrection.critical_scaled_norm_difference_limit
  CarryQuarticCorrection.critical_full_energy_limit
