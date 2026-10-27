import OddRegression
import Lean

open Lean Elab Command
elab "#audit_odd_energy " group:ident ids:ident+ : command => do
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
  logInfo m!"All-order odd energy {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryOddEnergy.nativeOddProfile
#print axioms CarryOddEnergy.oddPairKernel
#print axioms CarryOddEnergy.shifted_power_complex
#print axioms CarryOddEnergy.divided_coefficient_native
#print axioms CarryOddEnergy.divided_leading_native
#print axioms CarryOddEnergy.divided_first_odd
#print axioms CarryOddEnergy.radial_odd_calibration
#print axioms CarryOddEnergy.odd_profile_support
#print axioms CarryOddEnergy.odd_pair_static
#print axioms CarryOddEnergy.odd_pair_divided
#print axioms CarryOddEnergy.odd_pair_below
#print axioms CarryOddEnergy.odd_pair_leading
#print axioms CarryOddEnergy.odd_pair_correction
#print axioms CarryOddEnergy.odd_pair_taylor_sum
#print axioms CarryOddEnergy.odd_pair_taylor_cancellation
#print axioms CarryOddEnergy.odd_pair_response_expansion
#print axioms CarryOddEnergy.odd_pair_remainder_continuous
#print axioms CarryOddEnergy.normalizedOddPair
#print axioms CarryOddEnergy.normalized_odd_pair_expansion
#print axioms CarryOddEnergy.normalized_odd_pair_correction_tendsto
#print axioms CarryOddEnergy.finiteOddJetSource
#print axioms CarryOddEnergy.finite_odd_source_profile
#print axioms CarryOddEnergy.finite_odd_source_original
#print axioms CarryOddEnergy.finite_odd_source_support
#print axioms CarryOddEnergy.finite_odd_source_pairing
#print axioms CarryOddEnergy.finite_odd_energy_pairing
#print axioms CarryOddEnergy.finite_odd_green_recomposition
#print axioms CarryOddEnergy.oddCanonicalForm
#print axioms CarryOddEnergy.oddCanonicalCorrection
#print axioms CarryOddEnergy.finite_odd_energy_correction_tendsto
#print axioms CarryOddEnergy.finite_odd_green_correction_tendsto
#print axioms CarryOddEnergy.odd_profile_zero
#print axioms CarryOddEnergy.odd_profile_one
#print axioms CarryOddEnergy.odd_coefficient_regression
#print axioms CarryOddEnergy.odd_coefficient_minor_negative
#print axioms CarryOddEnergy.first_odd_correction
#print axioms CarryOddEnergy.cubicOddCoefficients
#print axioms CarryOddEnergy.odd_cubic_source
#print axioms CarryOddEnergy.odd_cubic_form
#print axioms CarryOddEnergy.odd_cubic_correction
#print axioms CarryOddEnergy.odd_cubic_correction_tendsto
#print axioms CarryOddEnergy.finite_odd_norm_difference_correction

#audit_odd_energy spatial
  CarryOddEnergy.nativeOddProfile
  CarryOddEnergy.oddPairKernel
  CarryOddEnergy.shifted_power_complex
  CarryOddEnergy.divided_coefficient_native
  CarryOddEnergy.divided_leading_native
  CarryOddEnergy.divided_first_odd
  CarryOddEnergy.radial_odd_calibration
  CarryOddEnergy.odd_profile_support
  CarryOddEnergy.odd_pair_static
  CarryOddEnergy.odd_pair_divided
  CarryOddEnergy.odd_pair_below
  CarryOddEnergy.odd_pair_leading
  CarryOddEnergy.odd_pair_correction
  CarryOddEnergy.finiteOddJetSource
  CarryOddEnergy.finite_odd_source_profile
  CarryOddEnergy.finite_odd_source_support
  CarryOddEnergy.odd_profile_zero
  CarryOddEnergy.odd_profile_one
  CarryOddEnergy.odd_coefficient_regression
  CarryOddEnergy.odd_coefficient_minor_negative
  CarryOddEnergy.cubicOddCoefficients

#audit_odd_energy provenance
  CarryOddEnergy.odd_pair_taylor_sum
  CarryOddEnergy.odd_pair_taylor_cancellation
  CarryOddEnergy.odd_pair_response_expansion
  CarryOddEnergy.odd_pair_remainder_continuous
  CarryOddEnergy.normalizedOddPair
  CarryOddEnergy.normalized_odd_pair_expansion
  CarryOddEnergy.normalized_odd_pair_correction_tendsto
  CarryOddEnergy.finite_odd_source_original
  CarryOddEnergy.finite_odd_source_pairing
  CarryOddEnergy.finite_odd_energy_pairing
  CarryOddEnergy.finite_odd_green_recomposition
  CarryOddEnergy.oddCanonicalForm
  CarryOddEnergy.oddCanonicalCorrection
  CarryOddEnergy.finite_odd_energy_correction_tendsto
  CarryOddEnergy.finite_odd_green_correction_tendsto
  CarryOddEnergy.first_odd_correction
  CarryOddEnergy.odd_cubic_source
  CarryOddEnergy.odd_cubic_form
  CarryOddEnergy.odd_cubic_correction
  CarryOddEnergy.odd_cubic_correction_tendsto
  CarryOddEnergy.finite_odd_norm_difference_correction
