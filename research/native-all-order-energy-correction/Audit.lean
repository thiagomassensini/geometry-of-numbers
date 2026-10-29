import RegressionEnergy
import Lean

open Lean Elab Command
elab "#audit_energy_correction " group:ident ids:ident+ : command => do
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
  logInfo m!"All-order energy correction {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryEnergyCorrection.oddTaylor
#print axioms CarryEnergyCorrection.response_taylor_polynomial
#print axioms CarryEnergyCorrection.response_odd_remainder
#print axioms CarryEnergyCorrection.nativeRemainder
#print axioms CarryEnergyCorrection.native_remainder_analytic
#print axioms CarryEnergyCorrection.native_response_expansion
#print axioms CarryEnergyCorrection.responseSamples
#print axioms CarryEnergyCorrection.taylorSamples
#print axioms CarryEnergyCorrection.remainderSamples
#print axioms CarryEnergyCorrection.response_samples_prefix
#print axioms CarryEnergyCorrection.kernel
#print axioms CarryEnergyCorrection.pairKernel
#print axioms CarryEnergyCorrection.kernel_add
#print axioms CarryEnergyCorrection.kernel_scale
#print axioms CarryEnergyCorrection.kernel_sum_weight
#print axioms CarryEnergyCorrection.native_profile_support
#print axioms CarryEnergyCorrection.response_synthesis_expansion
#print axioms CarryEnergyCorrection.pair_taylor_sum
#print axioms CarryEnergyCorrection.pair_below
#print axioms CarryEnergyCorrection.pair_leading
#print axioms CarryEnergyCorrection.pair_correction
#print axioms CarryEnergyCorrection.pair_taylor_cancellation
#print axioms CarryEnergyCorrection.pair_response_expansion
#print axioms CarryEnergyCorrection.weighted_synthesis_sum
#print axioms CarryEnergyCorrection.weighted_synthesis_continuous
#print axioms CarryEnergyCorrection.pair_remainder_continuous
#print axioms CarryEnergyCorrection.normalizedPair
#print axioms CarryEnergyCorrection.normalized_pair_expansion
#print axioms CarryEnergyCorrection.normalized_pair_correction_tendsto
#print axioms CarryEnergyCorrection.finiteJetSource
#print axioms CarryEnergyCorrection.finite_source_profile
#print axioms CarryEnergyCorrection.finite_source_original
#print axioms CarryEnergyCorrection.finite_source_support
#print axioms CarryEnergyCorrection.weight_sum_input
#print axioms CarryEnergyCorrection.kernel_sum_inputs
#print axioms CarryEnergyCorrection.kernel_scale_inputs
#print axioms CarryEnergyCorrection.double_sum_symmetrize
#print axioms CarryEnergyCorrection.finite_source_pairing
#print axioms CarryEnergyCorrection.finite_energy_pairing
#print axioms CarryEnergyCorrection.finite_source_green_recomposition
#print axioms CarryEnergyCorrection.canonicalForm
#print axioms CarryEnergyCorrection.canonicalCorrection
#print axioms CarryEnergyCorrection.finite_energy_correction_tendsto
#print axioms CarryEnergyCorrection.finite_green_correction_tendsto
#print axioms CarryEnergyCorrection.quarticCoefficients
#print axioms CarryEnergyCorrection.finite_quartic_source
#print axioms CarryEnergyCorrection.finite_quartic_form
#print axioms CarryEnergyCorrection.finite_quartic_correction
#print axioms CarryEnergyCorrection.quartic_correction_regression
#print axioms CarryEnergyCorrection.original_norm_difference
#print axioms CarryEnergyCorrection.finite_norm_difference_correction

#audit_energy_correction spatial
  CarryEnergyCorrection.kernel
  CarryEnergyCorrection.pairKernel
  CarryEnergyCorrection.kernel_add
  CarryEnergyCorrection.kernel_scale
  CarryEnergyCorrection.kernel_sum_weight
  CarryEnergyCorrection.native_profile_support
  CarryEnergyCorrection.weighted_synthesis_sum
  CarryEnergyCorrection.weighted_synthesis_continuous
  CarryEnergyCorrection.finiteJetSource
  CarryEnergyCorrection.finite_source_profile
  CarryEnergyCorrection.finite_source_support
  CarryEnergyCorrection.weight_sum_input
  CarryEnergyCorrection.kernel_sum_inputs
  CarryEnergyCorrection.kernel_scale_inputs
  CarryEnergyCorrection.double_sum_symmetrize

#audit_energy_correction provenance
  CarryEnergyCorrection.oddTaylor
  CarryEnergyCorrection.response_taylor_polynomial
  CarryEnergyCorrection.response_odd_remainder
  CarryEnergyCorrection.nativeRemainder
  CarryEnergyCorrection.native_remainder_analytic
  CarryEnergyCorrection.native_response_expansion
  CarryEnergyCorrection.responseSamples
  CarryEnergyCorrection.taylorSamples
  CarryEnergyCorrection.remainderSamples
  CarryEnergyCorrection.response_samples_prefix
  CarryEnergyCorrection.response_synthesis_expansion
  CarryEnergyCorrection.pair_taylor_sum
  CarryEnergyCorrection.pair_below
  CarryEnergyCorrection.pair_leading
  CarryEnergyCorrection.pair_correction
  CarryEnergyCorrection.pair_taylor_cancellation
  CarryEnergyCorrection.pair_response_expansion
  CarryEnergyCorrection.pair_remainder_continuous
  CarryEnergyCorrection.normalizedPair
  CarryEnergyCorrection.normalized_pair_expansion
  CarryEnergyCorrection.normalized_pair_correction_tendsto
  CarryEnergyCorrection.finite_source_original
  CarryEnergyCorrection.finite_source_pairing
  CarryEnergyCorrection.finite_energy_pairing
  CarryEnergyCorrection.finite_source_green_recomposition
  CarryEnergyCorrection.canonicalForm
  CarryEnergyCorrection.canonicalCorrection
  CarryEnergyCorrection.finite_energy_correction_tendsto
  CarryEnergyCorrection.finite_green_correction_tendsto
  CarryEnergyCorrection.quarticCoefficients
  CarryEnergyCorrection.finite_quartic_source
  CarryEnergyCorrection.finite_quartic_form
  CarryEnergyCorrection.finite_quartic_correction
  CarryEnergyCorrection.quartic_correction_regression
  CarryEnergyCorrection.original_norm_difference
  CarryEnergyCorrection.finite_norm_difference_correction
