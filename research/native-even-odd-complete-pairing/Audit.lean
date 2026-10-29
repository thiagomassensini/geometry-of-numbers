import MixedRegression
import Lean

open Lean Elab Command
elab "#audit_mixed_parity " group:ident ids:ident+ : command => do
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
  logInfo m!"Complete even-odd pairing {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarryMixedParity.rotatedCharacteristic
#print axioms CarryMixedParity.rotated_characteristic_reflection
#print axioms CarryMixedParity.rotated_derivative_reflection
#print axioms CarryMixedParity.response_rotated_derivative
#print axioms CarryMixedParity.response_reflection
#print axioms CarryMixedParity.response_real_ray
#print axioms CarryMixedParity.response_samples_real
#print axioms CarryMixedParity.static_stencil_real
#print axioms CarryMixedParity.even_coefficients_real
#print axioms CarryMixedParity.odd_coefficients_imaginary
#print axioms CarryMixedParity.kernel_smul_left
#print axioms CarryMixedParity.kernel_smul_right
#print axioms CarryMixedParity.kernel_double_sum
#print axioms CarryMixedParity.kernel_real_imaginary
#print axioms CarryMixedParity.kernel_imaginary_real
#print axioms CarryMixedParity.signedPair
#print axioms CarryMixedParity.signed_mean_contrast
#print axioms CarryMixedParity.source_mean_and_contrast
#print axioms CarryMixedParity.contrast_mean_scale
#print axioms CarryMixedParity.complete_complex_pair
#print axioms CarryMixedParity.mixedPair
#print axioms CarryMixedParity.mixed_pair_exact
#print axioms CarryMixedParity.mixed_pair_conjugate
#print axioms CarryMixedParity.mixed_pair_real_zero
#print axioms CarryMixedParity.mixed_pair_green_recomposition
#print axioms CarryMixedParity.native_source_add
#print axioms CarryMixedParity.signed_form_add
#print axioms CarryMixedParity.full_energy_add
#print axioms CarryMixedParity.jointJetSource
#print axioms CarryMixedParity.joint_source_original
#print axioms CarryMixedParity.joint_energy_add
#print axioms CarryMixedParity.joint_energy_correction_tendsto
#print axioms CarryMixedParity.joint_source_support
#print axioms CarryMixedParity.joint_green_recomposition
#print axioms CarryMixedParity.joint_green_correction_tendsto
#print axioms CarryMixedParity.joint_norm_difference_correction
#print axioms CarryMixedParity.firstMixedPair
#print axioms CarryMixedParity.first_mixed_exact
#print axioms CarryMixedParity.firstMixedError
#print axioms CarryMixedParity.first_mixed_error_continuous
#print axioms CarryMixedParity.first_mixed_scaled_expansion
#print axioms CarryMixedParity.first_mixed_scaled_tendsto
#print axioms CarryMixedParity.complex_orthogonality_would_force_h1_zero

#audit_mixed_parity spatial
  CarryMixedParity.static_stencil_real
  CarryMixedParity.even_coefficients_real
  CarryMixedParity.odd_coefficients_imaginary
  CarryMixedParity.kernel_smul_left
  CarryMixedParity.kernel_smul_right
  CarryMixedParity.kernel_double_sum
  CarryMixedParity.kernel_real_imaginary
  CarryMixedParity.kernel_imaginary_real
  CarryMixedParity.signed_mean_contrast
  CarryMixedParity.contrast_mean_scale
  CarryMixedParity.signed_form_add

#audit_mixed_parity provenance
  CarryMixedParity.rotatedCharacteristic
  CarryMixedParity.rotated_characteristic_reflection
  CarryMixedParity.rotated_derivative_reflection
  CarryMixedParity.response_rotated_derivative
  CarryMixedParity.response_reflection
  CarryMixedParity.response_real_ray
  CarryMixedParity.response_samples_real
  CarryMixedParity.signedPair
  CarryMixedParity.source_mean_and_contrast
  CarryMixedParity.complete_complex_pair
  CarryMixedParity.mixedPair
  CarryMixedParity.mixed_pair_exact
  CarryMixedParity.mixed_pair_conjugate
  CarryMixedParity.mixed_pair_real_zero
  CarryMixedParity.mixed_pair_green_recomposition
  CarryMixedParity.native_source_add
  CarryMixedParity.full_energy_add
  CarryMixedParity.jointJetSource
  CarryMixedParity.joint_source_original
  CarryMixedParity.joint_energy_add
  CarryMixedParity.joint_energy_correction_tendsto
  CarryMixedParity.joint_source_support
  CarryMixedParity.joint_green_recomposition
  CarryMixedParity.joint_green_correction_tendsto
  CarryMixedParity.joint_norm_difference_correction
  CarryMixedParity.firstMixedPair
  CarryMixedParity.first_mixed_exact
  CarryMixedParity.firstMixedError
  CarryMixedParity.first_mixed_error_continuous
  CarryMixedParity.first_mixed_scaled_expansion
  CarryMixedParity.first_mixed_scaled_tendsto
  CarryMixedParity.complex_orthogonality_would_force_h1_zero
