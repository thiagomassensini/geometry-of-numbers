import QuadraticSign
import Lean

open Lean Elab Command
elab "#audit_cubic_tfvd " group:ident ids:ident+ : command => do
  let spatial := group.getId == `spatial
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
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
          (spatial && name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic) ||
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
  logInfo m!"Cubic TFVD {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moments; characteristic forbidden={spatial}"

#print axioms CarryCubicTfvd.cubicForwardWeight
#print axioms CarryCubicTfvd.cubicBackwardWeight
#print axioms CarryCubicTfvd.cubicTrace
#print axioms CarryCubicTfvd.cubic_commutator_succ
#print axioms CarryCubicTfvd.cubic_shift_numerator
#print axioms CarryCubicTfvd.cubic_physical_numerator
#print axioms CarryCubicTfvd.cubicKernel
#print axioms CarryCubicTfvd.cubic_kernel_original
#print axioms CarryCubicTfvd.cubic_green_polarized
#print axioms CarryCubicTfvd.cubic_green_diagonal
#print axioms CarryCubicTfvd.cubic_seed_negative
#print axioms CarryCubicTfvd.criticalFamily
#print axioms CarryCubicTfvd.critical_family_original_source
#print axioms CarryCubicTfvd.critical_family_synthesis
#print axioms CarryCubicTfvd.critical_family_two_traces
#print axioms CarryCubicTfvd.critical_family_cubic_trace
#print axioms CarryCubicTfvd.critical_family_explicit
#print axioms CarryCubicTfvd.critical_family_support
#print axioms CarryCubicTfvd.critical_cubic_commutator_support
#print axioms CarryCubicTfvd.cubic_three_input_expansion
#print axioms CarryCubicTfvd.critical_cubic_expansion
#print axioms CarryCubicTfvd.cubicQuadraticMultiplier
#print axioms CarryCubicTfvd.cubicTangent
#print axioms CarryCubicTfvd.nativeU3
#print axioms CarryCubicTfvd.cubic_native_tangent
#print axioms CarryCubicTfvd.cubic_multiplier_advance
#print axioms CarryCubicTfvd.cubic_multiplier_complement
#print axioms CarryCubicTfvd.resolvent_cubic_multiplier
#print axioms CarryCubicTfvd.cubic_tangent_resolvent
#print axioms CarryCubicTfvd.cubic_multiplier_gradient_pairing
#print axioms CarryCubicTfvd.cubic_curvature_polarized
#print axioms CarryCubicTfvd.cubic_curvature_diagonal
#print axioms CarryCubicTfvd.cubic_multiplier_upper_positive
#print axioms CarryCubicTfvd.cubic_multiplier_inner_upper
#print axioms CarryCubicTfvd.cubic_curvature_lower
#print axioms CarryCubicTfvd.native_cubic_identification
#print axioms CarryCubicTfvd.native_cubic_lower_bound
#print axioms CarryCubicTfvd.native_cubic_uniform_lower
#print axioms CarryCubicTfvd.native_cubic_pos

#audit_cubic_tfvd spatial
  CarryCubicTfvd.cubicForwardWeight
  CarryCubicTfvd.cubicBackwardWeight
  CarryCubicTfvd.cubicTrace
  CarryCubicTfvd.cubic_commutator_succ
  CarryCubicTfvd.cubic_shift_numerator
  CarryCubicTfvd.cubic_physical_numerator
  CarryCubicTfvd.cubicKernel
  CarryCubicTfvd.cubic_kernel_original
  CarryCubicTfvd.cubic_green_polarized
  CarryCubicTfvd.cubic_green_diagonal
  CarryCubicTfvd.cubic_seed_negative
  CarryCubicTfvd.criticalFamily
  CarryCubicTfvd.critical_family_synthesis
  CarryCubicTfvd.critical_family_two_traces
  CarryCubicTfvd.critical_family_cubic_trace
  CarryCubicTfvd.critical_family_explicit
  CarryCubicTfvd.critical_family_support
  CarryCubicTfvd.critical_cubic_commutator_support
  CarryCubicTfvd.cubic_three_input_expansion
  CarryCubicTfvd.critical_cubic_expansion
  CarryCubicTfvd.cubicQuadraticMultiplier
  CarryCubicTfvd.cubicTangent
  CarryCubicTfvd.nativeU3
  CarryCubicTfvd.cubic_native_tangent
  CarryCubicTfvd.cubic_multiplier_advance
  CarryCubicTfvd.cubic_multiplier_complement
  CarryCubicTfvd.resolvent_cubic_multiplier
  CarryCubicTfvd.cubic_tangent_resolvent
  CarryCubicTfvd.cubic_multiplier_gradient_pairing
  CarryCubicTfvd.cubic_curvature_polarized
  CarryCubicTfvd.cubic_curvature_diagonal
  CarryCubicTfvd.cubic_multiplier_upper_positive
  CarryCubicTfvd.cubic_multiplier_inner_upper
  CarryCubicTfvd.cubic_curvature_lower
  CarryCubicTfvd.native_cubic_identification
  CarryCubicTfvd.native_cubic_lower_bound
  CarryCubicTfvd.native_cubic_uniform_lower
  CarryCubicTfvd.native_cubic_pos

#audit_cubic_tfvd provenance
  CarryCubicTfvd.critical_family_original_source
