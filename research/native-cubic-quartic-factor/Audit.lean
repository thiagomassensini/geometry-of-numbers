import MixedFactors
import Lean

open Lean Elab Command
elab "#audit_cubic_quartic " group:ident ids:ident+ : command => do
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
  logInfo m!"Cubic quartic {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moments; characteristic forbidden={spatial}"

#print axioms CarryCubicQuartic.quarticForward
#print axioms CarryCubicQuartic.quarticBackward
#print axioms CarryCubicQuartic.quartic_forward_in_advance
#print axioms CarryCubicQuartic.quartic_backward_in_advance
#print axioms CarryCubicQuartic.forward_advance
#print axioms CarryCubicQuartic.backward_advance
#print axioms CarryCubicQuartic.forward_complement
#print axioms CarryCubicQuartic.backward_complement
#print axioms CarryCubicQuartic.resolvent_forward
#print axioms CarryCubicQuartic.resolvent_backward
#print axioms CarryCubicQuartic.forward_as_multiplier
#print axioms CarryCubicQuartic.backward_as_multiplier
#print axioms CarryCubicQuartic.quarticCubicTangent
#print axioms CarryCubicQuartic.nativeQuarticU3
#print axioms CarryCubicQuartic.quartic_cubic_commutator
#print axioms CarryCubicQuartic.quartic_cubic_halo_nonzero
#print axioms CarryCubicQuartic.quartic_cubic_tangent_native
#print axioms CarryCubicQuartic.quartic_cubic_tangent_resolvent
#print axioms CarryCubicQuartic.quartic_forward_pairing
#print axioms CarryCubicQuartic.quartic_backward_pairing
#print axioms CarryCubicQuartic.quartic_cubic_polarized
#print axioms CarryCubicQuartic.quartic_cubic_diagonal
#print axioms CarryCubicQuartic.native_quartic_cubic_identification
#print axioms CarryCubicQuartic.native_quartic_cubic_factor
#print axioms CarryCubicQuartic.quartic_backward_upper_positive
#print axioms CarryCubicQuartic.quartic_margin_positive
#print axioms CarryCubicQuartic.quartic_margin_inner_lower
#print axioms CarryCubicQuartic.quartic_cubic_lower
#print axioms CarryCubicQuartic.native_quartic_cubic_lower_bound
#print axioms CarryCubicQuartic.native_quartic_cubic_pos
#print axioms CarryCubicQuartic.mixedQuarticQuadratic
#print axioms CarryCubicQuartic.mixedQuadraticQuartic
#print axioms CarryCubicQuartic.quartic_quadratic_pairing
#print axioms CarryCubicQuartic.quartic_quadratic_polarized
#print axioms CarryCubicQuartic.forward_gradient_pairing
#print axioms CarryCubicQuartic.backward_gradient_pairing
#print axioms CarryCubicQuartic.quadratic_quartic_polarized
#print axioms CarryCubicQuartic.native_quadratic_quartic_upper
#print axioms CarryCubicQuartic.native_quartic_quadratic_upper
#print axioms CarryCubicQuartic.native_ordered_crosses_negative
#print axioms CarryCubicQuartic.two_jet_expansion
#print axioms CarryCubicQuartic.two_jet_cone_lower
#print axioms CarryCubicQuartic.two_jet_cone_pos

#audit_cubic_quartic spatial
  CarryCubicQuartic.quarticForward
  CarryCubicQuartic.quarticBackward
  CarryCubicQuartic.quartic_forward_in_advance
  CarryCubicQuartic.quartic_backward_in_advance
  CarryCubicQuartic.forward_advance
  CarryCubicQuartic.backward_advance
  CarryCubicQuartic.forward_complement
  CarryCubicQuartic.backward_complement
  CarryCubicQuartic.resolvent_forward
  CarryCubicQuartic.resolvent_backward
  CarryCubicQuartic.forward_as_multiplier
  CarryCubicQuartic.backward_as_multiplier
  CarryCubicQuartic.quarticCubicTangent
  CarryCubicQuartic.nativeQuarticU3
  CarryCubicQuartic.quartic_cubic_commutator
  CarryCubicQuartic.quartic_cubic_halo_nonzero
  CarryCubicQuartic.quartic_cubic_tangent_native
  CarryCubicQuartic.quartic_cubic_tangent_resolvent
  CarryCubicQuartic.quartic_forward_pairing
  CarryCubicQuartic.quartic_backward_pairing
  CarryCubicQuartic.quartic_cubic_polarized
  CarryCubicQuartic.quartic_cubic_diagonal
  CarryCubicQuartic.native_quartic_cubic_identification
  CarryCubicQuartic.native_quartic_cubic_factor
  CarryCubicQuartic.quartic_backward_upper_positive
  CarryCubicQuartic.quartic_margin_positive
  CarryCubicQuartic.quartic_margin_inner_lower
  CarryCubicQuartic.quartic_cubic_lower
  CarryCubicQuartic.native_quartic_cubic_lower_bound
  CarryCubicQuartic.native_quartic_cubic_pos
  CarryCubicQuartic.mixedQuarticQuadratic
  CarryCubicQuartic.mixedQuadraticQuartic
  CarryCubicQuartic.quartic_quadratic_pairing
  CarryCubicQuartic.quartic_quadratic_polarized
  CarryCubicQuartic.forward_gradient_pairing
  CarryCubicQuartic.backward_gradient_pairing
  CarryCubicQuartic.quadratic_quartic_polarized
  CarryCubicQuartic.native_quadratic_quartic_upper
  CarryCubicQuartic.native_quartic_quadratic_upper
  CarryCubicQuartic.native_ordered_crosses_negative
  CarryCubicQuartic.two_jet_expansion
  CarryCubicQuartic.two_jet_cone_lower
  CarryCubicQuartic.two_jet_cone_pos
