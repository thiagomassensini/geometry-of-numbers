import QuarticCoefficient
import Lean

open Lean Elab Command
elab "#audit_quartic_boundary " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic,
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
      if forbidden.contains name || name.toString.startsWith "CarrySixthEven." ||
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
  logInfo m!"Quartic boundary audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical sequence or characteristic"

#print axioms CarryQuarticBoundary.boundaryPolynomial
#print axioms CarryQuarticBoundary.boundary_polynomial_identity
#print axioms CarryQuarticBoundary.boundary_polynomial_nonnegative
#print axioms CarryQuarticBoundary.boundary_polynomial_lower
#print axioms CarryQuarticBoundary.boundary_polynomial_two
#print axioms CarryQuarticBoundary.boundary_polynomial_in_native_coordinate
#print axioms CarryQuarticBoundary.quarticVector
#print axioms CarryQuarticBoundary.boundaryVector
#print axioms CarryQuarticBoundary.quarticGradient
#print axioms CarryQuarticBoundary.resolvent_advance_complement
#print axioms CarryQuarticBoundary.quartic_gradient_as_complement
#print axioms CarryQuarticBoundary.quartic_resolvent_advance
#print axioms CarryQuarticBoundary.boundary_resolvent
#print axioms CarryQuarticBoundary.complement_twice_pairing
#print axioms CarryQuarticBoundary.quartic_base_pairing
#print axioms CarryQuarticBoundary.quartic_advance_pairing
#print axioms CarryQuarticBoundary.quartic_boundary_polarized_factor
#print axioms CarryQuarticBoundary.quartic_boundary_diagonal_factor
#print axioms CarryQuarticBoundary.advance_inner_upper
#print axioms CarryQuarticBoundary.quartic_boundary_lower
#print axioms CarryQuarticBoundary.nativeBoundaryVector
#print axioms CarryQuarticBoundary.nativeBoundaryPair
#print axioms CarryQuarticBoundary.nativeQuarticCoefficient
#print axioms CarryQuarticBoundary.native_quartic_vector
#print axioms CarryQuarticBoundary.native_boundary_vector
#print axioms CarryQuarticBoundary.native_quartic_gradient
#print axioms CarryQuarticBoundary.fourth_lift_gradient
#print axioms CarryQuarticBoundary.native_boundary_pair_factor
#print axioms CarryQuarticBoundary.native_quartic_seed_norm_square
#print axioms CarryQuarticBoundary.native_quartic_gradient_lower
#print axioms CarryQuarticBoundary.native_boundary_pair_lower
#print axioms CarryQuarticBoundary.native_boundary_pair_pos
#print axioms CarryQuarticBoundary.native_quartic_coefficient_split
#print axioms CarryQuarticBoundary.native_quartic_coefficient_factor
#print axioms CarryQuarticBoundary.native_quartic_coefficient_lower
#print axioms CarryQuarticBoundary.native_quartic_coefficient_pos

#audit_quartic_boundary
  CarryQuarticBoundary.boundaryPolynomial
  CarryQuarticBoundary.boundary_polynomial_identity
  CarryQuarticBoundary.boundary_polynomial_nonnegative
  CarryQuarticBoundary.boundary_polynomial_lower
  CarryQuarticBoundary.boundary_polynomial_two
  CarryQuarticBoundary.boundary_polynomial_in_native_coordinate
  CarryQuarticBoundary.quarticVector
  CarryQuarticBoundary.boundaryVector
  CarryQuarticBoundary.quarticGradient
  CarryQuarticBoundary.resolvent_advance_complement
  CarryQuarticBoundary.quartic_gradient_as_complement
  CarryQuarticBoundary.quartic_resolvent_advance
  CarryQuarticBoundary.boundary_resolvent
  CarryQuarticBoundary.complement_twice_pairing
  CarryQuarticBoundary.quartic_base_pairing
  CarryQuarticBoundary.quartic_advance_pairing
  CarryQuarticBoundary.quartic_boundary_polarized_factor
  CarryQuarticBoundary.quartic_boundary_diagonal_factor
  CarryQuarticBoundary.advance_inner_upper
  CarryQuarticBoundary.quartic_boundary_lower
  CarryQuarticBoundary.nativeBoundaryVector
  CarryQuarticBoundary.nativeBoundaryPair
  CarryQuarticBoundary.nativeQuarticCoefficient
  CarryQuarticBoundary.native_quartic_vector
  CarryQuarticBoundary.native_boundary_vector
  CarryQuarticBoundary.native_quartic_gradient
  CarryQuarticBoundary.fourth_lift_gradient
  CarryQuarticBoundary.native_boundary_pair_factor
  CarryQuarticBoundary.native_quartic_seed_norm_square
  CarryQuarticBoundary.native_quartic_gradient_lower
  CarryQuarticBoundary.native_boundary_pair_lower
  CarryQuarticBoundary.native_boundary_pair_pos
  CarryQuarticBoundary.native_quartic_coefficient_split
  CarryQuarticBoundary.native_quartic_coefficient_factor
  CarryQuarticBoundary.native_quartic_coefficient_lower
  CarryQuarticBoundary.native_quartic_coefficient_pos
