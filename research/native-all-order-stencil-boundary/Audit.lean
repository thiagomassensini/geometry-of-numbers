import Regression
import Lean

open Lean Elab Command
elab "#audit_stencil_boundary " group:ident ids:ident+ : command => do
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
  logInfo m!"Stencil boundary {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moments; characteristic forbidden={spatial}"

#print axioms CarryStencilBoundary.rawStencil
#print axioms CarryStencilBoundary.staticStencil
#print axioms CarryStencilBoundary.radialJetCoefficients
#print axioms CarryStencilBoundary.radialLeadingScalar
#print axioms CarryStencilBoundary.raw_stencil_apply
#print axioms CarryStencilBoundary.raw_stencil_zero
#print axioms CarryStencilBoundary.raw_stencil_one
#print axioms CarryStencilBoundary.radial_jet_two_traces
#print axioms CarryStencilBoundary.radial_jet_original_source
#print axioms CarryStencilBoundary.advance_power_feature
#print axioms CarryStencilBoundary.negative_unit_power
#print axioms CarryStencilBoundary.raw_stencil_binomial
#print axioms CarryStencilBoundary.raw_stencil_complement
#print axioms CarryStencilBoundary.radial_jet_synthesis
#print axioms CarryStencilBoundary.radial_leading_nonzero
#print axioms CarryStencilBoundary.boundarySymbol
#print axioms CarryStencilBoundary.boundaryOperator
#print axioms CarryStencilBoundary.boundary_symbol_eval
#print axioms CarryStencilBoundary.multiplier_add
#print axioms CarryStencilBoundary.multiplier_zero
#print axioms CarryStencilBoundary.multiplier_pow
#print axioms CarryStencilBoundary.complement_multiplier
#print axioms CarryStencilBoundary.boundary_operator_zero
#print axioms CarryStencilBoundary.boundary_operator_succ
#print axioms CarryStencilBoundary.boundary_operator_identity
#print axioms CarryStencilBoundary.boundary_operator_positive
#print axioms CarryStencilBoundary.boundary_operator_lower_positive
#print axioms CarryStencilBoundary.boundary_operator_lower
#print axioms CarryStencilBoundary.multiplier_commute
#print axioms CarryStencilBoundary.boundary_advance
#print axioms CarryStencilBoundary.boundary_resolvent
#print axioms CarryStencilBoundary.boundary_product_positive
#print axioms CarryStencilBoundary.nativeLift
#print axioms CarryStencilBoundary.nativeBoundary
#print axioms CarryStencilBoundary.native_lift_curvature
#print axioms CarryStencilBoundary.native_tangent_boundary
#print axioms CarryStencilBoundary.advance_complement_power
#print axioms CarryStencilBoundary.resolvent_complement_power
#print axioms CarryStencilBoundary.boundary_polarized_factor
#print axioms CarryStencilBoundary.boundary_pair_nonnegative
#print axioms CarryStencilBoundary.native_boundary_pair_nonnegative
#print axioms CarryStencilBoundary.native_linear_coefficient_nonnegative
#print axioms CarryStencilBoundary.raw_stencil_two
#print axioms CarryStencilBoundary.radial_second_regression
#print axioms CarryStencilBoundary.static_fourth_regression
#print axioms CarryStencilBoundary.radial_fourth_regression
#print axioms CarryStencilBoundary.boundary_operator_two
#print axioms CarryStencilBoundary.fourth_boundary_regression

#audit_stencil_boundary spatial
  CarryStencilBoundary.rawStencil
  CarryStencilBoundary.staticStencil
  CarryStencilBoundary.radialJetCoefficients
  CarryStencilBoundary.radialLeadingScalar
  CarryStencilBoundary.raw_stencil_apply
  CarryStencilBoundary.raw_stencil_zero
  CarryStencilBoundary.raw_stencil_one
  CarryStencilBoundary.radial_jet_two_traces
  CarryStencilBoundary.advance_power_feature
  CarryStencilBoundary.negative_unit_power
  CarryStencilBoundary.raw_stencil_binomial
  CarryStencilBoundary.raw_stencil_complement
  CarryStencilBoundary.radial_jet_synthesis
  CarryStencilBoundary.radial_leading_nonzero
  CarryStencilBoundary.boundarySymbol
  CarryStencilBoundary.boundaryOperator
  CarryStencilBoundary.boundary_symbol_eval
  CarryStencilBoundary.multiplier_add
  CarryStencilBoundary.multiplier_zero
  CarryStencilBoundary.multiplier_pow
  CarryStencilBoundary.complement_multiplier
  CarryStencilBoundary.boundary_operator_zero
  CarryStencilBoundary.boundary_operator_succ
  CarryStencilBoundary.boundary_operator_identity
  CarryStencilBoundary.boundary_operator_positive
  CarryStencilBoundary.boundary_operator_lower_positive
  CarryStencilBoundary.boundary_operator_lower
  CarryStencilBoundary.multiplier_commute
  CarryStencilBoundary.boundary_advance
  CarryStencilBoundary.boundary_resolvent
  CarryStencilBoundary.boundary_product_positive
  CarryStencilBoundary.nativeLift
  CarryStencilBoundary.nativeBoundary
  CarryStencilBoundary.native_lift_curvature
  CarryStencilBoundary.native_tangent_boundary
  CarryStencilBoundary.advance_complement_power
  CarryStencilBoundary.resolvent_complement_power
  CarryStencilBoundary.boundary_polarized_factor
  CarryStencilBoundary.boundary_pair_nonnegative
  CarryStencilBoundary.native_boundary_pair_nonnegative
  CarryStencilBoundary.native_linear_coefficient_nonnegative
  CarryStencilBoundary.raw_stencil_two
  CarryStencilBoundary.radial_second_regression
  CarryStencilBoundary.static_fourth_regression
  CarryStencilBoundary.radial_fourth_regression
  CarryStencilBoundary.boundary_operator_two
  CarryStencilBoundary.fourth_boundary_regression

#audit_stencil_boundary provenance
  CarryStencilBoundary.radial_jet_original_source
