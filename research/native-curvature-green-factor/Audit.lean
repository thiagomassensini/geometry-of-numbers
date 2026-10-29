import FourthBoundaryDefect
import CriticalSectorSign
import Lean

open Lean Elab Command
elab "#audit_curvature_green " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let finiteSigns := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
      if name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." ||
          name == `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier then
        throwError "Forbidden downstream positivity consumer: {name}"
      if tier.getNat == 0 && (name == moments || name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic) then
        throwError "Moment-dependent physical construction: {name}"
      if tier.getNat <= 1 && finiteSigns.contains name then
        throwError "Finite moment sign outside explicit seed test: {name}"
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
  logInfo m!"Curvature Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryCurvatureGreen.PhysicalSpace
#print axioms CarryCurvatureGreen.physicalComplement
#print axioms CarryCurvatureGreen.physical_valve_norm_le_one
#print axioms CarryCurvatureGreen.physical_complement_norm_le_one
#print axioms CarryCurvatureGreen.physical_complement_contracts
#print axioms CarryCurvatureGreen.physical_complement_selfAdjoint
#print axioms CarryCurvatureGreen.resolvent_norm_lower
#print axioms CarryCurvatureGreen.physicalCurvature
#print axioms CarryCurvatureGreen.physicalTangent
#print axioms CarryCurvatureGreen.baseGradient
#print axioms CarryCurvatureGreen.transportedGradient
#print axioms CarryCurvatureGreen.advance_complement
#print axioms CarryCurvatureGreen.resolvent_advance
#print axioms CarryCurvatureGreen.resolvent_complement
#print axioms CarryCurvatureGreen.gradient_as_complement
#print axioms CarryCurvatureGreen.curvature_resolvent_advance
#print axioms CarryCurvatureGreen.tangent_resolvent
#print axioms CarryCurvatureGreen.green_inner_transport
#print axioms CarryCurvatureGreen.gradient_pairing
#print axioms CarryCurvatureGreen.curvature_green_polarized_factor
#print axioms CarryCurvatureGreen.curvature_green_diagonal_factor
#print axioms CarryCurvatureGreen.curvature_green_lower_bound
#print axioms CarryCurvatureGreen.curvature_green_nonnegative
#print axioms CarryCurvatureGreen.nativeU1
#print axioms CarryCurvatureGreen.native_curvature
#print axioms CarryCurvatureGreen.native_tangent
#print axioms CarryCurvatureGreen.native_transported_gradient
#print axioms CarryCurvatureGreen.native_u1_identification
#print axioms CarryCurvatureGreen.native_u1_factor
#print axioms CarryCurvatureGreen.native_difference_norm_square
#print axioms CarryCurvatureGreen.native_gradient_norm_lower
#print axioms CarryCurvatureGreen.native_u1_lower_bound
#print axioms CarryCurvatureGreen.native_u1_pos
#print axioms CarryCurvatureGreen.fourthShape
#print axioms CarryCurvatureGreen.liftedFourthSeed
#print axioms CarryCurvatureGreen.fourth_shape_explicit
#print axioms CarryCurvatureGreen.fourth_shape_synthesis
#print axioms CarryCurvatureGreen.fourth_native_curvature
#print axioms CarryCurvatureGreen.fourth_commutator
#print axioms CarryCurvatureGreen.fourth_tangent_defect
#print axioms CarryCurvatureGreen.fourth_tangent_not_direct_lift
#print axioms CarryCurvatureGreen.leading_coefficient_formula
#print axioms CarryCurvatureGreen.mixed_scaled_limit
#print axioms CarryCurvatureGreen.bulk_boundary_scaled_limit
#print axioms CarryCurvatureGreen.leading_coefficient_pos
#print axioms CarryCurvatureGreen.leading_coefficient_lower_bound
#print axioms CarryCurvatureGreen.mixed_eventually_positive
#print axioms CarryCurvatureGreen.bulk_boundary_eventually_negative

#audit_curvature_green 0
  CarryCurvatureGreen.PhysicalSpace
  CarryCurvatureGreen.physicalComplement
  CarryCurvatureGreen.physical_valve_norm_le_one
  CarryCurvatureGreen.physical_complement_norm_le_one
  CarryCurvatureGreen.physical_complement_contracts
  CarryCurvatureGreen.physical_complement_selfAdjoint
  CarryCurvatureGreen.resolvent_norm_lower
  CarryCurvatureGreen.physicalCurvature
  CarryCurvatureGreen.physicalTangent
  CarryCurvatureGreen.baseGradient
  CarryCurvatureGreen.transportedGradient
  CarryCurvatureGreen.advance_complement
  CarryCurvatureGreen.resolvent_advance
  CarryCurvatureGreen.resolvent_complement
  CarryCurvatureGreen.gradient_as_complement
  CarryCurvatureGreen.curvature_resolvent_advance
  CarryCurvatureGreen.tangent_resolvent
  CarryCurvatureGreen.green_inner_transport
  CarryCurvatureGreen.gradient_pairing
  CarryCurvatureGreen.curvature_green_polarized_factor
  CarryCurvatureGreen.curvature_green_diagonal_factor
  CarryCurvatureGreen.curvature_green_lower_bound
  CarryCurvatureGreen.curvature_green_nonnegative
  CarryCurvatureGreen.nativeU1
  CarryCurvatureGreen.native_curvature
  CarryCurvatureGreen.native_tangent
  CarryCurvatureGreen.native_transported_gradient
  CarryCurvatureGreen.native_u1_identification
  CarryCurvatureGreen.native_u1_factor
  CarryCurvatureGreen.native_difference_norm_square
  CarryCurvatureGreen.native_gradient_norm_lower
  CarryCurvatureGreen.native_u1_lower_bound
  CarryCurvatureGreen.native_u1_pos
  CarryCurvatureGreen.fourthShape
  CarryCurvatureGreen.liftedFourthSeed
  CarryCurvatureGreen.fourth_shape_explicit
  CarryCurvatureGreen.fourth_shape_synthesis
  CarryCurvatureGreen.fourth_native_curvature
  CarryCurvatureGreen.fourth_commutator
  CarryCurvatureGreen.fourth_tangent_defect
  CarryCurvatureGreen.fourth_tangent_not_direct_lift


#audit_curvature_green 1
  CarryCurvatureGreen.leading_coefficient_formula
  CarryCurvatureGreen.mixed_scaled_limit
  CarryCurvatureGreen.bulk_boundary_scaled_limit


#audit_curvature_green 2
  CarryCurvatureGreen.leading_coefficient_pos
  CarryCurvatureGreen.leading_coefficient_lower_bound
  CarryCurvatureGreen.mixed_eventually_positive
  CarryCurvatureGreen.bulk_boundary_eventually_negative
