import Regression
import Lean

open Lean Elab Command
elab "#audit_spatial_correction " group:ident ids:ident+ : command => do
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
  logInfo m!"All-order spatial correction {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

#print axioms CarrySpatialCorrection.differencePower
#print axioms CarrySpatialCorrection.choose_difference_zero
#print axioms CarrySpatialCorrection.choose_difference_one
#print axioms CarrySpatialCorrection.power_newton_expansion
#print axioms CarrySpatialCorrection.difference_power_stirling
#print axioms CarrySpatialCorrection.difference_power_below
#print axioms CarrySpatialCorrection.difference_power_diagonal
#print axioms CarrySpatialCorrection.difference_power_sum
#print axioms CarrySpatialCorrection.slope
#print axioms CarrySpatialCorrection.curvature
#print axioms CarrySpatialCorrection.difference_power_one_above
#print axioms CarrySpatialCorrection.stirling_two_above
#print axioms CarrySpatialCorrection.difference_power_two_above
#print axioms CarrySpatialCorrection.odd_divided_power
#print axioms CarrySpatialCorrection.dividedCoefficient
#print axioms CarrySpatialCorrection.divided_below
#print axioms CarrySpatialCorrection.divided_leading
#print axioms CarrySpatialCorrection.spatialCorrection
#print axioms CarrySpatialCorrection.divided_first_correction
#print axioms CarrySpatialCorrection.spatial_correction_diagonal
#print axioms CarrySpatialCorrection.nativeEvenProfile
#print axioms CarrySpatialCorrection.weight_finite_stencil
#print axioms CarrySpatialCorrection.raw_kernel_sum
#print axioms CarrySpatialCorrection.static_kernel_sum
#print axioms CarrySpatialCorrection.static_odd_divided
#print axioms CarrySpatialCorrection.native_odd_divided
#print axioms CarrySpatialCorrection.native_odd_stirling
#print axioms CarrySpatialCorrection.native_below
#print axioms CarrySpatialCorrection.native_first_correction
#print axioms CarrySpatialCorrection.native_leading
#print axioms CarrySpatialCorrection.native_profile_zero
#print axioms CarrySpatialCorrection.native_profile_one
#print axioms CarrySpatialCorrection.native_profile_two
#print axioms CarrySpatialCorrection.radial_even_calibration
#print axioms CarrySpatialCorrection.quartic_weight11_regression
#print axioms CarrySpatialCorrection.correction_table
#print axioms CarrySpatialCorrection.correction_table_negative_direction

#audit_spatial_correction spatial
  CarrySpatialCorrection.differencePower
  CarrySpatialCorrection.choose_difference_zero
  CarrySpatialCorrection.choose_difference_one
  CarrySpatialCorrection.power_newton_expansion
  CarrySpatialCorrection.difference_power_stirling
  CarrySpatialCorrection.difference_power_below
  CarrySpatialCorrection.difference_power_diagonal
  CarrySpatialCorrection.difference_power_sum
  CarrySpatialCorrection.slope
  CarrySpatialCorrection.curvature
  CarrySpatialCorrection.difference_power_one_above
  CarrySpatialCorrection.stirling_two_above
  CarrySpatialCorrection.difference_power_two_above
  CarrySpatialCorrection.odd_divided_power
  CarrySpatialCorrection.dividedCoefficient
  CarrySpatialCorrection.divided_below
  CarrySpatialCorrection.divided_leading
  CarrySpatialCorrection.spatialCorrection
  CarrySpatialCorrection.divided_first_correction
  CarrySpatialCorrection.spatial_correction_diagonal
  CarrySpatialCorrection.nativeEvenProfile
  CarrySpatialCorrection.weight_finite_stencil
  CarrySpatialCorrection.raw_kernel_sum
  CarrySpatialCorrection.static_kernel_sum
  CarrySpatialCorrection.static_odd_divided
  CarrySpatialCorrection.native_odd_divided
  CarrySpatialCorrection.native_odd_stirling
  CarrySpatialCorrection.native_below
  CarrySpatialCorrection.native_first_correction
  CarrySpatialCorrection.native_leading
  CarrySpatialCorrection.native_profile_zero
  CarrySpatialCorrection.native_profile_one
  CarrySpatialCorrection.native_profile_two
  CarrySpatialCorrection.radial_even_calibration
  CarrySpatialCorrection.quartic_weight11_regression
  CarrySpatialCorrection.correction_table
  CarrySpatialCorrection.correction_table_negative_direction
