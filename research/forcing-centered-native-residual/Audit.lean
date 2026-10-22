import RetainedLeg
import CriticalGreen
import Lean

open Lean Elab Command
elab "#audit_forcing_residual " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
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
      if forbidden.contains name then
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"Forcing residual audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryForcingResidual.forcing_scalar_zero_ne
#print axioms CarryForcingResidual.centeredCoefficients
#print axioms CarryForcingResidual.centeredParameters
#print axioms CarryForcingResidual.centeredCoefficients_injective
#print axioms CarryForcingResidual.forcing_vector_centered
#print axioms CarryForcingResidual.forcing_kernel_centered
#print axioms CarryForcingResidual.completed_centered
#print axioms CarryForcingResidual.remainder_centered_bilinear
#print axioms CarryForcingResidual.regularInput
#print axioms CarryForcingResidual.regularInput_exact
#print axioms CarryForcingResidual.physical_pullback_exact
#print axioms CarryForcingResidual.material_inner_self_re
#print axioms CarryForcingResidual.centeredForcingPair
#print axioms CarryForcingResidual.centeredForcingPair_as_synthesis
#print axioms CarryForcingResidual.centeredForcingPair_exact
#print axioms CarryForcingResidual.centeredForcingPair_ne_zero
#print axioms CarryForcingResidual.centeredForcingPair_self_green
#print axioms CarryForcingResidual.centeredForcingPair_polarized_green
#print axioms CarryForcingResidual.centeredForcingPair_native_cross
#print axioms CarryForcingResidual.forcing_scalar_continuous
#print axioms CarryForcingResidual.forcing_vector_continuous
#print axioms CarryForcingResidual.centeredForcingPair_nonzero_near
#print axioms CarryForcingResidual.retained_pair_tangent
#print axioms CarryForcingResidual.retained_leg_energy
#print axioms CarryForcingResidual.retained_leg_energy_limit
#print axioms CarryForcingResidual.retained_leg_limit_pos
#print axioms CarryForcingResidual.native_cross_limit
#print axioms CarryForcingResidual.native_cross_positive_near
#print axioms CarryForcingResidual.native_isotropic_not_radical
#print axioms CarryForcingResidual.no_green_preserving_erasure
#print axioms CarryForcingResidual.greenPolynomialForm
#print axioms CarryForcingResidual.centralMean
#print axioms CarryForcingResidual.centralMean_functional
#print axioms CarryForcingResidual.green_even_bilinear
#print axioms CarryForcingResidual.green_odd_bilinear
#print axioms CarryForcingResidual.criticalCoefficients
#print axioms CarryForcingResidual.criticalPolynomial_exact
#print axioms CarryForcingResidual.exact_even_centralMean_zero
#print axioms CarryForcingResidual.exact_even_green_residual
#print axioms CarryForcingResidual.exact_odd_green_residual
#print axioms CarryForcingResidual.even_green_boundary_energy
#print axioms CarryForcingResidual.odd_green_boundary_energy
#print axioms CarryForcingResidual.even_cauchy_green_limit
#print axioms CarryForcingResidual.odd_cauchy_green_limit

#audit_forcing_residual forcing
  CarryForcingResidual.forcing_scalar_zero_ne
  CarryForcingResidual.centeredCoefficients
  CarryForcingResidual.centeredParameters
  CarryForcingResidual.centeredCoefficients_injective
  CarryForcingResidual.forcing_vector_centered
  CarryForcingResidual.forcing_kernel_centered
  CarryForcingResidual.completed_centered
  CarryForcingResidual.remainder_centered_bilinear
  CarryForcingResidual.regularInput
  CarryForcingResidual.regularInput_exact
  CarryForcingResidual.physical_pullback_exact
  CarryForcingResidual.material_inner_self_re
  CarryForcingResidual.centeredForcingPair
  CarryForcingResidual.centeredForcingPair_as_synthesis
  CarryForcingResidual.centeredForcingPair_exact
  CarryForcingResidual.centeredForcingPair_ne_zero
  CarryForcingResidual.centeredForcingPair_self_green
  CarryForcingResidual.centeredForcingPair_polarized_green
  CarryForcingResidual.centeredForcingPair_native_cross
  CarryForcingResidual.forcing_scalar_continuous
  CarryForcingResidual.forcing_vector_continuous
  CarryForcingResidual.centeredForcingPair_nonzero_near
  CarryForcingResidual.retained_pair_tangent
  CarryForcingResidual.retained_leg_energy
  CarryForcingResidual.retained_leg_energy_limit
  CarryForcingResidual.retained_leg_limit_pos
  CarryForcingResidual.native_cross_limit
  CarryForcingResidual.native_cross_positive_near
  CarryForcingResidual.native_isotropic_not_radical
  CarryForcingResidual.no_green_preserving_erasure

#audit_forcing_residual critical
  CarryForcingResidual.greenPolynomialForm
  CarryForcingResidual.centralMean
  CarryForcingResidual.centralMean_functional
  CarryForcingResidual.green_even_bilinear
  CarryForcingResidual.green_odd_bilinear
  CarryForcingResidual.criticalCoefficients
  CarryForcingResidual.criticalPolynomial_exact
  CarryForcingResidual.exact_even_centralMean_zero
  CarryForcingResidual.exact_even_green_residual
  CarryForcingResidual.exact_odd_green_residual
  CarryForcingResidual.even_green_boundary_energy
  CarryForcingResidual.odd_green_boundary_energy
  CarryForcingResidual.even_cauchy_green_limit
  CarryForcingResidual.odd_cauchy_green_limit
