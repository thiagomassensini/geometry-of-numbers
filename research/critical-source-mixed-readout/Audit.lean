import EulerOrientation
import Lean

open Lean Elab Command
elab "#audit_critical_mixed " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {decl}: {name}"
  let forbidden := #[
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarryCriticalSource.sourceMatrices_through_four_posDef,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then
        throwError "Circular finite-positivity dependency: {name}"
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
  logInfo m!"Critical source mixed audit roots: {ids.size}; type/body closure: {seen.size}; foundational and finite-positivity guards passed"

#print axioms CarryCriticalMixed.jetStencil
#print axioms CarryCriticalMixed.nativeInput_factor
#print axioms CarryCriticalMixed.amplitude_value_cancel
#print axioms CarryCriticalMixed.valueCoefficients_eq_stencil
#print axioms CarryCriticalMixed.sourceValue_eq_stencil
#print axioms CarryCriticalMixed.sourceCompanion_eq_stencil
#print axioms CarryCriticalMixed.storage_eq_stencil_slope
#print axioms CarryCriticalMixed.chiral_polarized_balance
#print axioms CarryCriticalMixed.critical_balance_eventually_mixed
#print axioms CarryCriticalMixed.critical_mixed_tendsto
#print axioms CarryCriticalMixed.secondEvenJet
#print axioms CarryCriticalMixed.secondStencil
#print axioms CarryCriticalMixed.secondBalance
#print axioms CarryCriticalMixed.second_stencil_exact
#print axioms CarryCriticalMixed.second_balance_three_slopes
#print axioms CarryCriticalMixed.sourceCoefficient
#print axioms CarryCriticalMixed.balanceConstant
#print axioms CarryCriticalMixed.balanceCorrection
#print axioms CarryCriticalMixed.balanceFourth
#print axioms CarryCriticalMixed.normalizedSourceRemainder
#print axioms CarryCriticalMixed.second_balance_exact_source_remainder
#print axioms CarryCriticalMixed.realStep_tendsto_zero
#print axioms CarryCriticalMixed.normalizedSourceRemainder_continuousAt
#print axioms CarryCriticalMixed.second_balance_tendsto
#print axioms CarryCriticalMixed.second_balance_correction_tendsto
#print axioms CarryCriticalMixed.nonlinearMarginBox
#print axioms CarryCriticalMixed.correctionSignBox
#print axioms CarryCriticalMixed.nonlinearMarginBox_positive
#print axioms CarryCriticalMixed.correctionSignBox_positive
#print axioms CarryCriticalMixed.source_nonlinear_margin_pos
#print axioms CarryCriticalMixed.source_correction_numerator_pos
#print axioms CarryCriticalMixed.secondCriticalParameter
#print axioms CarryCriticalMixed.sourceCoefficient_eq_canonical
#print axioms CarryCriticalMixed.second_old_posDef
#print axioms CarryCriticalMixed.second_old_solve
#print axioms CarryCriticalMixed.second_critical_coordinates
#print axioms CarryCriticalMixed.second_critical_balance_exact
#print axioms CarryCriticalMixed.second_pivot_formula
#print axioms CarryCriticalMixed.second_constant_eq_pivot
#print axioms CarryCriticalMixed.second_correction_formula
#print axioms CarryCriticalMixed.second_correction_neg
#print axioms CarryCriticalMixed.second_pivot_source_pos
#print axioms CarryCriticalMixed.second_critical_correction_tendsto
#print axioms CarryCriticalMixed.second_critical_between_zero_and_limit
#print axioms CarryCriticalMixed.secondNonlinearReadout
#print axioms CarryCriticalMixed.second_value_sum
#print axioms CarryCriticalMixed.eulerScale_eq_sourceCoefficient
#print axioms CarryCriticalMixed.second_euler_exact
#print axioms CarryCriticalMixed.second_nonlinear_tendsto
#print axioms CarryCriticalMixed.second_critical_nonlinear_eventually_pos
#print axioms CarrySelfAdjointOperator.nativeSourceTransverseSlope_exact_remainder
#print axioms CarrySelfAdjointOperator.ChiralReturn.storage_one_eq_euler_boundary_add_remainder
#print axioms CarryIntegralCertificate.material_theta_integral_input

#audit_critical_mixed
  CarryCriticalMixed.jetStencil
  CarryCriticalMixed.nativeInput_factor
  CarryCriticalMixed.amplitude_value_cancel
  CarryCriticalMixed.valueCoefficients_eq_stencil
  CarryCriticalMixed.sourceValue_eq_stencil
  CarryCriticalMixed.sourceCompanion_eq_stencil
  CarryCriticalMixed.storage_eq_stencil_slope
  CarryCriticalMixed.chiral_polarized_balance
  CarryCriticalMixed.critical_balance_eventually_mixed
  CarryCriticalMixed.critical_mixed_tendsto
  CarryCriticalMixed.secondEvenJet
  CarryCriticalMixed.secondStencil
  CarryCriticalMixed.secondBalance
  CarryCriticalMixed.second_stencil_exact
  CarryCriticalMixed.second_balance_three_slopes
  CarryCriticalMixed.sourceCoefficient
  CarryCriticalMixed.balanceConstant
  CarryCriticalMixed.balanceCorrection
  CarryCriticalMixed.balanceFourth
  CarryCriticalMixed.normalizedSourceRemainder
  CarryCriticalMixed.second_balance_exact_source_remainder
  CarryCriticalMixed.realStep_tendsto_zero
  CarryCriticalMixed.normalizedSourceRemainder_continuousAt
  CarryCriticalMixed.second_balance_tendsto
  CarryCriticalMixed.second_balance_correction_tendsto
  CarryCriticalMixed.nonlinearMarginBox
  CarryCriticalMixed.correctionSignBox
  CarryCriticalMixed.nonlinearMarginBox_positive
  CarryCriticalMixed.correctionSignBox_positive
  CarryCriticalMixed.source_nonlinear_margin_pos
  CarryCriticalMixed.source_correction_numerator_pos
  CarryCriticalMixed.secondCriticalParameter
  CarryCriticalMixed.sourceCoefficient_eq_canonical
  CarryCriticalMixed.second_old_posDef
  CarryCriticalMixed.second_old_solve
  CarryCriticalMixed.second_critical_coordinates
  CarryCriticalMixed.second_critical_balance_exact
  CarryCriticalMixed.second_pivot_formula
  CarryCriticalMixed.second_constant_eq_pivot
  CarryCriticalMixed.second_correction_formula
  CarryCriticalMixed.second_correction_neg
  CarryCriticalMixed.second_pivot_source_pos
  CarryCriticalMixed.second_critical_correction_tendsto
  CarryCriticalMixed.second_critical_between_zero_and_limit
  CarryCriticalMixed.secondNonlinearReadout
  CarryCriticalMixed.second_value_sum
  CarryCriticalMixed.eulerScale_eq_sourceCoefficient
  CarryCriticalMixed.second_euler_exact
  CarryCriticalMixed.second_nonlinear_tendsto
  CarryCriticalMixed.second_critical_nonlinear_eventually_pos
  CarrySelfAdjointOperator.nativeSourceTransverseSlope_exact_remainder
  CarrySelfAdjointOperator.ChiralReturn.storage_one_eq_euler_boundary_add_remainder
  CarryIntegralCertificate.material_theta_integral_input
