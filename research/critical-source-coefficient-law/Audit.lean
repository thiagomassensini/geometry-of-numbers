import KernelCoefficient
import GeneralExtraction
import AllOrderEuler
import Lean

open Lean Elab Command
elab "#audit_source_coefficient " ids:ident+ : command => do
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
  logInfo m!"Source coefficient audit roots: {ids.size}; type/body closure: {seen.size}; foundational and finite-positivity guards passed"

#print axioms CarrySourceLaw.transverseSource
#print axioms CarrySourceLaw.transverseCoefficient
#print axioms CarrySourceLaw.transverseSource_analytic
#print axioms CarrySourceLaw.transverseCoefficient_eq_derivative
#print axioms CarrySourceLaw.transverseCoefficient_even
#print axioms CarrySourceLaw.transverseCoefficient_odd
#print axioms CarrySourceLaw.source_exact_remainder
#print axioms CarrySourceLaw.sourceNode
#print axioms CarrySourceLaw.slope_eq_transverse
#print axioms CarrySourceLaw.sourceNode_tendsto
#print axioms CarrySourceLaw.sourceTaylorPrefix
#print axioms CarrySourceLaw.prefixCompanion
#print axioms CarrySourceLaw.tailCompanion
#print axioms CarrySourceLaw.companion_exact_taylor_sewing
#print axioms CarrySourceLaw.balance_exact_taylor_sewing
#print axioms CarrySourceLaw.analytic_sample_remainder_tendsto
#print axioms CarrySourceLaw.stencilPower
#print axioms CarrySourceLaw.stencilPower_below
#print axioms CarrySourceLaw.stencilPower_self
#print axioms CarrySourceLaw.firstStencilSurplus
#print axioms CarrySourceLaw.secondStencilSurplus
#print axioms CarrySourceLaw.greenContraction
#print axioms CarrySourceLaw.greenContraction_below
#print axioms CarrySourceLaw.greenContraction_leading
#print axioms CarrySourceLaw.greenContraction_second
#print axioms CarrySourceLaw.correctionWeight
#print axioms CarrySourceLaw.correctionWeight_eq_contraction
#print axioms CarrySourceLaw.correctionWeight_canaries
#print axioms CarrySourceLaw.h
#print axioms CarrySourceLaw.oddJet
#print axioms CarrySourceLaw.oddStencil
#print axioms CarrySourceLaw.oddBalance
#print axioms CarrySourceLaw.odd_stencil_exact
#print axioms CarrySourceLaw.odd_balance_four_slopes
#print axioms CarrySourceLaw.oddConstant
#print axioms CarrySourceLaw.oddCorrection
#print axioms CarrySourceLaw.oddHigher
#print axioms CarrySourceLaw.oddRemainder
#print axioms CarrySourceLaw.odd_balance_exact_remainder
#print axioms CarrySourceLaw.oddRemainder_continuousAt
#print axioms CarrySourceLaw.oddHigher_continuous
#print axioms CarrySourceLaw.odd_balance_tendsto
#print axioms CarrySourceLaw.odd_balance_correction_tendsto
#print axioms CarrySourceLaw.oddCorrectionBox
#print axioms CarrySourceLaw.oddPivotBox
#print axioms CarrySourceLaw.oddCorrectionBox_positive
#print axioms CarrySourceLaw.oddPivotBox_positive
#print axioms CarrySourceLaw.source_h1_pos
#print axioms CarrySourceLaw.source_odd_correction_pos
#print axioms CarrySourceLaw.source_odd_pivot_margin_pos
#print axioms CarrySourceLaw.oddCriticalParameter
#print axioms CarrySourceLaw.odd_old_posDef
#print axioms CarrySourceLaw.odd_old_solve
#print axioms CarrySourceLaw.odd_critical_coordinates
#print axioms CarrySourceLaw.odd_critical_balance_exact
#print axioms CarrySourceLaw.odd_pivot_formula
#print axioms CarrySourceLaw.odd_constant_eq_pivot
#print axioms CarrySourceLaw.odd_correction_formula
#print axioms CarrySourceLaw.odd_correction_pos
#print axioms CarrySourceLaw.odd_pivot_source_pos
#print axioms CarrySourceLaw.odd_critical_correction_tendsto
#print axioms CarrySourceLaw.odd_critical_eventually_above
#print axioms CarrySourceLaw.no_universal_critical_approach_from_below
#print axioms CarrySourceLaw.two_critical_corrections_opposite
#print axioms CarrySourceLaw.no_universal_critical_approach_from_above
#print axioms CarrySourceLaw.original_weight_re
#print axioms CarrySourceLaw.greenContraction_eq_shifted_weights
#print axioms CarrySourceLaw.odd_power_cauchy_quotient
#print axioms CarrySourceLaw.source_power_coefficient_exact
#print axioms CarrySourceLaw.canonicalCorrection
#print axioms CarrySourceLaw.canonicalCorrection_even_two
#print axioms CarrySourceLaw.canonicalCorrection_odd_two
#print axioms CarrySourceLaw.forwardWeight_sum
#print axioms CarrySourceLaw.stencil_sum
#print axioms CarrySourceLaw.nonlinearReadout
#print axioms CarrySourceLaw.all_order_euler_exact
#print axioms CarrySourceLaw.all_order_nonlinear_tendsto
#print axioms CarrySourceLaw.critical_nonlinear_tendsto
#print axioms CarrySourceLaw.critical_odd_zero_coordinate
#print axioms CarrySourceLaw.critical_odd_nonlinear_exact
#print axioms CarrySourceLaw.critical_odd_nonlinear_tendsto
#print axioms CarrySelfAdjointOperator.nativeSourceTransverseSlope_exact_remainder
#print axioms CarrySelfAdjointOperator.ChiralReturn.storage_one_eq_euler_boundary_add_remainder
#print axioms CarryIntegralCertificate.material_theta_integral_input

#audit_source_coefficient
  CarrySourceLaw.transverseSource
  CarrySourceLaw.transverseCoefficient
  CarrySourceLaw.transverseSource_analytic
  CarrySourceLaw.transverseCoefficient_eq_derivative
  CarrySourceLaw.transverseCoefficient_even
  CarrySourceLaw.transverseCoefficient_odd
  CarrySourceLaw.source_exact_remainder
  CarrySourceLaw.sourceNode
  CarrySourceLaw.slope_eq_transverse
  CarrySourceLaw.sourceNode_tendsto
  CarrySourceLaw.sourceTaylorPrefix
  CarrySourceLaw.prefixCompanion
  CarrySourceLaw.tailCompanion
  CarrySourceLaw.companion_exact_taylor_sewing
  CarrySourceLaw.balance_exact_taylor_sewing
  CarrySourceLaw.analytic_sample_remainder_tendsto
  CarrySourceLaw.stencilPower
  CarrySourceLaw.stencilPower_below
  CarrySourceLaw.stencilPower_self
  CarrySourceLaw.firstStencilSurplus
  CarrySourceLaw.secondStencilSurplus
  CarrySourceLaw.greenContraction
  CarrySourceLaw.greenContraction_below
  CarrySourceLaw.greenContraction_leading
  CarrySourceLaw.greenContraction_second
  CarrySourceLaw.correctionWeight
  CarrySourceLaw.correctionWeight_eq_contraction
  CarrySourceLaw.correctionWeight_canaries
  CarrySourceLaw.h
  CarrySourceLaw.oddJet
  CarrySourceLaw.oddStencil
  CarrySourceLaw.oddBalance
  CarrySourceLaw.odd_stencil_exact
  CarrySourceLaw.odd_balance_four_slopes
  CarrySourceLaw.oddConstant
  CarrySourceLaw.oddCorrection
  CarrySourceLaw.oddHigher
  CarrySourceLaw.oddRemainder
  CarrySourceLaw.odd_balance_exact_remainder
  CarrySourceLaw.oddRemainder_continuousAt
  CarrySourceLaw.oddHigher_continuous
  CarrySourceLaw.odd_balance_tendsto
  CarrySourceLaw.odd_balance_correction_tendsto
  CarrySourceLaw.oddCorrectionBox
  CarrySourceLaw.oddPivotBox
  CarrySourceLaw.oddCorrectionBox_positive
  CarrySourceLaw.oddPivotBox_positive
  CarrySourceLaw.source_h1_pos
  CarrySourceLaw.source_odd_correction_pos
  CarrySourceLaw.source_odd_pivot_margin_pos
  CarrySourceLaw.oddCriticalParameter
  CarrySourceLaw.odd_old_posDef
  CarrySourceLaw.odd_old_solve
  CarrySourceLaw.odd_critical_coordinates
  CarrySourceLaw.odd_critical_balance_exact
  CarrySourceLaw.odd_pivot_formula
  CarrySourceLaw.odd_constant_eq_pivot
  CarrySourceLaw.odd_correction_formula
  CarrySourceLaw.odd_correction_pos
  CarrySourceLaw.odd_pivot_source_pos
  CarrySourceLaw.odd_critical_correction_tendsto
  CarrySourceLaw.odd_critical_eventually_above
  CarrySourceLaw.no_universal_critical_approach_from_below
  CarrySourceLaw.two_critical_corrections_opposite
  CarrySourceLaw.no_universal_critical_approach_from_above
  CarrySourceLaw.original_weight_re
  CarrySourceLaw.greenContraction_eq_shifted_weights
  CarrySourceLaw.odd_power_cauchy_quotient
  CarrySourceLaw.source_power_coefficient_exact
  CarrySourceLaw.canonicalCorrection
  CarrySourceLaw.canonicalCorrection_even_two
  CarrySourceLaw.canonicalCorrection_odd_two
  CarrySourceLaw.forwardWeight_sum
  CarrySourceLaw.stencil_sum
  CarrySourceLaw.nonlinearReadout
  CarrySourceLaw.all_order_euler_exact
  CarrySourceLaw.all_order_nonlinear_tendsto
  CarrySourceLaw.critical_nonlinear_tendsto
  CarrySourceLaw.critical_odd_zero_coordinate
  CarrySourceLaw.critical_odd_nonlinear_exact
  CarrySourceLaw.critical_odd_nonlinear_tendsto
  CarrySelfAdjointOperator.nativeSourceTransverseSlope_exact_remainder
  CarrySelfAdjointOperator.ChiralReturn.storage_one_eq_euler_boundary_add_remainder
  CarryIntegralCertificate.material_theta_integral_input
