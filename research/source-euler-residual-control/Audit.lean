import PolarizedEuler
import SourceWitness
import Lean

open Lean Elab Command
elab "#audit_residual_euler " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one]
  let forbidden := alwaysForbidden ++ if mode.getId == `structural then #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one]
    else #[]
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
        throwError "Unexpected finite sign dependency: {name}"
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
  logInfo m!"Residual Euler audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryResidualEuler.jetValues
#print axioms CarryResidualEuler.nonlinearReadout
#print axioms CarryResidualEuler.forward_weights_sum
#print axioms CarryResidualEuler.jet_value_eq_sum
#print axioms CarryResidualEuler.jet_values_sum
#print axioms CarryResidualEuler.euler_scale_native
#print axioms CarryResidualEuler.storage_jet_euler_exact
#print axioms CarryResidualEuler.budget_euler_exact
#print axioms CarryResidualEuler.nonlinear_tendsto
#print axioms CarryResidualEuler.pr41_nonlinear_tendsto
#print axioms CarryResidualEuler.pr41_even_euler_coefficient
#print axioms CarryResidualEuler.pr41_odd_euler_coefficient
#print axioms CarryResidualEuler.nonlinearPairing
#print axioms CarryResidualEuler.nonlinearPairing_self_re
#print axioms CarryResidualEuler.budget_slope_polarized
#print axioms CarryResidualEuler.budget_euler_polarized
#print axioms CarryResidualEuler.seventhTrialBoundary
#print axioms CarryResidualEuler.seventh_trial_energy
#print axioms CarryResidualEuler.seventh_trial_zero
#print axioms CarryResidualEuler.trial_pairing_mem
#print axioms CarryResidualEuler.seventhNonlinearMargin
#print axioms CarryResidualEuler.seventhNonlinearBox
#print axioms CarryResidualEuler.seventh_nonlinear_mem
#print axioms CarryResidualEuler.seventh_nonlinear_checks
#print axioms CarryResidualEuler.seventh_nonlinear_bounds
#print axioms CarryResidualEuler.seventh_trial_positive_margin
#print axioms CarryResidualEuler.seventh_nonlinear_tendsto
#print axioms CarryResidualEuler.seventh_nonlinear_eventually_negative
#print axioms CarryResidualEuler.seventh_trial_relative_budget
#print axioms CarryResidualEuler.seventh_signed_compensation

#audit_residual_euler structural
  CarryResidualEuler.jetValues
  CarryResidualEuler.nonlinearReadout
  CarryResidualEuler.forward_weights_sum
  CarryResidualEuler.jet_value_eq_sum
  CarryResidualEuler.jet_values_sum
  CarryResidualEuler.euler_scale_native
  CarryResidualEuler.storage_jet_euler_exact
  CarryResidualEuler.budget_euler_exact
  CarryResidualEuler.nonlinear_tendsto
  CarryResidualEuler.pr41_nonlinear_tendsto
  CarryResidualEuler.pr41_even_euler_coefficient
  CarryResidualEuler.pr41_odd_euler_coefficient
  CarryResidualEuler.nonlinearPairing
  CarryResidualEuler.nonlinearPairing_self_re
  CarryResidualEuler.budget_slope_polarized
  CarryResidualEuler.budget_euler_polarized

#audit_residual_euler central
  CarryResidualEuler.seventhTrialBoundary
  CarryResidualEuler.seventh_trial_energy
  CarryResidualEuler.seventh_trial_zero
  CarryResidualEuler.trial_pairing_mem
  CarryResidualEuler.seventhNonlinearMargin
  CarryResidualEuler.seventhNonlinearBox
  CarryResidualEuler.seventh_nonlinear_mem
  CarryResidualEuler.seventh_nonlinear_checks
  CarryResidualEuler.seventh_nonlinear_bounds
  CarryResidualEuler.seventh_trial_positive_margin
  CarryResidualEuler.seventh_nonlinear_tendsto
  CarryResidualEuler.seventh_nonlinear_eventually_negative
  CarryResidualEuler.seventh_trial_relative_budget
  CarryResidualEuler.seventh_signed_compensation
