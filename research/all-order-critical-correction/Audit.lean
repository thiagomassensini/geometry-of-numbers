import Regression
import Lean

open Lean Elab Command
elab "#audit_all_order_correction " ids:ident+ : command => do
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
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_tendsto_coefficient,
    `CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto,
    `CarryCriticalRelative.critical_balance_tendsto_of_isUnit,
    `CarryCriticalMixed.second_balance_correction_tendsto,
    `CarryCriticalMixed.second_critical_correction_tendsto,
    `CarrySourceLaw.odd_balance_correction_tendsto,
    `CarrySourceLaw.odd_critical_correction_tendsto]
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
  logInfo m!"All-order correction audit roots: {ids.size}; type/body closure: {seen.size}; foundational and finite-positivity guards passed"

#print axioms CarryAllOrderCorrection.taylorCoefficient
#print axioms CarryAllOrderCorrection.analytic_second_coefficient_tendsto
#print axioms CarryAllOrderCorrection.response
#print axioms CarryAllOrderCorrection.rawAtom
#print axioms CarryAllOrderCorrection.rawGreenRay
#print axioms CarryAllOrderCorrection.response_ray_analytic
#print axioms CarryAllOrderCorrection.rawAtom_analytic
#print axioms CarryAllOrderCorrection.rawGreenRay_analytic
#print axioms CarryAllOrderCorrection.rawAtom_coefficient
#print axioms CarryAllOrderCorrection.rawGreenRay_coefficient
#print axioms CarryAllOrderCorrection.rawGreenRay_even
#print axioms CarryAllOrderCorrection.rawAtom_odd_quotient
#print axioms CarryAllOrderCorrection.forwardWeight_eq_real
#print axioms CarryAllOrderCorrection.rawGreenRay_odd
#print axioms CarryAllOrderCorrection.native_sample_eq_atom
#print axioms CarryAllOrderCorrection.raw_kernel_difference_eq_ray
#print axioms CarryAllOrderCorrection.phaseFactor
#print axioms CarryAllOrderCorrection.parity_phase
#print axioms CarryAllOrderCorrection.normalization_eq_phase
#print axioms CarryAllOrderCorrection.projective_pairing_eventually_ray
#print axioms CarryAllOrderCorrection.raw_parity_below
#print axioms CarryAllOrderCorrection.combined_parity_sign
#print axioms CarryAllOrderCorrection.raw_parity_leading
#print axioms CarryAllOrderCorrection.raw_parity_next_zero
#print axioms CarryAllOrderCorrection.raw_parity_second
#print axioms CarryAllOrderCorrection.phaseFactor_cancels
#print axioms CarryAllOrderCorrection.projective_pairing_second_correction
#print axioms CarryAllOrderCorrection.synthesis_parity
#print axioms CarryAllOrderCorrection.parityPairing
#print axioms CarryAllOrderCorrection.boundaryPairing
#print axioms CarryAllOrderCorrection.boundaryCorrection
#print axioms CarryAllOrderCorrection.parityPairing_eq_sum
#print axioms CarryAllOrderCorrection.finite_polarized_second_correction
#print axioms CarryAllOrderCorrection.storage_eq_twice_pairing
#print axioms CarryAllOrderCorrection.finite_balance_second_correction
#print axioms CarryAllOrderCorrection.boundaryPairing_eq_quadratic
#print axioms CarryAllOrderCorrection.critical_boundary_pairing
#print axioms CarryAllOrderCorrection.criticalCorrection
#print axioms CarryAllOrderCorrection.critical_second_correction
#print axioms CarryAllOrderCorrection.critical_nonlinear_second_correction
#print axioms CarryAllOrderCorrection.critical_eventually_above_of_correction_pos
#print axioms CarryAllOrderCorrection.critical_eventually_below_of_correction_neg
#print axioms CarryAllOrderCorrection.criticalCoefficients_empty
#print axioms CarryAllOrderCorrection.empty_prefix_isUnit
#print axioms CarryAllOrderCorrection.first_even_correction
#print axioms CarryAllOrderCorrection.first_odd_correction
#print axioms CarryAllOrderCorrection.first_odd_second_correction
#print axioms CarryAllOrderCorrection.source_h2_positive
#print axioms CarryAllOrderCorrection.first_odd_correction_neg
#print axioms CarryAllOrderCorrection.first_odd_eventually_below
#print axioms CarryAllOrderCorrection.even_two_coefficients
#print axioms CarryAllOrderCorrection.odd_two_coefficients
#print axioms CarryAllOrderCorrection.even_two_correction_matches
#print axioms CarryAllOrderCorrection.odd_two_correction_matches
#print axioms CarryAllOrderCorrection.even_two_law_from_general
#print axioms CarryAllOrderCorrection.odd_two_law_from_general
#print axioms CarryAllOrderCorrection.odd_sector_opposite_corrections
#print axioms CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical
#print axioms CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
#print axioms NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit

#audit_all_order_correction
  CarryAllOrderCorrection.taylorCoefficient
  CarryAllOrderCorrection.analytic_second_coefficient_tendsto
  CarryAllOrderCorrection.response
  CarryAllOrderCorrection.rawAtom
  CarryAllOrderCorrection.rawGreenRay
  CarryAllOrderCorrection.response_ray_analytic
  CarryAllOrderCorrection.rawAtom_analytic
  CarryAllOrderCorrection.rawGreenRay_analytic
  CarryAllOrderCorrection.rawAtom_coefficient
  CarryAllOrderCorrection.rawGreenRay_coefficient
  CarryAllOrderCorrection.rawGreenRay_even
  CarryAllOrderCorrection.rawAtom_odd_quotient
  CarryAllOrderCorrection.forwardWeight_eq_real
  CarryAllOrderCorrection.rawGreenRay_odd
  CarryAllOrderCorrection.native_sample_eq_atom
  CarryAllOrderCorrection.raw_kernel_difference_eq_ray
  CarryAllOrderCorrection.phaseFactor
  CarryAllOrderCorrection.parity_phase
  CarryAllOrderCorrection.normalization_eq_phase
  CarryAllOrderCorrection.projective_pairing_eventually_ray
  CarryAllOrderCorrection.raw_parity_below
  CarryAllOrderCorrection.combined_parity_sign
  CarryAllOrderCorrection.raw_parity_leading
  CarryAllOrderCorrection.raw_parity_next_zero
  CarryAllOrderCorrection.raw_parity_second
  CarryAllOrderCorrection.phaseFactor_cancels
  CarryAllOrderCorrection.projective_pairing_second_correction
  CarryAllOrderCorrection.synthesis_parity
  CarryAllOrderCorrection.parityPairing
  CarryAllOrderCorrection.boundaryPairing
  CarryAllOrderCorrection.boundaryCorrection
  CarryAllOrderCorrection.parityPairing_eq_sum
  CarryAllOrderCorrection.finite_polarized_second_correction
  CarryAllOrderCorrection.storage_eq_twice_pairing
  CarryAllOrderCorrection.finite_balance_second_correction
  CarryAllOrderCorrection.boundaryPairing_eq_quadratic
  CarryAllOrderCorrection.critical_boundary_pairing
  CarryAllOrderCorrection.criticalCorrection
  CarryAllOrderCorrection.critical_second_correction
  CarryAllOrderCorrection.critical_nonlinear_second_correction
  CarryAllOrderCorrection.critical_eventually_above_of_correction_pos
  CarryAllOrderCorrection.critical_eventually_below_of_correction_neg
  CarryAllOrderCorrection.criticalCoefficients_empty
  CarryAllOrderCorrection.empty_prefix_isUnit
  CarryAllOrderCorrection.first_even_correction
  CarryAllOrderCorrection.first_odd_correction
  CarryAllOrderCorrection.first_odd_second_correction
  CarryAllOrderCorrection.source_h2_positive
  CarryAllOrderCorrection.first_odd_correction_neg
  CarryAllOrderCorrection.first_odd_eventually_below
  CarryAllOrderCorrection.even_two_coefficients
  CarryAllOrderCorrection.odd_two_coefficients
  CarryAllOrderCorrection.even_two_correction_matches
  CarryAllOrderCorrection.odd_two_correction_matches
  CarryAllOrderCorrection.even_two_law_from_general
  CarryAllOrderCorrection.odd_two_law_from_general
  CarryAllOrderCorrection.odd_sector_opposite_corrections
  CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical
  CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
  NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit

elab "#audit_generic_no_sign " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarryCriticalMixed.source_nonlinear_margin_pos,
    `CarryCriticalMixed.source_correction_numerator_pos,
    `CarrySourceLaw.source_h1_pos,
    `CarrySourceLaw.source_odd_correction_pos,
    `CarrySourceLaw.source_odd_pivot_margin_pos,
    `CarryAllOrderCorrection.source_h2_positive]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then
        throwError "Generic rate consumes finite source sign: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
  logInfo m!"Generic rate sign audit roots: {ids.size}; type/body closure: {seen.size}; no listed finite source sign input"

#audit_generic_no_sign
  CarryAllOrderCorrection.rawGreenRay_odd
  CarryAllOrderCorrection.projective_pairing_second_correction
  CarryAllOrderCorrection.finite_polarized_second_correction
  CarryAllOrderCorrection.finite_balance_second_correction
  CarryAllOrderCorrection.critical_second_correction
  CarryAllOrderCorrection.critical_nonlinear_second_correction
