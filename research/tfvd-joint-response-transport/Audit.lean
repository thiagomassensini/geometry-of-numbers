import Regression
import Lean

open Lean Elab Command
elab "#audit_tfvd_joint " mode:ident ids:ident+ : command => do
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
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
  let forbidden := if mode.getId == `orientation then forbidden else forbidden ++ #[
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
  logInfo m!"TFVD joint numerator audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryTfvdJoint.value
#print axioms CarryTfvdJoint.logJet
#print axioms CarryTfvdJoint.completionResponse
#print axioms CarryTfvdJoint.jointNumerator
#print axioms CarryTfvdJoint.numerator
#print axioms CarryTfvdJoint.jointNumerator_cocycle
#print axioms CarryTfvdJoint.jointNumerator_self
#print axioms CarryTfvdJoint.jointNumerator_swap
#print axioms CarryTfvdJoint.jointNumerator_quotient
#print axioms CarryTfvdJoint.full_response
#print axioms CarryTfvdJoint.numerator_eq_full_difference
#print axioms CarryTfvdJoint.readouts_cutoff_independent
#print axioms CarryTfvdJoint.numerator_cutoff_independent
#print axioms CarryTfvdJoint.numerator_transport
#print axioms CarryTfvdJoint.value_hasDerivAt_zero
#print axioms CarryTfvdJoint.value_zero_ne
#print axioms CarryTfvdJoint.full_response_zero
#print axioms CarryTfvdJoint.centered_numerator_eventuallyEq
#print axioms CarryTfvdJoint.centered_numerator_hasDerivAt
#print axioms CarryTfvdJoint.centered_numerator_coefficient
#print axioms CarryTfvdJoint.centered_numerator_coefficient_cutoff
#print axioms CarryTfvdJoint.normalizedCenteredNumerator
#print axioms CarryTfvdJoint.normalizedCenteredNumerator_eventuallyEq
#print axioms CarryTfvdJoint.normalizedCenteredNumerator_odd_coefficient
#print axioms CarryTfvdJoint.polarizedNumerator
#print axioms CarryTfvdJoint.polarizedNumerator_quotient
#print axioms CarryTfvdJoint.basisSource
#print axioms CarryTfvdJoint.basisSource_pairing
#print axioms CarryTfvdJoint.radial_cauchy_denominator
#print axioms CarryTfvdJoint.physical_polarized_numerator
#print axioms CarryTfvdJoint.graph_pairing_sum
#print axioms CarryTfvdJoint.physical_basis_quotient
#print axioms CarryTfvdJoint.centeredPolarizedReadout
#print axioms CarryTfvdJoint.centeredPolarizedReadout_eventuallyEq
#print axioms CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient
#print axioms CarryTfvdJoint.jointKernel
#print axioms CarryTfvdJoint.fullSource_eventually_graph
#print axioms CarryTfvdJoint.fullSources_eventually_jointKernel
#print axioms CarryTfvdJoint.critical_jointKernel_tendsto
#print axioms CarryTfvdJoint.Control.response
#print axioms CarryTfvdJoint.Control.characteristic
#print axioms CarryTfvdJoint.Control.characteristic_ne_zero
#print axioms CarryTfvdJoint.Control.characteristic_even
#print axioms CarryTfvdJoint.Control.response_eq_logDerivative
#print axioms CarryTfvdJoint.Control.response_odd
#print axioms CarryTfvdJoint.Control.response_radial
#print axioms CarryTfvdJoint.Control.radial_diagonal_pos
#print axioms CarryTfvdJoint.Control.normalized_response
#print axioms CarryTfvdJoint.Control.second_residual_negative
#print axioms CarryTfvdJoint.Control.material
#print axioms CarryTfvdJoint.Control.material_endpoint
#print axioms CarryTfvdJoint.Control.sampled_response
#print axioms CarryTfvdJoint.Control.full_original_form_negative
#print axioms CarryTfvdJoint.Control.composition_still_holds

#audit_tfvd_joint joint_transport
  CarryTfvdJoint.value
  CarryTfvdJoint.logJet
  CarryTfvdJoint.completionResponse
  CarryTfvdJoint.jointNumerator
  CarryTfvdJoint.numerator
  CarryTfvdJoint.jointNumerator_cocycle
  CarryTfvdJoint.jointNumerator_self
  CarryTfvdJoint.jointNumerator_swap
  CarryTfvdJoint.jointNumerator_quotient
  CarryTfvdJoint.full_response
  CarryTfvdJoint.numerator_eq_full_difference
  CarryTfvdJoint.readouts_cutoff_independent
  CarryTfvdJoint.numerator_cutoff_independent
  CarryTfvdJoint.numerator_transport

#audit_tfvd_joint joint_extraction
  CarryTfvdJoint.value_hasDerivAt_zero
  CarryTfvdJoint.value_zero_ne
  CarryTfvdJoint.full_response_zero
  CarryTfvdJoint.centered_numerator_eventuallyEq
  CarryTfvdJoint.centered_numerator_hasDerivAt
  CarryTfvdJoint.centered_numerator_coefficient
  CarryTfvdJoint.centered_numerator_coefficient_cutoff
  CarryTfvdJoint.normalizedCenteredNumerator
  CarryTfvdJoint.normalizedCenteredNumerator_eventuallyEq
  CarryTfvdJoint.normalizedCenteredNumerator_odd_coefficient

#audit_tfvd_joint polarized
  CarryTfvdJoint.polarizedNumerator
  CarryTfvdJoint.polarizedNumerator_quotient
  CarryTfvdJoint.basisSource
  CarryTfvdJoint.basisSource_pairing
  CarryTfvdJoint.radial_cauchy_denominator
  CarryTfvdJoint.physical_polarized_numerator
  CarryTfvdJoint.graph_pairing_sum
  CarryTfvdJoint.physical_basis_quotient
  CarryTfvdJoint.centeredPolarizedReadout
  CarryTfvdJoint.centeredPolarizedReadout_eventuallyEq
  CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient

#audit_tfvd_joint source_application
  CarryTfvdJoint.jointKernel
  CarryTfvdJoint.fullSource_eventually_graph
  CarryTfvdJoint.fullSources_eventually_jointKernel
  CarryTfvdJoint.critical_jointKernel_tendsto

#audit_tfvd_joint auxiliary_control
  CarryTfvdJoint.Control.response
  CarryTfvdJoint.Control.characteristic
  CarryTfvdJoint.Control.characteristic_ne_zero
  CarryTfvdJoint.Control.characteristic_even
  CarryTfvdJoint.Control.response_eq_logDerivative
  CarryTfvdJoint.Control.response_odd
  CarryTfvdJoint.Control.response_radial
  CarryTfvdJoint.Control.radial_diagonal_pos
  CarryTfvdJoint.Control.normalized_response
  CarryTfvdJoint.Control.second_residual_negative
  CarryTfvdJoint.Control.material
  CarryTfvdJoint.Control.material_endpoint
  CarryTfvdJoint.Control.sampled_response
  CarryTfvdJoint.Control.full_original_form_negative
  CarryTfvdJoint.Control.composition_still_holds
