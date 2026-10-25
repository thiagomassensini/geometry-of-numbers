import NativeJets
import SeedMixedLimit
import Lean

open Lean Elab Command
elab "#audit_commutator_control " tier:num ids:ident+ : command => do
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
      if tier.getNat == 0 && name == moments then
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
  logInfo m!"Native commutator audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryCommutatorControl.chiralDifference
#print axioms CarryCommutatorControl.responseWeight
#print axioms CarryCommutatorControl.chiral_difference_ne_zero
#print axioms CarryCommutatorControl.chiral_weight_difference
#print axioms CarryCommutatorControl.incident_amplitude_response
#print axioms CarryCommutatorControl.radial_weight_difference
#print axioms CarryCommutatorControl.radial_weight_difference_eventually
#print axioms CarryCommutatorControl.coefficient_outside_prefix
#print axioms CarryCommutatorControl.commutator_weight_scale
#print axioms CarryCommutatorControl.commutator_equal_of_constant_difference
#print axioms CarryCommutatorControl.native_commutator_response
#print axioms CarryCommutatorControl.completed_commutator_equal_legs
#print axioms CarryCommutatorControl.completed_commutator_pairing_zero
#print axioms CarryCommutatorControl.completed_commutator_eventually_null
#print axioms CarryCommutatorControl.coefficient_weight_difference
#print axioms CarryCommutatorControl.completed_source_contrast
#print axioms CarryCommutatorControl.completed_commutator_mixed_pairing
#print axioms CarryCommutatorControl.completed_kernel_mixed_reduction
#print axioms CarryCommutatorControl.finiteEmbedding
#print axioms CarryCommutatorControl.finite_embedding_apply
#print axioms CarryCommutatorControl.finite_embedding_support
#print axioms CarryCommutatorControl.finite_embedding_weight
#print axioms CarryCommutatorControl.finite_embedding_synthesis
#print axioms CarryCommutatorControl.rawJetCoefficients
#print axioms CarryCommutatorControl.original_jet_input_factor
#print axioms CarryCommutatorControl.raw_jet_original_source
#print axioms CarryCommutatorControl.native_jet_commutator_eventually_null
#print axioms CarryCommutatorControl.seed_is_native_zero_jet
#print axioms CarryCommutatorControl.commutator_seed
#print axioms CarryCommutatorControl.physical_commutator_seed
#print axioms CarryCommutatorControl.physical_resolvent_selfAdjoint
#print axioms CarryCommutatorControl.green_seed_cross
#print axioms CarryCommutatorControl.green_seed_cross_re_pos
#print axioms CarryCommutatorControl.seedMixed
#print axioms CarryCommutatorControl.seed_mixed_exact
#print axioms CarryCommutatorControl.incident_amplitude_hasDerivAt_h0
#print axioms CarryCommutatorControl.incident_amplitude_step_tendsto
#print axioms CarryCommutatorControl.seed_mixed_tendsto
#print axioms CarryCommutatorControl.seed_mixed_eventually_negative
#print axioms CarryCommutatorControl.seed_commutator_eventually_nonzero

#audit_commutator_control 0
  CarryCommutatorControl.chiralDifference
  CarryCommutatorControl.responseWeight
  CarryCommutatorControl.chiral_difference_ne_zero
  CarryCommutatorControl.chiral_weight_difference
  CarryCommutatorControl.incident_amplitude_response
  CarryCommutatorControl.radial_weight_difference
  CarryCommutatorControl.radial_weight_difference_eventually
  CarryCommutatorControl.coefficient_outside_prefix
  CarryCommutatorControl.commutator_weight_scale
  CarryCommutatorControl.commutator_equal_of_constant_difference
  CarryCommutatorControl.native_commutator_response
  CarryCommutatorControl.completed_commutator_equal_legs
  CarryCommutatorControl.completed_commutator_pairing_zero
  CarryCommutatorControl.completed_commutator_eventually_null
  CarryCommutatorControl.coefficient_weight_difference
  CarryCommutatorControl.completed_source_contrast
  CarryCommutatorControl.completed_commutator_mixed_pairing
  CarryCommutatorControl.completed_kernel_mixed_reduction
  CarryCommutatorControl.finiteEmbedding
  CarryCommutatorControl.finite_embedding_apply
  CarryCommutatorControl.finite_embedding_support
  CarryCommutatorControl.finite_embedding_weight
  CarryCommutatorControl.finite_embedding_synthesis
  CarryCommutatorControl.rawJetCoefficients
  CarryCommutatorControl.original_jet_input_factor
  CarryCommutatorControl.raw_jet_original_source
  CarryCommutatorControl.native_jet_commutator_eventually_null
  CarryCommutatorControl.seed_is_native_zero_jet
  CarryCommutatorControl.commutator_seed
  CarryCommutatorControl.physical_commutator_seed
  CarryCommutatorControl.physical_resolvent_selfAdjoint
  CarryCommutatorControl.green_seed_cross
  CarryCommutatorControl.green_seed_cross_re_pos
  CarryCommutatorControl.seedMixed
  CarryCommutatorControl.seed_mixed_exact


#audit_commutator_control 1
  CarryCommutatorControl.incident_amplitude_hasDerivAt_h0
  CarryCommutatorControl.incident_amplitude_step_tendsto
  CarryCommutatorControl.seed_mixed_tendsto


#audit_commutator_control 2
  CarryCommutatorControl.seed_mixed_eventually_negative
  CarryCommutatorControl.seed_commutator_eventually_nonzero
