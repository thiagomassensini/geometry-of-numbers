import RefinementCoherence
import DomainCompatibility
import SourceCompatibility
import CommonJets
import Lean

open Lean Elab Command
elab "#audit_completed_pairing " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let signs := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial]
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden downstream sign consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-defined construction: {name}"
      if tier.getNat <= 1 && signs.contains name then
        throwError "Finite sign or theta-moment dependency outside canary: {name}"
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
  logInfo m!"Physical radial refinement audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryRadialRefinement.refinedAddress
#print axioms CarryRadialRefinement.refined_address_succ
#print axioms CarryRadialRefinement.powerColumn
#print axioms CarryRadialRefinement.power_column_function
#print axioms CarryRadialRefinement.power_column_inner
#print axioms CarryRadialRefinement.powerSynthesis
#print axioms CarryRadialRefinement.power_synthesis_inner
#print axioms CarryRadialRefinement.power_synthesis_norm
#print axioms CarryRadialRefinement.powerExtension
#print axioms CarryRadialRefinement.power_extension_synthesis
#print axioms CarryRadialRefinement.power_extension_norm
#print axioms CarryRadialRefinement.powerIsometry
#print axioms CarryRadialRefinement.power_isometry_feature
#print axioms CarryRadialRefinement.power_isometry_inner
#print axioms CarryRadialRefinement.radialVector
#print axioms CarryRadialRefinement.radial_vector_feature
#print axioms CarryRadialRefinement.refined_mass
#print axioms CarryRadialRefinement.refined_point
#print axioms CarryRadialRefinement.power_isometry_radial
#print axioms CarryRadialRefinement.power_isometry_finite_source
#print axioms CarryRadialRefinement.projectiveLegs
#print axioms CarryRadialRefinement.projective_legs_original
#print axioms CarryRadialRefinement.pairPower
#print axioms CarryRadialRefinement.pair_power_refines_projective
#print axioms CarryRadialRefinement.commonGrade
#print axioms CarryRadialRefinement.common_grade_comm
#print axioms CarryRadialRefinement.refined_address_comp
#print axioms CarryRadialRefinement.commonPairing
#print axioms CarryRadialRefinement.common_pairing_same_grade
#print axioms CarryRadialRefinement.further_refinement_pairing
#print axioms CarryRadialRefinement.power_composition_feature
#print axioms CarryRadialRefinement.power_composition
#print axioms CarryRadialRefinement.power_identity
#print axioms CarryRadialRefinement.equal_radial_point_common_states
#print axioms CarryRadialRefinement.powerCoefficient
#print axioms CarryRadialRefinement.power_coefficient_single
#print axioms CarryRadialRefinement.embedding_power_coefficient
#print axioms CarryRadialRefinement.powerCore
#print axioms CarryRadialRefinement.power_core_coe
#print axioms CarryRadialRefinement.coefficient_euler_power
#print axioms CarryRadialRefinement.euler_power_core
#print axioms CarryRadialRefinement.endpoint_power_coefficient
#print axioms CarryRadialRefinement.positive_value_refined
#print axioms CarryRadialRefinement.dirichlet_power_coefficient
#print axioms CarryRadialRefinement.critical_dirichlet_factor_norm_sq
#print axioms CarryRadialRefinement.originalFields
#print axioms CarryRadialRefinement.six_fields_common_isometry
#print axioms CarryRadialRefinement.original_source_legs_refined
#print axioms CarryRadialRefinement.refined_complete_balance
#print axioms CarryRadialRefinement.refined_head_tail
#print axioms CarryRadialRefinement.sample_form_factor
#print axioms CarryRadialRefinement.common_radial_gram
#print axioms CarryRadialRefinement.common_pairing_kernel
#print axioms CarryRadialRefinement.PhysicalPair
#print axioms CarryRadialRefinement.physicalForm
#print axioms CarryRadialRefinement.physicalJet
#print axioms CarryRadialRefinement.commonJetPairing
#print axioms CarryRadialRefinement.physical_form_smul
#print axioms CarryRadialRefinement.physical_form_sum
#print axioms CarryRadialRefinement.ambientPair
#print axioms CarryRadialRefinement.ambient_projective_legs
#print axioms CarryRadialRefinement.physical_jet_original
#print axioms CarryRadialRefinement.common_jet_pairing_weighted
#print axioms CarryRadialRefinement.common_jet_pairing_dslope
#print axioms CarryRadialRefinement.common_jet_pairing_eventually_dslope
#print axioms CarryRadialRefinement.common_jet_pairing_tendsto
#print axioms CarryRadialRefinement.common_even_jets
#print axioms CarryRadialRefinement.common_odd_jets
#print axioms CarryRadialRefinement.common_even_odd_jets

#audit_completed_pairing 0
  CarryRadialRefinement.refinedAddress
  CarryRadialRefinement.refined_address_succ
  CarryRadialRefinement.powerColumn
  CarryRadialRefinement.power_column_function
  CarryRadialRefinement.power_column_inner
  CarryRadialRefinement.powerSynthesis
  CarryRadialRefinement.power_synthesis_inner
  CarryRadialRefinement.power_synthesis_norm
  CarryRadialRefinement.powerExtension
  CarryRadialRefinement.power_extension_synthesis
  CarryRadialRefinement.power_extension_norm
  CarryRadialRefinement.powerIsometry
  CarryRadialRefinement.power_isometry_feature
  CarryRadialRefinement.power_isometry_inner
  CarryRadialRefinement.radialVector
  CarryRadialRefinement.radial_vector_feature
  CarryRadialRefinement.refined_mass
  CarryRadialRefinement.refined_point
  CarryRadialRefinement.power_isometry_radial
  CarryRadialRefinement.power_isometry_finite_source
  CarryRadialRefinement.projectiveLegs
  CarryRadialRefinement.projective_legs_original
  CarryRadialRefinement.pairPower
  CarryRadialRefinement.pair_power_refines_projective
  CarryRadialRefinement.commonGrade
  CarryRadialRefinement.common_grade_comm
  CarryRadialRefinement.refined_address_comp
  CarryRadialRefinement.commonPairing
  CarryRadialRefinement.common_pairing_same_grade
  CarryRadialRefinement.further_refinement_pairing
  CarryRadialRefinement.power_composition_feature
  CarryRadialRefinement.power_composition
  CarryRadialRefinement.power_identity
  CarryRadialRefinement.equal_radial_point_common_states
  CarryRadialRefinement.powerCoefficient
  CarryRadialRefinement.power_coefficient_single
  CarryRadialRefinement.embedding_power_coefficient
  CarryRadialRefinement.powerCore
  CarryRadialRefinement.power_core_coe
  CarryRadialRefinement.coefficient_euler_power
  CarryRadialRefinement.euler_power_core
  CarryRadialRefinement.endpoint_power_coefficient
  CarryRadialRefinement.positive_value_refined
  CarryRadialRefinement.dirichlet_power_coefficient
  CarryRadialRefinement.critical_dirichlet_factor_norm_sq
  CarryRadialRefinement.originalFields
  CarryRadialRefinement.six_fields_common_isometry
  CarryRadialRefinement.original_source_legs_refined
  CarryRadialRefinement.refined_complete_balance
  CarryRadialRefinement.refined_head_tail
  CarryRadialRefinement.sample_form_factor
  CarryRadialRefinement.common_radial_gram
  CarryRadialRefinement.common_pairing_kernel
  CarryRadialRefinement.PhysicalPair
  CarryRadialRefinement.physicalForm
  CarryRadialRefinement.physicalJet
  CarryRadialRefinement.commonJetPairing
  CarryRadialRefinement.physical_form_smul
  CarryRadialRefinement.physical_form_sum
  CarryRadialRefinement.ambientPair
  CarryRadialRefinement.ambient_projective_legs
  CarryRadialRefinement.physical_jet_original
  CarryRadialRefinement.common_jet_pairing_weighted
  CarryRadialRefinement.common_jet_pairing_dslope
  CarryRadialRefinement.common_jet_pairing_eventually_dslope

#audit_completed_pairing 1
  CarryRadialRefinement.common_jet_pairing_tendsto
  CarryRadialRefinement.common_even_jets
  CarryRadialRefinement.common_odd_jets
  CarryRadialRefinement.common_even_odd_jets

#audit_completed_pairing 1
  CarryRadialRefinement.refinedAddress
  CarryRadialRefinement.refined_address_succ
  CarryRadialRefinement.powerColumn
  CarryRadialRefinement.power_column_function
  CarryRadialRefinement.power_column_inner
  CarryRadialRefinement.powerSynthesis
  CarryRadialRefinement.power_synthesis_inner
  CarryRadialRefinement.power_synthesis_norm
  CarryRadialRefinement.powerExtension
  CarryRadialRefinement.power_extension_synthesis
  CarryRadialRefinement.power_extension_norm
  CarryRadialRefinement.powerIsometry
  CarryRadialRefinement.power_isometry_feature
  CarryRadialRefinement.power_isometry_inner
  CarryRadialRefinement.radialVector
  CarryRadialRefinement.radial_vector_feature
  CarryRadialRefinement.refined_mass
  CarryRadialRefinement.refined_point
  CarryRadialRefinement.power_isometry_radial
  CarryRadialRefinement.power_isometry_finite_source
  CarryRadialRefinement.projectiveLegs
  CarryRadialRefinement.projective_legs_original
  CarryRadialRefinement.pairPower
  CarryRadialRefinement.pair_power_refines_projective
  CarryRadialRefinement.commonGrade
  CarryRadialRefinement.common_grade_comm
  CarryRadialRefinement.refined_address_comp
  CarryRadialRefinement.commonPairing
  CarryRadialRefinement.common_pairing_same_grade
  CarryRadialRefinement.further_refinement_pairing
  CarryRadialRefinement.power_composition_feature
  CarryRadialRefinement.power_composition
  CarryRadialRefinement.power_identity
  CarryRadialRefinement.equal_radial_point_common_states
  CarryRadialRefinement.powerCoefficient
  CarryRadialRefinement.power_coefficient_single
  CarryRadialRefinement.embedding_power_coefficient
  CarryRadialRefinement.powerCore
  CarryRadialRefinement.power_core_coe
  CarryRadialRefinement.coefficient_euler_power
  CarryRadialRefinement.euler_power_core
  CarryRadialRefinement.endpoint_power_coefficient
  CarryRadialRefinement.positive_value_refined
  CarryRadialRefinement.dirichlet_power_coefficient
  CarryRadialRefinement.critical_dirichlet_factor_norm_sq
  CarryRadialRefinement.originalFields
  CarryRadialRefinement.six_fields_common_isometry
  CarryRadialRefinement.original_source_legs_refined
  CarryRadialRefinement.refined_complete_balance
  CarryRadialRefinement.refined_head_tail
  CarryRadialRefinement.sample_form_factor
  CarryRadialRefinement.common_radial_gram
  CarryRadialRefinement.common_pairing_kernel
  CarryRadialRefinement.PhysicalPair
  CarryRadialRefinement.physicalForm
  CarryRadialRefinement.physicalJet
  CarryRadialRefinement.commonJetPairing
  CarryRadialRefinement.physical_form_smul
  CarryRadialRefinement.physical_form_sum
  CarryRadialRefinement.ambientPair
  CarryRadialRefinement.ambient_projective_legs
  CarryRadialRefinement.physical_jet_original
  CarryRadialRefinement.common_jet_pairing_weighted
  CarryRadialRefinement.common_jet_pairing_dslope
  CarryRadialRefinement.common_jet_pairing_eventually_dslope
  CarryRadialRefinement.common_jet_pairing_tendsto
  CarryRadialRefinement.common_even_jets
  CarryRadialRefinement.common_odd_jets
  CarryRadialRefinement.common_even_odd_jets
