import WholeSourceReadout
import ResolventDomain
import ResidualCrossings
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
  logInfo m!"Native Green intertwiner audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryRadialGreen.physical_feature_zero_ne_zero
#print axioms CarryRadialGreen.physicalSpaceNontrivial
#print axioms CarryRadialGreen.advance_preserves_closure
#print axioms CarryRadialGreen.nativeAdvance
#print axioms CarryRadialGreen.native_advance_coe
#print axioms CarryRadialGreen.native_advance_feature
#print axioms CarryRadialGreen.native_advance_pow_feature
#print axioms CarryRadialGreen.native_advance_norm_le_one
#print axioms CarryRadialGreen.native_advance_isPositive
#print axioms CarryRadialGreen.power_advance_feature
#print axioms CarryRadialGreen.power_advance
#print axioms CarryRadialGreen.greenDenominator
#print axioms CarryRadialGreen.greenResolvent
#print axioms CarryRadialGreen.green_denominator_isUnit
#print axioms CarryRadialGreen.green_left_inverse
#print axioms CarryRadialGreen.green_right_inverse
#print axioms CarryRadialGreen.green_resolvent_denominator
#print axioms CarryRadialGreen.green_denominator_resolvent
#print axioms CarryRadialGreen.power_green_denominator
#print axioms CarryRadialGreen.power_green_resolvent
#print axioms CarryRadialGreen.power_green_resolvent_squared
#print axioms CarryRadialGreen.native_advance_pow_coe
#print axioms CarryRadialGreen.green_denominator_coe
#print axioms CarryRadialGreen.green_resolvent_one_original
#print axioms CarryRadialGreen.pairAdvance
#print axioms CarryRadialGreen.pairResolvent
#print axioms CarryRadialGreen.ambient_pair_injective
#print axioms CarryRadialGreen.ambient_pair_advance
#print axioms CarryRadialGreen.ambient_pair_resolvent
#print axioms CarryRadialGreen.ambient_pair_resolvent_squared
#print axioms CarryRadialGreen.completedSource
#print axioms CarryRadialGreen.completed_source_original
#print axioms CarryRadialGreen.completedResidual
#print axioms CarryRadialGreen.completed_residual_original
#print axioms CarryRadialGreen.bulkBoundary
#print axioms CarryRadialGreen.residualNumerator
#print axioms CarryRadialGreen.bulk_boundary_original
#print axioms CarryRadialGreen.residual_numerator_original
#print axioms CarryRadialGreen.completed_numerator
#print axioms CarryRadialGreen.completed_reconstruct
#print axioms CarryRadialGreen.pair_power_resolvent
#print axioms CarryRadialGreen.pair_power_resolvent_squared
#print axioms CarryRadialGreen.refined_completed_reconstruct
#print axioms CarryRadialGreen.physical_form_four_sectors
#print axioms CarryRadialGreen.refined_completed_four_sectors
#print axioms CarryRadialGreen.reconstructedBulk
#print axioms CarryRadialGreen.reconstructedResidual
#print axioms CarryRadialGreen.correctedGreenPairing
#print axioms CarryRadialGreen.corrected_green_pairing_is_common
#print axioms CarryRadialGreen.corrected_green_pairing_is_canonical
#print axioms CarryRadialGreen.corrected_green_weight_independent
#print axioms CarryRadialGreen.CorePair
#print axioms CarryRadialGreen.corePairEmbedding
#print axioms CarryRadialGreen.projectiveCore
#print axioms CarryRadialGreen.projective_core_coe
#print axioms CarryRadialGreen.completedCoreSource
#print axioms CarryRadialGreen.completed_core_source_coe
#print axioms CarryRadialGreen.pairCorePower
#print axioms CarryRadialGreen.pair_core_power_coe
#print axioms CarryRadialGreen.materialPairReadout
#print axioms CarryRadialGreen.material_readout_power
#print axioms CarryRadialGreen.whole_green_material_readout
#print axioms CarryRadialGreen.core_pair_embedding_injective
#print axioms CarryRadialGreen.whole_green_core_witness_unique
#print axioms CarryRadialGreen.advance_embedding_shift
#print axioms CarryRadialGreen.resolvent_first_column_not_finite
#print axioms CarryRadialGreen.sourceRegular
#print axioms CarryRadialGreen.numeratorRegular
#print axioms CarryRadialGreen.completed_residual_equal_legs
#print axioms CarryRadialGreen.residual_numerator_equal_legs
#print axioms CarryRadialGreen.reconstructed_residual_equal_legs
#print axioms CarryRadialGreen.reconstructed_residual_pairing_zero
#print axioms CarryRadialGreen.source_regular_eventually
#print axioms CarryRadialGreen.numerator_regular_eventually
#print axioms CarryRadialGreen.residual_pairing_eventually_zero
#print axioms CarryRadialGreen.corrected_green_three_sectors
#print axioms CarryRadialGreen.refined_source_green_split
#print axioms CarryRadialGreen.physical_form_re_symm
#print axioms CarryRadialGreen.signed_energy_bulk_plus_mixed

#audit_completed_pairing 0
  CarryRadialGreen.physical_feature_zero_ne_zero
  CarryRadialGreen.physicalSpaceNontrivial
  CarryRadialGreen.advance_preserves_closure
  CarryRadialGreen.nativeAdvance
  CarryRadialGreen.native_advance_coe
  CarryRadialGreen.native_advance_feature
  CarryRadialGreen.native_advance_pow_feature
  CarryRadialGreen.native_advance_norm_le_one
  CarryRadialGreen.native_advance_isPositive
  CarryRadialGreen.power_advance_feature
  CarryRadialGreen.power_advance
  CarryRadialGreen.greenDenominator
  CarryRadialGreen.greenResolvent
  CarryRadialGreen.green_denominator_isUnit
  CarryRadialGreen.green_left_inverse
  CarryRadialGreen.green_right_inverse
  CarryRadialGreen.green_resolvent_denominator
  CarryRadialGreen.green_denominator_resolvent
  CarryRadialGreen.power_green_denominator
  CarryRadialGreen.power_green_resolvent
  CarryRadialGreen.power_green_resolvent_squared
  CarryRadialGreen.native_advance_pow_coe
  CarryRadialGreen.green_denominator_coe
  CarryRadialGreen.green_resolvent_one_original
  CarryRadialGreen.pairAdvance
  CarryRadialGreen.pairResolvent
  CarryRadialGreen.ambient_pair_injective
  CarryRadialGreen.ambient_pair_advance
  CarryRadialGreen.ambient_pair_resolvent
  CarryRadialGreen.ambient_pair_resolvent_squared
  CarryRadialGreen.completedSource
  CarryRadialGreen.completed_source_original
  CarryRadialGreen.completedResidual
  CarryRadialGreen.completed_residual_original
  CarryRadialGreen.bulkBoundary
  CarryRadialGreen.residualNumerator
  CarryRadialGreen.bulk_boundary_original
  CarryRadialGreen.residual_numerator_original
  CarryRadialGreen.completed_numerator
  CarryRadialGreen.completed_reconstruct
  CarryRadialGreen.pair_power_resolvent
  CarryRadialGreen.pair_power_resolvent_squared
  CarryRadialGreen.refined_completed_reconstruct
  CarryRadialGreen.physical_form_four_sectors
  CarryRadialGreen.refined_completed_four_sectors
  CarryRadialGreen.reconstructedBulk
  CarryRadialGreen.reconstructedResidual
  CarryRadialGreen.correctedGreenPairing
  CarryRadialGreen.corrected_green_pairing_is_common
  CarryRadialGreen.corrected_green_pairing_is_canonical
  CarryRadialGreen.corrected_green_weight_independent
  CarryRadialGreen.CorePair
  CarryRadialGreen.corePairEmbedding
  CarryRadialGreen.projectiveCore
  CarryRadialGreen.projective_core_coe
  CarryRadialGreen.completedCoreSource
  CarryRadialGreen.completed_core_source_coe
  CarryRadialGreen.pairCorePower
  CarryRadialGreen.pair_core_power_coe
  CarryRadialGreen.materialPairReadout
  CarryRadialGreen.material_readout_power
  CarryRadialGreen.whole_green_material_readout
  CarryRadialGreen.core_pair_embedding_injective
  CarryRadialGreen.whole_green_core_witness_unique
  CarryRadialGreen.advance_embedding_shift
  CarryRadialGreen.resolvent_first_column_not_finite
  CarryRadialGreen.sourceRegular
  CarryRadialGreen.numeratorRegular
  CarryRadialGreen.completed_residual_equal_legs
  CarryRadialGreen.residual_numerator_equal_legs
  CarryRadialGreen.reconstructed_residual_equal_legs
  CarryRadialGreen.reconstructed_residual_pairing_zero
  CarryRadialGreen.source_regular_eventually
  CarryRadialGreen.numerator_regular_eventually
  CarryRadialGreen.residual_pairing_eventually_zero
  CarryRadialGreen.corrected_green_three_sectors
  CarryRadialGreen.refined_source_green_split
  CarryRadialGreen.physical_form_re_symm
  CarryRadialGreen.signed_energy_bulk_plus_mixed

#audit_completed_pairing 0
  CarryRadialGreen.physical_feature_zero_ne_zero
  CarryRadialGreen.physicalSpaceNontrivial
  CarryRadialGreen.advance_preserves_closure
  CarryRadialGreen.nativeAdvance
  CarryRadialGreen.native_advance_coe
  CarryRadialGreen.native_advance_feature
  CarryRadialGreen.native_advance_pow_feature
  CarryRadialGreen.native_advance_norm_le_one
  CarryRadialGreen.native_advance_isPositive
  CarryRadialGreen.power_advance_feature
  CarryRadialGreen.power_advance
  CarryRadialGreen.greenDenominator
  CarryRadialGreen.greenResolvent
  CarryRadialGreen.green_denominator_isUnit
  CarryRadialGreen.green_left_inverse
  CarryRadialGreen.green_right_inverse
  CarryRadialGreen.green_resolvent_denominator
  CarryRadialGreen.green_denominator_resolvent
  CarryRadialGreen.power_green_denominator
  CarryRadialGreen.power_green_resolvent
  CarryRadialGreen.power_green_resolvent_squared
  CarryRadialGreen.native_advance_pow_coe
  CarryRadialGreen.green_denominator_coe
  CarryRadialGreen.green_resolvent_one_original
  CarryRadialGreen.pairAdvance
  CarryRadialGreen.pairResolvent
  CarryRadialGreen.ambient_pair_injective
  CarryRadialGreen.ambient_pair_advance
  CarryRadialGreen.ambient_pair_resolvent
  CarryRadialGreen.ambient_pair_resolvent_squared
  CarryRadialGreen.completedSource
  CarryRadialGreen.completed_source_original
  CarryRadialGreen.completedResidual
  CarryRadialGreen.completed_residual_original
  CarryRadialGreen.bulkBoundary
  CarryRadialGreen.residualNumerator
  CarryRadialGreen.bulk_boundary_original
  CarryRadialGreen.residual_numerator_original
  CarryRadialGreen.completed_numerator
  CarryRadialGreen.completed_reconstruct
  CarryRadialGreen.pair_power_resolvent
  CarryRadialGreen.pair_power_resolvent_squared
  CarryRadialGreen.refined_completed_reconstruct
  CarryRadialGreen.physical_form_four_sectors
  CarryRadialGreen.refined_completed_four_sectors
  CarryRadialGreen.reconstructedBulk
  CarryRadialGreen.reconstructedResidual
  CarryRadialGreen.correctedGreenPairing
  CarryRadialGreen.corrected_green_pairing_is_common
  CarryRadialGreen.corrected_green_pairing_is_canonical
  CarryRadialGreen.corrected_green_weight_independent
  CarryRadialGreen.CorePair
  CarryRadialGreen.corePairEmbedding
  CarryRadialGreen.projectiveCore
  CarryRadialGreen.projective_core_coe
  CarryRadialGreen.completedCoreSource
  CarryRadialGreen.completed_core_source_coe
  CarryRadialGreen.pairCorePower
  CarryRadialGreen.pair_core_power_coe
  CarryRadialGreen.materialPairReadout
  CarryRadialGreen.material_readout_power
  CarryRadialGreen.whole_green_material_readout
  CarryRadialGreen.core_pair_embedding_injective
  CarryRadialGreen.whole_green_core_witness_unique
  CarryRadialGreen.advance_embedding_shift
  CarryRadialGreen.resolvent_first_column_not_finite
  CarryRadialGreen.sourceRegular
  CarryRadialGreen.numeratorRegular
  CarryRadialGreen.completed_residual_equal_legs
  CarryRadialGreen.residual_numerator_equal_legs
  CarryRadialGreen.reconstructed_residual_equal_legs
  CarryRadialGreen.reconstructed_residual_pairing_zero
  CarryRadialGreen.source_regular_eventually
  CarryRadialGreen.numerator_regular_eventually
  CarryRadialGreen.residual_pairing_eventually_zero
  CarryRadialGreen.corrected_green_three_sectors
  CarryRadialGreen.refined_source_green_split
  CarryRadialGreen.physical_form_re_symm
  CarryRadialGreen.signed_energy_bulk_plus_mixed
