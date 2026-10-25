import CriticalKernel
import FinitePorts
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
  logInfo m!"Interior critical Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryInteriorGreen.interior_bulk
#print axioms CarryInteriorGreen.interior_numerator
#print axioms CarryInteriorGreen.greenColumn
#print axioms CarryInteriorGreen.interiorPort
#print axioms CarryInteriorGreen.reconstructed_interior
#print axioms CarryInteriorGreen.finite_bulk_add
#print axioms CarryInteriorGreen.numerator_add
#print axioms CarryInteriorGreen.finite_bulk_zero
#print axioms CarryInteriorGreen.numerator_zero
#print axioms CarryInteriorGreen.numerator_smul
#print axioms CarryInteriorGreen.residualMap
#print axioms CarryInteriorGreen.residual_map_apply
#print axioms CarryInteriorGreen.bulk_eq_source_sub_residual
#print axioms CarryInteriorGreen.bulkMap
#print axioms CarryInteriorGreen.bulk_map_original
#print axioms CarryInteriorGreen.residualFeature
#print axioms CarryInteriorGreen.threeRegular
#print axioms CarryInteriorGreen.three_residual_columns
#print axioms CarryInteriorGreen.three_residual_cross_zero
#print axioms CarryInteriorGreen.three_ordered_crossing
#print axioms CarryInteriorGreen.secondScale
#print axioms CarryInteriorGreen.criticalWeight
#print axioms CarryInteriorGreen.criticalInput
#print axioms CarryInteriorGreen.critical_source_original
#print axioms CarryInteriorGreen.criticalBulk
#print axioms CarryInteriorGreen.criticalResidual
#print axioms CarryInteriorGreen.critical_residual_expansion
#print axioms CarryInteriorGreen.critical_bulk_expansion
#print axioms CarryInteriorGreen.critical_residual_pair
#print axioms CarryInteriorGreen.critical_residual_self_zero
#print axioms CarryInteriorGreen.critical_mixed_nine_crossings
#print axioms CarryInteriorGreen.critical_vector_split
#print axioms CarryInteriorGreen.critical_energy_three_sectors
#print axioms CarryInteriorGreen.prefixRegular
#print axioms CarryInteriorGreen.residual_basis_all
#print axioms CarryInteriorGreen.input_basis_expansion
#print axioms CarryInteriorGreen.finiteResidualFeature
#print axioms CarryInteriorGreen.finite_residual_closed
#print axioms CarryInteriorGreen.finite_residual_cross_zero
#print axioms CarryInteriorGreen.three_regular_eventually
#print axioms CarryInteriorGreen.finite_prefix_eventually
#print axioms CarryInteriorGreen.finite_residual_eventually_closed
#print axioms CarryInteriorGreen.criticalPairing
#print axioms CarryInteriorGreen.form_smul_left
#print axioms CarryInteriorGreen.form_smul_right
#print axioms CarryInteriorGreen.critical_pairing_four
#print axioms CarryInteriorGreen.critical_pairing_limit
#print axioms CarryInteriorGreen.critical_source_limit
#print axioms CarryInteriorGreen.critical_green_limit
#print axioms CarryInteriorGreen.first_source_schur_eq
#print axioms CarryInteriorGreen.schur_green_limit
#print axioms CarryInteriorGreen.critical_limit_complete_square

#audit_completed_pairing 0
  CarryInteriorGreen.interior_bulk
  CarryInteriorGreen.interior_numerator
  CarryInteriorGreen.greenColumn
  CarryInteriorGreen.interiorPort
  CarryInteriorGreen.reconstructed_interior
  CarryInteriorGreen.finite_bulk_add
  CarryInteriorGreen.numerator_add
  CarryInteriorGreen.finite_bulk_zero
  CarryInteriorGreen.numerator_zero
  CarryInteriorGreen.numerator_smul
  CarryInteriorGreen.residualMap
  CarryInteriorGreen.residual_map_apply
  CarryInteriorGreen.bulk_eq_source_sub_residual
  CarryInteriorGreen.bulkMap
  CarryInteriorGreen.bulk_map_original
  CarryInteriorGreen.residualFeature
  CarryInteriorGreen.threeRegular
  CarryInteriorGreen.three_residual_columns
  CarryInteriorGreen.three_residual_cross_zero
  CarryInteriorGreen.three_ordered_crossing
  CarryInteriorGreen.secondScale
  CarryInteriorGreen.criticalWeight
  CarryInteriorGreen.criticalInput
  CarryInteriorGreen.critical_source_original
  CarryInteriorGreen.criticalBulk
  CarryInteriorGreen.criticalResidual
  CarryInteriorGreen.critical_residual_expansion
  CarryInteriorGreen.critical_bulk_expansion
  CarryInteriorGreen.critical_residual_pair
  CarryInteriorGreen.critical_residual_self_zero
  CarryInteriorGreen.critical_mixed_nine_crossings
  CarryInteriorGreen.critical_vector_split
  CarryInteriorGreen.critical_energy_three_sectors
  CarryInteriorGreen.prefixRegular
  CarryInteriorGreen.residual_basis_all
  CarryInteriorGreen.input_basis_expansion
  CarryInteriorGreen.finiteResidualFeature
  CarryInteriorGreen.finite_residual_closed
  CarryInteriorGreen.finite_residual_cross_zero

#audit_completed_pairing 1
  CarryInteriorGreen.three_regular_eventually
  CarryInteriorGreen.finite_prefix_eventually
  CarryInteriorGreen.finite_residual_eventually_closed
  CarryInteriorGreen.criticalPairing
  CarryInteriorGreen.form_smul_left
  CarryInteriorGreen.form_smul_right
  CarryInteriorGreen.critical_pairing_four
  CarryInteriorGreen.critical_pairing_limit
  CarryInteriorGreen.critical_source_limit
  CarryInteriorGreen.critical_green_limit
  CarryInteriorGreen.first_source_schur_eq
  CarryInteriorGreen.schur_green_limit
  CarryInteriorGreen.critical_limit_complete_square

#audit_completed_pairing 1
  CarryInteriorGreen.interior_bulk
  CarryInteriorGreen.interior_numerator
  CarryInteriorGreen.greenColumn
  CarryInteriorGreen.interiorPort
  CarryInteriorGreen.reconstructed_interior
  CarryInteriorGreen.finite_bulk_add
  CarryInteriorGreen.numerator_add
  CarryInteriorGreen.finite_bulk_zero
  CarryInteriorGreen.numerator_zero
  CarryInteriorGreen.numerator_smul
  CarryInteriorGreen.residualMap
  CarryInteriorGreen.residual_map_apply
  CarryInteriorGreen.bulk_eq_source_sub_residual
  CarryInteriorGreen.bulkMap
  CarryInteriorGreen.bulk_map_original
  CarryInteriorGreen.residualFeature
  CarryInteriorGreen.threeRegular
  CarryInteriorGreen.three_residual_columns
  CarryInteriorGreen.three_residual_cross_zero
  CarryInteriorGreen.three_ordered_crossing
  CarryInteriorGreen.secondScale
  CarryInteriorGreen.criticalWeight
  CarryInteriorGreen.criticalInput
  CarryInteriorGreen.critical_source_original
  CarryInteriorGreen.criticalBulk
  CarryInteriorGreen.criticalResidual
  CarryInteriorGreen.critical_residual_expansion
  CarryInteriorGreen.critical_bulk_expansion
  CarryInteriorGreen.critical_residual_pair
  CarryInteriorGreen.critical_residual_self_zero
  CarryInteriorGreen.critical_mixed_nine_crossings
  CarryInteriorGreen.critical_vector_split
  CarryInteriorGreen.critical_energy_three_sectors
  CarryInteriorGreen.prefixRegular
  CarryInteriorGreen.residual_basis_all
  CarryInteriorGreen.input_basis_expansion
  CarryInteriorGreen.finiteResidualFeature
  CarryInteriorGreen.finite_residual_closed
  CarryInteriorGreen.finite_residual_cross_zero
  CarryInteriorGreen.three_regular_eventually
  CarryInteriorGreen.finite_prefix_eventually
  CarryInteriorGreen.finite_residual_eventually_closed
  CarryInteriorGreen.criticalPairing
  CarryInteriorGreen.form_smul_left
  CarryInteriorGreen.form_smul_right
  CarryInteriorGreen.critical_pairing_four
  CarryInteriorGreen.critical_pairing_limit
  CarryInteriorGreen.critical_source_limit
  CarryInteriorGreen.critical_green_limit
  CarryInteriorGreen.first_source_schur_eq
  CarryInteriorGreen.schur_green_limit
  CarryInteriorGreen.critical_limit_complete_square
