import EntrywiseSquare
import NativeWitness
import Lean

open Lean Elab Command
elab "#audit_entrywise " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
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
  logInfo m!"Entrywise-square audit {mode.getId}: roots {ids.size}; closure {seen.size}; allowed foundations passed"

#print axioms CarryEntrywiseSquare.squaredMoments
#print axioms CarryEntrywiseSquare.hankel_square
#print axioms CarryEntrywiseSquare.shifted_square
#print axioms CarryEntrywiseSquare.squared_psd_of_psd
#print axioms CarryEntrywiseSquare.squared_shifted_psd_of_psd
#print axioms CarryEntrywiseSquare.singletonEigenvalue
#print axioms CarryEntrywiseSquare.singleton_congruence
#print axioms CarryEntrywiseSquare.actual_singleton_section
#print axioms CarryEntrywiseSquare.singleton_square
#print axioms CarryEntrywiseSquare.inverse_sqrt_gt_one
#print axioms CarryEntrywiseSquare.singleton_square_not_height
#print axioms CarryEntrywiseSquare.singleton_squared_height
#print axioms CarryEntrywiseSquare.singleton_mass_cancels
#print axioms CarryEntrywiseSquare.square_changes_logarithmic_sequence
#print axioms CarryEntrywiseSquare.finite_product_moments
#print axioms CarryEntrywiseSquare.paired_feature
#print axioms CarryEntrywiseSquare.badMoments
#print axioms CarryEntrywiseSquare.squared_bad_quadratic
#print axioms CarryEntrywiseSquare.squared_bad_not_psd
#print axioms CarryEntrywiseSquare.maskedMoments
#print axioms CarryEntrywiseSquare.masked_original_not_psd
#print axioms CarryEntrywiseSquare.masked_square_psd
#print axioms CarryEntrywiseSquare.native_first_pair
#print axioms CarryEntrywiseSquare.native_squared_eigenvalue_not_height
#print axioms CarryEntrywiseSquare.native_squared_mass_changed

#audit_entrywise EntrywiseSquare
  CarryEntrywiseSquare.squaredMoments
  CarryEntrywiseSquare.hankel_square
  CarryEntrywiseSquare.shifted_square
  CarryEntrywiseSquare.squared_psd_of_psd
  CarryEntrywiseSquare.squared_shifted_psd_of_psd
  CarryEntrywiseSquare.singletonEigenvalue
  CarryEntrywiseSquare.singleton_congruence
  CarryEntrywiseSquare.actual_singleton_section
  CarryEntrywiseSquare.singleton_square
  CarryEntrywiseSquare.inverse_sqrt_gt_one
  CarryEntrywiseSquare.singleton_square_not_height
  CarryEntrywiseSquare.singleton_squared_height
  CarryEntrywiseSquare.singleton_mass_cancels
  CarryEntrywiseSquare.square_changes_logarithmic_sequence
  CarryEntrywiseSquare.finite_product_moments
  CarryEntrywiseSquare.paired_feature
  CarryEntrywiseSquare.badMoments
  CarryEntrywiseSquare.squared_bad_quadratic
  CarryEntrywiseSquare.squared_bad_not_psd
  CarryEntrywiseSquare.maskedMoments
  CarryEntrywiseSquare.masked_original_not_psd
  CarryEntrywiseSquare.masked_square_psd

#audit_entrywise NativeWitness
  CarryEntrywiseSquare.native_first_pair
  CarryEntrywiseSquare.native_squared_eigenvalue_not_height
  CarryEntrywiseSquare.native_squared_mass_changed
