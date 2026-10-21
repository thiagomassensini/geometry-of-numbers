import SquareEnergy
import ShiftMoments
import SourceSquare
import NativeTests
import Lean

open Lean Elab Command
elab "#audit_positive_square " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg,
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
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
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
  logInfo m!"Positive square audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryPositiveSquare.gramOperator
#print axioms CarryPositiveSquare.weightedMoment
#print axioms CarryPositiveSquare.gramOperator_pairing
#print axioms CarryPositiveSquare.gramOperator_symmetric
#print axioms CarryPositiveSquare.weighted_even_pairing
#print axioms CarryPositiveSquare.weighted_odd_pairing
#print axioms CarryPositiveSquare.weighted_even_gram
#print axioms CarryPositiveSquare.weighted_odd_gram
#print axioms CarryPositiveSquare.weighted_moment_gap
#print axioms CarryPositiveSquare.shiftBoundary
#print axioms CarryPositiveSquare.physical_shift_boundary
#print axioms CarryPositiveSquare.physical_shift_square
#print axioms CarryPositiveSquare.boundaryVector
#print axioms CarryPositiveSquare.shiftSquare
#print axioms CarryPositiveSquare.boundary_adjoint_apply
#print axioms CarryPositiveSquare.boundary_readout
#print axioms CarryPositiveSquare.shiftSquare_apply
#print axioms CarryPositiveSquare.shiftSquare_twice
#print axioms CarryPositiveSquare.shiftWeightedMoment
#print axioms CarryPositiveSquare.shift_moment_recurrence
#print axioms CarryPositiveSquare.positiveSourceJet
#print axioms CarryPositiveSquare.negativeSourceJet
#print axioms CarryPositiveSquare.source_jordan_budget
#print axioms CarryPositiveSquare.source_jordan_euler
#print axioms CarryPositiveSquare.oneReturn
#print axioms CarryPositiveSquare.oneDeficit
#print axioms CarryPositiveSquare.oneSource
#print axioms CarryPositiveSquare.one_return_apply
#print axioms CarryPositiveSquare.one_defect_apply
#print axioms CarryPositiveSquare.one_storage_scalar
#print axioms CarryPositiveSquare.one_squared_defect_energy
#print axioms CarryPositiveSquare.one_deficit_tendsto_zero
#print axioms CarryPositiveSquare.one_signed_energy_tendsto
#print axioms CarryPositiveSquare.one_squared_energy_tendsto_zero
#print axioms CarryPositiveSquare.native_low_order_comparison
#print axioms CarryPositiveSquare.original_green_square_not_canonical
#print axioms CarryPositiveSquare.squared_defect_not_canonical_mass
#print axioms CarryPositiveSquare.native_no_order_two_recurrence
#print axioms CarryPositiveSquare.physical_shift_square_not_canonical

#audit_positive_square structural
  CarryPositiveSquare.gramOperator
  CarryPositiveSquare.weightedMoment
  CarryPositiveSquare.gramOperator_pairing
  CarryPositiveSquare.gramOperator_symmetric
  CarryPositiveSquare.weighted_even_pairing
  CarryPositiveSquare.weighted_odd_pairing
  CarryPositiveSquare.weighted_even_gram
  CarryPositiveSquare.weighted_odd_gram
  CarryPositiveSquare.weighted_moment_gap
  CarryPositiveSquare.shiftBoundary
  CarryPositiveSquare.physical_shift_boundary
  CarryPositiveSquare.physical_shift_square
  CarryPositiveSquare.boundaryVector
  CarryPositiveSquare.shiftSquare
  CarryPositiveSquare.boundary_adjoint_apply
  CarryPositiveSquare.boundary_readout
  CarryPositiveSquare.shiftSquare_apply
  CarryPositiveSquare.shiftSquare_twice
  CarryPositiveSquare.shiftWeightedMoment
  CarryPositiveSquare.shift_moment_recurrence
  CarryPositiveSquare.positiveSourceJet
  CarryPositiveSquare.negativeSourceJet
  CarryPositiveSquare.source_jordan_budget
  CarryPositiveSquare.source_jordan_euler
  CarryPositiveSquare.oneReturn
  CarryPositiveSquare.oneDeficit
  CarryPositiveSquare.oneSource
  CarryPositiveSquare.one_return_apply
  CarryPositiveSquare.one_defect_apply
  CarryPositiveSquare.one_storage_scalar
  CarryPositiveSquare.one_squared_defect_energy
  CarryPositiveSquare.one_deficit_tendsto_zero
  CarryPositiveSquare.one_signed_energy_tendsto
  CarryPositiveSquare.one_squared_energy_tendsto_zero

#audit_positive_square central
  CarryPositiveSquare.native_low_order_comparison
  CarryPositiveSquare.original_green_square_not_canonical
  CarryPositiveSquare.squared_defect_not_canonical_mass
  CarryPositiveSquare.native_no_order_two_recurrence
  CarryPositiveSquare.physical_shift_square_not_canonical
