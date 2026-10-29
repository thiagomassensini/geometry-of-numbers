import ZeroJetObstruction
import PrimeTowerCanary
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
  logInfo m!"Mixed radial jet audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryMixedRadial.zeroJet
#print axioms CarryMixedRadial.zeroPairing
#print axioms CarryMixedRadial.differencePairing
#print axioms CarryMixedRadial.zero_jet_original
#print axioms CarryMixedRadial.zero_jet_boundary
#print axioms CarryMixedRadial.original_zero_balance_eq_twice_pairing
#print axioms CarryMixedRadial.zero_pairing_original
#print axioms CarryMixedRadial.zero_pairing_factor_kernel
#print axioms CarryMixedRadial.zero_pairing_conj
#print axioms CarryMixedRadial.difference_pairing_four_crosses
#print axioms CarryMixedRadial.doubled_zero_factor
#print axioms CarryMixedRadial.doubled_zero_factor_gt_one
#print axioms CarryMixedRadial.native_kernel_limit
#print axioms CarryMixedRadial.zero_pairing_limit_of_factor
#print axioms CarryMixedRadial.diagonal_zero_limit
#print axioms CarryMixedRadial.doubled_index_tendsto
#print axioms CarryMixedRadial.doubled_zero_limit
#print axioms CarryMixedRadial.doubled_difference_limit
#print axioms CarryMixedRadial.doubled_limit_ne_diagonal
#print axioms CarryMixedRadial.no_joint_zero_limit
#print axioms CarryMixedRadial.doubled_difference_negative_eventually
#print axioms CarryMixedRadial.no_hilbert_gram_for_raw_radial_union
#print axioms CarryMixedRadial.doubled_factor_determinant
#print axioms CarryMixedRadial.native_two_lt_one_sixteenth
#print axioms CarryMixedRadial.tower_closed_forms_gap
#print axioms CarryMixedRadial.tower_closed_forms_not_native
#print axioms CarryMixedRadial.prime_log_ge_half
#print axioms CarryMixedRadial.prime_tower_closed_forms_not_native

#audit_completed_pairing 0
  CarryMixedRadial.zeroJet
  CarryMixedRadial.zeroPairing
  CarryMixedRadial.differencePairing
  CarryMixedRadial.zero_jet_original
  CarryMixedRadial.zero_jet_boundary
  CarryMixedRadial.original_zero_balance_eq_twice_pairing
  CarryMixedRadial.zero_pairing_original
  CarryMixedRadial.zero_pairing_factor_kernel
  CarryMixedRadial.zero_pairing_conj
  CarryMixedRadial.difference_pairing_four_crosses
  CarryMixedRadial.doubled_zero_factor
  CarryMixedRadial.doubled_zero_factor_gt_one

#audit_completed_pairing 1
  CarryMixedRadial.native_kernel_limit
  CarryMixedRadial.zero_pairing_limit_of_factor
  CarryMixedRadial.diagonal_zero_limit
  CarryMixedRadial.doubled_index_tendsto
  CarryMixedRadial.doubled_zero_limit
  CarryMixedRadial.doubled_difference_limit

#audit_completed_pairing 2
  CarryMixedRadial.doubled_limit_ne_diagonal
  CarryMixedRadial.no_joint_zero_limit
  CarryMixedRadial.doubled_difference_negative_eventually
  CarryMixedRadial.no_hilbert_gram_for_raw_radial_union
  CarryMixedRadial.doubled_factor_determinant

#audit_completed_pairing 3
  CarryMixedRadial.native_two_lt_one_sixteenth
  CarryMixedRadial.tower_closed_forms_gap
  CarryMixedRadial.tower_closed_forms_not_native
  CarryMixedRadial.prime_log_ge_half
  CarryMixedRadial.prime_tower_closed_forms_not_native

#audit_completed_pairing 4
  CarryMixedRadial.zeroJet
  CarryMixedRadial.zeroPairing
  CarryMixedRadial.differencePairing
  CarryMixedRadial.zero_jet_original
  CarryMixedRadial.zero_jet_boundary
  CarryMixedRadial.original_zero_balance_eq_twice_pairing
  CarryMixedRadial.zero_pairing_original
  CarryMixedRadial.zero_pairing_factor_kernel
  CarryMixedRadial.zero_pairing_conj
  CarryMixedRadial.difference_pairing_four_crosses
  CarryMixedRadial.doubled_zero_factor
  CarryMixedRadial.doubled_zero_factor_gt_one
  CarryMixedRadial.native_kernel_limit
  CarryMixedRadial.zero_pairing_limit_of_factor
  CarryMixedRadial.diagonal_zero_limit
  CarryMixedRadial.doubled_index_tendsto
  CarryMixedRadial.doubled_zero_limit
  CarryMixedRadial.doubled_difference_limit
  CarryMixedRadial.doubled_limit_ne_diagonal
  CarryMixedRadial.no_joint_zero_limit
  CarryMixedRadial.doubled_difference_negative_eventually
  CarryMixedRadial.no_hilbert_gram_for_raw_radial_union
  CarryMixedRadial.doubled_factor_determinant
  CarryMixedRadial.native_two_lt_one_sixteenth
  CarryMixedRadial.tower_closed_forms_gap
  CarryMixedRadial.tower_closed_forms_not_native
  CarryMixedRadial.prime_log_ge_half
  CarryMixedRadial.prime_tower_closed_forms_not_native
