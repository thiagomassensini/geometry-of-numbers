import GreenPairing
import Lean

open Lean Elab Command
elab "#audit_linear_tfvd " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
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
      if forbidden.contains name || name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Canonical or downstream sign dependency in spatial proof: {name}"
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
  logInfo m!"Linear TFVD audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical sequence or characteristic"

#print axioms CarryLinearTfvd.linear_commutator_succ
#print axioms CarryLinearTfvd.linear_commutator_shift_numerator
#print axioms CarryLinearTfvd.linear_commutator_tfvd_numerator
#print axioms CarryLinearTfvd.synthesis_shift
#print axioms CarryLinearTfvd.physicalTrace
#print axioms CarryLinearTfvd.physical_linear_numerator
#print axioms CarryLinearTfvd.physical_linear_tfvd_numerator
#print axioms CarryLinearTfvd.green_inner_right_numerator
#print axioms CarryLinearTfvd.double_advance_pairing
#print axioms CarryLinearTfvd.green_linear_polarized_factor
#print axioms CarryLinearTfvd.green_linear_diagonal_factor
#print axioms CarryLinearTfvd.advance_contracts
#print axioms CarryLinearTfvd.green_linear_lower
#print axioms CarryLinearTfvd.green_linear_zero_traces_lower
#print axioms CarryLinearTfvd.green_linear_zero_traces_pos
#print axioms CarryLinearTfvd.green_linear_seed_negative

#audit_linear_tfvd
  CarryLinearTfvd.linear_commutator_succ
  CarryLinearTfvd.linear_commutator_shift_numerator
  CarryLinearTfvd.linear_commutator_tfvd_numerator
  CarryLinearTfvd.synthesis_shift
  CarryLinearTfvd.physicalTrace
  CarryLinearTfvd.physical_linear_numerator
  CarryLinearTfvd.physical_linear_tfvd_numerator
  CarryLinearTfvd.green_inner_right_numerator
  CarryLinearTfvd.double_advance_pairing
  CarryLinearTfvd.green_linear_polarized_factor
  CarryLinearTfvd.green_linear_diagonal_factor
  CarryLinearTfvd.advance_contracts
  CarryLinearTfvd.green_linear_lower
  CarryLinearTfvd.green_linear_zero_traces_lower
  CarryLinearTfvd.green_linear_zero_traces_pos
  CarryLinearTfvd.green_linear_seed_negative
