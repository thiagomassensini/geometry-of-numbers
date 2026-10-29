import CompletedSourceBridge
import Lean

open Lean Elab Command
elab "#audit_native_tfvd " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
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
      if name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Canonical moments or downstream positivity used to construct source: {name}"
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
  logInfo m!"Native TFVD completion audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moment construction"

#print axioms CarryNativeTfvd.vertical_shift_basis
#print axioms CarryNativeTfvd.native_synthesis_shift
#print axioms CarryNativeTfvd.vertical_shift_backward_trace
#print axioms CarryNativeTfvd.native_backward_numerator
#print axioms CarryNativeTfvd.vertical_numerator_two_traces
#print axioms CarryNativeTfvd.synthesized_tfvd
#print axioms CarryNativeTfvd.physical_numerator_two_traces
#print axioms CarryNativeTfvd.physical_resolvent_commutes_advance
#print axioms CarryNativeTfvd.physical_resolvent_solve
#print axioms CarryNativeTfvd.physical_tfvd_reconstruction
#print axioms CarryNativeTfvd.physical_boundary_return
#print axioms CarryNativeTfvd.physical_green_on_bracket
#print axioms CarryNativeTfvd.coefficientQuadratures
#print axioms CarryNativeTfvd.coefficient_quadratures_fst
#print axioms CarryNativeTfvd.coefficient_quadratures_snd
#print axioms CarryNativeTfvd.coefficient_tower_synthesis
#print axioms CarryNativeTfvd.coefficient_real_bracket
#print axioms CarryNativeTfvd.coefficient_imag_bracket
#print axioms CarryNativeTfvd.physical_finite_reconstruction
#print axioms CarryNativeTfvd.coefficientWeight
#print axioms CarryNativeTfvd.coefficient_weight_apply
#print axioms CarryNativeTfvd.completionCommutator
#print axioms CarryNativeTfvd.completion_commutator_zero
#print axioms CarryNativeTfvd.completion_commutator_succ
#print axioms CarryNativeTfvd.completion_bulk_split
#print axioms CarryNativeTfvd.completion_commutator_constant
#print axioms CarryNativeTfvd.completion_commutator_product
#print axioms CarryNativeTfvd.completion_commutator_vanishes_iff
#print axioms CarryNativeTfvd.weighted_physical_reconstruction
#print axioms CarryNativeTfvd.weighted_source_sum
#print axioms CarryNativeTfvd.incidentWeight
#print axioms CarryNativeTfvd.returnedWeight
#print axioms CarryNativeTfvd.completed_source_weighted_identity
#print axioms CarryNativeTfvd.completedSourceParts
#print axioms CarryNativeTfvd.completed_source_three_parts
#print axioms CarryNativeTfvd.completed_source_nine_pairings

#audit_native_tfvd
  CarryNativeTfvd.vertical_shift_basis
  CarryNativeTfvd.native_synthesis_shift
  CarryNativeTfvd.vertical_shift_backward_trace
  CarryNativeTfvd.native_backward_numerator
  CarryNativeTfvd.vertical_numerator_two_traces
  CarryNativeTfvd.synthesized_tfvd
  CarryNativeTfvd.physical_numerator_two_traces
  CarryNativeTfvd.physical_resolvent_commutes_advance
  CarryNativeTfvd.physical_resolvent_solve
  CarryNativeTfvd.physical_tfvd_reconstruction
  CarryNativeTfvd.physical_boundary_return
  CarryNativeTfvd.physical_green_on_bracket
  CarryNativeTfvd.coefficientQuadratures
  CarryNativeTfvd.coefficient_quadratures_fst
  CarryNativeTfvd.coefficient_quadratures_snd
  CarryNativeTfvd.coefficient_tower_synthesis
  CarryNativeTfvd.coefficient_real_bracket
  CarryNativeTfvd.coefficient_imag_bracket
  CarryNativeTfvd.physical_finite_reconstruction
  CarryNativeTfvd.coefficientWeight
  CarryNativeTfvd.coefficient_weight_apply
  CarryNativeTfvd.completionCommutator
  CarryNativeTfvd.completion_commutator_zero
  CarryNativeTfvd.completion_commutator_succ
  CarryNativeTfvd.completion_bulk_split
  CarryNativeTfvd.completion_commutator_constant
  CarryNativeTfvd.completion_commutator_product
  CarryNativeTfvd.completion_commutator_vanishes_iff
  CarryNativeTfvd.weighted_physical_reconstruction
  CarryNativeTfvd.weighted_source_sum
  CarryNativeTfvd.incidentWeight
  CarryNativeTfvd.returnedWeight
  CarryNativeTfvd.completed_source_weighted_identity
  CarryNativeTfvd.completedSourceParts
  CarryNativeTfvd.completed_source_three_parts
  CarryNativeTfvd.completed_source_nine_pairings
