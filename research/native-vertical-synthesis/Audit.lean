import CompletedTransport
import HeadTail
import Lean

open Lean Elab Command
elab "#audit_vertical_synthesis " ids:ident+ : command => do
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
  logInfo m!"Native vertical synthesis audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moment construction"

#print axioms CarryVerticalSynthesis.cauchy_weight_step
#print axioms CarryVerticalSynthesis.cauchy_weight_row_range
#print axioms CarryVerticalSynthesis.cauchy_weight_row
#print axioms CarryVerticalSynthesis.cauchy_quadratic_bound
#print axioms CarryVerticalSynthesis.finiteTower
#print axioms CarryVerticalSynthesis.finiteSource
#print axioms CarryVerticalSynthesis.finite_tower_apply
#print axioms CarryVerticalSynthesis.finite_tower_norm_sq
#print axioms CarryVerticalSynthesis.finite_source_pairing
#print axioms CarryVerticalSynthesis.finite_source_bound
#print axioms CarryVerticalSynthesis.finite_tower_dense
#print axioms CarryVerticalSynthesis.nativeSynthesis
#print axioms CarryVerticalSynthesis.native_synthesis_finite
#print axioms CarryVerticalSynthesis.native_synthesis_bound
#print axioms CarryVerticalSynthesis.native_synthesis_opNorm
#print axioms CarryVerticalSynthesis.native_synthesis_column
#print axioms CarryVerticalSynthesis.native_synthesis_hasSum
#print axioms CarryVerticalSynthesis.native_synthesis_unique
#print axioms CarryVerticalSynthesis.native_synthesis_mem_original_closure
#print axioms CarryVerticalSynthesis.native_synthesis_inner_im
#print axioms CarryVerticalSynthesis.quadratureSynthesis
#print axioms CarryVerticalSynthesis.quadrature_synthesis_apply
#print axioms CarryVerticalSynthesis.quadrature_synthesis_norm_sq
#print axioms CarryVerticalSynthesis.quadrature_synthesis_bound
#print axioms CarryVerticalSynthesis.quadrature_synthesis_hasSum
#print axioms CarryVerticalSynthesis.quadrature_synthesis_pairing
#print axioms CarryVerticalSynthesis.quadrature_synthesis_J
#print axioms CarryVerticalSynthesis.finiteQuadratures
#print axioms CarryVerticalSynthesis.finite_quadratures_fst
#print axioms CarryVerticalSynthesis.finite_quadratures_snd
#print axioms CarryVerticalSynthesis.quadrature_synthesis_finite
#print axioms CarryVerticalSynthesis.finite_quadrature_synthesis_injective
#print axioms CarryVerticalSynthesis.native_synthesis_difference_bound
#print axioms CarryVerticalSynthesis.native_synthesis_pairing_head_tail
#print axioms CarryVerticalSynthesis.native_synthesis_prefix_tendsto
#print axioms CarryVerticalSynthesis.native_synthesis_prefix_pairing_tendsto
#print axioms CarryVerticalSynthesis.radial_incident_vector
#print axioms CarryVerticalSynthesis.radial_return_vector
#print axioms CarryVerticalSynthesis.completed_native_tower_pairing
#print axioms CarryVerticalSynthesis.native_center_energy
#print axioms CarryVerticalSynthesis.native_synthesis_not_isometry
#print axioms CarryVerticalSynthesis.equal_vertical_norm_negative_synthesized_balance

#audit_vertical_synthesis
  CarryVerticalSynthesis.cauchy_weight_step
  CarryVerticalSynthesis.cauchy_weight_row_range
  CarryVerticalSynthesis.cauchy_weight_row
  CarryVerticalSynthesis.cauchy_quadratic_bound
  CarryVerticalSynthesis.finiteTower
  CarryVerticalSynthesis.finiteSource
  CarryVerticalSynthesis.finite_tower_apply
  CarryVerticalSynthesis.finite_tower_norm_sq
  CarryVerticalSynthesis.finite_source_pairing
  CarryVerticalSynthesis.finite_source_bound
  CarryVerticalSynthesis.finite_tower_dense
  CarryVerticalSynthesis.nativeSynthesis
  CarryVerticalSynthesis.native_synthesis_finite
  CarryVerticalSynthesis.native_synthesis_bound
  CarryVerticalSynthesis.native_synthesis_opNorm
  CarryVerticalSynthesis.native_synthesis_column
  CarryVerticalSynthesis.native_synthesis_hasSum
  CarryVerticalSynthesis.native_synthesis_unique
  CarryVerticalSynthesis.native_synthesis_mem_original_closure
  CarryVerticalSynthesis.native_synthesis_inner_im
  CarryVerticalSynthesis.quadratureSynthesis
  CarryVerticalSynthesis.quadrature_synthesis_apply
  CarryVerticalSynthesis.quadrature_synthesis_norm_sq
  CarryVerticalSynthesis.quadrature_synthesis_bound
  CarryVerticalSynthesis.quadrature_synthesis_hasSum
  CarryVerticalSynthesis.quadrature_synthesis_pairing
  CarryVerticalSynthesis.quadrature_synthesis_J
  CarryVerticalSynthesis.finiteQuadratures
  CarryVerticalSynthesis.finite_quadratures_fst
  CarryVerticalSynthesis.finite_quadratures_snd
  CarryVerticalSynthesis.quadrature_synthesis_finite
  CarryVerticalSynthesis.finite_quadrature_synthesis_injective
  CarryVerticalSynthesis.native_synthesis_difference_bound
  CarryVerticalSynthesis.native_synthesis_pairing_head_tail
  CarryVerticalSynthesis.native_synthesis_prefix_tendsto
  CarryVerticalSynthesis.native_synthesis_prefix_pairing_tendsto
  CarryVerticalSynthesis.radial_incident_vector
  CarryVerticalSynthesis.radial_return_vector
  CarryVerticalSynthesis.completed_native_tower_pairing
  CarryVerticalSynthesis.native_center_energy
  CarryVerticalSynthesis.native_synthesis_not_isometry
  CarryVerticalSynthesis.equal_vertical_norm_negative_synthesized_balance
