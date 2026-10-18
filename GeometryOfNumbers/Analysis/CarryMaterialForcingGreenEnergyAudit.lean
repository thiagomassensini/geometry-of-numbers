import GeometryOfNumbers.Analysis.CarryMaterialForcingGreenEnergy
import Lean
open Lean Elab Command
elab "#audit_completed_green_balance " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected foundational dependency: {decl} depends on {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
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
  logInfo m!"Completed Green roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingVector
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreenKernel
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingRemainderGreen
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingVector_origin_ne_zero
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_factor
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_regular
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_diagonal
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_bilinear
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_energy
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_energy_nonpos
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_origin_neg
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_rank_one
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_cross
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingRemainder_ledger
#print axioms GeometryOfNumbers.Analysis.carryMaterialForcingGreen_continuous

#audit_completed_green_balance
  GeometryOfNumbers.Analysis.carryMaterialForcingVector
  GeometryOfNumbers.Analysis.carryMaterialForcingGreenKernel
  GeometryOfNumbers.Analysis.carryMaterialForcingRemainderGreen
  GeometryOfNumbers.Analysis.carryMaterialForcingVector_origin_ne_zero
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_factor
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_regular
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_diagonal
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_bilinear
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_energy
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_energy_nonpos
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_origin_neg
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_rank_one
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_cross
  GeometryOfNumbers.Analysis.carryMaterialForcingRemainder_ledger
  GeometryOfNumbers.Analysis.carryMaterialForcingGreen_continuous
