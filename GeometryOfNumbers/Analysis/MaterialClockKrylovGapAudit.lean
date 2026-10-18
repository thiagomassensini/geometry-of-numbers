import GeometryOfNumbers.Analysis.MaterialClockKrylovGap
import Lean
open Lean Elab Command
elab "#audit_material_krylov " ids:ident+ : command => do
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
  logInfo m!"Material Krylov roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.material_frequency_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_clock_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_even_first_column_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_normalized_jet_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_isometric_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.green_clock_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.parseval_clock_energy_gap
#print axioms GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_not_matching_two_diagonals

#audit_material_krylov
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.material_frequency_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_clock_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_even_first_column_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.finite_normalized_jet_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_isometric_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.green_clock_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.parseval_clock_energy_gap
  GeometryOfNumbers.Analysis.MaterialClockKrylovGap.infinite_clock_not_matching_two_diagonals
