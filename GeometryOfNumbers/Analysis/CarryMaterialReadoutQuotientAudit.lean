import GeometryOfNumbers.Analysis.CarryMaterialReadoutQuotient
import Lean

open Lean Elab Command
elab "#audit_quotient_roots " ids:ident+ : command => do
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
  logInfo m!"Quotient roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_readout
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_complement
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_norm_decomposition
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_minimum
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_norm
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_minimum_eq_iff
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_unique_minimum
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_complete_injective
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_finite_energy
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_cells
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_boundary_defect
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_mem_domain_iff
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_cells
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_boundary_defect
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_mem_domain_iff
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_physical_strict
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadout_source_projection_not_physical
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_not_isometric_domain

#audit_quotient_roots
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_readout
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_complement
  GeometryOfNumbers.Analysis.carryMaterialReadout_norm_decomposition
  GeometryOfNumbers.Analysis.carryMaterialReadout_minimum
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_norm
  GeometryOfNumbers.Analysis.carryMaterialReadout_minimum_eq_iff
  GeometryOfNumbers.Analysis.carryMaterialReadout_unique_minimum
  GeometryOfNumbers.Analysis.carryMaterialReadout_complete_injective
  GeometryOfNumbers.Analysis.carryMaterialReadout_finite_energy
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_cells
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_boundary_defect
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_mem_domain_iff
  GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_cells
  GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_boundary_defect
  GeometryOfNumbers.Analysis.carryMaterialReadoutComplement_mem_domain_iff
  GeometryOfNumbers.Analysis.carryMaterialReadout_physical_strict
  GeometryOfNumbers.Analysis.carryMaterialReadout_source_projection_not_physical
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_not_isometric_domain
