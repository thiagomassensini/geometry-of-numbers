import GeometryOfNumbers.Analysis.CriticalBranchComplementTransport
import Lean
open Lean Elab Command
elab "#audit_critical_branch " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    let deps ← collectAxioms decl
    for name in deps do
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
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Critical branch roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_apply
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_pairing
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy_pos_iff
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_synthesis_pairing
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy_nonneg
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_isometric_transport
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_isometric_pairing
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.realParseval
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.c2_clock_compression_energy
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.c2_clock_complement_parseval_pairing
#print axioms GeometryOfNumbers.Analysis.CriticalBranchComplement.rawGreen_complement_pairing
#print axioms GeometryOfNumbers.Analysis.realCriticalBranch_adjoint_comp_self
#print axioms GeometryOfNumbers.Analysis.globalC2_provenance_roundtrip
#print axioms GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry_pointwise
#print axioms GeometryOfNumbers.Analysis.C2GlobalGreenBridge.c2GlobalRestrictedGreenGram_source_factors
#print axioms GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy.canonicalRawGreenAnalysis_not_isometry
#print axioms GeometryOfNumbers.Analysis.GreenStateMaterialLog.c2Source_log_domain_iff
#print axioms GeometryOfNumbers.Analysis.GreenParsevalMaterialLog.greenParsevalMaterialLogOperator_c2Source_intertwining

#audit_critical_branch
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_apply
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_pairing
  GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy
  GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy_pos_iff
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_synthesis_pairing
  GeometryOfNumbers.Analysis.CriticalBranchComplement.compression_energy_nonneg
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_isometric_transport
  GeometryOfNumbers.Analysis.CriticalBranchComplement.complement_isometric_pairing
  GeometryOfNumbers.Analysis.CriticalBranchComplement.realParseval
  GeometryOfNumbers.Analysis.CriticalBranchComplement.c2_clock_compression_energy
  GeometryOfNumbers.Analysis.CriticalBranchComplement.c2_clock_complement_parseval_pairing
  GeometryOfNumbers.Analysis.CriticalBranchComplement.rawGreen_complement_pairing
  GeometryOfNumbers.Analysis.realCriticalBranch_adjoint_comp_self
  GeometryOfNumbers.Analysis.globalC2_provenance_roundtrip
  GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry_pointwise
  GeometryOfNumbers.Analysis.C2GlobalGreenBridge.c2GlobalRestrictedGreenGram_source_factors
  GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy.canonicalRawGreenAnalysis_not_isometry
  GeometryOfNumbers.Analysis.GreenStateMaterialLog.c2Source_log_domain_iff
  GeometryOfNumbers.Analysis.GreenParsevalMaterialLog.greenParsevalMaterialLogOperator_c2Source_intertwining
