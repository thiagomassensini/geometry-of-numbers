import VerticalControl
import GeometryOfNumbers.Analysis.C2GlobalGreenBridge
import CarrySelfAdjointOperator.NativeSourceThetaMomentPolynomials
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
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
    `CarrySelfAdjointOperator.nativeSourceFiveEvenDiscriminant_pos,
    `CarrySelfAdjointOperator.nativeSourceFiveEvenBoundaryEnergy_pos,
    `CarryCriticalMixed.source_nonlinear_margin_pos,
    `CarryCriticalMixed.source_correction_numerator_pos]
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
  logInfo m!"Physical Mellin domain audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryMellinDomain.boundaryCoefficients
#print axioms CarryMellinDomain.boundaryContinuous
#print axioms CarryMellinDomain.concentratingCoefficients
#print axioms CarryMellinDomain.concentratingContinuous
#print axioms CarryMellinDomain.physicalConcentration
#print axioms CarryMellinDomain.boundary_trace_zero
#print axioms CarryMellinDomain.concentrating_trace_zero
#print axioms CarryMellinDomain.boundary_tail_polynomial
#print axioms CarryMellinDomain.boundary_source_original
#print axioms CarryMellinDomain.concentrating_source_original
#print axioms CarryMellinDomain.physical_concentration_original
#print axioms CarryMellinDomain.concentrating_tail_polynomial
#print axioms CarryMellinDomain.cubic_one_sub_integral
#print axioms CarryMellinDomain.one_sub_integral
#print axioms CarryMellinDomain.physical_concentration_energy_integral
#print axioms CarryMellinDomain.physical_concentration_norm_sq
#print axioms CarryMellinDomain.physical_concentration_norm_sq_le
#print axioms CarryMellinDomain.concentrationReadout
#print axioms CarryMellinDomain.concentration_readout_native
#print axioms CarryMellinDomain.concentration_readout_formula
#print axioms CarryMellinDomain.physical_concentration_tendsto_zero
#print axioms CarryMellinDomain.concentration_readout_tendsto_one
#print axioms CarryMellinDomain.finiteZeroTraceGraph
#print axioms CarryMellinDomain.concentration_mem_graph
#print axioms CarryMellinDomain.zero_mem_finite_graph
#print axioms CarryMellinDomain.zero_one_mem_graph_closure
#print axioms CarryMellinDomain.closure_not_single_valued
#print axioms CarryMellinDomain.mellin_readout_no_norm_bound
#print axioms CarryMellinDomain.no_continuous_mellin_extension
#print axioms CarryMellinDomain.no_closed_mellin_extension
#print axioms CarryMellinDomain.no_continuous_mellin_extension_with_trace
#print axioms CarryMellinDomain.no_closed_mellin_extension_with_trace
#print axioms CarryMellinDomain.verticalReadout
#print axioms CarryMellinDomain.vertical_readout_finite_source
#print axioms CarryMellinDomain.vertical_readout_norm_bound
#print axioms CarryMellinDomain.finite_tower_coordinate
#print axioms CarryMellinDomain.concentrating_vertical_coordinate
#print axioms CarryMellinDomain.concentrating_vertical_norm_ge
#print axioms CarryMellinDomain.no_continuous_vertical_recovery

#audit_completed_pairing 0
  CarryMellinDomain.boundaryCoefficients
  CarryMellinDomain.boundaryContinuous
  CarryMellinDomain.concentratingCoefficients
  CarryMellinDomain.concentratingContinuous
  CarryMellinDomain.physicalConcentration
  CarryMellinDomain.boundary_trace_zero
  CarryMellinDomain.concentrating_trace_zero
  CarryMellinDomain.boundary_tail_polynomial
  CarryMellinDomain.boundary_source_original
  CarryMellinDomain.concentrating_source_original
  CarryMellinDomain.physical_concentration_original
  CarryMellinDomain.concentrating_tail_polynomial
  CarryMellinDomain.cubic_one_sub_integral
  CarryMellinDomain.one_sub_integral
  CarryMellinDomain.physical_concentration_energy_integral
  CarryMellinDomain.physical_concentration_norm_sq
  CarryMellinDomain.physical_concentration_norm_sq_le
  CarryMellinDomain.concentrationReadout
  CarryMellinDomain.concentration_readout_native
  CarryMellinDomain.concentration_readout_formula
  CarryMellinDomain.physical_concentration_tendsto_zero
  CarryMellinDomain.concentration_readout_tendsto_one
  CarryMellinDomain.finiteZeroTraceGraph
  CarryMellinDomain.concentration_mem_graph
  CarryMellinDomain.zero_mem_finite_graph
  CarryMellinDomain.zero_one_mem_graph_closure
  CarryMellinDomain.closure_not_single_valued
  CarryMellinDomain.mellin_readout_no_norm_bound
  CarryMellinDomain.no_continuous_mellin_extension
  CarryMellinDomain.no_closed_mellin_extension
  CarryMellinDomain.no_continuous_mellin_extension_with_trace
  CarryMellinDomain.no_closed_mellin_extension_with_trace
  CarryMellinDomain.verticalReadout
  CarryMellinDomain.vertical_readout_finite_source
  CarryMellinDomain.vertical_readout_norm_bound
  CarryMellinDomain.finite_tower_coordinate
  CarryMellinDomain.concentrating_vertical_coordinate
  CarryMellinDomain.concentrating_vertical_norm_ge
  CarryMellinDomain.no_continuous_vertical_recovery
#print axioms GeometryOfNumbers.Analysis.realCriticalBranchIsometry
#print axioms GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry_norm
#print axioms GeometryOfNumbers.Analysis.C2GlobalGreenBridge.c2GlobalGreenInput_norm
#print axioms CarrySelfAdjointOperator.nativeThetaMomentPolynomial_integral
