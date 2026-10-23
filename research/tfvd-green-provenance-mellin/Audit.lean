import CutoffResidual
import Lean

open Lean Elab Command
elab "#audit_theta_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
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
        throwError "Forbidden moment-derived or sign consumer: {name}"
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
  logInfo m!"TFVD Green provenance Mellin audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; moment-derived constructions and sign consumers absent"

#print axioms CarryGreenProvenance.materialGreenPort
#print axioms CarryGreenProvenance.material_green_port_eq
#print axioms CarryGreenProvenance.reflected_re_pos
#print axioms CarryGreenProvenance.mixed_direct_green_port
#print axioms CarryGreenProvenance.reflected_green_port
#print axioms CarryGreenProvenance.direct_port_mellin
#print axioms CarryGreenProvenance.reflected_port_mellin
#print axioms CarryGreenProvenance.green_edge_mellin
#print axioms CarryGreenProvenance.green_form_mellin
#print axioms CarryGreenProvenance.heatCellProvenance
#print axioms CarryGreenProvenance.heatBlockProvenance
#print axioms CarryGreenProvenance.originalBlockProvenance
#print axioms CarryGreenProvenance.heat_cell_address_calibration
#print axioms CarryGreenProvenance.block_provenance_mellin
#print axioms CarryGreenProvenance.visible_legs_mellin
#print axioms CarryGreenProvenance.dormant_legs_mellin
#print axioms CarryGreenProvenance.dormant_compensation_mellin
#print axioms CarryGreenProvenance.heatGreenProvenance
#print axioms CarryGreenProvenance.heat_green_eq_original_ledger
#print axioms CarryGreenProvenance.heatLedger
#print axioms CarryGreenProvenance.full_ledger_mellin
#print axioms CarryGreenProvenance.native_wronskian_full_mellin
#print axioms CarryGreenProvenance.material_port_coordinates
#print axioms CarryGreenProvenance.green_edge_radial
#print axioms CarryGreenProvenance.dormant_compensation_radial
#print axioms CarryGreenProvenance.critical_port_legs_equal
#print axioms CarryGreenProvenance.critical_green_edge_zero
#print axioms CarryGreenProvenance.critical_green_form_zero
#print axioms CarryGreenProvenance.critical_dormant_compensation_zero
#print axioms CarryGreenProvenance.critical_wronskian_in_ledger
#print axioms CarryGreenProvenance.heatLedgerTotal
#print axioms CarryGreenProvenance.heat_ledger_total_eq_native_defect
#print axioms CarryGreenProvenance.heat_ledger_total_tendsto
#print axioms CarryGreenProvenance.heat_completion_tendsto_zero
#print axioms CarryGreenProvenance.critical_ledger_total_eq
#print axioms CarryGreenProvenance.critical_ledger_total_cutoff_independent

#audit_theta_transport
  CarryGreenProvenance.materialGreenPort
  CarryGreenProvenance.material_green_port_eq
  CarryGreenProvenance.reflected_re_pos
  CarryGreenProvenance.mixed_direct_green_port
  CarryGreenProvenance.reflected_green_port
  CarryGreenProvenance.direct_port_mellin
  CarryGreenProvenance.reflected_port_mellin
  CarryGreenProvenance.green_edge_mellin
  CarryGreenProvenance.green_form_mellin
  CarryGreenProvenance.heatCellProvenance
  CarryGreenProvenance.heatBlockProvenance
  CarryGreenProvenance.originalBlockProvenance
  CarryGreenProvenance.heat_cell_address_calibration
  CarryGreenProvenance.block_provenance_mellin
  CarryGreenProvenance.visible_legs_mellin
  CarryGreenProvenance.dormant_legs_mellin
  CarryGreenProvenance.dormant_compensation_mellin
  CarryGreenProvenance.heatGreenProvenance
  CarryGreenProvenance.heat_green_eq_original_ledger
  CarryGreenProvenance.heatLedger
  CarryGreenProvenance.full_ledger_mellin
  CarryGreenProvenance.native_wronskian_full_mellin
  CarryGreenProvenance.material_port_coordinates
  CarryGreenProvenance.green_edge_radial
  CarryGreenProvenance.dormant_compensation_radial
  CarryGreenProvenance.critical_port_legs_equal
  CarryGreenProvenance.critical_green_edge_zero
  CarryGreenProvenance.critical_green_form_zero
  CarryGreenProvenance.critical_dormant_compensation_zero
  CarryGreenProvenance.critical_wronskian_in_ledger
  CarryGreenProvenance.heatLedgerTotal
  CarryGreenProvenance.heat_ledger_total_eq_native_defect
  CarryGreenProvenance.heat_ledger_total_tendsto
  CarryGreenProvenance.heat_completion_tendsto_zero
  CarryGreenProvenance.critical_ledger_total_eq
  CarryGreenProvenance.critical_ledger_total_cutoff_independent
