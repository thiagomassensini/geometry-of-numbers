#!/usr/bin/env python3
"""Audit the original-source transport; audit vector provenance, sign-free extraction and independent recomposition."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["CriticalBoundaryTransport", "FourSourcePathLimit", "DefectUniformControl", "CriticalCompleteMargin"]
roots = {}
for module in modules:
    roots[module] = ["CarryCriticalComplete." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import CriticalCompleteMargin
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
    `CarryBoundaryMargin.principal_uniform_physical_margin,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_boundary_coercive,
    `CarrySelfAdjointOperator.radialFourRegularizedStorage_eventually_unit_margin,
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos]
  let forbidden := #[
    `CarryAddressSplit.defect_physical_tendsto_zero,
    `CarryAddressSplit.defect_physical_scaled_tendsto,
    `CarryTailReturn.principal_four_eventually_positive,
    `CarryTailReturn.four_original_physical_positive,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarryCubicOdd.critical_cauchy_row,
    `CarryCubicOdd.critical_readout_four_samples,
    `CarryCubicOdd.critical_rho_alternating,
    `CarryCubicOdd.critical_diagonal_four_samples_exact,
    `CarryOddEnergy.finite_odd_source_pairing,
    `CarryOddEnergy.finite_odd_energy_pairing,
    `CarryOddEnergy.finite_odd_energy_correction_tendsto,
    `CarryOddEnergy.finite_odd_green_correction_tendsto,
    `CarryCrossRadial.first_cross_exact,
    `CarryCrossRadial.doubled_first_exact,
    `CarryCrossRadial.doubled_scaled_tendsto,
    `CarryCrossRadial.doubled_scaled_expansion,
    `CarryCrossRadial.doubled_unscaled_expansion,
    `CarryCrossRadial.doubled_next_tendsto,
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
      if forbidden.contains name ||
          (construction && signRoots.contains name) ||
          (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name.toString.startsWith "CarryCriticalGrid." ||
          name == `CarryAddressSplit.principal_physical_grid ||
          name == `CarryAddressSplit.principal_physical_tendsto) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden canonical/sign dependency: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  unless construction do
    for name in #[`CarryBoundaryMargin.principal_uniform_physical_margin,
        `CarrySelfAdjointOperator.storage_one_fourSample_eventually_boundary_coercive,
        `CarrySelfAdjointOperator.radialFourRegularizedStorage_eventually_unit_margin] do
      unless seen.contains name do
        throwError "Missing expected native coercivity dependency (check theorem-body traversal): {name}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native critical complete margin {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden=true; finite source-sign roots excluded from construction; scalar-asymptotic shortcuts forbidden"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
finite_margin = [name for name in names if name.rsplit(".",1)[-1] == "critical_uniform_physical_margin"]
construction = [n for n in names if n not in finite_margin]
for group,entries in [("construction",construction),("finite_margin",finite_margin)]:
    body += "\n\n#audit_odd_green " + group + "\n  " + "\n  ".join(entries) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules":roots,"groups":{"construction":construction,"finite_margin":finite_margin}},indent=2)+"\n")
print(json.dumps({"public_roots":len(names)}))
