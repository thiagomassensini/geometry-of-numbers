#!/usr/bin/env python3
"""Audit the original-source transport; audit vector provenance, sign-free extraction and independent recomposition."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["FiniteReturnDomain", "TailReturnGraph", "PolarizedReturnDefect", "FourSourceBridge"]
roots = {}
for module in modules:
    roots[module] = ["CarryTailReturn." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import FourSourceBridge
import Lean

open Lean Elab Command
elab "#audit_odd_green " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let signRoots := #[
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos]
  let forbidden := #[
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
          (construction && (signRoots.contains name || name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
          name.toString.startsWith "CarryCriticalGrid." ||
          name == `CarryAddressSplit.principal_physical_grid ||
          name == `CarryAddressSplit.principal_physical_tendsto)) ||
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
    for name in #[`CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
        `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
        `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one] do
      unless seen.contains name do
        throwError "Missing expected four-source proof dependency (check theorem-body traversal): {name}"
  logInfo m!"Actual finite sign roots used: {signRoots.filter seen.contains}"
  logInfo m!"Native tail return graph {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; finite source-sign roots excluded from construction; scalar-asymptotic shortcuts forbidden"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
finite_control = [name for name in names if name.rsplit(".",1)[-1] in {
    "four_original_physical_positive", "four_original_port_gram",
    "principal_four_port_gram", "principal_four_eventually_positive"}]
construction = [n for n in names if n not in finite_control]
for group,entries in [("construction",construction),("finite_control",finite_control)]:
    body += "\n\n#audit_odd_green " + group + "\n  " + "\n  ".join(entries) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules":roots,"groups":{"construction":construction,"finite_control":finite_control}},indent=2)+"\n")
print(json.dumps({"public_roots":len(names)}))
