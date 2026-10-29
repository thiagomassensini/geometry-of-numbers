#!/usr/bin/env python3
"""Enumerate public roots and audit every transitive declaration type/body."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["ShiftTransport", "PhysicalTfvd", "CoefficientPorts", "CompletionCommutator", "CompletedSourceBridge"]
roots = {}
for module in modules:
    roots[module] = ["CarryNativeTfvd." + m.group(2) for m in re.finditer(
        r"^(theorem|def|abbrev)\s+([\w.]+)", (root / f"{module}.lean").read_text(), re.M)]

header = r'''import CompletedSourceBridge
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

'''
names = [name for group in roots.values() for name in group]
body = "\n".join("#print axioms " + name for name in names)
body += "\n\n#audit_native_tfvd\n  " + "\n  ".join(names) + "\n"
(root / "Audit.lean").write_text(header + body)
(root / "public-roots.json").write_text(json.dumps(roots, indent=2) + "\n")
print(f"Generated audit for {len(names)} public roots.")
