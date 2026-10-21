#!/usr/bin/env python3
import json
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent
modules = ["TraceFiber", "NativeCompletion", "ReadoutTransport"]
names = []
for module in modules:
    source = (root / f"{module}.lean").read_text()
    names += ["CarryTraceFiber." + m.group(1) for m in
              re.finditer(r"^(?:theorem|def|abbrev)\s+(\w+)", source, re.M)]
header = """import ReadoutTransport
import Lean

open Lean Elab Command
elab "#audit_physical_trace " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef]
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
      if forbidden.contains name then
        throwError "Unexpected finite sign dependency: {name}"
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
  logInfo m!"Physical trace audit roots: {ids.size}; type/body closure: {seen.size}; foundations and named sign guards passed"

"""
body = "\n".join("#print axioms " + name for name in names)
body += "\n\n#audit_physical_trace\n  " + "\n  ".join(names) + "\n"
(root / "Audit.lean").write_text(header + body)
(root / "public-roots.json").write_text(json.dumps(names, indent=2) + "\n")
print(f"{len(names)} public declarations")
