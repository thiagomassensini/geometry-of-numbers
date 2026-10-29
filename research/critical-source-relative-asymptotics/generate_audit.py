#!/usr/bin/env python3
"""Enumerate every public declaration in the new research modules."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent
modules = ["SourceLeading", "WholeSourceLimit", "CriticalRelative", "RelativeDeficit", "InitialSource", "PolarizedLimit"]
names = []
for module in modules:
    source = (root / f"{module}.lean").read_text()
    for match in re.finditer(r"^(?:@\[[^\n]*\]\s+)?(?:theorem|def|abbrev)\s+(\w+)", source, re.M):
        names.append("CarryCriticalRelative." + match.group(1))
inherited = [
    "NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit",
    "CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource",
    "CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos",
]
header = '''import InitialSource
import PolarizedLimit
import Lean

open Lean Elab Command
elab "#audit_critical_relative " ids:ident+ : command => do
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
  logInfo m!"Critical source relative audit roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

'''
all_names = names + inherited
audit = header + "\n".join("#print axioms " + name for name in all_names)
audit += "\n\n#audit_critical_relative\n  " + "\n  ".join(all_names) + "\n"
(root / "Audit.lean").write_text(audit)
(root / "public-roots.txt").write_text("\n".join(names) + "\n")
print(f"{len(names)} new declarations; {len(inherited)} inherited source declarations")
