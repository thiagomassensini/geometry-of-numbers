#!/usr/bin/env python3
"""Audit the spatial factorization separately from canonical asymptotics and the h0 sign."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["ComplementNorm", "CurvatureKernel", "NativeCoefficient", "FourthBoundaryDefect", "CriticalSectorSign"]
roots = {}
groups = {"source": [], "identification": [], "finite_sign": []}
for module in modules:
    roots[module] = []
    for m in re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M):
        full = "CarryCurvatureGreen." + m.group(2)
        roots[module].append(full)
        group = "source" if module != "CriticalSectorSign" else "identification"
        if m.group(2) in ["leading_coefficient_pos", "leading_coefficient_lower_bound", "mixed_eventually_positive", "bulk_boundary_eventually_negative"]:
            group = "finite_sign"
        groups[group].append(full)

header = r'''import FourthBoundaryDefect
import CriticalSectorSign
import Lean

open Lean Elab Command
elab "#audit_curvature_green " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let finiteSigns := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
      if name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." ||
          name == `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier then
        throwError "Forbidden downstream positivity consumer: {name}"
      if tier.getNat == 0 && (name == moments || name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic) then
        throwError "Moment-dependent physical construction: {name}"
      if tier.getNat <= 1 && finiteSigns.contains name then
        throwError "Finite moment sign outside explicit seed test: {name}"
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
  logInfo m!"Curvature Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

'''
body = "\n".join("#print axioms " + name for names in roots.values() for name in names)
for tier, group in enumerate(["source", "identification", "finite_sign"]):
    body += f"\n\n#audit_curvature_green {tier}\n  " + "\n  ".join(groups[group]) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules": roots, "groups": groups}, indent=2)+"\n")
print(json.dumps({g: len(names) for g,names in groups.items()}))
