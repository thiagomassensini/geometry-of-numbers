#!/usr/bin/env python3
"""Audit the original-source transport; isolate sign-free spatial dependencies."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["MixedSpatialLeading", "MixedRayLeading", "FiniteImaginaryLaw", "ImaginaryRegression"]
roots = {}
for module in modules:
    roots[module] = ["CarryMixedImaginary." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import ImaginaryRegression
import Lean

open Lean Elab Command
elab "#audit_mixed_imaginary " group:ident ids:ident+ : command => do
  let spatial := group.getId == `spatial
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
          (spatial && (name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic ||
            name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment)) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Canonical or downstream sign dependency in spatial proof: {name}"
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
  logInfo m!"All-order mixed imaginary law {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
spatial = roots["MixedSpatialLeading"] + ["CarryMixedImaginary.mixed_weights_low_order", "CarryMixedImaginary.mixed_weight_ne_zero", "CarryMixedImaginary.not_all_mixed_weights_nonnegative"]
provenance = [n for n in names if n not in spatial]
body += "\n\n#audit_mixed_imaginary spatial\n  " + "\n  ".join(spatial) + "\n"
body += "\n#audit_mixed_imaginary provenance\n  " + "\n  ".join(provenance) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules": roots, "groups": {"spatial": spatial, "provenance": provenance}}, indent=2)+"\n")
print(json.dumps({"public_roots": len(names)}))
