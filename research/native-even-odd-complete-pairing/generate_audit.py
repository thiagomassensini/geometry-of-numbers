#!/usr/bin/env python3
"""Audit the original-source transport; isolate sign-free spatial dependencies."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["ResponseReality", "MixedPairing", "JointEnergy", "MixedRegression"]
roots = {}
for module in modules:
    roots[module] = ["CarryMixedParity." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import MixedRegression
import Lean

open Lean Elab Command
elab "#audit_mixed_parity " group:ident ids:ident+ : command => do
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
  logInfo m!"Complete even-odd pairing {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments and characteristic forbidden={spatial}"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
spatial_names = ["static_stencil_real", "even_coefficients_real", "odd_coefficients_imaginary",
    "kernel_smul_left", "kernel_smul_right", "kernel_double_sum", "kernel_real_imaginary", "kernel_imaginary_real",
    "signed_mean_contrast", "contrast_mean_scale", "signed_form_add"]
spatial = ["CarryMixedParity."+n for n in spatial_names]
provenance = [n for n in names if n not in spatial]
body += "\n\n#audit_mixed_parity spatial\n  " + "\n  ".join(spatial) + "\n"
body += "\n#audit_mixed_parity provenance\n  " + "\n  ".join(provenance) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules": roots, "groups": {"spatial": spatial, "provenance": provenance}}, indent=2)+"\n")
print(json.dumps({"public_roots": len(names)}))
