#!/usr/bin/env python3
"""Audit the original-source transport; isolate sign-free construction and the preexisting h0-sign canary."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["CrossRadialPairing", "CrossRadialGreen", "DoubledMixedExpansion", "RadialRegression"]
roots = {}
for module in modules:
    roots[module] = ["CarryCrossRadial." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import RadialRegression
import Lean

open Lean Elab Command
elab "#audit_cross_radial " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let signCanary := group.getId == `sign_canary
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
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
          (!signCanary && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos) ||
          (construction && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment) ||
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
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing dependency: {name}"
  logInfo m!"Complete cross-radial pairing {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting h0-sign allowed={signCanary}"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
construction = roots["CrossRadialPairing"] + roots["CrossRadialGreen"] + ["CarryCrossRadial."+n for n in [
    "firstCrossPair", "first_cross_exact", "doubled_index_tendsto", "doubled_step", "doubled_cross_scale",
    "doubledFirstPair", "doubled_first_exact", "first_cross_diagonal"]]
sign_canary = ["CarryCrossRadial.doubled_no_finite_limit"]
provenance = [n for n in names if n not in construction + sign_canary]
for group, entries in [("construction",construction),("provenance",provenance),("sign_canary",sign_canary)]:
    body += "\n\n#audit_cross_radial " + group + "\n  " + "\n  ".join(entries) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules": roots, "groups": {"construction": construction, "provenance": provenance, "sign_canary": sign_canary}}, indent=2)+"\n")
print(json.dumps({"public_roots": len(names)}))
