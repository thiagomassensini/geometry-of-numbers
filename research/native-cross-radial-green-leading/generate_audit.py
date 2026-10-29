#!/usr/bin/env python3
"""Audit the original-source transport; audit vector provenance, sign-free extraction and independent recomposition."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["PartVectors", "RadialPartExpansion", "LeadingCrossings", "GreenRegression"]
roots = {}
for module in modules:
    roots[module] = ["CarryGreenLeading." + m.group(2) for m in
        re.finditer(r"^(theorem|def|abbrev)\s+([\w.]+)", (root/f"{module}.lean").read_text(), re.M)]

header = r'''import GreenRegression
import Lean

open Lean Elab Command
elab "#audit_green_leading " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
  logInfo m!"Vector Green leading coefficient {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting moment-sign and scalar-asymptotic shortcuts forbidden"

'''
names = [name for names in roots.values() for name in names]
body = "\n".join("#print axioms " + name for name in names)
construction = roots["PartVectors"] + ["CarryGreenLeading."+n for n in [
    "constantPart", "linearPart", "native_part_coordinates", "native_part_contrast_mean",
    "part_field_continuous", "normalizedPart", "chiral_difference_square", "native_parts_pair",
    "partCross", "part_cross_exact", "part_cross_scaled_identity", "double_inner_sum",
    "sum_cross_coefficients", "part_cross_sum", "linear_even_residual", "linear_even_residual_ne_zero", "even_vector_compensation"]]
provenance = [n for n in names if n not in construction]
for group,entries in [("construction",construction),("provenance",provenance)]:
    body += "\n\n#audit_green_leading " + group + "\n  " + "\n  ".join(entries) + "\n"
(root/"Audit.lean").write_text(header+body)
(root/"public-roots.json").write_text(json.dumps({"modules": roots, "groups": {"construction":construction, "provenance":provenance}},indent=2)+"\n")
print(json.dumps({"public_roots":len(names)}))
