#!/usr/bin/env python3
"""Audit every new public declaration, including the complete type/body closure."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ["PolarizedGreen", "PolynomialInformation", "ThetaCrossObstruction",
           "ProductResidual", "IntegratedNormTest"]
roots = {
    module: ["CarryThetaPolarized." + match.group(1) for match in re.finditer(
        r"^(?:theorem|def|abbrev)\s+([\w.]+)", (root / f"{module}.lean").read_text(), re.M)]
    for module in modules
}
header = r'''import IntegratedNormTest
import Lean

open Lean Elab Command
elab "#audit_theta_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
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
        throwError "Forbidden canonical-sign consumer: {name}"
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
  logInfo m!"Theta transport audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical-sign consumers absent"

'''
body = "\n".join("#print axioms " + name for names in roots.values() for name in names)
body += "\n\n#audit_theta_transport\n  "
body += "\n  ".join(name for names in roots.values() for name in names)
(root / "Audit.lean").write_text(header + body + "\n")
(root / "public-roots.json").write_text(json.dumps(roots, indent=2) + "\n")
print(json.dumps({module: len(names) for module, names in roots.items()}))
