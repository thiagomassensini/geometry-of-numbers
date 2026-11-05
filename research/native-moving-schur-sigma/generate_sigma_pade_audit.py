#!/usr/bin/env python3
"""Generate public-root inventory and the transitive sigma Padé audit."""

from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = [
    "SigmaSignedPencil",
    "SigmaPadeCorrespondence",
    "SigmaTwoPoleModel",
    "SigmaZeroPairDecomposition",
    "SigmaPadeConvergence",
    "SigmaRemainderDescent",
    "SigmaPadeEventualNegativity",
]
roots = [
    ("CarrySigmaObstruction." if module in {
        "SigmaZeroPairDecomposition", "SigmaRemainderDescent",
        "SigmaPadeEventualNegativity"
    }
     else "CarrySigmaPade.") + match.group(1)
    for module in modules
    for match in re.finditer(
        r"^(?:theorem|def)\s+(\w+)",
        (root / f"{module}.lean").read_text(),
        re.M,
    )
]

header = r'''import SigmaPadeConvergence
import SigmaRemainderDescent
import SigmaPadeEventualNegativity
import Lean

open Lean Elab Command

elab "#audit_sigma_pade " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for axiomName in (← collectAxioms decl) do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {decl}: {axiomName}"
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
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing declaration: {name}"
  for required in #[
      `CarryMovingSigma.sigmaMatrix,
      `CarrySigmaSource.completedSigmaLogJet,
      `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic] do
    unless seen.contains required do
      throwError "Missing original-source provenance dependency: {required}"
  logInfo m!"Sigma pencil/Padé audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; original characteristic and sigma jets retained"

'''

body = "\n".join(f"#print axioms {name}" for name in roots)
body += "\n\n#audit_sigma_pade\n  " + "\n  ".join(roots) + "\n"
(root / "SigmaPadeAudit.lean").write_text(header + body)
(root / "sigma_pade_public_roots.json").write_text(
    json.dumps({"sigma_pade": roots}, indent=2) + "\n"
)
print({"sigma_pade": len(roots)})
