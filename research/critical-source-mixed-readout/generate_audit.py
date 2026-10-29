#!/usr/bin/env python3
"""Enumerate every public declaration in the new research modules."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent
modules = ["SourceCoordinates", "MixedCritical", "SecondEvenReadout", "SecondEvenLimit", "IntegralOrientation", "CriticalOrientation", "EulerOrientation"]
names = []
for module in modules:
    source = (root / f"{module}.lean").read_text()
    for match in re.finditer(r"^(?:@\[[^\n]*\]\s+)?(?:theorem|def|abbrev)\s+(\w+)", source, re.M):
        names.append("CarryCriticalMixed." + match.group(1))
inherited = [
    "CarrySelfAdjointOperator.nativeSourceTransverseSlope_exact_remainder",
    "CarrySelfAdjointOperator.ChiralReturn.storage_one_eq_euler_boundary_add_remainder",
    "CarryIntegralCertificate.material_theta_integral_input",
]
header = '''import EulerOrientation
import Lean

open Lean Elab Command
elab "#audit_critical_mixed " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {decl}: {name}"
  let forbidden := #[
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarryCriticalSource.sourceMatrices_through_four_posDef,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then
        throwError "Circular finite-positivity dependency: {name}"
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
  logInfo m!"Critical source mixed audit roots: {ids.size}; type/body closure: {seen.size}; foundational and finite-positivity guards passed"

'''
all_names = names + inherited
audit = header + "\n".join("#print axioms " + name for name in all_names)
audit += "\n\n#audit_critical_mixed\n  " + "\n  ".join(all_names) + "\n"
(root / "Audit.lean").write_text(audit)
(root / "public-roots.txt").write_text("\n".join(names) + "\n")
print(f"{len(names)} new declarations; {len(inherited)} inherited source declarations")
