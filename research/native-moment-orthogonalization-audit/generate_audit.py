#!/usr/bin/env python3
"""Enumerate every public declaration in the new research modules."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent
modules = ["MomentFunctional", "PolynomialCoordinates", "JacobiLogic", "Controls", "NativeApplication", "SchurLogic"]
names = []
for module in modules:
    source = (root / f"{module}.lean").read_text()
    for match in re.finditer(r"^(?:@\[[^\n]*\]\s+)?(?:theorem|def)\s+(\w+)", source, re.M):
        names.append("NativeMomentOrthogonalization." + match.group(1))
inherited = [
    "CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes",
    "CarrySelfAdjointOperator.nativeThetaCofactorSign_iff_stieltjes",
    "CarrySelfAdjointOperator.canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity",
    "CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate",
]
header = '''import SchurLogic
import PolynomialCoordinates
import NativeApplication
import Controls
import CarrySelfAdjointOperator.NativeThetaCofactorSignGate
import CarrySelfAdjointOperator.CompletedNativeChiralHankelDominance
import CarrySelfAdjointOperator.CompletedNativeDslopeSamplePositivity
import Lean

open Lean Elab Command
elab "#audit_native_orthogonalization " ids:ident+ : command => do
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
  logInfo m!"Native moment audit roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

'''
all_names = names + inherited
audit = header + "\n".join("#print axioms " + name for name in all_names)
audit += "\n\n#audit_native_orthogonalization\n  " + "\n  ".join(all_names) + "\n"
(root / "Audit.lean").write_text(audit)
(root / "public-roots.txt").write_text("\n".join(names) + "\n")
print(f"{len(names)} new declarations; {len(inherited)} inherited equivalences")
