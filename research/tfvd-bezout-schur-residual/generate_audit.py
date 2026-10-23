#!/usr/bin/env python3
"""Enumerate and audit every new public declaration and its type/body closure."""
from pathlib import Path
import json
import re
root = Path(__file__).resolve().parent
modules = ["SourceBezout", "SourceMap", "SourceNative", "SourceBlocks", "SchurTransport",
           "SourceSchur", "LiteralNativeTrace", "LiteralTfvd", "KernelBudget",
           "LiteralTailBounds", "LiteralBudgetLimit", "LiteralCompanion", "CompanionJets", "Repartition",
           "TwoEvenSourceMargin", "NativeRepartition64"]
roots = {}
for module in modules:
    namespace = "CarrySourceBezout.NativeTrace." if module == "LiteralNativeTrace" else "CarrySourceBezout."
    roots[module] = [namespace + m.group(1) for m in re.finditer(
        r"^(?:theorem|def|abbrev|instance)\s+([\w.]+)", (root / (module + ".lean")).read_text(), re.M)]
header = r'''import Regression
import Lean

open Lean Elab Command
elab "#audit_source_transport " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg,
    `CarryC3Boxes.canonical_two_even_determinant_pos_from_c3,
    `CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes]
  let forbidden := if mode.getId == `NativeRepartition64 then forbidden ++ #[
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third,
    `CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    `CarrySelfAdjointOperator.completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    `CarrySelfAdjointOperator.completedNativeThetaTailMoment_zero_le_calibration]
    else forbidden
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
        throwError "Circular/later sign dependency: {name}"
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
        throwError "Missing dependency in imported environment: {name}"
  let extra := if mode.getId == `NativeRepartition64 then "; C3 split excludes theta calibration" else ""
  logInfo m!"Source residual audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; standard axioms only; forbidden sign dependencies absent{extra}"

'''
body = "\n".join("#print axioms " + name for names in roots.values() for name in names)
for module, names in roots.items():
    body += "\n\n#audit_source_transport " + module + "\n  " + "\n  ".join(names)
(root / "Audit.lean").write_text(header + body + "\n")
(root / "public-roots.json").write_text(json.dumps(roots, indent=2) + "\n")
print({module: len(names) for module, names in roots.items()})
