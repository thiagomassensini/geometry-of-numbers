#!/usr/bin/env python3
"""Enumerate every public declaration in the new research modules."""
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent
modules = ["AnalyticExtraction", "RawGreenRay", "RadialPairing", "PairCorrection", "FiniteCorrection", "CriticalCorrection", "Regression"]
names = []
for module in modules:
    source = (root / f"{module}.lean").read_text()
    for match in re.finditer(r"^(?:@\[[^\n]*\]\s+)?(?:theorem|def|abbrev)\s+(\w+)", source, re.M):
        names.append("CarryAllOrderCorrection." + match.group(1))
inherited = [
    "CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical",
    "CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope",
    "NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit",
]

header = '''import Regression
import Lean

open Lean Elab Command
elab "#audit_all_order_correction " ids:ident+ : command => do
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
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.projectiveChiralDifferenceJet_pairing_tendsto_coefficient,
    `CarrySelfAdjointOperator.nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto,
    `CarryCriticalRelative.critical_balance_tendsto_of_isUnit,
    `CarryCriticalMixed.second_balance_correction_tendsto,
    `CarryCriticalMixed.second_critical_correction_tendsto,
    `CarrySourceLaw.odd_balance_correction_tendsto,
    `CarrySourceLaw.odd_critical_correction_tendsto]
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
  logInfo m!"All-order correction audit roots: {ids.size}; type/body closure: {seen.size}; foundational and finite-positivity guards passed"

'''
all_names = names + inherited
audit = header + "\n".join("#print axioms " + name for name in all_names)
audit += "\n\n#audit_all_order_correction\n  " + "\n  ".join(all_names) + "\n"
(root / "Audit.lean").write_text(audit)
(root / "public-roots.txt").write_text("\n".join(names) + "\n")
print(f"{len(names)} new declarations; {len(inherited)} inherited source declarations")

extra = r"""
elab "#audit_generic_no_sign " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarryCriticalMixed.source_nonlinear_margin_pos,
    `CarryCriticalMixed.source_correction_numerator_pos,
    `CarrySourceLaw.source_h1_pos,
    `CarrySourceLaw.source_odd_correction_pos,
    `CarrySourceLaw.source_odd_pivot_margin_pos,
    `CarryAllOrderCorrection.source_h2_positive]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name then
        throwError "Generic rate consumes finite source sign: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
  logInfo m!"Generic rate sign audit roots: {ids.size}; type/body closure: {seen.size}; no listed finite source sign input"

#audit_generic_no_sign
  CarryAllOrderCorrection.rawGreenRay_odd
  CarryAllOrderCorrection.projective_pairing_second_correction
  CarryAllOrderCorrection.finite_polarized_second_correction
  CarryAllOrderCorrection.finite_balance_second_correction
  CarryAllOrderCorrection.critical_second_correction
  CarryAllOrderCorrection.critical_nonlinear_second_correction
"""
(root / "Audit.lean").write_text(audit + extra)
