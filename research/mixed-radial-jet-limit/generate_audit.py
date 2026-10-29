#!/usr/bin/env python3
"""Audit construction, moment identification and finite canaries separately."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ['MixedRadialJets','MixedRadialLimits','ZeroJetObstruction','PrimeTowerCanary']
roots = {}
groups = {'source': [], 'identification': [], 'obstruction': [], 'prime_canary': []}
for module in modules:
    roots[module] = []
    for match in re.finditer(r'^(theorem|def|abbrev)\s+([\w.]+)',
                             (root / f'{module}.lean').read_text(), re.M):
        name = match.group(2)
        full = 'CarryMixedRadial.' + name
        roots[module].append(full)
        groups[{'MixedRadialJets':'source','MixedRadialLimits':'identification','ZeroJetObstruction':'obstruction','PrimeTowerCanary':'prime_canary'}[module]].append(full)

header = r'''import ZeroJetObstruction
import PrimeTowerCanary
import Lean

open Lean Elab Command
elab "#audit_completed_pairing " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let signs := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial]
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden downstream sign consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-defined construction: {name}"
      if tier.getNat <= 1 && signs.contains name then
        throwError "Finite sign or theta-moment dependency outside canary: {name}"
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
  logInfo m!"Mixed radial jet audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

'''
body = '\n'.join('#print axioms ' + name for names in roots.values() for name in names)
for tier, group in [(0,'source'),(1,'identification'),(2,'obstruction'),(3,'prime_canary')]:
    body += f'\n\n#audit_completed_pairing {tier}\n  ' + '\n  '.join(groups[group])
body += '\n\n#audit_completed_pairing 4\n  ' + '\n  '.join(
    name for names in roots.values() for name in names)
(root/'Audit.lean').write_text(header + body + '\n')
(root/'public-roots.json').write_text(json.dumps({'modules':roots,'audit_groups':groups},indent=2)+'\n')
print(json.dumps({group:len(names) for group,names in groups.items()}))
