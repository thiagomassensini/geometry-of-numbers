#!/usr/bin/env python3
"""Audit construction, moment identification and finite canaries separately."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent
modules = ['FullCarrierMass', 'NormalizedCrossing', 'NativeGaps']
moment_theorems = {'normalized_normal_tangent_pair', 'normal_component_energy_exact',
                   'normal_component_energy_upper'}
groups = {'source': [], 'moments': [], 'canaries': []}
roots = {}
for module in modules:
    roots[module] = []
    for match in re.finditer(r'^(theorem|def|abbrev|structure)\s+([\w.]+)',
                             (root / f'{module}.lean').read_text(), re.M):
        kind, name = match.groups()
        full = 'CarryFullSource.' + name
        roots[module].append(full)
        group = ('canaries' if module == 'NativeGaps' else
                 'moments' if name in moment_theorems else 'source')
        groups[group].append(full)
        if kind == 'structure':
            for suffix in ['mk', 'jetTransport', 'companionTransport']:
                roots[module].append(full + '.' + suffix)
                groups[group].append(full + '.' + suffix)

header = r'''import NativeGaps
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
  logInfo m!"Full source norm audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

'''
body = '\n'.join('#print axioms ' + name for names in roots.values() for name in names)
for tier, group in enumerate(['source', 'moments', 'canaries']):
    body += f'\n\n#audit_completed_pairing {tier}\n  ' + '\n  '.join(groups[group])
body += '\n\n#audit_completed_pairing 3\n  ' + '\n  '.join(
    name for names in roots.values() for name in names)
(root/'Audit.lean').write_text(header + body + '\n')
(root/'public-roots.json').write_text(json.dumps({'modules':roots,'audit_groups':groups},indent=2)+'\n')
print(json.dumps({group:len(names) for group,names in groups.items()}))
