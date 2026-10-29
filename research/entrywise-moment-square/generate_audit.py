#!/usr/bin/env python3
"""Audit public definitions/theorems, including transitive types and bodies."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parent
groups = {}
for module in ['EntrywiseSquare', 'NativeWitness']:
    groups[module] = ['CarryEntrywiseSquare.'+m.group(1) for m in
                      re.finditer(r'^(?:def|theorem)\s+(\w+)',
                                  (root/f'{module}.lean').read_text(), re.M)]
header = '''import EntrywiseSquare
import NativeWitness
import Lean

open Lean Elab Command
elab "#audit_entrywise " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
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
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"Entrywise-square audit {mode.getId}: roots {ids.size}; closure {seen.size}; allowed foundations passed"

'''
body = '\n'.join('#print axioms '+name for names in groups.values() for name in names)
for group, names in groups.items():
    body += '\n\n#audit_entrywise '+group+'\n  '+'\n  '.join(names)
(root/'Audit.lean').write_text(header+body+'\n')
(root/'public-roots.json').write_text(json.dumps(groups, indent=2)+'\n')
print({group: len(names) for group,names in groups.items()})
