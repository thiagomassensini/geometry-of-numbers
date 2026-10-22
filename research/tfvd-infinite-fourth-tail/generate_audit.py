#!/usr/bin/env python3
"""Inventory and audit all public constants, including types and proof bodies."""
from pathlib import Path
import json
import re
root = Path(__file__).resolve().parent
groups = {
    'fourth': ['FourthDifference'],
    'jets': ['RemainderJets'],
    'envelope': ['QuarticEnvelope'],
    'infinite': ['InfiniteOrdinary'],
    'clock': ['AcceleratedClock'],
    'critical': ['AcceleratedCritical'],
    'stencils': ['JetStencils'],
    'boundary': ['AcceleratedGreen'],
    'canary': ['Canary'],
}
roots = {group: ['CarryFourthTail.'+m.group(1) for module in modules
                 for m in re.finditer(r'^(?:theorem|def|abbrev|instance)\s+(\w+)',
                                      (root/f'{module}.lean').read_text(),re.M)]
         for group,modules in groups.items()}
header = '''import Canary
import Lean

open Lean Elab Command
elab "#audit_fourth_tail " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
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
  logInfo m!"Fourth tail audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

'''
body = '\n'.join('#print axioms '+name for names in roots.values() for name in names)
for group,names in roots.items():
    body += '\n\n#audit_fourth_tail '+group+'\n  '+'\n  '.join(names)
(root/'Audit.lean').write_text(header+body+'\n')
(root/'public-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
print({group:len(names) for group,names in roots.items()})
