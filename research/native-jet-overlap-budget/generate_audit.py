#!/usr/bin/env python3
import json
from pathlib import Path
import re
root=Path(__file__).resolve().parent
core=['OverlapGeometry','JetBudget','DampedCamera','StencilObstruction','PR41Bridge']
extra=['CentralResidual']
def names(modules):
    return ['CarryJetOverlap.'+m.group(1) for module in modules
            for m in re.finditer(r'^(?:theorem|def|abbrev)\s+(\w+)',(root/f'{module}.lean').read_text(),re.M)]
structural,central=names(core),names(extra)
header="""import DampedCamera
import StencilObstruction
import PR41Bridge
import CentralResidual
import Lean

open Lean Elab Command
elab "#audit_jet_overlap " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := if mode.getId == `structural then #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one]
    else #[]
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
        throwError "Unexpected finite sign dependency: {name}"
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
  logInfo m!"Jet overlap audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

"""
body='\n'.join('#print axioms '+n for n in structural+central)
body+='\n\n#audit_jet_overlap structural\n  '+'\n  '.join(structural)+'\n'
body+='\n#audit_jet_overlap central\n  '+'\n  '.join(central)+'\n'
(root/'Audit.lean').write_text(header+body)
(root/'public-roots.json').write_text(json.dumps({'structural':structural,'central':central},indent=2)+'\n')
print(len(structural),'structural roots;',len(central),'central-test roots')
