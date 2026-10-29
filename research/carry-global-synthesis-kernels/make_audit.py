from pathlib import Path
import re,json
folder=Path(__file__).resolve().parent
roots=[]
for file,namespace in [('GreenSynthesis','CarryGlobalGreenSynthesis'),('CameraBudget','CarryGlobalCameraBudget'),('ScaleCompatibility','CarryGlobalScaleCompatibility')]:
    roots += [namespace+'.'+n for n in re.findall(r'^(?:theorem|def|abbrev)\s+(\w+)',(folder/(file+'.lean')).read_text(),re.M)]
regressions=['CarryCameraObservationAudit.camera_two_four_distance',
 'GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_boundary_defect',
 'CarryMaterialCameraSeparation.all_cameras_finite_injective']
command='''open Lean Elab Command
elab "#audit_global_synthesis " ids:ident+ : command => do
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
  logInfo m!"Global synthesis roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"
'''
all_roots=roots+regressions
(folder/'Audit.lean').write_text('''import GreenSynthesis
import CameraBudget
import ScaleCompatibility
import CameraObservation
import GeometryOfNumbers.Analysis.CarryMaterialReadoutQuotient
import Lean
'''+command+'\n'+''.join('#print axioms '+n+'\n' for n in all_roots)+'\n#audit_global_synthesis\n'+''.join('  '+n+'\n' for n in all_roots))
(folder/'public-roots.json').write_text(json.dumps({'new':roots,'regressions':regressions},indent=2)+'\n')
print('Audit:',len(roots),'new roots and',len(regressions),'regression roots')
