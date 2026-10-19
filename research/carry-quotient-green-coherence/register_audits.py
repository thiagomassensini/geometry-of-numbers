from pathlib import Path
import re,json

folder=Path(__file__).resolve().parent
root=folder.parents[1]
lib=root/'GeometryOfNumbers/Analysis/CarryMaterialReadoutQuotient.lean'
lib_names=re.findall(r'^theorem\s+(\w+)',lib.read_text(),re.M)
command='''open Lean Elab Command
elab "#audit_quotient_roots " ids:ident+ : command => do
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
  logInfo m!"Quotient roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"
'''

def audit(imports,names):
    return ''.join('import '+i+'\n' for i in imports+['Lean'])+'\n'+command+'\n'+''.join('#print axioms '+n+'\n' for n in names)+'\n#audit_quotient_roots\n'+''.join('  '+n+'\n' for n in names)

lib_roots=['GeometryOfNumbers.Analysis.'+n for n in lib_names]
(lib.parent/'CarryMaterialReadoutQuotientAudit.lean').write_text(audit(['GeometryOfNumbers.Analysis.CarryMaterialReadoutQuotient'],lib_roots))
entry=root/'GeometryOfNumbers/Analysis.lean'
line='import GeometryOfNumbers.Analysis.CarryMaterialReadoutQuotient\n'
text=entry.read_text()
if line not in text:entry.write_text(line+text)
registry=root/'GeometryOfNumbers/Analysis/Audit.lean'
text=registry.read_text()
block='\nnamespace GeometryOfNumbers.Analysis\n'+''.join('#assert_analysis_axioms '+n+'\n#print axioms '+n+'\n' for n in lib_names)+'end GeometryOfNumbers.Analysis\n'
if '#assert_analysis_axioms '+lib_names[-1]+'\n' not in text:registry.write_text(text+block)
research_roots=[]
for name,ns in [('MaterialCameraSeparation','CarryMaterialCameraSeparation'),('CameraObservation','CarryCameraObservationAudit')]:
    research_roots += [ns+'.'+n for n in re.findall(r'^(?:theorem|def)\s+(\w+)',(folder/(name+'.lean')).read_text(),re.M)]
(folder/'Audit.lean').write_text(audit(['MaterialCameraSeparation','CameraObservation'],research_roots))
(folder/'public-roots.json').write_text(json.dumps({'library':lib_roots,'research':research_roots},indent=2)+'\n')
print('Registered',len(lib_roots),'library roots and',len(research_roots),'research roots')
