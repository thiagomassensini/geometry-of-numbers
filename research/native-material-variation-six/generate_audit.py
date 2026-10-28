#!/usr/bin/env python3
"""Audit every public root, including opaque theorem bodies and exact-source gates."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parent
modules=['MaterialVariation','PhysicalMaterialVariation','JetEulerVariation','SixSource','SixTaylor','SixSign','SixEnergyTransport']
roots={m:['CarryMaterialVariation.'+x[1] for x in re.findall(r'^(theorem|def|abbrev)\s+([\w.]+)',
    (root/(m+'.lean')).read_text(),re.M)] for m in modules}
algebra_names={'materialPair','materialVariation','materialPair_affine','materialPair_hasDerivAt',
 'scaled_material_hasDerivAt','radialJetVector','radial_jet_vector_at_grid','radial_jet_prefix_support',
 'radial_jet_hasDerivAt','materialPair_scale_inputs','materialPair_linear_readout','jet_material_variation',
 'jet_kernel_monomial','canonical_layer_annihilated','sixInput','sixWeight','sixRaw','six_input_outside',
 'six_input_support','six_raw_at_grid','six_raw_differentiable','sixNodeWeight','six_weight_real','six_raw_product'}
source_sign_defs={'prefixDelta','uNumerator','vNumerator','sixU','sixV'}
groups={'algebra':[],'source':[],'certificate':[]}
for m,names in roots.items():
 for n in names:
  short=n.rsplit('.',1)[-1]
  g='algebra' if short in algebra_names else ('certificate' if
      (m=='SixSign' and short not in source_sign_defs) or short=='six_original_eventually_above' else 'source')
  groups[g].append(n)
header=r'''import SixEnergyTransport
import JetEulerVariation
import Lean
open Lean Elab Command
elab "#audit_flow " group:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarryIntegralCertificate.material_fourth_pivot_bounds_integral,
    `CarryIntegralCertificate.material_fourth_pivot_pos_integral,
    `CarryIntegralCertificate.material_fourth_block_posDef_integral,
    `CarryIntegralCertificate.material_fourth_critical_positive_integral,
    `CarryIntegralCertificate.material_fourth_theta_integral_gate,
    `CarryIntegralCertificate.material_fourth_cholesky_integral]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for a in (← collectAxioms decl) do
      unless allowed.contains a do throwError "Unexpected axiom in {decl}: {a}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden finite positivity/equivalence dependency: {name}"
      if group.getId == `algebra &&
          (name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment ||
           name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic ||
           name == `CarrySelfAdjointOperator.completedNativeOperatorLogDerivative) then
        throwError "Source-dependent algebra root: {name}"
      if group.getId != `certificate && name == `CarryIntegralCertificate.material_theta_integral_input then
        throwError "Unexpected interval certificate in sign-free group: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing declaration: {name}"
  if group.getId == `certificate then
    for required in #[`CarryIntegralCertificate.material_theta_integral_input,
      `CarryIntegralCertificate.mem_logMomentBox,
      `CarryMaterialVariation.six_exact_remainder,
      `CarryMaterialVariation.six_physical_energy] do
      unless seen.contains required do throwError "Missing actual full physical source/certificate link: {required}"
  logInfo m!"Material variation audit {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; finite canonical positivity forbidden; opaque bodies traversed"
'''
names=sum(roots.values(),[])
body='\n'.join('#print axioms '+n for n in names)+'\n'
for group,entries in groups.items():
    body+='\n#audit_flow '+group+'\n  '+'\n  '.join(entries)+'\n'
(root/'Audit.lean').write_text(header+body)
(root/'public-roots.json').write_text(json.dumps({'modules':roots,'groups':groups},indent=2)+'\n')
print(json.dumps({'public_roots':len(names),'groups':{g:len(v) for g,v in groups.items()}}))
