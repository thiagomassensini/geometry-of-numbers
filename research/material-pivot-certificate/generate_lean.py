#!/usr/bin/env python3
"""Emit a kernel-replayed arithmetic implication for the literal theta moments.
The generated theorem deliberately has a theta-box hypothesis. The Python
quadrature is NOT converted into an axiom or hidden Lean assumption.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json, importlib.util, argparse
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('certify',here/'certify.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
I=mod.I;mod.S=10**55
T=lambda q:f'({F(q).numerator}/{F(q).denominator}:ℝ)'
class Gen:
 def __init__(self):self.lines=[];self.count=0;self.cache={};self.scopeStart=0
 def node(self,value,expr,proof):return N(self,value,expr,proof)
 def const(self,v):q=F(v);return self.node(I(q),T(q),f'(show {T(q)} ≤ {T(q)} ∧ {T(q)} ≤ {T(q)} from ⟨le_rfl,le_rfl⟩)')
 def op(self,a,b,op):
  if not isinstance(a,N):a=self.const(a)
  if not isinstance(b,N):b=self.const(b)
  key=(a.expr,b.expr,op)
  if key in self.cache:return self.cache[key]
  if op=='sub':return self.op(a,self.op(self.const(-1),b,'mul'),'add')
  n=self.count;self.count+=1;name=f'v{n}';pn=f'hv{n}'
  if op=='add':v=a.i+b.i;symbol='+';lemma='enclose_add';certs=[v.l<=a.i.l+b.i.l,a.i.u+b.i.u<=v.u];args='(by norm_num) (by norm_num)'
  elif op=='mul':
   v=a.i*b.i;symbol='*';lemma='enclose_mul';corn=[x*y for x in [a.i.l,a.i.u] for y in [b.i.l,b.i.u]];assert all(v.l<=x<=v.u for x in corn)
   args=' '.join(['(by norm_num)']*8)
  elif op=='div':
   assert b.i.l>0
   inv=self.node(1/b.i,f'(1/({b.expr}))',f'(show {T((1/b.i).l)} ≤ 1/({b.expr}) ∧ 1/({b.expr}) ≤ {T((1/b.i).u)} from enclose_inv {b.proof} (by norm_num) (by norm_num) (by norm_num))')
   prod=self.op(a,inv,'mul');v=a.i/b.i
   self.lines+= [f'  let {name} : ℝ := {a.expr}/{b.expr}',f'  have {pn} : {T(v.l)} ≤ {name} ∧ {name} ≤ {T(v.u)} := by',f'    change {T(v.l)} ≤ {a.expr}/{b.expr} ∧ {a.expr}/{b.expr} ≤ {T(v.u)}',f'    have hprod := {prod.proof}',f'    change {T(v.l)} ≤ {a.expr}*(1/{b.expr}) ∧ {a.expr}*(1/{b.expr}) ≤ {T(v.u)} at hprod',f'    simpa only [div_eq_mul_inv,one_mul] using hprod']
   out=self.node(v,name,pn);self.cache[key]=out;return out
  self.lines += [f'  let {name} : ℝ := {a.expr}{symbol}{b.expr}',f'  have {pn} : {T(v.l)} ≤ {name} ∧ {name} ≤ {T(v.u)} :=',f'    enclose_{op} {a.proof} {b.proof} {args}']
  out=self.node(v,name,pn);self.cache[key]=out;return out
 def identify(self,node,expr,eqproof,name):
  self.lines += [f'  have e{name} : {expr} = {node.expr} := by','    try dsimp only ['+','.join(f'v{i}' for i in range(self.scopeStart,self.count))+']',eqproof,
   f'  have h{name} : {T(node.i.l)} ≤ {expr} ∧ {expr} ≤ {T(node.i.u)} := by',f'    rw [e{name}]',f'    exact {node.proof}']
  return self.node(node.i,expr,f'h{name}')
class N:
 def __init__(s,g,i,expr,proof):s.g=g;s.i=i;s.expr=expr;s.proof=proof
 def __add__(s,o):return s.g.op(s,o,'add')
 __radd__=__add__
 def __mul__(s,o):return s.g.op(s,o,'mul')
 __rmul__=__mul__
 def __sub__(s,o):return s.g.op(s,o,'sub')
 def __rsub__(s,o):return s.g.op(o,s,'sub')
 def __truediv__(s,o):return s.g.op(s,o,'div')
 def __neg__(s):return -1*s

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--certificate',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
 rec=json.loads(args.certificate.read_text());g=Gen();A=[];L=[];U=[]
 for k,a in enumerate(rec['source_moments']):
  # Truncate only OUTWARDS, never infer analytic bounds from a midpoint.
  den=10**40;l=F((F(a['lower'])*den).__floor__(),den);u=F((F(a['upper'])*den).__ceil__(),den);L.append(l);U.append(u)
  e=f'completedNativeThetaTailMoment {2*k}';pn=f'hA{k}'
  g.lines += [f'  have {pn} : {T(l)} ≤ {e} ∧ {e} ≤ {T(u)} := by',f'    have hh := hb ⟨{k},by decide⟩', '    norm_num [material_fourth_theta_box_lower,material_fourth_theta_box_upper] at hh', '    exact hh']
  A.append(g.node(I(l,u),f'({e})',pn))
 c=[]
 for n in range(10):
  v=F(1,2)-A[0]/4 if n==0 else (-1)**n*(A[n-1]/factorial(2*n-2)-A[n]/(4*factorial(2*n)))
  # `change` unfolds the let DAG only for this short source expression.
  raw=f'(1/2-(completedNativeThetaTailMoment 0)/4)' if n==0 else f'((-1:ℝ)^{n}*((completedNativeThetaTailMoment {2*n-2})/{factorial(2*n-2)}-(completedNativeThetaTailMoment {2*n})/{4*factorial(2*n)}))'
  proof=f'    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]\n'
  if n==0:proof+='    rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]\n'
  else:proof+=f'    rw [show {n} = {n-1}+1 by rfl,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]\n'
  proof+='    norm_num [Nat.factorial] <;> ring'
  c.append(g.identify(v,f'(c {n})',proof,f'C{n}'))
 cEnd=len(g.lines);cEndN=g.count;g.scopeStart=g.count;g.cache={}
 h=[]
 for n in range(9):
  s=sum((h[k]*c[n-k] for k in range(n)),g.const(0));v=(-(n+1)*c[n+1]-s)/c[0]
  proof=f'    change h {n} = (-({n+1}:ℝ)*c {n+1}-(∑ k ∈ Finset.range {n}, h k*c ({n}-k)))/c 0\n    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2\n    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence {n}\n    norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at he\n    linarith only [he]'
  # sum is syntactically expanded: use a controlled conversion before `change`.
  expanded=' + '.join([f'(h {k}*c {n-k})' for k in range(n)]) or '0'
  proof=f'    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence {n}\n    norm_num [Finset.sum_range_succ] at he\n    apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2\n    try simp only [zero_add]\n    linarith only [he]'
  h.append(g.identify(v,f'(h {n})',proof,f'H{n}'))
 hEnd=len(g.lines);hEndN=g.count;g.scopeStart=g.count;g.cache={}
 R=[]
 for i in range(4):
  row=[]
  for j in range(4):
   v=h[i+j+2]-h[i+1]*h[j+1]/h[0]
   e=f'(carryPairingRemainder carryMaterialEvenPairing 0 {i} {j})'
   proof=f'    change carryMaterialEvenPairing {i} {j} = _\n    rw [material_even_pairing_source]\n    ring'
   row.append(g.identify(v,e,proof,f'R0{i}{j}'))
  R.append(row)
 piv=[];Q=g.const(0)
 for r in range(4):
  piv.append(R[r][r])
  if r==3:break
  Q+=R[3][r]*R[r][3]/R[r][r]
  RR=[row[:] for row in R]
  for i in range(r+1,4):
   for j in range(r+1,4):
    v=R[i][j]-R[i][r]*R[r][j]/R[r][r]
    e=f'(carryPairingRemainder carryMaterialEvenPairing {r+1} {i} {j})'
    proof=f'    change carryPairingRemainder carryMaterialEvenPairing {r} {i} {j}-carryPairingRemainder carryMaterialEvenPairing {r} {i} {r}*carryPairingRemainder carryMaterialEvenPairing {r} {r} {j}/carryPairingRemainder carryMaterialEvenPairing {r} {r} {r} = _\n    ring'
    RR[i][j]=g.identify(v,e,proof,f'R{r+1}{i}{j}')
  R=RR
 Thresh=h[4]*h[4]/h[0]+Q
 # Q keeps all ordered products; a finite algebraic identification is enough.
 Thresh=g.identify(Thresh,'carryMaterialFourthSourceThreshold','    rw [material_fourth_threshold_eq]\n    try dsimp only [carryMaterialFourthOldCoupling,carryPairingPivot,carryPairingRemainder]\n    try dsimp only ['+','.join(f'v{i}' for i in range(g.scopeStart,g.count))+']\n    ring','Threshold')
 B=-(sum((h[k]*c[8-k] for k in range(8)),g.const(0))+c[0]*Thresh)/9
 B=g.identify(B,'material_fourth_characteristic_ceiling','    rw [material_fourth_characteristic_ceiling]\n    try dsimp only ['+','.join(f'v{i}' for i in range(g.scopeStart,g.count))+']\n    norm_num [Finset.sum_range_succ]','Ceiling')
 gap=B-c[9];p=piv[3]
 # Keep final human bounds comfortably outside all replay roundoff.
 pl,pu=F(1666,10**29),F(1667,10**29);gl,gu=F(9203,10**31),F(9204,10**31);bl,bu=F(-367813189170,10**33),F(-367813189168,10**33)
 assert pl<p.i.l and p.i.u<pu and gl<gap.i.l and gap.i.u<gu and bl<B.i.l and B.i.u<bu
 body='\n'.join(g.lines[hEnd:])+f'''\n  change carryMaterialFourthPivot = _ at eR333
  have hp : {TEX(pl)} < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < {TEX(pu)} := by
    change {TEX(pl)} < carryPairingRemainder carryMaterialEvenPairing 3 3 3 ∧ carryPairingRemainder carryMaterialEvenPairing 3 3 3 < {TEX(pu)}
    constructor <;> linarith only [hR333.1,hR333.2]
  have hB : {TEX(bl)} < material_fourth_characteristic_ceiling ∧ material_fourth_characteristic_ceiling < {TEX(bu)} := by
    constructor <;> linarith only [hCeiling.1,hCeiling.2]
  have hgap : {TEX(gl)} < material_fourth_characteristic_ceiling-c 9 ∧ material_fourth_characteristic_ceiling-c 9 < {TEX(gu)} := by
    have egap : material_fourth_characteristic_ceiling-c 9 = {gap.expr} := by
      dsimp only [v{g.count-1},v{g.count-2}]
      ring
    rw [egap]
    constructor <;> linarith only [{gap.proof}.1,{gap.proof}.2]
  exact ⟨hp,hB,hgap⟩
'''
 header='''\nnamespace CarryMaterialPivotCertificate\nopen GeometryOfNumbers.Analysis CarrySelfAdjointOperator\nopen CarryMaterialSourceFactorComparison CarryMaterialFourthPivotComparison\nopen scoped Matrix\nnoncomputable section\nset_option autoImplicit false\nset_option maxHeartbeats 8000000\nset_option maxRecDepth 16384\nset_option linter.unnecessarySeqFocus false\nset_option backward.isDefEq.respectTransparency false\nlocal notation "h" => canonicalCompletedNativeLogDerivativeMoment\nlocal notation "c" => completedNativeRealEvenCharacteristicCoefficient\n'''
 defs='\ndef material_fourth_theta_box_lower : Fin 10 → ℝ := !['+','.join(map(TEX,L))+']\n\ndef material_fourth_theta_box_upper : Fin 10 → ℝ := !['+','.join(map(TEX,U))+']\n\n/-- Analytic input still requiring a kernel-checked quadrature bridge. The\nPython certificate supplies it as a rigorous computation, not a Lean axiom. -/\ndef material_fourth_theta_box : Prop := ∀ k : Fin 10,\n  material_fourth_theta_box_lower k ≤ completedNativeThetaTailMoment (2*k) ∧\n  completedNativeThetaTailMoment (2*k) ≤ material_fourth_theta_box_upper k\n'
 def tupleType(nodes):return ' ∧\n    '.join(f'({TEX(v.i.l)} ≤ {v.expr} ∧ {v.expr} ≤ {TEX(v.i.u)})' for v in nodes)
 def tupleProof(names):
  return '⟨'+','.join(names)+'⟩'
 def extract(lemma,names):
  out=[f'  have hh := {lemma} hb']
  for i,name in enumerate(names):out.append(f'  have {name} := hh'+('.2'*i)+('.1' if i<len(names)-1 else ''))
  return '\n'.join(out)+'\n'
 intermediate='\nprivate theorem characteristic_enclosures (hb : material_fourth_theta_box) :\n    '+tupleType(c)+' := by\n'+'\n'.join(g.lines[:cEnd])+'\n  exact '+tupleProof([f'hC{i}' for i in range(10)])+'\n'
 intermediate+='\nprivate theorem moment_enclosures (hb : material_fourth_theta_box) :\n    '+tupleType(h)+' := by\n'+extract('characteristic_enclosures',[f'hC{i}' for i in range(10)])+'\n'.join(g.lines[cEnd:hEnd])+'\n  exact '+tupleProof([f'hH{i}' for i in range(9)])+'\n'
 body=extract('characteristic_enclosures',[f'hC{i}' for i in range(10)])+extract('moment_enclosures',[f'hH{i}' for i in range(9)])+body
 stmt=f'''\n/-- Kernel-checked arithmetic implication for the actual theta moments.\nThis theorem does not assert `material_fourth_theta_box`. -/\ntheorem material_fourth_bounds_of_theta_box (hb : material_fourth_theta_box) :\n    ({TEX(pl)} < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < {TEX(pu)}) ∧\n    ({TEX(bl)} < material_fourth_characteristic_ceiling ∧ material_fourth_characteristic_ceiling < {TEX(bu)}) ∧\n    ({TEX(gl)} < material_fourth_characteristic_ceiling-c 9 ∧ material_fourth_characteristic_ceiling-c 9 < {TEX(gu)}) := by\n'''
 consequences='''
/-- The exact back-substituted material combination keeps a certified margin,
conditional on the displayed analytic source enclosure. -/
theorem material_fourth_critical_margin_of_theta_box (hb : material_fourth_theta_box) :
    (833/50000000000000000000000000000:ℝ) <
      carryPairingBilinear carryMaterialEvenPairing 4
        carryMaterialFourthCritical carryMaterialFourthCritical := by
  rw [material_fourth_critical_energy]
  exact (material_fourth_bounds_of_theta_box hb).1.1

theorem material_fourth_posDef_of_theta_box (hb : material_fourth_theta_box) :
    Matrix.PosDef (fun i j : Fin 4 => carryMaterialEvenPairing i j) := by
  apply material_fourth_block_posDef_iff.mpr
  exact lt_trans (by norm_num) (material_fourth_bounds_of_theta_box hb).1.1

theorem material_fourth_cholesky_of_theta_box (hb : material_fourth_theta_box) :
    carryMaterialEvenCholesky 4*(carryMaterialEvenCholesky 4)ᵀ =
      (fun i j : Fin 4 => carryMaterialEvenPairing i j) := by
  apply material_fourth_cholesky_of_source_estimate
  have he := (material_fourth_bounds_of_theta_box hb).2.2.1
  linarith only [he]
'''
 audits='\nend\nend CarryMaterialPivotCertificate\n\nnamespace CarryMaterialPivotCertificate\n'
 for name in ['enclose_add','enclose_neg','enclose_mul','enclose_inv','material_fourth_theta_box_lower','material_fourth_theta_box_upper','material_fourth_theta_box','material_fourth_bounds_of_theta_box','material_fourth_critical_margin_of_theta_box','material_fourth_posDef_of_theta_box','material_fourth_cholesky_of_theta_box']:
  audits+=f'#assert_central_comparison_axioms {name}\n#print axioms {name}\n'
 audits+='end CarryMaterialPivotCertificate\n'
 helpers=(here/'IntervalHelpers.lean').read_text().replace('import Mathlib\n','')
 args.out.write_text('\n'+helpers+header+defs+intermediate+stmt+body+consequences+audits)
 print('generated',g.count,'nodes',args.out.stat().st_size,'bytes')
TEX=T
if __name__=='__main__':main()
