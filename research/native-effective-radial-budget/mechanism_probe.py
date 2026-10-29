#!/usr/bin/env python3
"""Exact source-stencil controls and finite diagnostics of the effective budget."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
import csv,hashlib,json
root=Path(__file__).resolve().parent;ev=root/'evidence';ev.mkdir(exist_ok=True)
cp=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
sha='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
assert hashlib.sha256(cp.read_bytes()).hexdigest()==sha
coeff=[[40,-1040,F(-62,21),4800,F(320,7),F(1,21)],[-40,1280,F(85,21),-2400,F(-710,7),F(-5,84)],
 [F(120,7),-720,F(-65,21),0,120,F(5,126)],[F(-20,7),160,F(92,63),0,-80,F(-1,63)],
 [0,0,F(-25,63),0,F(200,7),F(5,1386)],[0,0,F(1,21),0,F(-30,7),F(-1,2772)]]
d1=[-1,1,0,0,0,0];d3=[-1,3,-3,1,0,0];d5=[-1,5,-10,10,-5,1]
def lim(a,u,v):return 2*(a[5]+2*u*a[4]+(u*u+2*v)*a[3]+2*u*v*a[2]+v*v*a[1])
def corr(a,u,v):return -10*v*v*a[2]-168*u*v*a[3]-60*(u*u+14*v)*a[4]-484*u*a[5]-182*a[6]
def higher(a,u,v,t):return (42*a[3]*v*v+3948*a[4]*u*v+1254*a[5]*u*u+65868*a[5]*v+32032*a[6]*u+
 t*t*(-170*a[4]*v*v-75856*a[5]*u*v-22880*a[6]*u*u-3649360*a[6]*v)+
 t**4*(682*a[5]*v*v+1333332*a[6]*u*v)-t**6*2730*a[6]*v*v)
checks=0
for u,v in [(F(0),F(0)),(F(-1,100),F(1,100000)),(F(2,5),F(-3,7)),(F(-1),F(2))]:
 for t in [F(1,7),F(1,16),F(1,33)]:
  a=[F((-1)**n*(n+1),13**(n+1)) for n in range(11)]
  w=[d5[i]-20*u*t*t*d3[i]+120*v*t**4*d1[i] for i in range(6)]
  q=[sum(2*(-1)**n*hn*((i+1)*t)**(2*n+1) for n,hn in enumerate(a)) for i in range(6)]
  I=sum(w[i]*w[j]*(q[i]+1)*(q[j]+1)/F(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
  R=sum(w[i]*w[j]*(q[i]-1)*(q[j]-1)/F(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
  E=sum(w[i]*w[j]*(q[i]+q[j])/F(i+j+2) for i in range(6) for j in range(6))/(14400*t**11)
  mono=[u*u*t**4,u*v*t**6,u*t*t,v*v*t**8,v*t**4,F(1)]
  nodes=[sum(c*m for c,m in zip(row,mono)) for row in coeff]
  tail=sum(nodes[j]*(j+1)**15*sum(2*hn*(-1)**n*((j+1)*t)**(2*n) for n,hn in enumerate(a[7:])) for j in range(6))/14400
  assert I-R==E==lim(a,u,v)+corr(a,u,v)*t*t+t**4*(higher(a,u,v,t)-tail)
  checks+=1
H=F(1,10**20);A=F(22,175)
node_norm=max(sum(abs(x) for x in row) for row in coeff)
higher_norm=sum([42,3948,1254,65868,32032,170,75856,22880,3649360,682,1333332,2730])
assert node_norm<100000 and higher_norm<10**10
assert 10**10+6*100000*6**15/F(14400)<10**20
assert F(2,1000)+4*H**2*10**20+H**3*10**22<2
assert F(15,10**17)-H**4*10**20>F(1,10**16)>H*H
with localcontext() as ctx:
 ctx.prec=450
 a=[D(r['canonical_h']) for r in csv.DictReader(cp.open())]
 delta=a[1]*a[3]-a[2]**2;u=(a[2]*a[3]-a[1]*a[4])/delta;v=(a[2]*a[4]-a[3]**2)/delta
 L=lim(a,u,v);C=corr(a,u,v);samples=[]
 for den in [10**20,10**20+1,2*10**20,4*10**20]:
  t=1/D(den);w=[D(d5[i])-20*u*t*t*D(d3[i])+120*v*t**4*D(d1[i]) for i in range(6)]
  q=[sum(2*D((-1)**n)*hn*((i+1)*t)**(2*n+1) for n,hn in enumerate(a)) for i in range(6)]
  I=sum(w[i]*w[j]*(q[i]+1)*(q[j]+1)/D(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
  R=sum(w[i]*w[j]*(q[i]-1)*(q[j]-1)/D(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
  E=sum(w[i]*w[j]*(q[i]+q[j])/D(i+j+2) for i in range(6) for j in range(6))/(14400*t**11)
  assert abs(I-R-E)<D('1e-180')
  assert E>D('1e-16') and t*t<D('1e-16')
  samples.append({'denominator':den,'balance_diagnostic':str(E),'incident_energy':str(I),
    'returned_energy':str(R),'budget_tail_upper':str(t*t),
    'source_remainder_energy_upper':str(t**4*D(10)**20)})
 record={'PASS':True,'exact_complete_six_stencil_checks':checks,'exact_budget_constant_checks':5,
  'checkpoint_sha256':sha,'input_column':'canonical_h','input_moments':len(a),'decimal_precision':450,
  'cutoff_k':10**20-1,'h_cutoff':'1e-20','increment_budget_B':1,'samples':samples,
  'scope':'Exact Fraction calculations test the finite algebra and conservative numerical constants, not an alternate native source. Decimal diagnostics use stored canonical data, not interval-certified true integrals. Actual infinite source/derivative bounds and the effective physical budget require Lean proofs; no new moments, zeros or heights were calculated.'}
 (ev/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: {checks} exact full-stencil identities, 5 exact budget controls, 4 finite canonical diagnostics at 450 arithmetic digits.')
