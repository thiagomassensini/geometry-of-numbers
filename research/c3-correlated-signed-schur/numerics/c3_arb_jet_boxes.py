#!/usr/bin/env python3
"""Arb (python-flint) rigorous interval jets: original completed C3 camera.
This *independent interval evaluation* uses the classical zeta identity for
the completed scalar solely to evaluate F, and the ORIGINAL C3 bracket
and 12-weight boundary to evaluate its head. Provenance of F from bracket
is established separately in Lean; the interval execution itself is not
a Lean proof and must not be promoted to one.

No zeros or heights as input.
"""
import json, sys, time
from pathlib import Path
from flint import arb, acb, acb_series, ctx

M = int(sys.argv[1]) if len(sys.argv)>1 else 384
maxj = int(sys.argv[2]) if len(sys.argv)>2 else 22
digits = int(sys.argv[3]) if len(sys.argv)>3 else 240
ctx.dps = digits
ctx.cap = 2*maxj+3
base=Path(__file__).resolve().parent.parent / "evidence"
start=time.time()
w=acb_series([0,acb(0,1)],prec=ctx.cap)
s=arb(1)/2+w
Pi=arb.pi()
Gamma=(s/2).gamma()
factor=(s*(s-1)/2)*((-s/2)*Pi.log()).exp()*Gamma
F=factor*s.zeta()
G=factor/(1-((1-s)*arb(3).log()).exp())
print("setup: cap",ctx.cap,"dps",ctx.dps,"F(0)",F[0],flush=True)
weights=[728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1]
def sample(addr:int):
    return ((-s)*arb(addr).log()).exp()
mass=acb_series([1],prec=ctx.cap)
for m in range(M):
    term=sample(3*m+2)-2*sample(3*m+3)+sample(3*m+4)
    mass+=term
    if (m+1)%128==0: print('mass',m+1,'elapsed',round(time.time()-start,1),'s',flush=True)
boundary=acb_series([0],prec=ctx.cap)
for j,weight in enumerate(weights):
    boundary+=arb(weight)/729*sample(3*M+2+j)
head=G*(mass+boundary)
tail=F-head
# Running high precision, verify the initial coefficient is small as expected.
print("F0",F[0],"head0",head[0],"tail0",tail[0],flush=True)
coeff=[]
for j in range(maxj+1):
    cf=F[2*j]; ch=head[2*j]; ct=tail[2*j]
    mag=ct.abs_upper()
    # Three-significant-digit rational decimal upper bound, verified by Arb.
    # Every eps_mantissa * 10**eps_exp is an exact decimal rational.
    if mag==0:
        e=-digits+10
    else:
        e=int(float(mag.log()/arb(10).log()))-3
    scale=arb(10)**e
    mant=max(1,int(float(mag/scale))+1)
    while not mag < arb(mant)*scale:
        mant+=1
    box=arb(mant)*scale
    assert mag<box
    coeff.append(dict(j=j, F=str(cf),head=str(ch),tail=str(ct),
        tail_abs_upper=str(mag),eps_mantissa=mant,eps_exp=e,
        box_certified_by_arb=bool(mag<box),F_real=str(cf.real),
        head_real=str(ch.real),tail_real=str(ct.real)))
    if j in (0,1,2,3,4,6,9,12,15,18,20,22):
        print('JET',j,'tail <',mant,'*10^',e,'tail',str(ct)[:120],flush=True)

# Native moment recursion, c0..cmaxj = even height jets of F.
c=[F[2*j].real for j in range(maxj+1)]
h=[]
for j in range(maxj):
    num=-(j+1)*c[j+1]
    for k in range(j):num-=h[k]*c[j-k]
    h.append(num/c[0])
# Arbitrary precision baseline from previous native moment dataset: test overlap.
from flint import arb
data=json.load(open('/home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json'))
for j in (0,1,2,3,8,16,18):
    v=arb(data['moments'][j][:100])
    if j<len(h):
        print('MOMENT',j,'Arb',str(h[j])[:125], 'relative_45digit_check', (h[j]/arb(data['moments'][j][:45])-1).abs_upper()<arb('1e-40'),flush=True)

out=base/f'C3_Arb_boxes_M{M}_j{maxj}_d{digits}.json'
out.write_text(json.dumps(dict(status='ARB_RIGOROUS_INTERVAL_EVALUATION_NOT_LEAN_CERTIFICATE',
    M=M,maxj=maxj,digits=digits,elapsed_seconds=round(time.time()-start,1),
    interval_backend='python-flint 0.8.0, acb_series, FLINT/Arb',
    origin='Original C3 bracket head + original 12-term boundary, completed factor; F evaluated with later proven classical xi identity only as interval crosscheck',
    max_required_index='The box for j uses even height-series coefficient 2j; no values of zeros entered.',
    coefficients=coeff),indent=2)+'\n')
print('BOXES_FILE',out,'elapsed',round(time.time()-start,1),flush=True)
