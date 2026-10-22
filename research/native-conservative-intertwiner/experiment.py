#!/usr/bin/env python3
"""Exact finite controls in the original Cauchy Gram. No moment/height inputs."""
from fractions import Fraction as Q
from pathlib import Path
import json

# The shared amplitude has squared modulus 1/2, proved from the native source.
def gram(x,y):
    return sum((a*b/Q(i+j+2) for i,a in enumerate(x) for j,b in enumerate(y)),Q(0))
def shift(x,power=1):
    return [a*Q(2*j+1,2*j+3)**power for j,a in enumerate(x)]
def add(x,y): return [a+b for a,b in zip(x,y)]
def sub(x,y): return [a-b for a,b in zip(x,y)]
def neg(x): return [-a for a in x]

def canary(x,expected):
    # Native limiting return is -x, not the proposed -shift(x).
    c=neg(shift(x)); eta=sub(neg(x),c)
    energy=gram(x,x)/2
    head=(gram(x,x)-gram(c,c))/2
    error=gram(eta,eta)/2
    cross=gram(c,eta) # includes factor 2 and squared amplitude 1/2
    actual=(energy,head,error,cross)
    assert actual==tuple(Q(t) for t in expected),actual
    assert head-cross-error==0
    assert error>0
    return dict(zip(('energy','head_energy','defect_energy','mixed_cross'),map(str,actual)))

results={
 'even':canary([Q(1)],['1/4','2/9','1/9','1/9']),
 'odd':canary([Q(-1),Q(1)],['1/24','8/225','19/450','-1/150']),
}
# Complex polarization with independent quadratures, represented as exact real pairs.
def cinner(x,y):
    xr,xi=x; yr,yi=y
    return (gram(xr,yr)+gram(xi,yi),gram(xr,yi)-gram(xi,yr))
def cadd(x,y):return tuple(add(a,b) for a,b in zip(x,y))
def csub(x,y):return tuple(sub(a,b) for a,b in zip(x,y))
def cneg(x):return tuple(neg(a) for a in x)
def cshift(x,p):return tuple(shift(a,p) for a in x)
def zadd(x,y):return tuple(a+b for a,b in zip(x,y))
def zsub(x,y):return tuple(a-b for a,b in zip(x,y))
controls=0
for power in (1,2,4):
    x=([Q(1),Q(-2),Q(3)],[Q(2),Q(1),Q(-1)])
    y=([Q(-3),Q(4),Q(2)],[Q(1),Q(-1),Q(3)])
    rx=([Q(2),Q(0),Q(-1)],[Q(3),Q(2),Q(1)])
    ry=([Q(1),Q(2),Q(-4)],[Q(-2),Q(1),Q(0)])
    cx=cneg(cshift(x,power));cy=cneg(cshift(y,power))
    ex=csub(rx,cx);ey=csub(ry,cy)
    head=zsub(cinner(x,y),cinner(cx,cy))
    lhs=zsub(cinner(x,y),cinner(rx,ry))
    rhs=zsub(zsub(zsub(head,cinner(cx,ey)),cinner(ex,cy)),cinner(ex,ey))
    assert lhs==rhs
    controls+=1
    # Regression must detect deleting either independently polarized cross.
    assert zadd(rhs,cinner(cx,ey))!=lhs
    assert zadd(rhs,cinner(ex,cy))!=lhs
results['independent_complex_polarized_controls']=controls
results['scope']='Exact finite regression of the proven metric and leading states; not all-order positivity.'
out=Path(__file__).resolve().parent/'evidence'
out.mkdir(exist_ok=True)
(out/'exact-controls.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
