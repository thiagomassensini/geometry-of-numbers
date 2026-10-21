#!/usr/bin/env python3
"""Independent exact rational controls for the full polarized decomposition.

Synthetic return quotients are explicitly controls, never native source data.
The final checkpoint test treats only the user-supplied decimals as rationals.
No zeros, heights, zeta/theta evaluation or numerical spectral solve is used.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

@dataclass(frozen=True)
class C:
    re: Q = Q(0)
    im: Q = Q(0)
    def __add__(self,other):
        other=cast(other)
        return C(self.re+other.re,self.im+other.im)
    __radd__=__add__
    def __neg__(self):
        return C(-self.re,-self.im)
    def __sub__(self,other):
        return self+-cast(other)
    def __rsub__(self,other):
        return cast(other)+-self
    def __mul__(self,other):
        other=cast(other)
        return C(self.re*other.re-self.im*other.im,
                 self.re*other.im+self.im*other.re)
    __rmul__=__mul__
    def conj(self):
        return C(self.re,-self.im)
    def __truediv__(self,other):
        other=cast(other)
        norm=other.re**2+other.im**2
        assert norm
        value=self*other.conj()
        return C(value.re/norm,value.im/norm)
    def json(self):
        return [str(self.re),str(self.im)]

def cast(x):
    return x if isinstance(x,C) else C(Q(x))

def inner(k,x,y):
    return sum((x[i].conj()*y[j]*Q(k+1,i+j+2)
                for i in range(len(x)) for j in range(len(y))),C())

def split(k,q,c):
    r=q[0]
    u=[(1-r.conj()*qi)*ci for qi,ci in zip(q,c)]
    v=[(qi-r)*ci for qi,ci in zip(q,c)]
    e=[C(1)]+[C()]*(len(q)-1)
    a=inner(k,e,u)/inner(k,e,e)
    p=[a]+[C()]*(len(q)-1)
    z=[ui-pi for ui,pi in zip(u,p)]
    return u,v,p,z

records=[]
for k in (0,3,10):
    for n in (1,2,7):
        q=[C(Q(1,2),Q(1,3))]+[C(Q(i+1,4),Q(i%3,5)) for i in range(1,n)]
        c=[C(Q((-1)**i,i+1),Q(i,7)) for i in range(n)]
        d=[C(Q(i+2,9),Q((-1)**i,i+3)) for i in range(n)]
        uc,vc,pc,zc=split(k,q,c)
        ud,vd,pd,zd=split(k,q,d)
        r=q[0]
        delta=1-r.conj()*r
        rc=[qi*ci for qi,ci in zip(q,c)]
        rd=[qi*di for qi,di in zip(q,d)]
        full=inner(k,c,d)-inner(k,rc,rd)
        remaining=inner(k,zc,zd)-inner(k,vc,vd)
        assert delta*full==inner(k,pc,pd)+remaining
        assert all(delta*ci==pi+zi+r.conj()*vi for ci,pi,zi,vi in zip(c,pc,zc,vc))
        assert all(delta*ri==vi+r*(pi+zi) for ri,pi,zi,vi in zip(rc,pc,zc,vc))
        e=[C(1)]+[C()]*(n-1)
        bx=inner(k,e,c)-r.conj()*inner(k,e,rc)
        by=inner(k,e,d)-r.conj()*inner(k,e,rd)
        assert remaining/delta==full-bx.conj()*by/(delta*inner(k,e,e))
        tailc=[C()]+c[1:]
        taild=[C()]+d[1:]
        _,tvc,_,tzc=split(k,q,tailc)
        _,tvd,_,tzd=split(k,q,taild)
        assert remaining==inner(k,tzc,tzd)-inner(k,tvc,tvd)
        records.append({'k':k,'N':n,'full':full.json(),'remaining':remaining.json(),
                        'projected':inner(k,pc,pd).json(),
                        'scope':'SYNTHETIC_RATIONAL_CONTROL_NOT_NATIVE_QUOTIENT'})

# An exact example on the same Cauchy matrix shape: a positive first deficit
# does not imply positivity for other independent source directions.
q=[C(Q(1,2)),C(2)]
c=[C(),C(1)]
u,v,p,z=split(0,q,c)
remaining=inner(0,z,z)-inner(0,v,v)
assert (1-q[0].conj()*q[0]).re>0
assert remaining.im==0 and remaining.re<0

# Canonical checkpoint: algebra of the actual h decimals, kept distinct from
# the source-level Lean proofs and from the synthetic feedback controls.
path=ROOT/'data/user-N6.json'
content=path.read_bytes()
h=list(map(Q,json.loads(content)['momentos']))
checkpoint=[]
for n in (2,4,6):
    g=[[h[i+j] for j in range(n)]for i in range(n)]
    p=[[h[i]*h[j]/h[0] for j in range(n)]for i in range(n)]
    s=[[g[i][j]-p[i][j] for j in range(n)]for i in range(n)]
    assert all(s[0][i]==s[i][0]==0 for i in range(n))
    a=[Q((-1)**i*(i+1)) for i in range(n)]
    b=[Q(i+2,3) for i in range(n)]
    form=lambda m:sum(a[i]*m[i][j]*b[j] for i in range(n) for j in range(n))
    assert form(g)==form(p)+form(s)
    checkpoint.append({'N':n,'full':str(form(g)),'first_schur':str(form(s)),
                       'scope':'EXACT_STORED_DECIMALS_NOT_ORIGINAL_INTEGRAL_ENCLOSURE'})

output={'controls':records,'negative_remainder_control':remaining.json(),
        'checkpoint_sha256':hashlib.sha256(content).hexdigest(),
        'checkpoint_first_schur':checkpoint}
(ROOT/'evidence').mkdir(exist_ok=True)
(ROOT/'evidence/experiment.json').write_text(json.dumps(output,indent=2)+'\n')
print('PASS: 9 exact complex-rational polarized controls, both reconstruction identities,')
print('Schur identity, head removal, negative-residual control, 3 stored-decimal canaries')
