#!/usr/bin/env python3
"""Independent Arb finite-order interval audit of the ORIGINAL completed C3 source.
Consumes c3_arb_jet_boxes.py and the original C3 head+boundary. No zeros.
NOT Lean formalization. Stronger than mere floating point: every comparison
uses outward enclosures in Arb arithmetic (FLINT/Arb).
"""
import json,sys,runpy
from pathlib import Path
from flint import arb,acb,arb_mat,ctx

M=int(sys.argv[1]) if len(sys.argv)>1 else 384
nmax=int(sys.argv[2]) if len(sys.argv)>2 else 9
dps=int(sys.argv[3]) if len(sys.argv)>3 else 240
SCRIPTS=Path(__file__).resolve().parent
P=SCRIPTS.parent / "evidence"
oldargs=sys.argv[:]
sys.argv=[str(P/'c3_arb_jet_boxes.py'),str(M),str(2*nmax+4),str(dps)]
data=runpy.run_path(str(SCRIPTS/'c3_arb_jet_boxes.py'))
sys.argv=oldargs
H=[data["head"][2*j] for j in range(2*nmax+5)]
T=[data["tail"][2*j] for j in range(2*nmax+5)]
C=data["c"]; h=data["h"]; boxes=data["coeff"]
ctx.cap=2*(2*nmax+4)+3

def source_lift(v):
    n=len(v);z=[arb(0)]*n
    for i in range(n-1,-1,-1):
        z[i]=(v[i]-sum((C[j-i]*z[j] for j in range(i+1,n)),arb(0)))/C[0]
    return z

def schur_vector(s,n):
    A=arb_mat([[h[s+i+j] for j in range(n)] for i in range(n)])
    b=arb_mat([[h[s+i+n]] for i in range(n)])
    q=A.solve(b)
    v=[-q[i,0] for i in range(n)]+[arb(1)]
    p=h[s+2*n]-sum((b[i,0]*q[i,0] for i in range(n)),arb(0))
    return v,p

def resp(arr,odd,k):
    return -(k+1)*arr[k+1] if odd else (-k*arr[k] if k else acb(0))

def pair(arr,darr,odd,zx,zy):
    r=len(zx);ans=acb(0)
    assert r==len(zy)
    for i in range(r):
        for j in range(r):
            v=acb(0)
            for k in range(j+1):
                v+=darr[j-k]*resp(arr,odd,i+k+1)
                v-=resp(arr,odd,j-k)*darr[i+k+1]
            ans+=zx[i]*zy[j]*v
    return ans

def two_source(s,n,v):
    if s==0:
        z=source_lift(v)
        return True,False,z,z
    else:
        zB=source_lift([arb(0)]+v)
        zP=source_lift(v)
        return False,True,zB,zP

def signed_pair(alpha,betaA,bB,bP,zB,zP,left,right):
    return alpha*pair(left,right,bB,zB,zB)-betaA*pair(left,right,bP,zP,zP)

def schur_critical_u(s,n,v):
    r=[arb(i-n)*v[i] for i in range(n)]
    if s==0:
        return True, source_lift(r), source_lift([arb(1)]+[arb(0)]*(n-1))
    else:
        return False, source_lift([arb(0)]+r), source_lift([arb(0),arb(1)]+[arb(0)]*(n-1))

def prefix_posdef(s,n):
    out=[]
    for k in range(1,n+1):
        if k==1:p=h[s]
        else:
            mat=arb_mat([[h[s+i+j] for j in range(k-1)] for i in range(k-1)])
            b=arb_mat([[h[s+i+k-1]] for i in range(k-1)])
            q=mat.solve(b)
            p=h[s+2*k-2]-sum((b[i,0]*q[i,0] for i in range(k-1)),arb(0))
        out.append(bool(p>0))
    return all(out)

N=2*(nmax+2)+1
tailcoeff=[T[j] for j in range(N)]
# rational eps verified independently from the computed tail complex intervals
eps=[]
for j in range(N):
    b=boxes[j]
    x=arb(b["eps_mantissa"])*arb(10)**b["eps_exp"]
    assert tailcoeff[j].abs_upper()<x
    eps.append(x)

out=[]
for s in (0,1):
    for n in range(1,nmax+1):
        v,p=schur_vector(s,n)
        alpha=arb((2*n+s+1)*(4*n+2*s+3))
        beta=arb(16*n+8*s+6)
        betaA=beta*v[n-1]
        bB,bP,zB,zP=two_source(s,n,v)
        uodd,zu,z0=schur_critical_u(s,n,v)
        uh=pair(H,H,uodd,zu,z0)
        ut=pair(H,T,uodd,zu,z0)+pair(T,H,uodd,zu,z0)+pair(T,T,uodd,zu,z0)
        Eu=ut.abs_upper()
        Lu=abs(uh.real)-Eu
        SHead=signed_pair(alpha,betaA,bB,bP,zB,zP,H,H)
        STT=signed_pair(alpha,betaA,bB,bP,zB,zP,T,T)
        ell=[]
        for k in range(N):
            one=[acb(0)]*N
            one[k]=acb(1)
            el=signed_pair(alpha,betaA,bB,bP,zB,zP,H,one)+signed_pair(alpha,betaA,bB,bP,zB,zP,one,H)
            ell.append(el)
        Elinear=sum((ell[j].abs_upper()*eps[j] for j in range(N)),arb(0))
        ETT=STT.abs_upper()
        Es=Elinear+ETT
        # The same original source full head+tail:
        SF=signed_pair(alpha,betaA,bB,bP,zB,zP,
          [acb(C[j]) for j in range(N)],
          [acb(C[j]) for j in range(N)])
        # compare S(true) from original moment matrix to transferred source.
        B=sum((v[i]*v[j]*h[s+1+i+j] for i in range(n+1) for j in range(n+1)),arb(0))
        S=alpha*B-betaA*p
        source_discrep=(SF.real-S).abs_upper()
        # S estimate: exact interval check, independent of true value.
        head_error=(S-SHead.real).abs_upper()
        errOkay=bool(head_error < Es)
        pre=prefix_posdef(s+1,n)
        lpos=bool(Lu>0)
        gate=bool(h[s+1]*(Es-SHead.real)<4*(Lu**2)) if lpos else False
        rat=(h[s+1]*(Es-SHead.real)/(4*Lu**2)) if lpos else arb('1000')
        result=dict(s=s,n=n,alpha=str(alpha),a=str(v[n-1]),
            hprefix_posdef_Arb=pre,lu_positive_Arb=lpos,
            joint_error_covers_Arb=errOkay,
            corrected_source_identity_Arb=bool(source_discrep < arb('1e-100')),
            ratio=str(rat),gate_pass_Arb=gate,
            p_positive_Arb=bool(p>0),
            u_head=str(uh.real),u_error_bound=str(Eu),
            S_head=str(SHead.real),S_error_bound=str(Es),
            source_discrep_abs_upper=str(source_discrep),
            S_actual_error_abs_upper=str(head_error))
        out.append(result)
        print('ARB_GATE s',s,'n',n,'prefix',pre,'lower',lpos,
            'budget',gate,'ratio',str(rat)[:110],
            'joint_err',errOkay,'source_ok',result["corrected_source_identity_Arb"],
            flush=True)
output=P/f"C3_Arb_signed_gate_M{M}_n{nmax}_d{dps}.json"
output.write_text(json.dumps(dict(status="ARB_INTERVAL_VERIFICATION_NOT_LEAN_THEOREM",
 M=M,nmax=nmax,dps=dps,jet_boxes=N,rows=out),indent=2)+"\n")
print('ARB_GATE_SUMMARY',sum(x["gate_pass_Arb"] for x in out),'/',len(out))
print('ARB_GATE_FILE',output)
