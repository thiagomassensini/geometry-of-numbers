#!/usr/bin/env python3
"""Mixed native u/B/p with accelerated C3/64 TFVD boundaries.
NUMERICAL DIAGNOSTIC ONLY; neither native all-order signs nor Lean intervals.
The C3 bracket supplies head+boundary; xi(1/2) via an equivalent classical
formula initializes c0 ONLY for high-precision numeric cross-check.
"""
import json,sys
from pathlib import Path
import mpmath as mp
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
mp.mp.dps=115
HOME=Path(__file__).resolve().parent.parent / "evidence"
data=json.load(open("/home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json"))
h=[mp.mpf(x[:410]) for x in data["moments"][:80]]
M=int(sys.argv[2]) if len(sys.argv)>2 else 64
nmax=int(sys.argv[1]) if len(sys.argv)>1 else 4
maxdim=nmax+2
maxc=2*maxdim
highest=2*maxc
s0=mp.mpf("0.5")
c0=s0*(s0-1)*mp.pi**(-s0/2)*mp.gamma(s0/2)*mp.zeta(s0)/2
c=[c0]
for j in range(maxc):
    c.append(-mp.fsum(h[k]*c[j-k] for k in range(j+1))/(j+1))
def multiplier(w):
    ss=mp.mpf("0.5")+1j*w
    return ss*(ss-1)*mp.exp(-ss*mp.log(mp.pi)/2)*mp.gamma(ss/2)/2 / (1-mp.exp((1-ss)*mp.log(3)))
print("Computing C3 height jets",highest,flush=True)
a=mp.taylor(multiplier,0,highest)
prefix=[mp.mpc(1)]+[mp.mpc(0)]*highest
for mm in range(M):
    for addr,weight in ((3*mm+2,1),(3*mm+3,-2),(3*mm+4,1)):
        log=mp.log(addr);amp=mp.exp(-log/2)
        for q in range(highest+1):
            prefix[q]+=weight*amp*(-1j*log)**q/mp.factorial(q)
head=[mp.fsum(a[k]*prefix[2*j-k] for k in range(2*j+1)) for j in range(maxc+1)]
weights=[mp.mpf(k)/729 for k in (728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1)]
boundary=[mp.fsum(weights[k]*mp.exp(-mp.log(3*M+2+k)/2)*
  (-1j*mp.log(3*M+2+k))**q/mp.factorial(q) for k in range(12)) for q in range(highest+1)]
adj=[head[j]+mp.fsum(a[k]*boundary[2*j-k] for k in range(2*j+1)) for j in range(len(head))]
tail=[c[j]-adj[j] for j in range(len(head))]
print("c0",mp.nstr(c0,24),"tail first", [mp.nstr(abs(t),6) for t in tail[:8]],flush=True)

def source_lift(x):
    N=len(x);z=[mp.mpf(0)]*N
    for i in range(N-1,-1,-1):
        z[i]=(x[i]-mp.fsum(c[j-i]*z[j] for j in range(i+1,N)))/c[0]
    return z
def response(C,b,k):
    return -(k+1)*C[k+1] if b else (-k*C[k] if k else mp.mpc(0))
def cb(C,D,b,i,j):
    return mp.fsum(D[j-k]*response(C,b,i+k+1)-response(C,b,j-k)*D[i+k+1] for k in range(j+1))
def budgetentry(C,D,b,i,j):
    return mp.fsum(abs(D[j-k])*abs(response(C,b,i+k+1))+
      abs(response(C,b,j-k))*abs(D[i+k+1]) for k in range(j+1))
def term(C,D,b,zx,zy):
    return mp.fsum(zx[i]*zy[j]*cb(C,D,b,i,j) for i in range(len(zx)) for j in range(len(zy)))
def budget(C,D,b,zx,zy):
    return mp.fsum(abs(zx[i])*abs(zy[j])*budgetentry(C,D,b,i,j) for i in range(len(zx)) for j in range(len(zy)))
def comp(name,sector,x,y,truth):
    pad=sector=="shift2"
    b=True if sector=="odd" else False
    if pad:
        x=[mp.mpf(0)]+list(x);y=[mp.mpf(0)]+list(y)
    zx,zy=source_lift(x),source_lift(y)
    terms=[term(adj,adj,b,zx,zy),term(adj,tail,b,zx,zy),
           term(tail,adj,b,zx,zy),term(tail,tail,b,zx,zy)]
    E=budget(adj,tail,b,zx,zy)+budget(tail,adj,b,zx,zy)+budget(tail,tail,b,zx,zy)
    val=mp.fsum(terms)
    delta=abs(val-truth)
    result=dict(name=name,chart=sector,dim=len(x),true=mp.nstr(truth,22),
        HH_real=mp.nstr(terms[0].real,22), HH_imag=mp.nstr(terms[0].imag,9),
        HT=mp.nstr(terms[1],13),TH=mp.nstr(terms[2],13),
        TT=mp.nstr(terms[3],13),E=mp.nstr(E,22),
        E_rel=mp.nstr(E/abs(truth),15) if truth else "inf",
        crosscheck=mp.nstr(delta,10),
        source_lift_norm_x=mp.nstr(sum(map(abs,zx)),15),
        source_lift_norm_y=mp.nstr(sum(map(abs,zy)),15),
        lower=mp.nstr(max(0,abs(terms[0].real)-E),22),
        upper=mp.nstr(abs(terms[0].real)+E,22))
    print("pair",name,sector,"dim",len(x),"true",mp.nstr(truth,8),
      "head",mp.nstr(terms[0].real,8),"E",mp.nstr(E,8),
      "ratio",mp.nstr(E/abs(truth),8) if truth else "inf",
      "cross",mp.nstr(delta,5),flush=True)
    if delta>mp.mpf("1e-70"):
        print("LARGE CROSS-CHECK",name,mp.nstr(delta,25),flush=True)
    return result

rows=[]
for s in (0,1):
    for n in range(1,nmax+1):
        A=mp.matrix([[h[s+i+j] for j in range(n)] for i in range(n)])
        q=mp.matrix([h[s+n+i] for i in range(n)])
        xsol=mp.lu_solve(A,q)
        v=[-xsol[i] for i in range(n)]+[mp.mpf(1)]
        r=[mp.mpf(i-n)*v[i] for i in range(n)]
        p=h[s+2*n]-(q.T*xsol)[0]
        B=mp.fsum(v[i]*v[j]*h[s+1+i+j] for i in range(n+1) for j in range(n+1))
        u=mp.fsum(r[i]*h[s+1+i] for i in range(n))
        R=mp.fsum(r[i]*r[j]*h[s+1+i+j] for i in range(n) for j in range(n))
        # u uses the shifted opposite parity; B uses same shift but v length n+1
        shift="odd" if s==0 else "shift2"
        unit=[mp.mpf(1)]+[mp.mpf(0)]*(n-1)
        U=comp("u",shift,r,unit,u)
        BV=comp("B",shift,v,v,B)
        PV=comp("p","even" if s==0 else "odd",v,v,p)
        alpha=(2*n+s+1)*(4*n+2*s+3);beta=16*n+8*s+6
        lu=mp.mpf(U["lower"])
        budget_approx=(h[s+1]*(alpha*mp.mpf(BV["upper"])+beta*abs(v[n-1])*mp.mpf(PV["upper"])))/(4*lu*lu) if lu>0 else mp.inf
        budget_exact=(h[s+1]*(alpha*abs(B)+beta*abs(v[n-1]*p)))/(4*u*u)
        row=dict(s=s,n=n,u=U,B=BV,p=PV,R=mp.nstr(R,22),
            alpha=alpha,beta=beta,a=mp.nstr(v[n-1],15),
            exact_gate_ratio=mp.nstr(budget_exact,18),
            TFVD_gate_ratio=mp.nstr(budget_approx,18),
            TFVD_gate_pass=bool(budget_approx<1))
        rows.append(row)
        print("GATE",s,n,"ideal",mp.nstr(budget_exact,9),
          "c3_upper_ratio",mp.nstr(budget_approx,9), "pass",budget_approx<1,flush=True)
output=HOME/f"c3_mixed_u_B_p_M{M}_n{nmax}_numeric.json"
output.write_text(json.dumps(dict(status="NUMERICAL_DIAGNOSTIC_ONLY_NOT_LEAN_CERTIFICATE",
   M=M,precision=mp.mp.dps,nmax=nmax,
   c0_initialized_from_classical_identity_numeric_only=True,
   original_C3_head_and_fixed_boundary=True,
   complex_bilinear_two_vector_kernel=True,rows=rows),indent=2)+"\n")
print("RESULTS",output)

exec((Path(__file__).resolve().parent/"joint_S_tail_probe.py").read_text())
