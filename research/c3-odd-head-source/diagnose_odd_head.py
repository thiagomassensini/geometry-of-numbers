from mpmath import mp
mp.dps=70
N=8

def multiplier(w):
 s=mp.mpf("0.5")+1j*w
 return s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/(2*(1-mp.exp((1-s)*mp.log(3))))
a=mp.taylor(multiplier,0,N)
p=[mp.mpc(1)]+[mp.mpc(0)]*N
for M in range(64):
 for addr,weight in ((3*M+2,1),(3*M+3,-2),(3*M+4,1)):
  ell=mp.log(addr)
  for q in range(N+1): p[q]+=weight*mp.exp(-ell/2)*(-1j*ell)**q/mp.factorial(q)
weights=[mp.mpf(k)/729 for k in (728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1)]
for j in range(12):
 ell=mp.log(194+j)
 for q in range(N+1): p[q]+=weights[j]*mp.exp(-ell/2)*(-1j*ell)**q/mp.factorial(q)
H=[mp.fsum(a[k]*p[2*j-k] for k in range(2*j+1)) for j in range(5)]
A=H[1]**2-2*H[0]*H[2]
B=H[1]*H[2]-3*H[0]*H[3]
D=2*H[2]**2-2*H[1]*H[3]-4*H[0]*H[4]
mat=mp.matrix([[A.real,B.real],[B.real,D.real]])
lam=mp.eigsy(mat)[0][0]
rho=[96*mp.factorial(14)/(729*mp.mpf(191)**13)*4**(2*j) for j in range(5)]
# Exact coefficient envelope for the three ordered error kernels, x,y both in l2 unit ball.
# Bound each |x_i|, |y_j| by 1, using the generic coefficientBudget of PR 70.
def response_bound(v,k): return (k+1)*v[k+1]
def budget(v,w):
 return mp.fsum(w[j-k]*response_bound(v,i+k+1)+response_bound(v,j-k)*w[i+k+1] for i in range(2) for j in range(2) for k in range(j+1))
habs=[abs(z) for z in H]
E=budget(habs,rho)+budget(rho,habs)+budget(rho,rho)
print("H",[mp.nstr(z,20) for z in H])
print("head_entries",*[mp.nstr(x,20) for x in [A.real,B.real,D.real]])
print("head_eigen_min",mp.nstr(lam,20))
print("tail_envelopes",[mp.nstr(x,12) for x in rho])
print("error_l2_upper",mp.nstr(E,20),"ratio",mp.nstr(E/lam,14),"passes",lam>E)
print("NUMERICAL_DIAGNOSTIC; gamma taylor and head are not rational certified")
