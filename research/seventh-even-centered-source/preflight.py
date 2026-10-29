import argparse, csv, json, hashlib, re, math
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
import mpmath as mp

ap=argparse.ArgumentParser(description="Checkpoint LU/QR canaries and literal integer-box preflight; NOT a theta proof")
ap.add_argument('--checkpoint-root',type=Path,required=True,help='auditoria_corrected_vs_canonical directory')
ap.add_argument('--source-root',type=Path,required=True,help='material-integral-certificate directory')
ap.add_argument('--normalized-coefficients',type=Path,required=True,help='JSON containing only normalized_completed_c values')
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args()

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def fmt(x): return mp.nstr(x,55)
data={}
for stage in ['A','B']:
 p=a.checkpoint_root/f'stage_{stage}'/'moments.csv'
 rows=list(csv.DictReader(p.open()))
 vals=[r['canonical_h'] for r in rows]
 results=[]
 for dps in [40,80,160,300]:
  with mp.workdps(dps):
   h=list(map(mp.mpf,vals[:14]))
   for s in [0,1]:
    for n in range(1,7):
     A=mp.matrix([[h[i+j+s] for j in range(n)] for i in range(n)])
     b=mp.matrix([h[i+n+s] for i in range(n)]); c=h[2*n+s]
     x=mp.lu_solve(A,b)
     qr_error=None
     try:y,_=mp.qr_solve(A,b)
     except ValueError as e:y=None;qr_error=str(e)
     cross=mp.fdot(b,x); sigma=c-cross
     den=abs(c)+mp.fsum(abs(b[i]*x[i]) for i in range(n))
     residual=A*x-b
     with mp.workdps(max(400,dps+80)):
      av=mp.matrix([[mp.mpf(vals[i+j+s]) for j in range(n)] for i in range(n)])
      bv=mp.matrix([mp.mpf(vals[i+n+s]) for i in range(n)])
      verification_residual=av*x-bv
      verified_residual=[fmt(v) for v in verification_residual]
      verified_residual_inf=fmt(mp.norm(verification_residual,mp.inf))
     results.append(dict(s=s,n=n,dps=dps,c=fmt(c),bt_x=fmt(cross),sigma=fmt(sigma),
       relative=fmt(sigma/den),cancellation_digits=fmt(-mp.log10(abs(sigma/den))),
       Ax_minus_b=[fmt(v) for v in residual],residual_inf=fmt(mp.norm(residual,mp.inf)),
       higher_precision_Ax_minus_b=verified_residual,higher_precision_residual_inf=verified_residual_inf,
       backward_error=fmt(mp.norm(residual,mp.inf)/(mp.mnorm(A,mp.inf)*mp.norm(x,mp.inf)+mp.norm(b,mp.inf))),
       qr_sigma=fmt(c-mp.fdot(b,y)) if y is not None else None,qr_error=qr_error,route_difference=fmt(mp.fdot(b,x-y)) if y is not None else None))
 data[stage]=dict(path=str(p),sha256=sha(p),rows=len(rows),saved_dps={'A':500,'B':2000}[stage],results=results)
with mp.workdps(300):
 h=[mp.mpf(r['canonical_h']) for r in csv.DictReader((a.checkpoint_root/'stage_A/moments.csv').open())][:14]
 cp=a.normalized_coefficients; c=list(map(mp.mpf,json.loads(cp.read_text())['values']))
 A=mp.matrix([[h[i+j] for j in range(6)] for i in range(6)]); b=mp.matrix([h[i+6] for i in range(6)])
 feedback=mp.fdot(b,mp.lu_solve(A,b))
 C=-(mp.fsum(h[k]*c[12-k] for k in range(12))+c[0]*feedback)/13
 data['diagnostic_c0_1']=dict(c13=fmt(c[13]),ceiling=fmt(C),difference=fmt(C-c[13]),pivot=fmt(13*(C-c[13])),coefficient_file_sha256=sha(cp))

# Literal integer-box mirror for the unchanged Lean enclosure program.
S=10**60
def point(n): return (n*S,n*S)
def rat(a,b): return (a*S//b,-((-a*S)//b))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[1],-a[0])
def mul(a,b):
 v=[x*y for x in a for y in b]; return (min(v)//S,-((-max(v))//S))
def inv(a):
 if a[0]<=0: raise ValueError('nonpositive divisor')
 return (S*S//a[1],-((-S*S)//a[0]))
def div(a,b): return mul(a,inv(b))
def power(a,n):
 if n==0:return point(1)
 assert a[0]>=0
 return (a[0]**n//S**(n-1),-((-a[1]**n)//S**(n-1)))
def scale(a,w): return (a[0]*w.numerator//w.denominator,-((-a[1]*w.numerator)//w.denominator))
def boxes(s):return [(int(a),int(b)) for a,b in re.findall(r'(?:Box\.)?finite\s+\((-?\d+)\)\s+\((-?\d+)\)',s)]
def table(path,name):
 s=path.read_text().split('def '+name+' :')[1].split('\ndef ')[0]
 return [boxes(s.split(f'| {m} => ')[1].split('\n  | ')[0]) for m in range(3)]
cache=a.source_root/'QuadratureCacheData.lean'; nodes=a.source_root/'NodeCacheData.lean'
co=table(cache,'quadratureCoefficientData'); er=table(cache,'quadratureErrorData')
ar=table(nodes,'argumentNodeData'); mo=table(nodes,'modeNodeData'); counts=[96,64,48]
@lru_cache(None)
def weight(p,r,j): return sum((Q(math.comb(p,k)*j**(p-k),k+r+1) for k in range(p+1)),Q())/64**(p+r+1)
@lru_cache(None)
def theta(p):
 total=point(0); breakdown=[]
 for m,count in enumerate(counts):
  v=point(0); taylor_width=0; coeff_width=0
  for j in range(count):
   val=point(0)
   for r in range(16):val=add(val,scale(co[m][j*16+r],weight(p,r,j)))
   e=scale(er[m][j],weight(p,16,j))
   v=add(v,(val[0]-e[1],val[1]+e[1]));taylor_width+=2*e[1];coeff_width+=val[1]-val[0]
  L=rat(count,64)
  decay=add(add(mul(point(2),ar[m][count]),neg(rat(1,2))),neg(div(point(p),L)))
  tail=div(mul(mo[m][count],power(L,p)),decay)
  total=add(total,add(v,(0,tail[1])))
  breakdown.append(dict(m=m,coefficient_width=coeff_width,taylor_width=taylor_width,retained_tail_upper=tail[1]))
 omitted=rat(math.factorial(p),10**20*95**(p+1))[1]
 return add(total,(0,omitted)),breakdown,omitted
def showbox(b):
 with mp.workdps(80):return dict(lo=fmt(mp.mpf(b[0])/S),hi=fmt(mp.mpf(b[1])/S),width=fmt(mp.mpf(b[1]-b[0])/S),integers=list(map(str,b)))
data['theta_boxes']={str(p):dict(**showbox(theta(p)[0]),breakdown=theta(p)[1],omitted_upper_integer=str(theta(p)[2])) for p in range(0,27,2)}
@lru_cache(None)
def cb(n):
 if n==0:return add(rat(1,2),neg(div(theta(0)[0],point(4))))
 if n==13:return neg(div(add(mul(point(2600),theta(24)[0]),neg(theta(26)[0])),point(4*math.factorial(26))))
 return mul(point((-1)**n),add(div(theta(2*n-2)[0],point(math.factorial(2*n-2))),neg(div(theta(2*n)[0],point(4*math.factorial(2*n))))))
@lru_cache(None)
def hb(n):
 v=point(0)
 for k in range(n):v=add(v,mul(hb(k),cb(n-k)))
 return div(add(mul(point(-n-1),cb(n+1)),neg(v)),cb(0))
@lru_cache(None)
def rem(r,i,j):
 if r==0:return hb(i+j)
 q=r-1; return add(rem(q,i,j),neg(div(mul(rem(q,i,q),rem(q,q,j)),rem(q,q,q))))
data['source_enclosures']={'c13':showbox(cb(13)),'h12':showbox(hb(12)),'seventh_even_pivot':showbox(rem(6,6,6)),'source_c0':showbox(cb(0))}
data['hashes']={str(p):sha(p) for p in [cache,nodes,a.source_root/'PivotFromIntegral.lean']}
a.output.write_text(json.dumps(data,indent=2)+'\n')
for stage in ['A','B']:
 for r in data[stage]['results']:
  if r['dps']==80 and r['n']==6:print(stage,{k:r[k] for k in ['s','sigma','c','bt_x','relative','cancellation_digits','residual_inf','route_difference']})
print(data['diagnostic_c0_1'])
print('I26',data['theta_boxes']['26'])
print('source_enclosures',data['source_enclosures'])

# Untrusted trial directions / fixed congruence witnesses, NEVER new moments.
def scale_signed(b,w):return scale(b,w) if w>=0 else neg(scale(b,-w))
def linear_moments(coeff):
 out=point(0)
 for k,w in enumerate(coeff):out=add(out,scale_signed(hb(k),w))
 return out
def gram_box(v,w):
 coeff=[Q(0)]*(len(v)+len(w))
 for i,a0 in enumerate(v):
  for j,b0 in enumerate(w):coeff[i+j]+=a0*b0
 return linear_moments(coeff)
with mp.workdps(150):
 h=[mp.mpf(r['canonical_h']) for r in csv.DictReader((a.checkpoint_root/'stage_A/moments.csv').open())][:14]
 scales=[10,10**4,10**7,10**10,10**13,10**16,10**20]
 cols=[]
 for j in range(7):
  if j==0:vals=[]
  else:
   A=mp.matrix([[h[i+k] for k in range(j)] for i in range(j)])
   b=mp.matrix([h[i+j] for i in range(j)])
   vals=list(-mp.lu_solve(A,b))
  cols.append([Q(mp.nstr(t*scales[j],40)) for t in vals]+[Q(scales[j])]+[Q(0)]*(6-j))
 # Evaluate literal box products as the Lean verifier will; all crossings.
 def gram_box_literal(v,w):
  out=point(0)
  for i in range(7):
   for j in range(7):
    out=add(out,mul(mul(rat(v[i].numerator,v[i].denominator),hb(i+j)),rat(w[j].numerator,w[j].denominator)))
  return out
 gram=[[gram_box_literal(v,w) for w in cols] for v in cols]
 @lru_cache(None)
 def transformed_rem(r,i,j):
  if r==0:return gram[i][j]
  q=r-1
  return add(transformed_rem(q,i,j),neg(div(mul(transformed_rem(q,i,q),transformed_rem(q,q,j)),transformed_rem(q,q,q))))
 pivots=[showbox(transformed_rem(j,j,j)) for j in range(7)]
 rows=[]
 for i in range(7):
  off=sum(max(abs(gram[i][j][0]),abs(gram[i][j][1])) for j in range(7) if j!=i)
  rows.append(showbox((gram[i][i][0]-off,gram[i][i][1]+off)))
 print('FIXED_TRIAL_TRANSFORMED_PIVOTS',pivots)
 print('MOMENTWIDTHS',[(k,showbox(hb(k))['width']) for k in range(13)])
 print('ORDERED_PIVOT_BOXES',[showbox(rem(k,k,k)) for k in range(7)])
 data['trial_preflight']={'selection':'Old-prefix LU solves only; 40 significant digit rational witnesses; diagonal powers of ten. No physical vectors or source parameters changed.',
  'witness_columns':[[str(x) for x in v] for v in cols],
  'gram_boxes':[[showbox(v) for v in row] for row in gram],
  'moment_boxes':[showbox(hb(k)) for k in range(13)],
  'pivot_boxes':pivots,'dominance_rows':rows}
 a.output.write_text(json.dumps(data,indent=2)+'\n')
# Execute after the common box program has built theta, cb and hb.
from fractions import Fraction as F
C=[F(sum(cb(j)),2*S) for j in range(14)]
H=[];D=[]
for n in range(13):
 H.append((-(n+1)*C[n+1]-sum(H[k]*C[n-k] for k in range(n)))/C[0])
 D.append([(-(n+1)*F(j==n+1)-sum(D[k][j]*C[n-k] for k in range(n))-sum(H[k]*F(j==n-k) for k in range(n+1)))/C[0] for j in range(14)])
E=[add(cb(j),neg(rat(C[j].numerator,C[j].denominator))) for j in range(14)]
Lin=[];U=[];T=[]
for n in range(13):
 l=point(0)
 for j in range(14):l=add(l,mul(rat(D[n][j].numerator,D[n][j].denominator),E[j]))
 Lin.append(l)
 u=point(0)
 for k in range(n):u=add(u,mul(U[k],cb(n-k)))
 for k in range(n+1):u=add(u,mul(Lin[k],E[n-k]))
 U.append(div(neg(u),cb(0)))
 T.append(add(add(rat(H[n].numerator,H[n].denominator),l),U[-1]))
print('CENTERED_H12',showbox(T[12]))
print('CENTERED_REMAINDER_H12',showbox(U[12]))
cols=data['trial_preflight']['witness_columns'];cols=[[F(z) for z in v] for v in cols]
def cg(v,w):
 out=point(0)
 for i in range(7):
  for j in range(7):out=add(out,mul(mul(rat(v[i].numerator,v[i].denominator),T[i+j]),rat(w[j].numerator,w[j].denominator)))
 return out
G=[[cg(v,w) for w in cols] for v in cols]
@lru_cache(None)
def cr(r,i,j):
 if r==0:return G[i][j]
 q=r-1;return add(cr(q,i,j),neg(div(mul(cr(q,i,q),cr(q,q,j)),cr(q,q,q))))
print('CENTERED_TRIAL_PIVOTS',[showbox(cr(k,k,k)) for k in range(7)])
data['centered_preflight']={'reference_coefficients':[str(z) for z in C],'reference_moments':[str(z) for z in H],
 'linear_coefficients':[[str(z) for z in row] for row in D],
 'error_boxes':[showbox(z) for z in E],'linear_boxes':[showbox(z) for z in Lin],'remainder_boxes':[showbox(z) for z in U],
 'moment_boxes':[showbox(z) for z in T],'gram_boxes':[[showbox(z) for z in row] for row in G],
 'pivot_boxes':[showbox(cr(k,k,k)) for k in range(7)]}
a.output.write_text(json.dumps(data,indent=2)+'\n')

# Extra outward padding bounds the cache-only rounding when an equivalent
# source coefficient formula is evaluated in a different exact order.
Tcompact=[(int(v['integers'][0])-10**8,int(v['integers'][1])+10**8)
          for v in data['centered_preflight']['moment_boxes']]
def compact_cg(v,w):
 out=point(0)
 for i in range(7):
  for j in range(7):out=add(out,mul(mul(rat(v[i].numerator,v[i].denominator),Tcompact[i+j]),rat(w[j].numerator,w[j].denominator)))
 return out
Gcompact=[[compact_cg(v,w) for w in cols] for v in cols]
@lru_cache(None)
def ccr(r,i,j):
 if r==0:return Gcompact[i][j]
 q=r-1;return add(ccr(q,i,j),neg(div(mul(ccr(q,i,q),ccr(q,q,j)),ccr(q,q,q))))
data['compact_centered_moment_boxes']=[showbox(z) for z in Tcompact]
data['compact_centered_gram_boxes']=[[showbox(z) for z in row] for row in Gcompact]
data['compact_centered_pivot_boxes']=[showbox(ccr(k,k,k)) for k in range(7)]
a.output.write_text(json.dumps(data,indent=2)+'\n')
print('PADDED_TRIAL_LAST',data['compact_centered_pivot_boxes'][-1])
