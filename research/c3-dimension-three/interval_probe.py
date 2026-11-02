import re
from pathlib import Path
from fractions import Fraction as F
s=(Path(__file__).parent / "evidence/boxes.log").read_text()
pairs=re.findall(r"Box\.finite\s+\(?(-?\d+)\)?\s+\(?(-?\d+)\)?",s)
assert len(pairs)==13, len(pairs)
I=[(F(int(a),10**60),F(int(b),10**60)) for a,b in pairs]
c=I[:7]; h=I[7:]
def add(a,b): return a[0]+b[0],a[1]+b[1]
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
 p=[a[i]*b[j] for i in (0,1) for j in (0,1)]
 return min(p),max(p)
def div(a,b):
 assert b[0]>0 or b[1]<0
 return mul(a,(1/b[1],1/b[0]))
def show(name,a): print(name, float(a[0]),float(a[1]),"width",float(a[1]-a[0]))
for sector in (0,1):
 u,v,w,t=h[sector:sector+4]
 D=sub(mul(u,w),mul(v,v))
 v0=div(sub(mul(v,t),mul(w,w)),D)
 v1=div(sub(mul(v,w),mul(u,t)),D)
 ratio=div(c[1],c[0]); r2=div(c[2],c[0])
 z1=sub(v1,ratio)
 z0=sub(sub(v0,mul(ratio,z1)),r2)
 print("sector",sector)
 for name,val in [("D",D),("v0",v0),("v1",v1),("z0",z0),("z1",z1)]:show(name,val)
 zero=(F(0),F(0)); one=(F(1),F(1)); z=[z0,z1,one]
 def scale(n,a):return mul((F(n),F(n)),a)
 def response(sector,k):
  return scale(-(k+1),c[k+1]) if sector else (scale(-k,c[k]) if k else zero)
 total=zero
 for i in range(3):
  for j in range(3):
   entry=zero
   for k in range(j+1):
    entry=add(entry,sub(mul(c[j-k],response(sector,i+k+1)),mul(response(sector,j-k),c[i+k+1])))
   total=add(total,mul(mul(z[i],z[j]),entry))
 show('coefficient kernel interval',total)
 assert total[0] > F(6,10**18), (sector, total)
