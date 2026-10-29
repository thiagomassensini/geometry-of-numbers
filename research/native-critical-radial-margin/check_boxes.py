from fractions import Fraction
from math import factorial
import re
from pathlib import Path
S=10**60
text=(Path(__file__).resolve().parents[1] / 'material-integral-certificate/PivotFromIntegral.lean').read_text()
raw=text.split('def momentInputTable',1)[1].split('def momentInputBox',1)[0]
boxes=[tuple(map(int,x)) for x in re.findall(r'Box\.finite \((\d+)\) \((\d+)\)',raw)]
assert len(boxes)==10

def point(x):return (x*S,x*S)
def neg(a):return (-a[1],-a[0])
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):
 p=[x*y for x in a for y in b];return (min(p)//S, -((-max(p))//S))
def inv(a):
 if a[0]<=0:raise ValueError('denominator box not positive '+str(tuple(float(Fraction(z,S)) for z in a)))
 return ((S*S)//a[1], -((-(S*S))//a[0]))
def div(a,b):return mul(a,inv(b))
def rat(a,b): return div(point(a),point(b))
def desc(a):return (f'{float(Fraction(a[0],S)):.6e}', f'{float(Fraction(a[1],S)):.6e}',f'width={float(Fraction(a[1]-a[0],S)):.3g}')
cs=[]
for n in range(9):
 if n==0: c=add(rat(1,2),neg(div(boxes[0],point(4))))
 else:c=mul(point((-1)**n),add(div(boxes[n-1],point(factorial(2*n-2))),neg(div(boxes[n],point(4*factorial(2*n))))))
 cs.append(c)
h=[]
for n in range(8):
 q=point(0)
 for k in range(n):q=add(q,mul(h[k],cs[n-k]))
 h.append(div(add(mul(point(-(n+1)),cs[n+1]),neg(q)),cs[0]))
 print('h',n,desc(h[n]))
def sub(a,b):return add(a,neg(b))
def det3(a):
 return add(sub(mul(a[0][0],sub(mul(a[1][1],a[2][2]),mul(a[1][2],a[2][1]))),mul(a[0][1],sub(mul(a[1][0],a[2][2]),mul(a[1][2],a[2][0])))),mul(a[0][2],sub(mul(a[1][0],a[2][1]),mul(a[1][1],a[2][0]))))
a=[[h[i+j+1] for j in range(3)] for i in range(3)]
b=[h[i+4] for i in range(3)]
det=det3(a); print('det old block',desc(det))
try:
 xs=[]
 for j in range(3):
  m=[[b[i] if k==j else a[i][k] for k in range(3)] for i in range(3)]
  xs.append(neg(div(det3(m),det))); print('c',j,desc(xs[-1]))
 energy=point(0); coeff=xs+[point(1)]
 for i in range(4):
  for j in range(4): energy=add(energy,mul(mul(coeff[i],coeff[j]),h[i+j+1]))
 print('full critical energy',desc(energy))
except ValueError as e:print('BLOCKED',e)
print('rounded source boxes')
for n,z in enumerate(h):
 exp=[20,21,22,23,24,25,26,28][n]
 unit=10**(60-exp)
 lo=z[0]//unit*unit; hi=-((-z[1])//unit)*unit
 print(n,lo,hi, 'exp',exp)
h=[(z[0]//10**(60-e)*10**(60-e),-((-z[1])//10**(60-e))*10**(60-e)) for e,z in zip([20,21,22,23,24,25,26,28],h)]
a=[[h[i+j+1] for j in range(3)] for i in range(3)]; b=[h[i+4] for i in range(3)]; det=det3(a)
xs=[]
for j in range(3):
 m=[[b[i] if k==j else a[i][k] for k in range(3)] for i in range(3)]
 xs.append(neg(div(det3(m),det)))
energy=point(0); coeff=xs+[point(1)]
for i in range(4):
 for j in range(4):energy=add(energy,mul(mul(coeff[i],coeff[j]),h[i+j+1]))
print('rounded critical energy',desc(energy))
print('coefficient boxes')
for i,(z,e) in enumerate(zip(xs,[15,13,10])):
 unit=10**(60-e); lo=z[0]//unit*unit; hi=-((-z[1])//unit)*unit
 print(i,lo,hi,desc((lo,hi)))
xs=[(z[0]//10**(60-e)*10**(60-e),-((-z[1])//10**(60-e))*10**(60-e)) for e,z in zip([15,13,10],xs)]
energy=point(0); coeff=xs+[point(1)]
for i in range(4):
 for j in range(4):energy=add(energy,mul(mul(coeff[i],coeff[j]),h[i+j+1]))
print('rounded coeff energy',desc(energy))
