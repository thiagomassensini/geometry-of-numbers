"""Simulação racional de condicionamento: dados ilustrativos, não certificado."""
from fractions import Fraction as F
c=[F(x) for x in ['0.49712077818831410991277373968539752','-0.011485972157572718767624938248816062','0.00012345201807031800689034579149729634','-0.00000083235548138552707200475872782457979','0.0000000039922265513441371747252703823393767','-0.000000000014616025760110960862411857883057739','0.000000000000042745400455368449576641221192081631']]
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 p=[a[i]*b[j] for i in (0,1) for j in (0,1)];return min(p),max(p)
def div(a,b):
 assert b[0]>0 or b[1]<0,(float(b[0]),float(b[1]));return mul(a,(1/b[1],1/b[0]))
def scalar(x):return F(x),F(x)
def scale(x,a):return mul(scalar(x),a)
print("status=diagnostico; referencias aproximadas; c4_c5_c6_pontuais_nao_certificados")
for tol in [F(1,10**12),F(1,10**14),F(1,10**15),F(1,10**16),F(1,10**17),F(1,10**18)]:
 C=[(x-tol,x+tol) if i<4 else (x,x) for i,x in enumerate(c)]
 print('tolerance',float(tol))
 for s in [0,1]:
  def rr(k):return scale(-(k+1),C[k+1]) if s else (scale(-k,C[k]) if k else scalar(0))
  def sumI(xs):
   v=scalar(0)
   for x in xs:v=add(v,x)
   return v
  B=[[sumI([sub(mul(C[j-k],rr(i+k+1)),mul(rr(j-k),C[i+k+1])) for k in range(j+1)]) for i in range(3)] for j in range(3)]
  A,Bb,D=B[0][0],B[0][1],B[1][1]; U,V=B[0][2],B[1][2]
  det=sub(mul(A,D),mul(Bb,Bb))
  correction=div(add(sub(mul(D,mul(U,U)),scale(2,mul(Bb,mul(U,V)))),mul(A,mul(V,V))),det)
  margin=sub(B[2][2],correction)
  print(s,'schur interval',float(margin[0]),float(margin[1]))
