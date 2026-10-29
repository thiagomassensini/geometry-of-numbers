#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial, comb

def A(m):return F((m+1)*(m+2),2)
def V(m):return F((m+1)*(m+2)*(2*m+3),12)
def lam(m,n):return V(m)+V(n)+(A(m)-A(n))**2/2

def double(m,n,d):
    s=sum((F((-1)**(m+n-i-j)*comb(m,i)*comb(n,j)*((i+1)**d+(j+1)**d),i+j+2)
      for i in range(m+1) for j in range(n+1)),F())
    return s/factorial(m)/factorial(n)
def centered(m,n,d):
    N=m+n+2
    return -sum(((-1)**j*comb(N,j)*(j-(n+1))**(d+1) for j in range(N+1)))/factorial(N)

def stirling(x,k):
    row=[1]+[0]*k
    for _ in range(x):
        row=[0]+[q*row[q]+row[q-1] for q in range(1,k+1)]
    return row[k]
for m in range(1,18,2):
    for n in range(1,18,2):
        N=m+n+2
        for d in (N-1,N+1): assert double(m,n,d)==centered(m,n,d),(m,n,d)
        assert centered(m,n,N-1)==-1
        s2=stirling(N+2,N)
        candidate=F((N+2)*(N+1),2)*(n+1)**2-(N+2)*(n+1)*F(N*(N+1),2)+s2
        assert candidate==lam(m,n)
        assert centered(m,n,N+1)==-candidate
for m in range(1,10,2):
    for n in range(1,10,2):
        for d in range(1,17,2):
            assert double(m,n,d)==centered(m,n,d),(m,n,d)
print('PASS: 81 pares ímpares nas duas camadas; 200 controles de expoentes ímpares adicionais; Stirling coincide com Lambda.')
print('Controle exato finito, não uma prova Lean para ordens arbitrárias.')
