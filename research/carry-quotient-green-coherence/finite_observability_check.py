"""Finite integer regression of the original profile formulas; no moment input."""
from fractions import Fraction
import json

def profile(b,n):
    if b==2:return 1-int(n%2==0)-2*int(n%4==0)
    if b%2:return 1-b*int(n%b==0)
    return 1+int(n%(b//2)==0)-(b+2)*int(n%b==0)

def determinant(matrix):
    a=[[Fraction(x) for x in row] for row in matrix]
    det=Fraction(1)
    for k in range(len(a)):
        p=next((p for p in range(k,len(a)) if a[p][k]),None)
        if p is None:return Fraction(0)
        if p!=k:a[p],a[k]=a[k],a[p];det=-det
        pivot=a[k][k];det*=pivot
        for j in range(k,len(a)):a[k][j]/=pivot
        for i in range(k+1,len(a)):
            v=a[i][k]
            for j in range(k,len(a)):a[i][j]-=v*a[k][j]
    return det

def readout(b,a):return sum(a[n-1]*profile(b,n) for n in range(1,len(a)+1))

def reconstruct(a):
    n=len(a);total=readout(2*n+1,a);mass={}
    for d in range(n,1,-1):mass[d]=readout(2*d,a)-total+(2*d+2)*mass.get(2*d,0)
    mass[1]=total;out={}
    for d in range(n,0,-1):out[d]=mass[d]-sum(out[k] for k in range(2*d,n+1,d))
    return [out[d] for d in range(1,n+1)]

rows=[]
for n in [1,2,3,4,6,12,24,32]:
    cameras=[2*n+1]+list(range(4,2*n+1,2))
    matrix=[[profile(b,k) for k in range(1,n+1)] for b in cameras]
    det=determinant(matrix)
    assert det==1,(n,det)
    for quadrature in range(2):
        a=[Fraction((-1)**(k+quadrature)*(k*k+quadrature+1),k+1) for k in range(1,n+1)]
        assert reconstruct(a)==a
    rows.append({'N':n,'cameras':cameras,'determinant':str(det),'two_rational_quadratures_recovered':True})
print(json.dumps({'status':'PASS_FINITE_REGRESSION','not_a_canonical_moment_or_infinite_completion_test':True,'checks':rows},indent=2))
