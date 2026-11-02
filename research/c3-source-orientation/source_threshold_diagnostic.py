#!/usr/bin/env python3
"""Uncertified diagnostic: original C3/256 head and its source Schur thresholds.
No theta, zeta, zeros, heights, or moment-table input. Uses mpmath only.
"""
from mpmath import mp

mp.dps = 70
M, degree = 256, 12

def multiplier(w):
    s = mp.mpf('0.5') + 1j*w
    xi = s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/2
    return xi/(1-mp.exp((1-s)*mp.log(3)))

a = mp.taylor(multiplier, 0, degree)
prefix = [mp.mpc(1)] + [mp.mpc(0)]*degree
for m in range(M):
    for address, weight in ((3*m+2, 1), (3*m+3, -2), (3*m+4, 1)):
        logn = mp.log(address)
        amp = mp.exp(-logn/2)
        for k in range(degree+1):
            prefix[k] += weight*amp*(-1j*logn)**k/mp.factorial(k)
weights = [mp.mpf(k)/729 for k in (728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1)]
boundary = [mp.fsum(weights[j]*mp.exp(-mp.log(3*M+2+j)/2)*
              (-1j*mp.log(3*M+2+j))**k/mp.factorial(k)
              for j in range(len(weights))) for k in range(degree+1)]
c = [mp.fsum(a[k]*(prefix[2*j-k]+boundary[2*j-k]) for k in range(2*j+1))
     for j in range(7)]
for sector in (0, 1):
    def response(k):
        return -(k+1)*c[k+1] if sector else (-k*c[k] if k else 0)
    B = mp.matrix([[mp.fsum(c[j-k]*response(i+k+1)-response(j-k)*c[i+k+1]
                              for k in range(j+1)) for j in range(3)] for i in range(3)])
    A = mp.matrix([[B[i,j] for j in range(2)] for i in range(2)])
    cross = mp.matrix([B[i,2] for i in range(2)])
    schur = B[2,2] - (cross.T*mp.lu_solve(A,cross))[0]
    index, factor = ((6, 6) if sector else (5, 5))
    threshold = c[index] + schur/(factor*c[0])
    print(f'setor={sector} indice={index} coeficiente={mp.nstr(c[index], 25)}')
    print(f'limiar={mp.nstr(threshold, 25)} diferenca={mp.nstr(threshold-c[index], 20)}')
    print(f'schur_cabeca={mp.nstr(schur, 20)}')
print('status=diagnostico_nao_intervalar; cabeca_finita_nao_e_a_fonte_completa')
