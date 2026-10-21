#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Auditoria numerica do operador finito CANONICO a partir dos momentos.

Sem tabela de zeros e sem theta. Reproduz, via xi, a mesma caracteristica
completada do pipeline geometricamente sintetizado, conforme identidade
formal de prime-depth e auditoria historica do repositorio 'momentos'.

Ordem: xi(t) -> phi_n=[t^(2n)]xi(t) -> h_n=[u^n](-Phi'/Phi)
       -> G=(h_{i+j}), K=(h_{i+j+1})
       -> G=L L^T -> J=L^-1 K L^-T -> T=J^-1/2.

Cholesky faz certificacao de positividade FINITA; NAO e a fonte dos h_n.
Nao prova positividade de todas as ordens nem uma gramizacao nativa all-order.
"""
import argparse
import json
from pathlib import Path
from time import perf_counter
import mpmath as mp


def xi_height(t):
    s = mp.mpf('0.5') + 1j*t
    return mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)


def cauchy_even_coefficients(count,nodes,radius):
    phases=[mp.exp(2j*mp.pi*j/nodes) for j in range(nodes)]
    vals=[xi_height(radius*z) for z in phases]
    return [mp.re(mp.fsum(vals[j]/phases[j]**(2*n) for j in range(nodes)) / nodes /radius**(2*n)) for n in range(count)]


def canonical_moments(c):
    h=[]
    for n in range(len(c)-1):
        h.append((-(n+1)*c[n+1]-mp.fsum(h[k]*c[n-k] for k in range(n)))/c[0])
    return h


def hankel(h,N,shift=0):
    return mp.matrix([[h[i+j+shift] for j in range(N)] for i in range(N)])


def max_abs(M):
    return max(abs(M[i,j]) for i in range(M.rows) for j in range(M.cols))


def fmt(M,digits=7):
    return '\n'.join('[ '+ ' '.join(f'{mp.nstr(M[i,j],digits):>17}' for j in range(M.cols))+' ]' for i in range(M.rows))


def nums(xs):
    return [mp.nstr(x,28) for x in xs]


def test(N,dps,nodes,radius,check_nodes=0):
    mp.mp.dps=dps
    radius=mp.mpf(radius)
    print(f'Momentos (sem theta/zetazero): N={N} dps={dps} nodes={nodes} raio={radius}',flush=True)
    start=perf_counter()
    coeff=cauchy_even_coefficients(2*N+1,nodes,radius)
    h=canonical_moments(coeff)
    print(f'Momentos obtidos em {perf_counter()-start:.1f}s',flush=True)
    if check_nodes:
        hc=canonical_moments(cauchy_even_coefficients(2*N+1,check_nodes,radius+1))
        e=max(abs((h[i]-hc[i])/h[i]) for i in range(2*N))
        print('Erro relativo maximo verificacao independente:',mp.nstr(e,5),flush=True)
    else:e=None
    G=hankel(h,N,0)
    K=hankel(h,N,1)
    L=mp.cholesky(G)
    Lk=mp.cholesky(K)
    B=L**-1
    J=B*K*B.T
    eig,U=mp.eigsy(J)
    if not all(eig[i]>0 for i in range(N)):
        raise AssertionError('Autovalor nao positivo em J')
    heights=[eig[i]**(-mp.mpf('0.5')) for i in range(N)]
    T=U*mp.diag(heights)*U.T
    checks={
        'G_LLt_maxerr':max_abs(G-L*L.T),
        'K_LkLkT_maxerr':max_abs(K-Lk*Lk.T),
        'whitening_maxerr':max_abs(B*G*B.T-mp.eye(N)),
        'J_symmetry_maxerr':max_abs(J-J.T),
        'T_symmetry_maxerr':max_abs(T-T.T),
        'T2_Jinv_maxerr':max_abs(T*T-J**-1),
        'TJT_identity_maxerr':max_abs(T*J*T-mp.eye(N)),
        'J_nontridiagonal_maxabs':max([abs(J[i,j]) for i in range(N) for j in range(N) if abs(i-j)>1] or [mp.mpf(0)]),
        'canon_recurrence_maxerr':max(abs(mp.fsum(h[k]*coeff[n-k] for k in range(n+1))+(n+1)*coeff[n+1]) for n in range(2*N)),
    }
    print('h_n =',', '.join(mp.nstr(x,12) for x in h[:min(8,len(h))]))
    for label,M in [('G Hankel',G),('K Hankel deslocada',K),('L Cholesky de G',L),('J Jacobi',J),('T alturas',T)]:
        print('\n'+label+':\n'+fmt(M))
    print('\nAutovalores J:',[mp.nstr(x,14) for x in eig])
    print('Alturas finitas (ordenadas):',sorted([mp.nstr(x,13) for x in heights],key=lambda x:mp.mpf(x)))
    print('Todos os pivos G,K positivos:',all(L[i,i]>0 and Lk[i,i]>0 for i in range(N)))
    print('Residuos:')
    for k,v in checks.items():print(' ',k,mp.nstr(v,7))
    # teste de quadrados para x arbitrario
    x=mp.matrix([mp.mpf(v) for v in [1,-2,3,-1,2,-3,4,-5][:N]])
    lhs=(x.T*G*x)[0]
    rhs=sum((L.T*x)[i]**2 for i in range(N))
    print('x^T G x=',mp.nstr(lhs,20),' SOS=',mp.nstr(rhs,20),' |delta|=',mp.nstr(abs(lhs-rhs),6))
    def matrix_json(M):return [[mp.nstr(M[i,j],48) for j in range(M.cols)] for i in range(M.rows)]
    result={'N':N,'precision_decimal':dps,'nodes':nodes,'radius':str(radius),'momentos':nums(h),
            'matrizes':{'G':matrix_json(G),'K':matrix_json(K),'L':matrix_json(L),'J':matrix_json(J),'T':matrix_json(T)},
            'eigenvalues_J':nums(eig),'finite_heights':nums(heights),'residuos':{k:mp.nstr(v,18) for k,v in checks.items()},
            'crosscheck_relerr':mp.nstr(e,15) if e is not None else None,
            'sos':{'x':nums(x),'quadratic':mp.nstr(lhs,32),'sum_of_squares':mp.nstr(rhs,32)},
            'scope':'FINITE_NUMERICAL_CERTIFICATE_NOT_ALL_ORDER_PROOF'}
    p=Path('/mnt/data/operador_finito_canonico_resultados.json')
    p.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--N',type=int,default=4)
    parser.add_argument('--dps',type=int,default=90)
    parser.add_argument('--nodes',type=int,default=128)
    parser.add_argument('--radius',type=str,default='3')
    parser.add_argument('--check-nodes',type=int,default=0)
    a=parser.parse_args()
    if a.N<2 or a.N>8:parser.error('2 <= N <= 8')
    test(a.N,a.dps,a.nodes,a.radius,a.check_nodes)
