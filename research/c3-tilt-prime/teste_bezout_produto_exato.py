"""Auditoria simbolica independente da identidade de produto do kernel de Bezout.

Requer apenas sympy. Nao representa a caracteristica Carry; o exemplo
racional e um controle negativo de implicacoes puramente algebricas.
"""
import sympy as sp

u, v = sp.symbols('u v')
H = 1 - u + sp.Rational(1, 8)*u**2
C = 1 - u - u**2
T = sp.expand(C-H)
U = sp.cancel(C/H)


def kernel(f, shifted):
    # shifted=False: fonte A=-u*C' (setor falso/par no SourceBezout.lean)
    # shifted=True:  fonte A=-C'   (setor verdadeiro/impar)
    a = -sp.diff(f, u) * (1 if shifted else u)
    return sp.cancel((a*f.subs(u, v)-a.subs(u, v)*f)/(u-v))


def toeplitz(f, r=2):
    coeff = sp.series(f, u, 0, r).removeO().expand()
    seq = [coeff.coeff(u, k) for k in range(r)]
    return sp.Matrix([[seq[i-j] if i >= j else 0 for j in range(r)]
                      for i in range(r)])


def block(f, shifted=False, r=2):
    z = kernel(f, shifted)
    return sp.Matrix([
        [sp.cancel(sp.diff(z, u, i, v, j).subs({u: 0, v: 0}) /
                   (sp.factorial(i)*sp.factorial(j))) for j in range(r)]
        for i in range(r)
    ])


print('Fonte C(u):', C)
print('Cabeca H(u):', H)
print('Cauda T(u):', T)
print('Correcao multiplicativa U(u):', U)
assert sp.cancel(C-H*U) == 0
for shifted in (False, True):
    bc, bh, bu = (kernel(f, shifted) for f in (C, H, U))
    identity = sp.cancel(bc - (U*U.subs(u,v)*bh + H*H.subs(u,v)*bu))
    assert identity == 0
    print('\nSetor:', 'impar (A=-C\')' if shifted else 'par (A=-u*C\')')
    print('Identidade exata do produto: PASS')
    print('Bloco completo: ', block(C, shifted))
    print('Bloco cabeca:   ', block(H, shifted))
    print('Determinantes completo/cabeca:',
          block(C, shifted).det(), block(H, shifted).det())
    th, tu = toeplitz(H), toeplitz(U)
    exact = tu*block(H, shifted)*tu.T + th*block(U, shifted)*th.T
    assert exact == block(C, shifted)
    print('Conservacao matricial por transporte triangular: PASS')

qC = -sp.diff(C,u)/C
qH = -sp.diff(H,u)/H
qU = -sp.diff(U,u)/U
assert sp.cancel(qC-qH-qU)==0
print('\nLei exata da derivada logaritmica: PASS')
print('q_C=', sp.series(qC,u,0,5))
print('q_H=', sp.series(qH,u,0,5))
print('q_U=', sp.series(qU,u,0,5))
assert block(H, False)[0,0] > 0 and block(H, False).det() > 0
assert block(C, False).det() < 0
print('Controle negativo: cabeca 2x2 positiva definida; fonte completa 2x2 indefinida: PASS')

# Direcao negativa explicita no setor original, sem descartar cruzamentos.
z = sp.Matrix([0,1])
head_vec, correction_vec = toeplitz(U).T*z, toeplitz(H).T*z
head_energy = (head_vec.T*block(H,False)*head_vec)[0]
correction_energy = (correction_vec.T*block(U,False)*correction_vec)[0]
assert (head_energy,correction_energy)==(sp.Rational(1,8),-sp.Rational(9,8))
print('Decomposicao exata da direcao e2: cabeca = 1/8, correcao = -9/8, total = -1: PASS')
