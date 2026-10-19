#!/usr/bin/env python3
"""Teste algébrico exato: lei de escala de Hankel, Cholesky e alturas.

Referências usadas para as definições:
- GeometryOfNumbers/Analysis/RealDepthMass.lean
- CarrySelfAdjointOperator/FiniteClockHeightLedger.lean (scaledMoment)
- research/finite-clock-height-2026-10-02/historical/native_autoadjunto.py

IMPORTANTE: A transformação h'_r = a*c**r*h_r é uma ação algébrica
sobre momentos. Este teste NÃO afirma que uma troca de câmera física
executa tal transformação. No repositório, as câmeras normalizadas
produzem os MESMOS momentos canônicos.
"""
import sympy as sp

# Três massas espectrais de teste com alturas 2, 3, 5;
# são racionais sintéticas, NÃO valores de zeros da zeta.
lambdas = [sp.Rational(1, 4), sp.Rational(1, 9), sp.Rational(1, 25)]
weights = [sp.Integer(2), sp.Integer(3), sp.Integer(5)]
N = len(lambdas)

# h_r = soma_j w_j * lambda_j**r; casos de r=0,...,2N-1.
h = [sum(w * lam**r for w, lam in zip(weights, lambdas))
     for r in range(2*N)]
G = sp.Matrix(N, N, lambda i, j: h[i+j])
K = sp.Matrix(N, N, lambda i, j: h[i+j+1])
L = G.cholesky()
J = sp.simplify(L.inv()*K*L.inv().T)

# Escala posicional de exemplo: b^k = 2^3 = 8.
b, k = 2, 3
c = sp.Integer(b)**k
# Peso quadrático geométrico a = 1/(b^k); amplitude sqrt(a).
a = sp.Rational(1, 1)/c
D = sp.diag(*[c**i for i in range(N)])

# Ação abstrata de escala dos momentos; não confundir com mudar câmera.
h2 = [a*c**r*hr for r, hr in enumerate(h)]
G2 = sp.Matrix(N, N, lambda i, j: h2[i+j])
K2 = sp.Matrix(N, N, lambda i, j: h2[i+j+1])
L2 = G2.cholesky()
J2 = sp.simplify(L2.inv()*K2*L2.inv().T)

checks = {
    "G'=a D G D": G2 == a*D*G*D,
    "K'=a c D K D": K2 == a*c*D*K*D,
    "L'=sqrt(a) D L": sp.simplify(L2-sp.sqrt(a)*D*L) == sp.zeros(N),
    "J'=c J": sp.simplify(J2-c*J) == sp.zeros(N),
}
for name, ok in checks.items():
    print(f"{name}: {ok}")
    assert ok

pivots = [sp.simplify(L[i,i]**2) for i in range(N)]
pivots2 = [sp.simplify(L2[i,i]**2) for i in range(N)]
print("Razoes dos pivos:", [sp.simplify(y/x) for x,y in zip(pivots,pivots2)])
assert all(sp.simplify(pivots2[i]-a*c**(2*i)*pivots[i]) == 0 for i in range(N))

# Invariante relacional adimensional de três pivôs consecutivos.
I = sp.factor(pivots[2]*pivots[0]/pivots[1]**2)
I2 = sp.factor(pivots2[2]*pivots2[0]/pivots2[1]**2)
print("Razao relacional de pivos e sua transformada:", I, I2)
assert I == I2

orig_eigen = set(J.eigenvals().keys())
new_eigen = set(J2.eigenvals().keys())
assert orig_eigen == set(lambdas)
assert new_eigen == set(c*x for x in lambdas)

orig_heights = sorted([1/sp.sqrt(x) for x in lambdas], key=float)
new_heights = sorted([1/sp.sqrt(c*x) for x in lambdas], key=float)
print("Alturas originais:", [str(x) for x in orig_heights])
print("Alturas transformadas:", [sp.sstr(sp.simplify(x)) for x in new_heights])
print("Fator das alturas:", sp.simplify(new_heights[0]/orig_heights[0]))
print("Amplitude geometrica:", sp.simplify(sp.sqrt(a)))
assert all(sp.simplify(y-sp.sqrt(a)*x) == 0 for x,y in zip(orig_heights,new_heights))

# Lei posicional exata com centro e duas pernas (nao descarta o horizontal).
center = sp.Integer(24)     # por exemplo 2^3 * 3
leg = sp.Integer(1)
zoom = c                    # fator 8
f = lambda x: 1/sp.sqrt(x)
delta2 = lambda x, r: f(x-r) + f(x+r) - 2*f(x)
d_before = delta2(center, leg)
d_after = delta2(zoom*center, zoom*leg)
check_defect = sp.simplify(d_after - d_before/sp.sqrt(zoom)) == 0
check_ratio = sp.simplify(d_after/f(zoom*center) - d_before/f(center)) == 0
print("Diferenca discreta centro-pernas covariante:", check_defect)
print("Defeito relativo centro-pernas invariante:", check_ratio)
assert check_defect and check_ratio
print("CONCLUSAO: igualdades verificadas por aritmetica exata em N=3 e centro-pernas.")
