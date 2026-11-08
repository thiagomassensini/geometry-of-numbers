#!/usr/bin/env python3
"""Exploratory (NOT interval-certified) contour-51 and exact rational B1 margins.

The original completed native characteristic is identified with the classical
completed zeta by the separately proved source bridge. Its logarithmic response
is evaluated here; zero heights are comparison data, not a definition of
the original moments.
"""
from fractions import Fraction as Q
import mpmath as mp

mp.mp.dps = 65


def native_completed_log_response(z):
    """R(z) = -F'(z)/(2F(z)), F(z) = xi(1/2+iz).

    xi'/xi is evaluated on Re(s)>=1/2 by xi(s)=xi(1-s), to avoid
    gamma/zeta cancellation when Re(s) is very negative.
    """
    s = mp.mpf('0.5') + 1j * z
    sign = 1 if mp.re(s) >= mp.mpf('0.5') else -1
    if sign == -1:
        s = 1 - s
    L = (1/s + 1/(s-1) - mp.log(mp.pi)/2
         + mp.digamma(s/2)/2 + mp.zeta(s, derivative=1)/mp.zeta(s))
    return -(1j/2) * sign * L


def moment_probe():
    radius = mp.mpf(8)
    N = 256
    acc = [mp.mpc(0) for _ in range(6)]
    for k in range(N):
        omega = mp.exp((2j * mp.pi * k)/N)
        z = radius * omega
        R = native_completed_log_response(z)
        for n in range(6):
            acc[n] += R / z**(2*n+2) * z  # Fourier form of Cauchy's formula
    H = [mp.re(v/N) for v in acc]
    gamma = [mp.im(mp.zetazero(k)) for k in range(1, 11)]
    P = [sum(g**(-2*n-2) for g in gamma) for n in range(6)]
    print('Central first six jets and residuals: numerical only')
    for n in range(6):
        e = H[n] - P[n]
        print(f'n={n}: H={mp.nstr(H[n], 21)}  e={mp.nstr(e, 18)}'
              f'  e/eta^(n+1)={mp.nstr(e*2500**(n+1), 13)}')


def contour_probe():
    radius = mp.mpf(51)
    N = 2048
    norms = []
    for k in range(N):
        z = radius * mp.exp((2j * mp.pi * k)/N)
        norms.append(abs(native_completed_log_response(z)))
    print('Circle |z|=51: grid N=', N)
    print('max sample norm R =', mp.nstr(max(norms), 18))
    print('mean sample norm R =', mp.nstr(sum(norms)/N, 18))
    print('Target uniform norm R <= 4/5 (NOT certified by this grid)')


def rational_gate():
    lower_ordinates = [Q(x, 100) for x in
       (1413, 2102, 2501, 3042, 3293, 3758, 4091, 4332, 4800, 4977)]
    upper_ordinates = [Q(x, 100) for x in
       (1414, 2103, 2502, 3043, 3294, 3759, 4092, 4333, 4801, 4978)]
    scale_lower = [1 / x**2 for x in upper_ordinates]
    scale_upper = [1 / x**2 for x in lower_ordinates]
    moment_lo = lambda n: sum(a**(n+1) for a in scale_lower)
    moment_hi = lambda n: sum(a**(n+1) for a in scale_upper)
    eta = Q(1, 2500)
    print('EXACT Fraction inequalities: early-window C=40 margins')
    for s in range(4):
        margin = (moment_lo(s)*moment_lo(s+2)
                  - (moment_hi(s+1)+40*eta**(s+2))**2)
        assert margin > 0, ('nonpositive rational margin', s)
        print(f's={s}: strict rational positive; approx {float(margin):.15e}')


if __name__ == '__main__':
    contour_probe()
    moment_probe()
    rational_gate()
