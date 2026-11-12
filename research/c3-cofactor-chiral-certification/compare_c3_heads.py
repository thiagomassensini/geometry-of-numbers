#!/usr/bin/env python3
"""Numerical regression of the two original-source completions. No sign certificate."""
from mpmath import mp

mp.dps = 75
highest = 12

# Coefficients of the first and doubled boundary stencils in the shift basis.
single = (728, -1444, 638, 1092, -2445, 2640, -1911, 987, -363, 91, -14, 1)
double = (
    531440, -1062856, 531116, 534040, -1077806, 596896, 303810, -420006,
    -965379, 3428360, -5731741, 6760781, -6229340, 4668859, -2896919,
    1496820, -642876, 227631, -65455, 14924, -2599, 325, -26, 1,
)


def multiplier(w):
    s = mp.mpf(1) / 2 + mp.j * w
    return s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) / (
        2 * (1 - mp.power(3, 1 - s))
    )


completion = mp.taylor(multiplier, 0, highest)


def completed_head(cutoff, stencil, denominator):
    jets = [mp.mpc(1)] + [mp.mpc(0)] * highest

    def sample(address, weight):
        log = mp.log(address)
        term = weight * mp.exp(-log / 2)
        for order in range(highest + 1):
            jets[order] += term
            term *= -mp.j * log / (order + 1)

    for cell in range(cutoff):
        for offset, weight in enumerate((1, -2, 1)):
            sample(3 * cell + 2 + offset, weight)
    for offset, weight in enumerate(stencil):
        sample(3 * cutoff + 2 + offset, mp.mpf(weight) / denominator)

    return [
        mp.fsum(completion[k] * jets[order - k] for k in range(order + 1))
        for order in range(0, highest + 1, 2)
    ]


head48 = completed_head(48, double, 729**2)
head256 = completed_head(256, single, 729)
for j, (a, b) in enumerate(zip(head48, head256)):
    tau48 = 96 * mp.factorial(26) * 4 ** (2 * j) / (729**2 * mp.mpf(143)**25)
    tau256 = 96 * mp.factorial(14) * 4 ** (2 * j) / (729 * mp.mpf(767)**13)
    discrepancy = abs(a - b)
    if discrepancy > tau48 + tau256:
        raise SystemExit(f"C3 head comparison outside the combined tail bound at c{j}")
    print(f"c{j}: |head48-head256|={mp.nstr(discrepancy, 8)}, "
          f"combined tails={mp.nstr(tau48 + tau256, 8)}")
print("C3/48 vs C3/256: numerical diagnostic only")
