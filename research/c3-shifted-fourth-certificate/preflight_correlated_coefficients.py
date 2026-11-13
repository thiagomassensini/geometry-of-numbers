#!/usr/bin/env python3
"""Exact-rational preflight using the correlated completion polynomial.

This extends the method in c3-cofactor-correlation-gate through jet 16.  It is
only a diagnostic: all source boxes, the Gamma ledger, the tail and the final
gate still need Lean proofs before this can certify the native source.
"""
from __future__ import annotations

import math
import re
import sys
from functools import lru_cache
from fractions import Fraction as F
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TASK = ROOT / "research/c3-cofactor-chiral-certification"
CORR = ROOT / "research/c3-cofactor-correlation-gate"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(CORR))
import preflight_source_boxes as src  # noqa: E402
from diagnose_c3_shifted_fourth import (  # noqa: E402
    decimal_fraction, exact_cofactor_gate, fixed_direction, rational_center,
    source_coefficients,
)

ORDER = 16
Interval = tuple[F, F]
DEN = 10**30


def add(a: Interval, b: Interval) -> Interval:
    return a[0] + b[0], a[1] + b[1]


def neg(a: Interval) -> Interval:
    return -a[1], -a[0]


def sub(a: Interval, b: Interval) -> Interval:
    return add(a, neg(b))


def mul(a: Interval, b: Interval) -> Interval:
    v = [x * y for x in a for y in b]
    return min(v), max(v)


def inv(a: Interval) -> Interval:
    if a[0] <= 0 <= a[1]:
        raise ValueError("interval inverse contains zero")
    return F(1, a[1]), F(1, a[0])


def total(items) -> Interval:
    lo = hi = F(0)
    for x in items:
        lo += x[0]
        hi += x[1]
    return lo, hi


def power(a: Interval, n: int) -> Interval:
    out = (F(1), F(1))
    for _ in range(n):
        out = mul(out, a)
    return out


def horner(coeffs: list[Interval], x: Interval) -> Interval:
    out = (F(0), F(0))
    for c in reversed(coeffs):
        out = add(mul(out, x), c)
    return out


def rounded(x: Interval) -> Interval:
    lo = x[0] * DEN
    hi = x[1] * DEN
    return F(lo.numerator // lo.denominator, DEN), F(hi.numerator // hi.denominator + 1, DEN)


def badd(a: Interval, b: Interval) -> Interval:
    return rounded(add(a,b))


def bsub(a: Interval, b: Interval) -> Interval:
    return rounded(sub(a,b))


def bmul(a: Interval, b: Interval) -> Interval:
    return rounded(mul(a,b))


@lru_cache(maxsize=None)
def tight_unit_log(a: F) -> Interval:
    value = -sum((1-a)**(j+1)/F(j+1) for j in range(128))
    return rounded((value-F(1,10**35), value+F(1,10**35)))


@lru_cache(maxsize=None)
def tight_log(n: int) -> Interval:
    p = n.bit_length()
    unit_half = tight_unit_log(F(1,2))
    unit_scaled = tight_unit_log(F(n,2**p))
    return badd(bmul((F(p),F(p)),neg(unit_half)),unit_scaled)


@lru_cache(maxsize=None)
def tight_exp(a: Interval) -> Interval:
    total_box = (F(0),F(0))
    power_box = (F(1),F(1))
    for k in range(64):
        total_box = badd(total_box,bmul(power_box,(F(1,math.factorial(k)),)*2))
        power_box = bmul(power_box,a)
    return rounded((total_box[0]-F(1,10**30),total_box[1]+F(1,10**30)))


@lru_cache(maxsize=None)
def tight_sample_box(n: int, r: int) -> Interval:
    log_box = tight_log(n)
    amp_box = tight_exp(bmul((F(-1,2),F(-1,2)),log_box))
    log_power = (F(1),F(1))
    for _ in range(r):
        log_power = bmul(log_power,neg(log_box))
    return bmul(amp_box,bmul(log_power,(F(1,math.factorial(r)),)*2))


def tight_head_box(r: int) -> Interval:
    cell_total = (F(0),F(0))
    # Keep the same cutoff as the native C3 head/tail identity and its ledger.
    for m in range(80):
        x,y,z=(tight_sample_box(3*m+j,r) for j in (2,3,4))
        cell_total=badd(cell_total,badd(bsub(x,bmul((F(2),F(2)),y)),z))
    boundary=(F(0),F(0))
    stencil=(531440,-1062856,531116,534040,-1077806,596896,303810,-420006,
      -965379,3428360,-5731741,6760781,-6229340,4668859,-2896919,1496820,
      -642876,227631,-65455,14924,-2599,325,-26,1)
    for k,w in enumerate(stencil):
        boundary=badd(boundary,bmul((F(w,729**2),)*2,tight_sample_box(242+k,r)))
    return badd(badd((F(1) if r==0 else F(0),)*2,cell_total),boundary)


def read_values(path: Path, first: str, stop: str) -> list[F]:
    s = path.read_text()
    body = s[s.index(first):s.index(stop, s.index(first))]
    matches = re.findall(r"(-?\d+)\s*/\s*(\d+)(?:\^(\d+))?", body)
    return [F(int(a), int(b) ** int(power or 1)) for a, b, power in matches]


def gamma_reference17() -> list[F]:
    """Evaluate the exact rational Gamma centers defined by the Lean module."""
    old = read_values(TASK / "GammaThirteen.lean",
                      "def coefficientReference13", "theorem rational_coefficient_boxes13")
    high = read_values(HERE / "GammaSeventeen.lean",
                       "def coefficientReferenceHigh", "def coefficientReference17")
    log_ref = read_values(TASK / "GammaThirteen.lean",
                          "def logReferenceTight", "theorem log_approx_tight_box")
    if len(old) != 13 or len(high) != 4 or len(log_ref) != 1:
        raise AssertionError("Lean Gamma input tables changed shape")
    coeffs = old + high
    L = log_ref[0]
    return [F(3) * sum(
        (2*L)**j / math.factorial(j) * F(-1,2)**(n-j) * coeffs[n-j]
        for j in range(n+1)) for n in range(ORDER+1)]


def enclosure() -> tuple[list[Interval], list[Interval], list[Interval], Interval, list[Interval], list[Interval]]:
    # Use the same proved rational log series and exp enclosure, but retain
    # its tighter evaluator boxes rather than the older decimal target table.
    head = [tight_head_box(r) for r in range(ORDER+1)]
    # Original pi and chart boxes; log(pi) remains a shared Horner variable.
    pi_amp = src.pair_definition(src.PRIMITIVES, "piAmplitudeReference")
    pi_log = src.pair_definition(src.PRIMITIVES, "piLogReference")
    chart_amp = src.pair_definition(src.CHIRAL_BOXES, "chartAmplitudeReferenceTight")
    log3_center = src.point_definition(src.GAMMA, "logReferenceTight")
    log3 = (log3_center - F(1,10**44), log3_center + F(1,10**44))
    chart_scale = sub((F(1),F(1)), chart_amp)
    q = mul(chart_amp, inv(chart_scale))

    # D(t)=1+q(1-exp(-ell*t)); R(t)=1/D(t).
    djet = [(F(1),F(1))]
    for n in range(1, ORDER+1):
        djet.append(mul(mul(q, power(log3,n)), (F((-1)**(n+1), math.factorial(n)),)*2))
    rjet = [(F(1),F(1))]
    for n in range(1, ORDER+1):
        rjet.append(neg(total(mul(rjet[n-j], djet[j]) for j in range(1,n+1))))

    # P(t)=1-4t^2 and exp(-log(pi)*t/2), with coefficients collected by
    # powers of the single shared log(pi) interval.
    base: list[list[Interval]] = []
    for n in range(ORDER+1):
        row = [(F(0),F(0)) for _ in range(n+1)]
        for i in (0,2):
            if i > n:
                continue
            pcoeff = F(1) if i == 0 else F(-4)
            for e in range(n-i+1):
                rem = n-i-e
                fac = F(pcoeff * (-1)**e, 2**e * math.factorial(e))
                row[e] = add(row[e], mul(rjet[rem], (fac,fac)))
        base.append(row)

    gamma_ref = gamma_reference17()
    gamma0 = gamma_ref[0]
    gamma_norm = [(g/gamma0,g/gamma0) for g in gamma_ref]
    full: list[list[Interval]] = []
    for n in range(ORDER+1):
        row = [(F(0),F(0)) for _ in range(n+1)]
        for g in range(n+1):
            for e in range(len(base[n-g])):
                row[e] = add(row[e], mul(base[n-g][e], gamma_norm[g]))
        full.append(row)

    base_jet = [horner(base[n], pi_log) for n in range(ORDER+1)]
    full_jet = [horner(full[n], pi_log) for n in range(ORDER+1)]
    left_scale = mul((F(-1,8),F(-1,8)), mul(pi_amp, inv(chart_scale)))
    source_scale = mul(left_scale, (gamma0,gamma0))
    left_jet = [mul(left_scale, total(mul(head[k],base_jet[n-k]) for k in range(n+1)))
                for n in range(ORDER+1)]
    normalized_completed = [total(mul(head[k],full_jet[n-k]) for k in range(n+1))
                            for n in range(ORDER+1)]
    coeff_finite = [mul(source_scale, mul((F((-1)**j),)*2,normalized_completed[2*j]))
                    for j in range(9)]
    return head, left_jet, coeff_finite, source_scale, full_jet, normalized_completed


def main() -> None:
    mp.dps = 150
    head, left, coeff_finite, scale, full_jet, normalized = enclosure()
    numerical = source_coefficients(80)
    # The Gamma residual follows the weighted M=80 Lean estimate, using the
    # per-jet native tail 2*4^q/10^34 and the polynomial replacement bound 10^-29.
    source_boxes = []
    source_errors = []
    print("correlated source coefficient boxes through c8 (M=80)")
    print("Gamma centers and weighted residual match the Lean M=80 transport")
    radii = []
    for j, finite in enumerate(coeff_finite):
        r = 2*j
        gamma_err = sum(
            max(abs(left[k][0]),abs(left[k][1])) *
                (F(2*4**(r-k),10**34)+F(1,10**29))
            for k in range(r+1)
        )
        tail = F(96*math.factorial(26)*4**r,729**2*239**25)
        interval = finite[0]-gamma_err-tail, finite[1]+gamma_err+tail
        source_boxes.append(interval)
        source_errors.append(gamma_err+tail)
        center = rational_center(numerical[j])
        radii.append(max(abs(interval[0]-center),abs(interval[1]-center)))
        print(f"  c{j}: width={decimal_fraction(interval[1]-interval[0],18)} "
              f"radius~{decimal_fraction(radii[-1],18)}")

    # The common completion scale cancels in c_j/c_0. Transfer the rigorously
    # bounded Gamma/tail residual through that ratio with c0>0.49 and N0>0.99.
    n0 = normalized[0]
    if n0[0] <= F(99,100):
        raise AssertionError("normalized c0 lower bound is not > 0.99")
    normalized_source_boxes = [(F(1),F(1))]
    for j in range(1,9):
        nj = mul(normalized[2*j], (F((-1)**j),)*2)
        finite_ratio = mul(nj,inv(n0))
        n0_abs=max(abs(n0[0]),abs(n0[1]))
        nj_abs=max(abs(nj[0]),abs(nj[1]))
        residual=(source_errors[j]*n0_abs+source_errors[0]*nj_abs)/(F(99,100)*F(49,100))
        normalized_source_boxes.append((finite_ratio[0]-residual,finite_ratio[1]+residual))

    normalized_centers=[rational_center(numerical[j]/numerical[0]) for j in range(9)]
    centers = normalized_centers
    normalized_radii=[]
    for j,box in enumerate(normalized_source_boxes):
        normalized_radii.append(max(abs(box[0]-centers[j]),abs(box[1]-centers[j])))
    print("normalized source coefficient ratio boxes c_j/c_0")
    for j,(box,radius) in enumerate(zip(normalized_source_boxes,normalized_radii)):
        print(f"  a{j}: radius~{decimal_fraction(radius,18)}")
    # Round each rigorous interval radius upward to a decimal power.  This
    # keeps the symbolic exact gate compact while making the enclosure wider.
    simple_radii = []
    for radius in normalized_radii:
        if radius == 0:
            simple_radii.append(F(0))
            continue
        e = 0
        while F(1,10**(e+1)) >= radius:
            e += 1
        simple_radii.append(F(1,10**e))
    print("gate radii after outward simplification:",
          ", ".join(decimal_fraction(x,8) for x in simple_radii))
    direction = fixed_direction(numerical)
    constant, variation, lower, terms, det_a = exact_cofactor_gate(centers,simple_radii,direction)
    print(f"exact fixed-direction gate: terms={terms}")
    print(f"  center={decimal_fraction(constant,42)}")
    print(f"  variation={decimal_fraction(variation,42)}")
    print(f"  lower={decimal_fraction(lower,42)}")
    print("status:","candidate source boxes certify the gate" if lower > 0 else "interval gate crosses zero")
    print("Diagnostic exact interval calculation only; the matching native coefficient-box inclusion and the determinant/Schur transport are proved in Lean by FourthSourceGate17.lean and FourthIntervalGate17.lean.")


if __name__ == "__main__":
    main()
