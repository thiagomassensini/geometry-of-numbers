from pathlib import Path
from runpy import run_path

from flint import acb, arb, arb_series, ctx, fmpq


TRANSVERSE = run_path(str(Path(__file__).with_name("certify-transverse-schur.py")))
# Forward differences in the native C3/64 boundary, expanded in sample values.
BOUNDARY_WEIGHTS = (728, -1444, 638, 1092, -2445, 2640, -1911, 987, -363, 91, -14, 1)


def raw_head_and_boundary(s, cutoff):
    def sample(address):
        return (-s * arb(address).log()).exp()

    finite = 1
    for cell in range(cutoff):
        a = 3 * cell + 2
        finite += sample(a) - 2 * sample(a + 1) + sample(a + 2)
    first = 3 * cutoff + 2
    boundary = sum(weight * sample(first + j) for j, weight in enumerate(BOUNDARY_WEIGHTS)) / 729
    return finite + boundary, boundary


def completed_c3_parts(count, displacement=fmpq(0), cutoff=64):
    """Exact accelerated C3 split, evaluated with outward-rounded series."""
    ctx.cap = 2 * count + 2
    s = arb_series([arb(fmpq(1, 2) + displacement), 1])
    log_three = arb(3).log()
    chart = 1 - ((1 - s) * log_three).exp()
    dressing = s * (s - 1) * (s / 2).gamma() * (-s * arb.pi().log() / 2).exp() / (2 * chart)

    head, boundary = raw_head_and_boundary(s, cutoff)
    first = 3 * cutoff + 2
    # The three Hurwitz terms describe the three ordered legs of the
    # original omitted cells. Deflating at 1 cancels in their second difference.
    omitted = sum(
        weight * s.zeta(arb(fmpq(first + j, 3)), deflate=True)
        for j, weight in enumerate((1, -2, 1))
    ) * (-s * log_three).exp()
    return dressing * head, dressing * (omitted - boundary)


def log_moments(characteristic, count):
    response = characteristic.derivative() / characteristic
    return [(-1) ** j * response[2 * j + 1] / 2 for j in range(count)]


def parity_coefficients(characteristic, count):
    return [(-1) ** j * characteristic[2 * j] for j in range(count)]


def critical_bezout_direction(coefficients, monic):
    n = len(monic)
    direction = [arb(0)] * n
    c0 = coefficients[0]
    for i in reversed(range(n)):
        cross = sum(coefficients[j - i] * direction[j] for j in range(i + 1, n))
        direction[i] = (c0 * monic[i] - cross) / c0
    return direction


def projected_bezout(left, right, sector, direction):
    """Ordered mixed Bezout kernel on the original monic direction."""
    n = len(direction) - 1
    weighted = [-(j + sector) * left[j + sector] for j in range(2 * n + 2)]
    previous = []
    total = arb(0)
    for j in range(n + 1):
        column = [
            right[j] * weighted[i + 1] - weighted[j] * right[i + 1]
            + (previous[i + 1] if j else 0)
            for i in range(2 * n - j + 1)
        ]
        total += direction[j] * sum(x * value for x, value in zip(direction, column))
        previous = column
    return total


def check_split(head, tail, moments, degree, sector):
    k = 2 * degree + sector + 2
    h, t = [parity_coefficients(part, k) for part in (head, tail)]
    full = [x + y for x, y in zip(h, t)]
    pivot, monic = TRANSVERSE["schur"](moments, sector, degree)
    direction = critical_bezout_direction(full, monic)
    hh, ht, th, tt = [
        projected_bezout(left, right, sector, direction)
        for left, right in ((h, h), (h, t), (t, h), (t, t))
    ]
    total = hh + ht + th + tt
    if not total.overlaps(full[0] ** 2 * pivot):
        raise ArithmeticError("four-term Bezout reconstruction disagrees with the Schur pivot")
    absolute_budget = abs(ht) + abs(th) + abs(tt)
    if not hh > absolute_budget:
        raise ArithmeticError("head dominance is not certified on the critical direction")
    relative_gap = (hh - absolute_budget) / hh
    highest = 2 * degree + sector + 1
    last_jet_correction = -highest * full[0] * t[highest]
    print(f"sector {sector}, degree {degree}", flush=True)
    print(f"  HH = {hh.str(12)}", flush=True)
    print(f"  HT = {ht.str(12)}", flush=True)
    print(f"  TH = {th.str(12)}", flush=True)
    print(f"  TT = {tt.str(12)}", flush=True)
    print(f"  full = {total.str(12)}", flush=True)
    print(f"  head dominance relative gap = {relative_gap.str(12)}", flush=True)
    print(f"  isolated last tail jet / full = {(last_jet_correction / total).str(12)}", flush=True)


def main():
    ctx.prec = 6144
    count = 124
    head, tail = completed_c3_parts(count)
    central = log_moments(head + tail, count)
    print("central h0:", central[0].str(20), flush=True)
    for degree in (2, 56):
        for sector in (0, 1):
            check_split(head, tail, central, degree, sector)

    distance = fmpq(1, 10 ** 100)
    head, tail = completed_c3_parts(count, distance)
    shifted = log_moments(head + tail, count)
    dimension, pivot = TRANSVERSE["first_negative_dimension"](shifted)
    even_dimension, _ = TRANSVERSE["first_negative_dimension"](shifted, sector=0)
    print(f"first interleaved failure: {dimension}, pivot {pivot.str(12)}", flush=True)
    print(f"first unshifted failure: {even_dimension}", flush=True)

    for sector in (0, 1):
        size = (dimension - sector) // 2
        quadratic, remainder = TRANSVERSE["normalized_quadratic_model"](
            central, sector, size, 6, arb(distance)
        )
        lower = TRANSVERSE["isotropic_shift"](quadratic, 1 - remainder)
        if TRANSVERSE["symmetric_sign"](lower) != 1:
            raise ArithmeticError("C3 transverse window positivity unresolved")
    print(f"positive prefix in the full transverse interval: {dimension - 1}", flush=True)

    # The two separate completed pieces can have chart poles even though
    # the complete characteristic is regular there.
    ctx.prec = 256
    chart_zero = acb(1, 2 * arb.pi() / arb(3).log())
    raw_head, _ = raw_head_and_boundary(chart_zero, 64)
    if not abs(raw_head) > 0:
        raise ArithmeticError("head zero at the chart pole is unresolved")
    print(f"absolute raw head at the first nonreal chart zero: {abs(raw_head).str(12)}", flush=True)


if __name__ == "__main__":
    main()
