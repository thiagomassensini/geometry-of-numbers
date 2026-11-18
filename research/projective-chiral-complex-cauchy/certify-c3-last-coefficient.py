from pathlib import Path
from runpy import run_path

from flint import arb, arb_mat, arb_series, ctx, fmpq


C3 = run_path(str(Path(__file__).with_name("certify-c3-head-tail.py")))
SCHUR = C3["TRANSVERSE"]["schur"]
PARITY_COEFFICIENTS = C3["parity_coefficients"]


def direct_prefix(count):
    """Coefficients c_0 through c_(count-1) by direct completed zeta."""
    ctx.cap = 2 * count - 1
    s = arb_series([arb(fmpq(1, 2)), 1])
    return PARITY_COEFFICIENTS(C3["completion_prefactor"](s) * s.zeta(), count)


def recomposed_c3_coefficients(count, cutoff=64):
    """Combine the original cells and omitted bracket sum before the chart."""
    ctx.cap = 2 * count - 1
    s = arb_series([arb(fmpq(1, 2)), 1])
    # The same boundary occurs with opposite signs in the accelerated
    # pieces, so recomposition cancels it algebraically.
    raw = C3["raw_c3_prefix"](s, cutoff) + C3["raw_c3_omitted"](s, cutoff)
    value = C3["completion_prefactor"](s) * raw / C3["camera_factor"](s)
    return PARITY_COEFFICIENTS(value, count)


def prefix_moments(coefficients):
    """Read h_0 through h_(m-2) from c_0 through c_(m-1)."""
    moments = []
    for j in range(len(coefficients) - 1):
        convolution = sum(coefficients[j - k] * moment for k, moment in enumerate(moments))
        numerator = (j + 1) * coefficients[j + 1] + convolution
        moments.append(-numerator / coefficients[0])
    return moments


def schur_threshold(coefficients, degree, sector):
    """Compute T_m with c_m absent. The placeholder is for h_(m-1)."""
    m = 2 * degree + sector + 1
    if len(coefficients) != m or not coefficients[0] > 0:
        raise ValueError("the threshold needs exactly the old coefficients and positive c_0")
    moments = prefix_moments(coefficients)
    negative_coupling, monic = SCHUR(moments + [arb(0)], sector, degree)
    convolution = sum(coefficients[m - 1 - k] * value for k, value in enumerate(moments))
    threshold = (coefficients[0] * negative_coupling - convolution) / m
    return threshold, moments, monic


def preceding_coefficient_budget(coefficients, degree, sector, gap, threshold, moments, monic):
    """Certify a radius for c_(m-1) alone using its exact quadratic effect."""
    m = len(coefficients)
    previous_pivot, _ = SCHUR(moments, sector, degree - 1)
    linear = coefficients[1] / coefficients[0] - fmpq(2 * (m - 1), m) * monic[-2]
    quadratic = (m - 1) ** 2 / (m * coefficients[0] * previous_pivot)
    lower_gap = gap.lower()
    radius = (lower_gap / (2 * (abs(linear) + (quadratic * lower_gap).sqrt()))).lower()
    error = abs(linear) * radius + quadratic * radius ** 2
    if not (radius > 0 and error < lower_gap):
        raise ArithmeticError("the preceding coefficient radius was not certified")

    # Check the exact quadratic against recomputation of the old jets.
    for delta in (-radius, radius):
        updated = coefficients[:-1] + [coefficients[-1] + delta]
        evaluated, _, _ = schur_threshold(updated, degree, sector)
        predicted = threshold + linear * delta - quadratic * delta ** 2
        if not evaluated.overlaps(predicted):
            raise ArithmeticError("preceding coefficient perturbation identity disagrees")
    return radius, linear


def bound_in_normalized_basis(series, absolute_basis, sector):
    size = absolute_basis.nrows()
    envelope = arb_mat([
        [series[i + j + sector].upper() for j in range(size)]
        for i in range(size)
    ])
    transported = absolute_basis.transpose() * envelope * absolute_basis
    return max(sum(transported[i, j] for j in range(size)).upper() for i in range(size))


def joint_prefix_budget(coefficients, degree, sector):
    """Certified relative budget for all old c_j, with the last c_m fixed."""
    m = len(coefficients) - 1
    basis = C3["TRANSVERSE"]["normalized_central_basis"](
        prefix_moments(coefficients), sector, degree + 1,
    )
    absolute_basis = arb_mat([
        [abs(basis[i, j]).upper() for j in range(degree + 1)]
        for i in range(degree + 1)
    ])
    ctx.cap = m + 1
    reciprocal = 1 / arb_series(coefficients)
    # Coefficientwise bound for U = delta C / C with unit relative error
    # on the old coefficients. The last coefficient is fixed.
    weights = arb_series([abs(c).upper() for c in coefficients[:-1]])
    weights *= arb_series([abs(reciprocal[j]).upper() for j in range(m + 1)])
    linear_bound = bound_in_normalized_basis(weights.derivative(), absolute_basis, sector)
    epsilon = min((1 / (4 * linear_bound)).lower(), (1 / (4 * weights[0])).lower())
    envelope = epsilon * weights
    if not (epsilon > 0 and envelope[0] < 1):
        raise ArithmeticError("bad joint error majorant")
    # Delta h = -U' / (1 + U), bounded coefficientwise by D' / (1 - D).
    error = bound_in_normalized_basis(
        envelope.derivative() / (1 - envelope), absolute_basis, sector,
    )
    if not error < 1:
        raise ArithmeticError("joint prefix perturbation not certified")
    return epsilon, error


def main():
    ctx.prec = 6144
    maximum_degree = 57
    last_index = 2 * maximum_degree + 2
    prefix = direct_prefix(last_index)
    c3 = recomposed_c3_coefficients(last_index + 1)
    if not all(x.overlaps(y) for x, y in zip(prefix, c3)):
        raise ArithmeticError("the two evaluations of the old coefficients disagree")

    # This source prefix omits c_(last_index). It suffices for every
    # preceding pivot used below, including degree 56 in both sectors.
    moments = prefix_moments(prefix)
    for sector in (0, 1):
        for degree in range(maximum_degree):
            if not SCHUR(moments, sector, degree)[0] > 0:
                raise ArithmeticError(f"uncertified preceding pivot at {sector=}, {degree=}")
    print("all preceding pivots through degree 56 certified in both sectors", flush=True)

    for degree in (56, 57):
        for sector in (0, 1):
            m = 2 * degree + sector + 1
            old = prefix[:m]
            threshold, moments, monic = schur_threshold(old, degree, sector)
            coefficient = c3[m]
            gap = threshold - coefficient
            if not threshold.lower() > coefficient.upper():
                raise ArithmeticError(f"threshold boxes overlap at {sector=}, {degree=}")
            pivot = m * gap / old[0]
            check, _ = SCHUR(prefix_moments(old + [coefficient]), sector, degree)
            if not check.overlaps(pivot):
                raise ArithmeticError("the exact threshold margin disagrees with the full pivot")

            radius, linear = preceding_coefficient_budget(
                old, degree, sector, gap, threshold, moments, monic
            )
            print(f"sector={sector}, degree={degree}, m={m}", flush=True)
            print(f"  C3 coefficient = {coefficient.str(14)}", flush=True)
            print(f"  threshold margin = {gap.str(14)}", flush=True)
            print(f"  relative last coefficient margin = {(gap / abs(coefficient)).str(12)}")
            print(f"  Hankel pivot = {pivot.str(14)}", flush=True)
            print(f"  threshold radius = {threshold.rad().str(5)}")
            print(f"  C3 coefficient radius = {coefficient.rad().str(5)}")
            print(f"  preceding coefficient derivative = {linear.str(12)}")
            print(f"  safe preceding relative radius = {(radius / abs(old[-1])).str(12)}", flush=True)


    epsilon, error = joint_prefix_budget(prefix + [c3[last_index]], maximum_degree, 1)
    print(f"joint relative radius for the old coefficients = {epsilon.str(12)}")
    print(f"joint normalized perturbation bound = {error.str(12)}", flush=True)


if __name__ == "__main__":
    main()
