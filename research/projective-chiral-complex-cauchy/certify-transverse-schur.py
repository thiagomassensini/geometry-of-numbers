"""Certified finite sign tests for the original completed log-modulus moments."""

from argparse import ArgumentParser
from math import comb

from flint import arb, arb_mat, arb_series, ctx, fmpq


# canonicalCompletedNativeLogDerivativeMoment_sharp_decay implies |h_j| <= q^(j+1).
MOMENT_RATIO = fmpq(22, 175)
ROOT_RATIO_UPPER = fmpq(3, 8)


def source_moments(count, displacement=fmpq(0)):
    """Taylor jets of xi in the real direction, with their height phases."""
    ctx.cap = 2 * count + 2
    z = arb_series([arb(fmpq(1, 2)) + arb(displacement), 1])
    xi = z * (z - 1) * z.zeta() * (z / 2).gamma()
    xi *= (-z * arb.pi().log() / 2).exp() / 2
    log_derivative = xi.derivative() / xi
    return [(-1) ** j * log_derivative[2 * j + 1] / 2 for j in range(count)]


def transverse_coefficient(moments, index, order):
    return (-1) ** order * comb(2 * index + 2 * order + 1, 2 * order) * moments[index + order]


def moment_tail_bound(index, terms, distance):
    """Bound all transverse terms with order >= terms, on the original source."""
    ratio = ROOT_RATIO_UPPER * abs(distance)
    if not ratio < 1:
        raise ValueError("displacement exceeds the majorant radius")
    return (
        comb(2 * index + 2 * terms + 1, 2 * terms)
        * arb(MOMENT_RATIO) ** (index + terms + 1)
        * distance ** (2 * terms)
        / (1 - ratio) ** (2 * index + 2 * terms + 2)
    )


def transverse_moments(moments, count, terms, distance):
    out = []
    squared = distance ** 2
    powers = [squared ** r for r in range(terms)]
    for j in range(count):
        polynomial = sum(transverse_coefficient(moments, j, r) * powers[r] for r in range(terms))
        tail = moment_tail_bound(j, terms, distance)
        out.append(polynomial + arb(0, tail.upper()))
    return out


def schur(moments, sector, degree):
    if degree == 0:
        return moments[sector], [arb(1)]
    old = arb_mat([[moments[i + j + sector] for j in range(degree)] for i in range(degree)])
    crossing = [moments[i + degree + sector] for i in range(degree)]
    projected = old.solve(arb_mat([[value] for value in crossing]))
    vector = [-projected[i, 0] for i in range(degree)] + [arb(1)]
    return moments[2 * degree + sector] + sum(
        crossing[i] * vector[i] for i in range(degree)
    ), vector


def first_negative_dimension(moments, *, sector=None):
    indices = range(len(moments)) if sector is None else range(sector, len(moments), 2)
    for order in indices:
        degree, parity = divmod(order, 2)
        dimension = order + 1 if sector is None else degree + 1
        pivot, _ = schur(moments, parity, degree)
        if pivot < 0:
            return dimension, pivot
        if not pivot > 0:
            raise ArithmeticError(f"pivot sign unresolved at dimension {dimension}: {pivot}")
    raise ArithmeticError("no negative pivot within the tested prefix")


def fixed_form(coefficients, vector):
    """Quadratic form on a fixed vector, collecting weights by moment index."""
    return sum(
        coefficients[i + j] * x * y
        for i, x in enumerate(vector)
        for j, y in enumerate(vector)
    )


def fixed_direction_test(moments, sector, degree, terms):
    pivot, vector = schur(moments, sector, degree)
    curvature = -fixed_form(
        [transverse_coefficient(moments, j + sector, 1) for j in range(2 * degree + 1)],
        vector,
    )
    if not (pivot > 0 and curvature > 0):
        raise ArithmeticError("positive central pivot and curvature required for the test")
    quadratic_scale = (pivot / curvature).sqrt()
    distance = (2 * pivot / curvature).sqrt()
    if not distance < arb(fmpq(1, 2)):
        raise ArithmeticError("quadratic-scale test lies outside the critical strip")
    remainder = arb(0)
    for order in range(2, terms):
        coefficient = fixed_form(
            [transverse_coefficient(moments, j + sector, order) for j in range(2 * degree + 1)],
            vector,
        )
        remainder += abs(coefficient) * distance ** (2 * order)
    # Sum after forming each finite quadratic coefficient, then bound the
    # remaining infinite tail by entrywise absolute bounds.
    weights = [abs(x) for x in vector]
    remainder += fixed_form(
        [moment_tail_bound(j + sector, terms, distance) for j in range(2 * degree + 1)],
        weights,
    )
    relative_remainder = remainder / pivot
    if not relative_remainder < 1:
        raise ArithmeticError("the remainder estimate does not certify this crossing")
    return quadratic_scale, relative_remainder


def normalized_central_basis(moments, sector, size):
    columns = []
    for degree in range(size):
        pivot, vector = schur(moments, sector, degree)
        if not pivot > 0:
            raise ArithmeticError("central prefix positivity unresolved")
        scale = pivot.sqrt()
        columns.append([value / scale for value in vector] + [arb(0)] * (size - len(vector)))
    return arb_mat([[columns[j][i] for j in range(size)] for i in range(size)])


def normalized_error_bound(moments, sector, basis, terms, radius, first_order):
    """Operator norm bound for the Taylor tail in the normalized central basis."""
    size = basis.nrows()
    absolute_basis = arb_mat([[abs(basis[i, j]) for j in range(size)] for i in range(size)])
    error = arb_mat(size, size)
    for order in range(first_order, terms):
        coefficient = arb_mat([
            [transverse_coefficient(moments, i + j + sector, order) for j in range(size)]
            for i in range(size)
        ])
        transported = basis.transpose() * coefficient * basis
        power = radius ** (2 * order)
        for i in range(size):
            for j in range(size):
                error[i, j] += abs(transported[i, j]) * power
    tail = arb_mat([
        [moment_tail_bound(i + j + sector, terms, radius) for j in range(size)]
        for i in range(size)
    ])
    error += absolute_basis.transpose() * tail * absolute_basis
    return max(sum(error[i, j] for j in range(size)).upper() for i in range(size))


def interval_perturbation_bound(moments, sector, size, terms, radius):
    if size == 0:
        return arb(0)
    basis = normalized_central_basis(moments, sector, size)
    return normalized_error_bound(moments, sector, basis, terms, radius, first_order=1)


def isotropic_shift(matrix, diagonal):
    size = matrix.nrows()
    return arb_mat([
        [matrix[i, j] + (diagonal if i == j else 0) for j in range(size)]
        for i in range(size)
    ])


def symmetric_sign(matrix):
    """Return 1 for positive definite, -1 for a negative direction, or 0 if unresolved."""
    rows = matrix.tolist()
    for k in range(len(rows)):
        pivot = rows[k][k]
        if pivot < 0:
            return -1
        if not pivot > 0:
            return 0
        for i in range(k + 1, len(rows)):
            factor = rows[i][k] / pivot
            for j in range(k + 1, i + 1):
                rows[i][j] -= factor * rows[j][k]
    return 1


def normalized_quadratic_model(moments, sector, size, terms, radius):
    basis = normalized_central_basis(moments, sector, size)
    curvature = arb_mat([
        [transverse_coefficient(moments, i + j + sector, 1) for j in range(size)]
        for i in range(size)
    ])
    quadratic = (basis.transpose() * curvature * basis) * (radius ** 2)
    remainder = normalized_error_bound(moments, sector, basis, terms, radius, first_order=2)
    return quadratic, remainder


def critical_radius_bracket(quadratic, remainder, steps):
    """Bracket the first loss using the positive window and a negative endpoint."""
    lo, hi = fmpq(0), fmpq(1)
    for _ in range(steps):
        middle = (lo + hi) / 2
        scaled = quadratic * (arb(middle) ** 2)
        tail = remainder * arb(middle) ** 4
        if symmetric_sign(isotropic_shift(scaled, 1 - tail)) == 1:
            lo = middle
        elif symmetric_sign(isotropic_shift(scaled, 1 + tail)) == -1:
            hi = middle
        else:
            break
    return lo, hi


def deep_window():
    ctx.prec = 6144
    count, terms = 168, 6
    radius = fmpq(1, 10 ** 100)
    central = source_moments(count + terms)
    shifted = transverse_moments(central, count, terms, arb(radius))
    dimension, pivot = first_negative_dimension(shifted)
    unshifted_dimension, _ = first_negative_dimension(shifted, sector=0)
    direct = source_moments(max(dimension, 2 * unshifted_dimension - 1), radius)
    if (
        first_negative_dimension(direct)[0] != dimension
        or first_negative_dimension(direct, sector=0)[0] != unshifted_dimension
        or not all(x.overlaps(y) for x, y in zip(shifted, direct))
    ):
        raise ArithmeticError("direct and transverse certificates disagree")

    last_degree, last_sector = divmod(dimension - 1, 2)
    central_pivot, _ = schur(central, last_sector, last_degree)
    if not central_pivot > 0:
        raise ArithmeticError("central pivot sign unresolved")
    models = [
        normalized_quadratic_model(central, s, (dimension + 1 - s) // 2, terms, arb(radius))
        for s in (0, 1)
    ]
    # Arithmetic after the central congruence still uses certified ball
    # operations. In these coordinates the matrices are close to the identity.
    ctx.prec = 256
    for sector, (quadratic, remainder) in enumerate(models):
        size = (dimension - sector) // 2
        prefix = arb_mat([[quadratic[i, j] for j in range(size)] for i in range(size)])
        if symmetric_sign(isotropic_shift(prefix, 1 - remainder)) != 1:
            raise ArithmeticError("positive interval unresolved")
        print(f"sector {sector}: normalized fourth-and-higher remainder <= {remainder.str(10)}")
    quadratic, remainder = models[last_sector]
    if symmetric_sign(isotropic_shift(quadratic, 1 + remainder)) != -1:
        raise ArithmeticError("quadratic model did not certify the endpoint failure")
    lo, hi = critical_radius_bracket(quadratic, remainder, 16)
    cutoff_ratio = (4 * last_degree + 2 * last_sector + 2) * arb(2) ** (
        4 * last_degree + 2 * last_sector + 3
    ) / central_pivot
    print(f"positive prefix on the full interval: {dimension - 1}")
    print(f"first negative dimension at the endpoint: {dimension}, pivot {pivot.str(12)}")
    print(f"first negative dimension in the unshifted sector: {unshifted_dimension}")
    print(f"first loss radius for dimension {dimension}, in units of 1e-100: [{lo}, {hi}]")
    print(f"central pivot in that direction: {central_pivot.str(12)}")
    print(f"lower bound for (16M-4)/clock scale in the existing cell budget: {cutoff_ratio.str(10)}")


def main():
    ctx.prec = 1024
    count = 48
    terms = 32
    central = source_moments(count + terms)
    print("distance,first negative interleaved dimension,pivot enclosure")
    distances = [fmpq(1, 5), fmpq(1, 10), fmpq(1, 20), fmpq(1, 50)]
    distances += [fmpq(1, 10 ** k) for k in (2, 3, 4, 6, 8, 10, 12)]
    dimensions = {}
    for distance in distances:
        shifted = transverse_moments(central, count, terms, arb(distance))
        dimension, pivot = first_negative_dimension(shifted)
        direct = source_moments(dimension, distance)
        if not all(x.overlaps(y) for x, y in zip(shifted, direct)):
            raise ArithmeticError("source readouts disagree")
        direct_dimension, _ = first_negative_dimension(direct)
        if direct_dimension != dimension:
            raise ArithmeticError("direct and transverse signs disagree")
        dimensions[distance] = dimension
        print(f"{distance},{dimension},{pivot.str(7)}", flush=True)

    print("sector,degree,quadratic scale,upper bound on |remainder|/pivot")
    for degree in (3, 4, 5, 8, 12):
        for sector in (0, 1):
            scale, relative = fixed_direction_test(central, sector, degree, terms)
            print(f"{sector},{degree},{scale.str(7)},{relative.upper().str(7)}", flush=True)


    print("radius,positive interleaved prefix throughout interval,operator norm upper bound")
    for exponent in (2, 6, 12):
        radius = fmpq(1, 10 ** exponent)
        prefix = dimensions[radius] - 1
        while prefix > 0:
            bounds = [
                interval_perturbation_bound(central, sector, (prefix + 1 - sector) // 2, terms, arb(radius))
                for sector in (0, 1)
            ]
            bound = max(bounds)
            if bound < 1:
                print(f"{radius},{prefix},{bound.str(7)}", flush=True)
                break
            prefix -= 1
        else:
            raise ArithmeticError("failed to certify any uniform positive prefix")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--deep", action="store_true", help="certify the window at distance 1e-100")
    if parser.parse_args().deep:
        deep_window()
    else:
        main()
