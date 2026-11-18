"""Certified finite sign tests for the original completed log-modulus moments."""

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


def first_negative_dimension(moments):
    for order in range(len(moments)):
        degree, sector = divmod(order, 2)
        pivot, _ = schur(moments, sector, degree)
        if pivot < 0:
            return order + 1, pivot
        if not pivot > 0:
            raise ArithmeticError(f"pivot sign unresolved at dimension {order + 1}: {pivot}")
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


def interval_perturbation_bound(moments, sector, size, terms, radius):
    """Operator norm bound on the entire interval in a central orthonormal basis."""
    if size == 0:
        return arb(0)
    basis = normalized_central_basis(moments, sector, size)
    absolute_basis = arb_mat([[abs(basis[i, j]) for j in range(size)] for i in range(size)])
    error = arb_mat(size, size)
    for order in range(1, terms):
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
    main()
