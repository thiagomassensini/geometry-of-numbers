"""Check the C2 Mellin cancellation and polarized kernel at high precision."""

import mpmath as mp
from flint import arb, arb_series, ctx


mp.mp.dps = 70
CENTER = mp.mpf("0.5")
LOG_TWO = mp.log(2)
MAX_ORDER = 12


def logistic_second(x):
    u = mp.exp(-x)
    return u * (-mp.expm1(-x)) / (1 + u)**3


def mellin_regularized(s, differentiation_order=0):
    return mp.quad(
        lambda x: x**(s + 1) * logistic_second(x) * mp.log(x)**differentiation_order,
        [0, 1, 4, 16, mp.inf],
    )


def interval_factor(s):
    return mp.expm1((1 - s) * LOG_TWO) / (1 - s)


def completed(s):
    return s * (s - 1) * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s) / 2


def log_coefficients(series):
    normalized = [coefficient / series[0] for coefficient in series]
    result = [mp.log(series[0])]
    for order in range(1, len(series)):
        correction = mp.fsum(k * result[k] * normalized[order - k] for k in range(1, order))
        result.append(normalized[order] - correction / order)
    return result


def log_mellin_without_gamma_derivative(s):
    return (
        mellin_regularized(s, 1) / mellin_regularized(s)
        - mp.digamma((s + 3) / 2) / 2
    )


def both_arguments_kernel(log_derivative, z, w):
    direct = 1j * w
    reflected = 1j * mp.conj(z)
    return (
        log_derivative(CENTER + direct) - log_derivative(CENTER - direct)
        - log_derivative(CENTER + reflected) + log_derivative(CENTER - reflected)
    ) / (4 * (direct - reflected))


def certify_camera_hankel_sign():
    ctx.prec = 192
    ctx.cap = MAX_ORDER + 1
    displacement = arb_series([0, 1])
    camera = (
        arb(2).sqrt() * (-arb(2).log() * displacement).exp() - 1
    ) / (arb_series([arb(1) / 2]) - displacement)
    log_camera = camera.log()
    moments = [(-1)**j * (j + 1) * log_camera[2*j + 2] for j in range(6)]

    for shift in (0, 1):
        a, b, c, d, e = moments[shift:shift + 5]
        leading_two = a * c - b**2
        determinant = a * (c * e - d**2) - b * (b * e - c * d) + c * (b * d - c**2)
        assert a > 0 and leading_two > 0 and determinant < 0
        print(f"camera sector {shift}: leading 2x2 {leading_two.str(16)}")
        print(f"camera sector {shift}: 3x3 determinant {determinant.str(16)}")


def main():
    regularized = log_coefficients([
        mellin_regularized(CENTER, n) / mp.factorial(n)
        for n in range(MAX_ORDER + 1)
    ])
    interval = mp.taylor(lambda s: mp.log(interval_factor(s)), CENTER, MAX_ORDER)
    dressing_removed = mp.taylor(
        lambda s: mp.log1p(mp.exp(-s * LOG_TWO)) - mp.log(s) - mp.log(s + 1),
        CENTER, MAX_ORDER,
    )
    actual = mp.taylor(lambda s: mp.log(completed(s)), CENTER, MAX_ORDER)
    reconstructed = (mp.sqrt(mp.pi) / 2) * (2 * mp.sqrt(mp.pi))**(-CENTER) * (
        mellin_regularized(CENTER) / mp.gamma((CENTER + 3) / 2) / interval_factor(CENTER)
    )
    assert abs(reconstructed - completed(CENTER)) < mp.mpf("1e-55")

    print("order | raw cumulant | source after gamma | camera remainder | completed | old fraction | new fraction")
    for n in range(2, MAX_ORDER + 1, 2):
        scale = mp.factorial(n)
        raw = (regularized[n] + dressing_removed[n]) * scale
        source = regularized[n] * scale - mp.polygamma(n-1, mp.mpf(7)/4) / 2**n
        reference = interval[n] * scale
        residual = source - reference
        assert abs(residual - scale * actual[n]) < mp.mpf("1e-44")
        values = raw, source, reference, residual, abs(residual / raw), abs(residual / source)
        print(n, "|", " | ".join(mp.nstr(value, 12) for value in values))

    points = [mp.mpc(".05", ".12"), mp.mpc("-.16", ".21"), mp.mpc(".24", ".09")]
    mellin_slopes = {}
    for point in points:
        for argument in (1j * point, 1j * mp.conj(point)):
            for sign in (-1, 1):
                s = CENTER + sign * argument
                mellin_slopes[s] = log_mellin_without_gamma_derivative(s)

    interval_slope = lambda s: mp.diff(lambda u: mp.log(interval_factor(u)), s)
    completed_slope = lambda s: mp.diff(completed, s) / completed(s)
    residuals = []
    for z in points:
        for w in points:
            via_mellin = (
                both_arguments_kernel(mellin_slopes.__getitem__, z, w)
                - both_arguments_kernel(interval_slope, z, w)
            )
            actual = (
                completed_slope(CENTER + 1j*w) - completed_slope(CENTER + 1j*mp.conj(z))
            ) / (2j * (w - mp.conj(z)))
            residuals.append(abs(via_mellin - actual))
    maximum = max(residuals)
    print("maximum error on 3 x 3 complex kernel:", mp.nstr(maximum, 8))
    assert maximum < mp.mpf("1e-55")
    certify_camera_hankel_sign()


if __name__ == "__main__":
    main()
