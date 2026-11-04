#!/usr/bin/env python3
"""Independent Cauchy extraction from the original completed xi characteristic.

The reference zero ordinates are deliberately not inputs to this script. It evaluates
F(z) = 1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s), s=1/2+i*z, and extracts the
original sigma jets from the Taylor coefficients of the displaced logarithmic response.
"""

from __future__ import annotations

import csv
import mpmath as mp


MP_DPS = 100
QUADRATURE_N = 128
CONTOUR_RADII = (mp.mpf(100), mp.mpf(150))
DISPLACEMENTS = (mp.mpf("0.1"), mp.mpf("0.2"))
SHIFTS = (0, 2, 4, 8, 12, 16, 20, 24)


def completed_native_F(z: mp.mpc) -> mp.mpc:
    """Classical formula for the source F=A*N, continued as completed xi."""
    s = mp.mpf("0.5") + 1j * z
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.exp(-s * mp.log(mp.pi) / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def original_log_response(z: mp.mpc) -> mp.mpc:
    """Q=-F'/(2F), using the exact logarithmic derivative of the displayed F."""
    s = mp.mpf("0.5") + 1j * z
    dlog_ds = (
        1 / s
        + 1 / (s - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(s / 2) / 2
        + mp.zeta(s, derivative=1) / mp.zeta(s)
    )
    return -1j * dlog_ds / 2


def sigma_generator_value(u: mp.mpc, d: mp.mpf) -> mp.mpc:
    """G_d(u)=sigmaTransverseMean(Q,sqrt(u),d)/sqrt(u), from the source identity."""
    t = mp.sqrt(u)
    transverse_mean = (
        original_log_response(t - 1j * d)
        + original_log_response(t + 1j * d)
    ) / 2
    return transverse_mean / t


def cauchy_jets(d: mp.mpf, radius: mp.mpf, nmax: int) -> tuple[list[mp.mpf], mp.mpf]:
    """Extract h_0,...,h_nmax on |u|=radius by the periodic trapezoid rule."""
    sums = [mp.mpc(0) for _ in range(nmax + 1)]
    for j in range(QUADRATURE_N):
        theta = 2 * mp.pi * j / QUADRATURE_N
        u = radius * mp.exp(1j * theta)
        value = sigma_generator_value(u, d)
        weight = 1 / QUADRATURE_N
        inverse_power = mp.mpc(1)
        for n in range(nmax + 1):
            sums[n] += weight * value * inverse_power
            inverse_power /= u
    jets = [mp.re(x) for x in sums]
    imag_residual = max(abs(mp.im(x)) for x in sums)
    return jets, imag_residual


def pencil_roots(jets: list[mp.mpf], shift: int) -> tuple[mp.mpc, mp.mpc]:
    h0, h1, h2, h3 = (jets[shift + k] for k in range(4))
    D = h0 * h2 - h1**2
    B = h0 * h3 - h1 * h2
    C = h1 * h3 - h2**2
    disc = mp.sqrt(B**2 - 4 * D * C)
    return (B + disc) / (2 * D), (B - disc) / (2 * D)


def recovered_positive_height(jets: list[mp.mpf], shift: int) -> mp.mpc:
    roots = pencil_roots(jets, shift)
    # For d>0 the member corresponding to (gamma+i*d)^(-2) has negative imaginary part.
    lam = min(roots, key=lambda value: mp.im(value))
    return mp.sqrt(1 / lam)


def main() -> None:
    mp.mp.dps = MP_DPS
    probe = mp.mpc("0.83", "2.17")
    direct_response = -mp.diff(completed_native_F, probe) / (2 * completed_native_F(probe))
    logarithmic_response = original_log_response(probe)
    if abs(direct_response - logarithmic_response) > mp.mpf(10) ** (-(MP_DPS // 2)):
        raise ArithmeticError("logarithmic derivative does not match the original completed F")
    nmax = max(SHIFTS) + 3
    writer = csv.writer(__import__("sys").stdout)
    writer.writerow(
        [
            "d",
            "shift_s",
            "contour_r100_height_re",
            "contour_r100_height_im",
            "contour_r150_height_re",
            "contour_r150_height_im",
            "height_contour_difference",
            "contour_r100_max_imag_jet",
            "contour_r150_max_imag_jet",
        ]
    )
    for d in DISPLACEMENTS:
        by_radius: dict[mp.mpf, list[mp.mpf]] = {}
        residuals: dict[mp.mpf, mp.mpf] = {}
        for radius in CONTOUR_RADII:
            jets, imag_residual = cauchy_jets(d, radius, nmax)
            by_radius[radius] = jets
            residuals[radius] = imag_residual
        for shift in SHIFTS:
            h100 = recovered_positive_height(by_radius[CONTOUR_RADII[0]], shift)
            h150 = recovered_positive_height(by_radius[CONTOUR_RADII[1]], shift)
            writer.writerow(
                [
                    mp.nstr(d, 6),
                    shift,
                    mp.nstr(mp.re(h100), 30),
                    mp.nstr(mp.im(h100), 30),
                    mp.nstr(mp.re(h150), 30),
                    mp.nstr(mp.im(h150), 30),
                    mp.nstr(abs(h100 - h150), 8),
                    mp.nstr(residuals[CONTOUR_RADII[0]], 8),
                    mp.nstr(residuals[CONTOUR_RADII[1]], 8),
                ]
            )


if __name__ == "__main__":
    main()
