#!/usr/bin/env python3
"""Certify the camera and source on each completed Hankel Schur direction."""

import argparse
from pathlib import Path
import runpy

from flint import acb, arb, arb_series, ctx


def camera_moments(size, drop_pairs):
    displacement = arb_series([0, 1])
    camera = (
        arb(2).sqrt() * (-arb(2).log() * displacement).exp() - 1
    ) / (arb_series([arb(1) / 2]) - displacement)
    logarithm = camera.log()
    moments = [(-1)**j * (j + 1) * logarithm[2*j + 2] for j in range(2 * size)]
    spacing = 2 * arb.pi() / arb(2).log()
    for k in range(1, drop_pairs + 1):
        inverse_pole = acb(k * spacing, -arb(1) / 2)**(-2)
        power = inverse_pole
        for j in range(len(moments)):
            moments[j] -= power.real
            power *= inverse_pole
    return moments


def matched_pivots(native_moments, reference_moments, shift, size):
    # Both matrices use the basis 1, (196*x), (196*x)^2, ... .
    scale = [arb(196)**j for j in range(2 * size)]
    native = [[native_moments[i+j+shift] * scale[i+j] for j in range(size)] for i in range(size)]
    camera = [[reference_moments[i+j+shift] * scale[i+j] for j in range(size)] for i in range(size)]

    for k in range(size):
        pivot, camera_value = native[k][k], camera[k][k]
        if not pivot > 0 or not camera_value.is_finite():
            raise ArithmeticError(f"Unresolved pivot or camera at shift={shift}, degree={k}")
        unscaled_pivot = pivot / scale[2*k]
        yield unscaled_pivot, camera_value / pivot

        weights = {i: native[i][k] / pivot for i in range(k + 1, size)}
        for i in range(k + 1, size):
            for j in range(i, size):
                # Apply the congruence from the native elimination to both forms.
                native_value = native[i][j] - weights[i] * native[j][k]
                updated_camera = (
                    camera[i][j] - weights[i] * camera[k][j] - weights[j] * camera[i][k]
                    + weights[i] * weights[j] * camera_value
                )
                native[i][j] = native[j][i] = native_value
                camera[i][j] = camera[j][i] = updated_camera


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=20)
    parser.add_argument("--bits", type=int, default=3072)
    parser.add_argument("--drop-pairs", type=int, default=0)
    args = parser.parse_args()
    if args.size < 1 or args.bits < 64 or args.drop_pairs < 0:
        parser.error("--size must be positive, --bits at least 64, and --drop-pairs nonnegative")

    upstream = Path(__file__).with_name("certify-radial-reduction-pivots.py")
    completed_moments = runpy.run_path(str(upstream))["completed_moments"]
    ctx.prec = args.bits
    native = completed_moments(args.size)
    camera = camera_moments(args.size, args.drop_pairs)
    print(f"Common camera pairs removed from both forms: {args.drop_pairs}", flush=True)

    print("shift,degree,native pivot,camera/native,source/native", flush=True)
    for shift in (0, 1):
        for degree, (pivot, ratio) in enumerate(matched_pivots(native, camera, shift, args.size)):
            print(
                f"{shift},{degree},{pivot.str(12)},{ratio.str(12)},{(1 + ratio).str(12)}",
                flush=True,
            )


if __name__ == "__main__":
    main()
