# C3 Taylor coefficient bridge — Lean 4.32

## Compiled result

`SigmaContour51TaylorCoefficientBridge.lean` proves four theorems:

- `contourTaylorCoefficient_deriv_eq_nat_mul` identifies the Taylor coefficient of a derivative
  with the next coefficient of the original function multiplied by `k+1`.
- `contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_contains` constructs a
  rectangle for the derivative Taylor polynomial from the same coefficient rectangles used for
  the function.
- `contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_inflate_contains`
  transports a rationally bounded derivative remainder through that rectangle.
- `contourTaylorCauchyValueAndDerivativeBoxes` combines the function and derivative Cauchy
  remainders with the shared coefficient and displacement boxes to produce both value enclosures.

The final theorem assumes `0<r`, `DiffContOnCl` of the function on the radius-`r` disk,
`DifferentiableOn` of its derivative there, a boundary norm majorant `M`, `z` in the disk,
`0≤q<1`, `‖z-c‖≤q*r`, rational boxes containing the Taylor coefficients through `N`, a rational
box containing `z-c`, and rational errors at least as large as both Cauchy tail formulas. Every
input is explicit.

## Boundary for the radius-51 source

For `f=riemannZeta`, this shares a single Taylor coefficient table between ζ and ζ′, matching
`acb_series.zeta()` in the Arb script. It does not prove the coefficient rectangles enclose the
exact Lean derivatives, nor does it prove the per-disk zeta analyticity and majorants, the
arc-displacement boxes, digamma boxes, or the final comparisons against the Arb residual
endpoints. Thus no 4096-arc residual inclusion, 512-arc circle inclusion, residual sign, or
unconditional central positivity follows from this module.

The residual ranges remain the original-source quantities `e_n=H_n-P_n` by the compiled C2
residue identity. The Taylor tail is only a bound for the evaluator on an arc; it becomes a bound
for `e_n` after pointwise inclusion and integration. It is distinct from both the ten-mode residue
and the material C2 tail. The determinant proof retains all five cross terms.

## Build and audit

Lean 4.32.0, warnings as errors, exclusive output root
`/home/thlinux/tmp/c2-contour51-20261108-lean432`, exit 0. The four `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or declared axiom occurs in the
source. Attempts 1 and 3 failed during proof development, attempt 2 compiled an intermediate
version, and attempt 4 is the final build; all logs are preserved beside this memo.

The source, OLean, and final log SHA-256 values are recorded in `../VALIDATION.md`.
