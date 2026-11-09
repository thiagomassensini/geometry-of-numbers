# Reuse C5's certified `log π` interval in C3

`SigmaContour51C5PiBridge.lean` defines `contour51C5LogPiBox` from the existing
`c5PiLogInterval 160` and proves that this complex rectangle contains
`Complex.log (Real.pi : ℂ)`. The proof reuses `c5_pi_log_interval_contains`; it does not repeat the
Machin bound or logarithm interval evaluation.

The committed C5 zeta-node results `c5RationalZetaNodeBox_contains` and
`c5RationalZetaCenteredNodeBox_contains` only enclose zeta at exact rational points near
`0.5 + 0i` (`a∈[2/5,3/5]`, `b∈[0,128/100000]`). They do not enclose a continuous rectangle, ζ′, or
Taylor coefficients and do not cover the radius-51 path. The C5 Gamma node certificates are
likewise fixed-node values and provide no digamma variation bound on `s/2`. The reusable C5 parts
for this contour are therefore the exact `log π` interval, rational interval arithmetic, and the
source normalization/transport already formalized separately. No Bernoulli table or full zeta or
Gamma node list was duplicated.

The bridge proves the `log π` component. `SigmaContour51ArcGeometry.lean` now supplies the
continuous 4096-arc boxes for the contour parameter and `s(u)`. The zeta/derivative coefficient
boxes, digamma box, positive norm-square bounds, and comparisons with each Arb arc endpoint remain
open. No residual sign or central positivity conclusion follows.

Lean 4.32.0, `-DwarningAsError=true`, exclusive C2 output root, exit 0. The theorem axiom report is
`[propext, Classical.choice, Quot.sound]`; the source has no `sorry`, `admit`, or declared axiom.
The final source, OLean, log, and imported C5 dependency OLean hashes are recorded in
`../VALIDATION.md`.
