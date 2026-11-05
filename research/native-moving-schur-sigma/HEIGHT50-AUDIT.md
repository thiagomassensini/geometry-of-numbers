# Height-50 certificate audit and Lean bridge status

## Pinned external source

The inspected source is `teal-sea/zeta-lab` at commit
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534` (Lean `v4.35.0-rc2`, Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`). The source checkout is
`/tmp/zeta-lab-rhheight-audit`; it is clean at that commit.

The declarations in `hunts/rh_height_lean/lean/RHHeight/Main.lean` are
unconditional theorems about Mathlib's `riemannZeta`:

- `RHHeight.rh_height_fifty : RHHeight.RHHeight50` expands to every zeta zero
  with `0 < re < 1` and `0 < im ≤ 50` having `re = 1/2` and analytic order 1.
- `RHHeight.zero_count_fifty : RHHeight.ZeroCountUpTo 50 10` counts ten
  *distinct* zeros in exactly that open-strip, positive-ordinate window.
- `RHHeight.rh_up_to_height_fiftytwo : RHHeight.RHUpToHeight 52` gives the
  same location and simplicity statement through height 52. It is not needed
  for the radius `sqrt 300` target.

`Main.lean` imports `Assembly`, `GammaIncrement`, `HorizontalLegs`,
`ExactArgument`, and `LowHeight`. The 50-height RH/count assembly reduces to
those four analytic/counting pieces: the argument identity, the two enclosures,
the low-height exclusion through 3, and ten line zeros. The 52-height theorem
also uses the ten-zero line input. The height-50 statement is not a hypothesis
or an axiom in the external source.

`HardyFirstZero.first_zero_on_line` is the unconditional existence statement
for a line zero in `(1413/100, 707/50)`, i.e. `(14.13, 14.14)`; its source
explicitly does not assert minimality. The nine individual declarations
`HardyTenZeros.zero_in_2102`, `zero_in_2501`, `zero_in_3042`, `zero_in_3293`,
`zero_in_3758`, `zero_in_4091`, `zero_in_4332`, `zero_in_4800`, and
`zero_in_4977` each assert existence in their respective consecutive
two-decimal intervals. `HardyTenZeros.ten_zeros_on_line_below_fifty` combines
them into ten increasing line zeros but forgets those interval bounds. Thus
the Lean bridge uses the nine individual box statements rather than pretending
the aggregate theorem still contains them.

## Axiom and dependency audit

`RHHeight/CheckMain.lean` pins the unfolded height-50, height-52, and count
statements directly to Mathlib `riemannZeta` and `analyticOrderAt`.
`HardyTenZeros/CheckAxioms.lean` pins the aggregate zero theorem, the first
zero, and all nine box theorems. The corresponding committed `RESULTS.md`
records clean source builds and an axiom audit accepting only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; it records no `sorry`, no
`native_decide`, and no declared axiom. The check scripts fail closed on
missing, duplicate, or nonstandard reports. I inspected those source modules
and audit declarations at the pinned commit. A fresh 4.35 full build has not
been run in this worktree.

## Local compatibility boundary and compiled result

The local project is pinned to Lean `v4.32.0`. `RHHeightEulerMaclaurin.lean`
is a source port from the same external commit, with its unused phase import
removed and tactic syntax adapted. `SigmaRHHeightBridge.lean` and the source
port compile locally with `-DwarningAsError=true`. No external `.olean` is
copied or imported. The bridge hypotheses are the explicit height-50 RH
statement, distinct-zero count, first interval witness, and nine individual
box witnesses.

The bridge proves that every completed-characteristic zero in the target disk
comes from the first certified height or its negative. It separately rules
out real-ordinate zeta zeros by a uniform Euler--Maclaurin lower bound near
the real axis, so the positive-ordinate RH statement is not applied at height
zero. It proves the displaced product's four-point zero set and simple orders,
constructs `SigmaDisplacedProductIsolation (1/5) γ (Real.sqrt 300) 1` without
taking its zero-set or order fields as hypotheses, and applies the existing
`completedNative_sigmaRemainder_pade_root_of_isolation` theorem. The resulting
conditional Padé package gives convergence to both complex heights and
eventual roots of the original sigma pencil.

The local `#print axioms` audit for the zero classification, order theorem,
isolation instance, and Padé recovery reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The external builders have an operational guard that waits for
`MemAvailable ≥ 30 GiB` before each Lean process. At the last check this host
had `MemAvailable = 25.69 GiB`; consequently no external compilation was
started and the guard was not weakened. Completion of the external 4.35 source
build, discharge of the four bridge hypotheses, and a closed final theorem
remain open pending a host that satisfies that guard.
