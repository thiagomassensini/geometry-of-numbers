# Height-50 certificate audit and integration

## Pinned source and theorem statements

The external proof is from `teal-sea/zeta-lab` commit
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`. The upstream checkout was built and audited with
Lean `v4.35.0-rc2` and Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The source-only compatibility port packaged here is rebuilt with this project's Lean
`v4.32.0` and Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`.

The external results are unconditional theorems about Mathlib's `riemannZeta`:

- `RHHeight.rh_height_fifty` gives location on the critical line and analytic order one for every
  zero with `0 < re < 1` and `0 < im ≤ 50`.
- `RHHeight.zero_count_fifty` counts exactly ten distinct zeros in that strip and ordinate window.
- `HardyFirstZero.first_zero_on_line` gives a line zero in `(1413/100, 707/50)`, which equals
  `(14.13, 14.14)`.
- The nine `HardyTenZeros.zero_in_*` theorems give individual boxes from `(21.02, 21.03)` through
  `(49.77, 49.78)`. The integration uses the individual boxes because the aggregate theorem keeps
  increasing ordinates but forgets the interval endpoints.
- `RHHeight.rh_up_to_height_fiftytwo` is also included in the axiom audit, but is not needed for
  the target radius `sqrt 300`.

The declarations and their external axiom reports are checked by the pinned package's
`check_axioms.py --full`. Its accepted footprint is only `propext`, `Classical.choice`, and
`Quot.sound`; it rejects missing or duplicate reports, `sorry`, and other axioms.

## Lean 4.32 port and closed theorem

The ported sources are under `height50-certified/`. `lean432-compat.patch` records the differences
from the pinned upstream commit. They address Lean/Mathlib version changes in derivative
conversion proofs, the integral proof of an arctangent inequality, a finite-product lemma name,
the logarithmic derivative product lemma name, unused simplifier arguments, and an unused binder.
No `.olean` file was copied or loaded across toolchain versions.

`SigmaHeight50Integration.lean` translates the external RH, exact count, first-zero interval, and
nine individual box theorems to the bridge's four inputs. It then derives closed theorems:

- `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate` proves the requested
  `SigmaDisplacedProductIsolation (1/5) γ (sqrt 300) 1` for some `γ ∈ (14.13, 14.14)`.
- `exists_firstSigmaHeight50PadeRecovery_from_certificate` applies the existing Padé recovery
  theorem to that proved isolation.

The integration does not add source-zero-set or source-order premises. Those fields are proved in
`SigmaRHHeightBridge.lean` from the external finite-height results. The final axiom report checks
the imported RH/count/zero-box theorems, the audited height-52 result, and both closed target
theorems; only the three standard axioms above are allowed.

## Rebuilding and limits

Run:

```sh
LAKE_DIR=/path/to/project/.lake \
  bash research/native-moving-schur-sigma/build_height50_sigma.sh /tmp/height50-build
```

The runner compiles the pinned external source closure with warnings as errors, applies the
external fail-closed audit, rebuilds the sigma dependency modules and bridge with warnings as
errors, compiles the final integration, and checks its axiom report. It writes `.olean` files and
logs only below the chosen output directory. Before each Lean process it waits until Linux reports
at least 30 GiB of `MemAvailable`.

The sigma dependency chain uses the local analysis/carry build outputs gathered by the existing
`compile_sigma_pade.sh`. On this workspace they are available from the main project build cache and
`/home/thlinux/carry-self-adjoint-operator`; another checkout may set `SIGMA_REFERENCE_ROOT` and
`CARRY_LEAN_ROOT` to its corresponding source/build roots. The external certificate itself is
rebuilt from the vendored Lean sources and does not depend on these cached artifacts.
