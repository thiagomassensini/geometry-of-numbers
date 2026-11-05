# Height-50 certificate provenance and Lean 4.32 port

The formal height-50 results come from `teal-sea/zeta-lab` commit
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, independently built and audited with its original
Lean 4.35.0-rc2 toolchain. The 4.32 port in this directory was compiled from source with the
project's Lean `v4.32.0`, Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`, and
warnings treated as errors. No `.olean` file is copied or version-reused.

`lean432-compat.patch` records the source-only compatibility edits against the pinned upstream
commit. They repair version-level API and linter differences in ten files: derivative conversion
proofs, the integral form of the arctangent inequality, one unused binder, unused `simp` rules,
the finite-product monotonicity lemma name, and the logarithmic derivative product lemma name.
The upstream evidence for the certificate remains in the pinned Lean proofs; the port changes
proof plumbing and imports needed by Lean 4.32.

The integrated theorem consumes these declarations directly:

- `RHHeight.rh_height_fifty` and `RHHeight.zero_count_fifty`;
- `HardyFirstZero.first_zero_on_line`;
- the nine `HardyTenZeros.zero_in_*` interval certificates from 21.02 through 49.77;
- `RHHeight.rh_up_to_height_fiftytwo`, included in the axiom report as an audited unused result.

`SigmaHeight50Integration.lean` translates those results to the four finite-height propositions
already used by `SigmaRHHeightBridge.lean`. Its closed isolation theorem proves the source-zero
set and order fields through that bridge; the companion theorem applies the existing Padé recovery
result. Neither theorem adds a source-zero or source-order premise.

Run `research/native-moving-schur-sigma/build_height50_sigma.sh [OUTPUT_DIR]` to rebuild the
external certificate, validate both fail-closed axiom reports, compile the sigma dependencies and
bridge from source, and compile the closed integration. The runner requires the pinned Lean 4.32
toolchain, the root project's Mathlib cache, and the previously built carry/analysis dependency
cache used by `compile_sigma_pade.sh`; `LAKE_DIR`, `LEAN_BIN`, `SIGMA_REFERENCE_ROOT`, and
`CARRY_LEAN_ROOT` may select those local paths. It waits until Linux reports at least 30 GiB of
`MemAvailable` before each Lean process. All generated `.olean` files and logs go to the selected
output directory.
