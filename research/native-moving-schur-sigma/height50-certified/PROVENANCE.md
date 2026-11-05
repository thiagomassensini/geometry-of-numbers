# Height-50 certificate provenance and Lean 4.32 port

The formal height-50 results come from `teal-sea/zeta-lab` commit
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, independently built and audited with its original
Lean 4.35.0-rc2 toolchain. The 4.32 port in this directory was compiled from source with the
project's Lean `v4.32.0`, Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`, and
warnings treated as errors. No `.olean` file is copied or version-reused.

The vendored sources are limited to the source files used by the 74 modules in the `--full`
runner, including the exact 38-module `Zeta23` closure, and its six axiom-check files. Unused hunt
and vendor modules are omitted; the build log and source hashes record the retained closure.

`lean432-compat.patch` records the source-only compatibility edits needed by the C1 first-zero
subset. `lean432-full-compat.patch.gz` preserves the full source-only API and linter changes needed
by the height-50 integration, including the ten patched files and changes to counting modules that
C1 does not import. The upstream evidence for the certificates remains in the pinned Lean proofs;
these patches adapt proof plumbing and imports to Lean 4.32.

The integrated theorem consumes these declarations directly:

- `RHHeight.rh_height_fifty` and `RHHeight.zero_count_fifty`;
- `HardyFirstZero.first_zero_on_line`;
- the nine `HardyTenZeros.zero_in_*` interval certificates from 21.02 through 49.77;
- `RHHeight.rh_up_to_height_fiftytwo`, included in the axiom report as an audited unused result.

`SigmaHeight50Integration.lean` translates those results to the four finite-height propositions
already used by `SigmaRHHeightBridge.lean`. Its closed isolation theorem proves the source-zero
set and order fields through that bridge; the companion theorem applies the existing Padé recovery
result. Neither theorem adds a source-zero or source-order premise.

`SigmaPadeEventualNegativity.lean` composes the certified isolation with the decomposition of the
original `completedSigmaLogJet`, the exponential zero-pair remainder bound, the normalized-minor
limit and the negative-limit lemma. It proves `∃ P, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0` without a
sign premise and without replacing the original jets by the two-pole model.

When the bridge was joined to C1, it redeclared
`sigmaNativeCompletionFactor_ne_zero_of_strip` and
`completedNativeCharacteristicContinuation_zero_iff_zeta`, already supplied by
`SigmaNativeZeroBridge.lean`. Those duplicates were removed and the bridge now imports
`SigmaCertifiedNegativeDirection.lean`, reusing its one definition of
`CarrySigmaObstruction.sigmaLineZero` as well.

Run `research/native-moving-schur-sigma/build_height50_sigma.sh [OUTPUT_DIR]` to rebuild the
external certificate, validate both fail-closed axiom reports, compile the shared C1 bridge and
sigma dependencies, then compile the closed integration and C2 conclusion. The runner requires
Lean 4.32, the root project's pinned Mathlib cache, and the previously built Carry/analysis
dependency cache used by `compile_sigma_pade.sh`. `CARRY_LEAN_ROOT` must point to a clean checkout
at `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; `LAKE_DIR`, `LEAN_BIN`, and `SIGMA_REFERENCE_ROOT`
select the local Mathlib and prior-source caches. It waits until Linux reports at least 30 GiB of
`MemAvailable` before each Lean process. All generated `.olean` files and logs go to the selected
output directory. The successful C2 build and axiom audits are recorded in
`mission-sigma-sign-20261105/evidence/c2-eventual-negativity/`.
