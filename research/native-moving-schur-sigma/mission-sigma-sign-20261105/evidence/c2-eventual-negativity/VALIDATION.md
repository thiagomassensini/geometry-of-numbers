# C2: eventual negativity of the original Padé minors

**Status:** proof, compilation and axiom audit passed locally; PR and merge are pending.

The compiled root is
`CarrySigmaObstruction.exists_eventually_negative_sigmaPadeD_from_height50_certificate` in
`SigmaPadeEventualNegativity.lean`. It proves

```lean
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0
```

The proof composes the certified isolation theorem, the exact decomposition of the original
`completedSigmaLogJet`, its exponential zero-pair remainder bound, the unit-circle normalized-minor
limit and the negative-limit transfer. The remainder stays in the argument; no sign premise is
added and the two-pole moments do not replace the original jets.

## Validation

- Toolchain: Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry source: clean checkout at `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Height-50 source: `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, ported to 4.32.
- `c2-focused-build.log.gz` records the sequential recompilation of the shared C1 bridge, the
  isolation/Pade/remainder modules, the height-50 integration and the C2 root, all with
  warnings treated as errors.
- `height50-axiom-audit.log` accepted all 72 external certificate reports.
- `integration-axiom-audit.log` accepted all 17 height-50 integration reports, including C2.
- `transitive-pade-audit.log` accepted 124 public sigma roots and 70,828 transitive type/body
  dependencies. It confirms the original characteristic and sigma jets remain in the proof
  closure. The C2 root depends only on `propext`, `Classical.choice` and `Quot.sound`.
- `height50-external-build.log.gz` preserves the full external Lean build output byte-for-byte
  after decompression.

During the first joined build, `SigmaRHHeightBridge.lean` redeclared two theorems already supplied
by `SigmaNativeZeroBridge.lean`: `sigmaNativeCompletionFactor_ne_zero_of_strip` and
`completedNativeCharacteristicContinuation_zero_iff_zeta`. The copies were removed, and the
bridge now reuses C1's existing `sigmaLineZero`; the joined bridge and integration then compiled.

## Reproduction

Provide paths to the pinned Mathlib/Carry caches and the existing C1 source cache, then run:

```bash
LAKE_DIR=/path/to/geometry-of-numbers/.lake \
CARRY_LEAN_ROOT=/path/to/clean-carry-at-045369 \
SIGMA_REFERENCE_ROOT=/path/to/geometry-of-numbers-c1-cache \
bash research/native-moving-schur-sigma/build_height50_sigma.sh /path/to/output
```

The runner gates each Lean process on at least 30 GiB of `MemAvailable`. The source and command
pins for resuming the separate Lean 4.35 experiment remain in
`../lean435-validation-incomplete/`; that experiment is not part of C2 validation.
