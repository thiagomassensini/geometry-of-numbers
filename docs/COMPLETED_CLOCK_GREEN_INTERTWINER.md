# Completed boundary clock: geometric intertwiner investigation

Initial main: `ce3077323ddb32df1931c1d0c2dba12a78d72c06`.

## Necessary candidate tests (increment 1)

A: raw nodal Decode is excluded on the critical orbit. The locally proved
`criticalMaterialSample_norm_sq` is 1/n and
`criticalMaterialSample_not_memℓp` invokes harmonic divergence. Material edges
are not vertical depths.

B: a linear isometry retaining the standard completed-product inner product
cannot intertwine the existing partial clock with a formally symmetric partial
operator. `completedClock_isometric_intertwiner_impossible` keeps both domain
preservation and operator equality explicit. This excludes metric-preserving
repair; it does not exclude a different geometrically derived transform.

C: core 1, left legs at depths 2 and 3 are material 3 and 7. The source imposes
energy ratio 1/2. Historical material samples have energies 1/3 and 1/7.
`no_direct_c2PhysicalSource_match` contradicts simultaneous matching at these
odd points alone. This is NO_GO_DIRECT_C2_PHYSICAL_SOURCE_MATCH, not a no-go
for enriched synthesis. The proof neither equates amplitudes nor uses moments.

## Read-only architectural comparison

`thiagomassensini/carry-self-adjoint-operator`, revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`:
`C3SeededClockShiftIdentity.lean`,
`CompletedNativeSeededClockTfvdSixSource.lean`,
`CompletedNativeReturnMetricReadoutCrosswalk.lean` (CarrySelfAdjointOperator/).
Incoming seed, ordinary gradients and one clock step precede TFVD. Lossless
reconstruction is distinct from isometry and moment calibration. Endpoint
plus Poisson return reproduces its source metric; the historical concrete
candidate is explicitly not calibrated to the canonical zeroth moment.
No historical theorem, dependency or Fin 3 block is imported.

## Audit

All five public theorems are registered in Analysis/Audit and the focused audit.
Expected transitive footprint: propext, Classical.choice, Quot.sound. No new
mathematical axiom or placeholder. Build/kernel/audit results are recorded after
execution. No moments, Hankel, metric instance or height operator is constructed.

## Next finite investigation

Retain seed, gradient, triangular clock gradient, whole-cell boundary and its
clock return before any readout. A candidate symmetric target must be tested
for its exact norm before taking an infinite limit. No enriched intertwiner
has been proved by the necessary tests above.

Increment 1 verification (all exit 0): `lake build --wfail` focused module,
focused audit, Analysis and Analysis.Audit; `lake env lean` focused audit;
`bash scripts/audit-analysis.sh`, `audit-foundation.sh`, `audit-geometry.sh`;
new-source forbidden-token scan; `git diff --check`. All five theorem footprints
are `[propext, Classical.choice, Quot.sound]`.
