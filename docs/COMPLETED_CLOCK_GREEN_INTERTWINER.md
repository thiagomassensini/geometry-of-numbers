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

## Finite enriched test (increment 2)

Status: **NO_GO_ENRICHED_TFVD_INFINITE_NORM**, scoped to the explicitly
constructed nodal Green/Parseval candidate below. No statement excludes every
possible TFVD-enriched transform.

First increment published: `4d472ad4ca824a02b6f9f09adc84747ffa287536`.

For N cells the existing synchronized cutoff is 4N material edges and 4N+1
samples. `finiteCompletedEnrichedSource N y = (y, L_N y)` retains incoming
seed, ordinary gradient, its triangular clock-gradient, whole-cell boundary,
and the clocked whole-cell return. The boundary slots are graph data, not
independent free coordinates. The orbit coordinate theorems identify both the
ordinary gradient and clock gradient with the existing completed orbit.
No component is defined through S, its derivative, or a moment.

`finiteCompletedGraphDecode` reconstructs the actual finite material samples.
`finiteMaterialGreenDomain` places these at PNat j+1 using finite sums of the
existing material basis. Its domain proof and coordinate theorem are explicit;
its inner-product/norm preservation comes from these material deltas.
`finiteCompletedGreenIntertwiner` then applies the existing canonical P. This
is a finite Green map, not a newly chosen TFVD weighting. It is injective and
satisfies the typed equality

```
greenParsevalMaterialLogOperator
  ⟨finiteCompletedGreenIntertwiner N y, domain_proof⟩
  = finiteCompletedGreenIntertwiner N (finiteCompletedBoundaryClock N y).
```

The target's self-adjointness is reused, not reproved. Consequently the
pulled-back finite Green pairing is symmetric. No global inner-product instance
is introduced and standard-product symmetry remains excluded.

The enriched Green analysis retains both this ordinary image and its clocked
image in the standard Hilbert product of two existing ConcreteAnalysisSpaces.
Both slots intertwine the existing partial Green clock and the map is injective.
A separate `ordinaryGradient_isometric_intertwiner_impossible` excludes repairing
the clock by an isometry of the ordinary-gradient ℓ² norm alone, even with seed
forgotten. Its witnesses are the already-local material deltas at 1 and 2.

## Exact energy test and infinite obstruction

On the current critical orbit the ordinary Green image has exactly

    sum_{n=1}^{4N+1} 1/n.

The enriched ordinary+clock image has exactly

    sum_{n=1}^{4N+1} (1 + (log n)^2)/n.

The two `critical_energy_tendsto` theorems prove divergence to +infinity.
The two `critical_no_limit` theorems exclude convergence to any vector of the
respective fixed ambient Hilbert carriers. Thus no infinite J is obtained by
this finite nodal reconstruction, even after retaining one clock step. This is
a proved obstruction for this route, not merely an unproved uniform bound.
No diagonal weights or metric adjustment is made.

## What remains and what does not follow

Local TFVD fiber synthesis is lossless but has no theorem identifying an
alternate completed material-edge enriched source with a finite-energy state
for the existing symmetric Green material clock. The actual missing transform
must act on retained `(seed, g, C(seed,g), B_N(g), B_N(C(seed,g)))`, preserve
material provenance and intertwine the existing target clock. It cannot be
this nodal J_N: its norm is proved divergent. For an orbit-specific candidate
its next required equation would be

    A_geom ⟨JY(t), target_domain_proof⟩ = JClockY(t),

only after a geometrically derived finite-energy JY has actually been built.
Neither such JY nor an infinite partial intertwiner is asserted here. Existing
C2 address decomposition may only use decoded physical depth; no edge-number
is relabeled as depth. The tested C2 source has depth amplitude and is not
identified with the historical material amplitude.

Return-metric blueprint cannot repair this candidate while preserving the
underlying material/Parseval Gram: its endpoint+Poisson cancellation equals the
original source Gram, so the harmonic energy test still applies. No return
metric is ported or declared to identify moments. No Krylov or canonical first
column is invoked. A genuinely different geometrically derived enriched
energy remains an investigation, not a free metric choice.

Public definitions and theorems are registered in both Analysis/Audit and the
focused audit. Build/kernel/audit execution is recorded below after completion.

Increment 2 verification (all exit 0): focused module and focused audit builds
with `--wfail`; Analysis and Analysis.Audit with `--wfail`; focused `lake env
lean` kernel report; Analysis/Foundation/Geometry audit scripts; forbidden-token
scan on new Lean sources and `git diff --check`. All new public names have
axiom guards. The intertwining, energy, divergence and no-limit capstones print
`[propext, Classical.choice, Quot.sound]`. Commit message:
`analysis: intertwine finite enriched boundary clocks and exclude nodal limit`.
