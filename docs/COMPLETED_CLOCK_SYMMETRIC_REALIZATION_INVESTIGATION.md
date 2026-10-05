# Completed material clock versus the separated center block

Initial HEAD = main = origin/main:
`cce1a25add301ff8050493769e7960dba0179d13`.
`git pull --ff-only origin main` reported already up to date; the tree was clean.

**STATUS: `NO_GO_SEPARATED_CENTER_AS_COMPLETE_CLOCK`.**

Scope: the **unchanged bounded** separated center block cannot faithfully
intertwine every finite cutoff of the completed material clock. This does not
exclude a particular smaller cutoff, an orbit-only/lossy map, cutoff-dependent
operators with growing norm, or a future realization with a genuine material
frequency diagonal. No canonical-moment or whole-theory obstruction is claimed.

## Inventory before construction

Names below are existing declarations, not proposed objects. Native finite
objects are in `Analysis.NativeMaterialClock` / `Analysis.FiniteClockJets`;
completed objects are in `Analysis.BaseTwoCompletion`. The Green generator and
ambient operator are in `Analysis.GreenStateMaterialLog` and
`Analysis.GreenParsevalMaterialLog`, respectively.

| Object | Domain / input | Codomain | Status | Provenance and retained channels |
| --- | --- | --- | --- | --- |
| `finiteMaterialClock M` = `finiteRealSpectralGenerator M` | `FiniteRealSpectralHilbert M` | same | finite, real-frequency symmetric linear operator | Existing diagonal log(j+1), all material samples |
| `finiteMaterialOrbit M t` | same | same | unitary finite evolution | exp(-it log(j+1)); generator of derivatives is -i L, not self-adjoint L |
| `historicalInitialState M` | cutoff M | finite material Hilbert | existing finite-energy state | amplitude 1/sqrt(j+1), independent of moments |
| `finiteSeedGradientEncode K`, `finiteSeedGradientDecode K` | samples / seeded gradients | seeded gradients / samples | inverse finite linear maps, not unitary | incoming seed and K consecutive material differences |
| `finiteSeedGradientClock K` | `FiniteSeedGradientCarrier K` | same | finite total operator; standard symmetry not presumed | Encode L Decode; diagonal plus causal prefix term |
| `finiteCompletedBoundaryGraph N` | graph in `FiniteCompletedBoundaryCarrier N` | submodule | finite | seed, 4N gradients, whole-cell return as redundant graph coordinate |
| `finiteCompletedBoundaryClock N` | this graph | same graph | finite total clock | derived clocked cell return; graph invariant |
| `finiteCompletedBoundaryOrbit N t` | initial 4N+1 samples | this graph | existing orbit | incoming seed, gradients and exact complete-cell boundary |
| `baseTwoConcreteSeededGradientState t` | real t | `BaseTwoSeededMaterialHilbert` | existing Hilbert state | seed plus completed material gradient, before scalar readout |
| `baseTwoCompletedMaterialGradientL2 t`, `baseTwoCompletedMaterialClockL2 t` | real t | `MaterialEdgeL2` | genuine l2 states | ordinary material differences and log-weighted differences |
| `baseTwoPhysicalOrdinaryC2State t`, `baseTwoPhysicalLogGradientC2State t` | completed difference states | `GlobalC2BranchCarrier` | realified Hilbert states | physical edge -> odd endpoint -> true C2 address; both quadratures |
| `baseTwoPhysicalResidualTfvdAnalysis eta` | `MaterialEdgeL2` | `C2RealTfvdChannels × MaterialEdgeL2` | injective real linear analysis; each fiber map continuous | full actual physical TFVD plus residual material edges |
| `baseTwoCompletedPhysicalResidualTfvdPair eta t` | completed ordinary/log pair | two such channel bundles | existing vector data | both difference channels, both residuals, TFVD traces |
| `realCarryTfvdAnalysis eta`, `realCarryTfvdSynthesis eta` | vertical l2 / bracket+trace | bracket+trace / vertical l2 | continuous; synthesis left inverse under 0<eta<1 | bracket, initial value and weighted initial slope; Green+return recovers state |
| `baseTwoCompletedBoundaryHilbertState t` | real t | `BaseTwoCompletedBoundaryHilbertCarrier` | strong limit of geometric prefixes | seed, complete material-gradient interior, derived total boundary |
| `completedBoundaryTransportedClock` | its graph domain in that carrier | same ambient carrier | partially defined; standard product nonsymmetric and not self-adjoint | triangular material clock interior and summable clocked complete-cell return |
| `greenStateMaterialLogGenerator` | log-square-summable domain in Green State | Green State | unbounded self-adjoint partial operator | existing unitary material reindexing; log(n) coordinate multiplier |
| `greenParsevalMaterialLogOperator` | transported maximal domain in `ConcreteAnalysisSpace` | same | unbounded self-adjoint partial operator | Parseval transport on range, zero on orthogonal gauge |
| `baseTwoNormalizedCenterReconstruction`, `baseTwoCenterLegSynthesis` | seeded material / center l2 | center l2 / physical edge l2 | continuous bound 4 / isometry | geometric log-gap normalization; incoming and outgoing roles distinct |
| `baseTwoSeparatedCenterBlock` | P + C_in + C_out | same | bounded symmetric continuous linear operator | T, S and their own adjoints; no material-frequency diagonal, independent seed, residual or full boundary |
| `baseTwoCompletedBoundaryHilbertReadout` | completed boundary carrier | Complex | bounded scalar readout | seed plus derived boundary equals complete signal; not a clock |

The infinite transported clock domain requires the actual boundary HasSum,
clock coordinates in l2, and summability of clocked cell returns. Existing
`completedBoundaryState_hasDerivAt_clock` gives Y'=-i L_boundary Y strongly.
This investigation does not extend its domain or change its metric.

## Finite model and exact necessary intertwining test

Use the **existing** synchronized geometry: N cells, 4N consecutive material
edges, 4N+1 samples. `finiteSeedGradientClock_intertwining` and
`finiteCompletedBoundaryClock_intertwining` already identify the exact material
clock in seed/gradient coordinates and in its redundant boundary graph. They
are reused, not rederived.

The tested target is A = `baseTwoSeparatedCenterBlock`, unchanged. We quantify
over every linear U, not only a preferred chart or an isometric embedding:

```lean
U : FiniteRealSpectralHilbert M →ₗ[ℂ] BaseTwoSeparatedCenterHilbert
Function.Injective U
∀ x, U (finiteMaterialClock M x) = A (U x)
```

For the existing basis e_j, L e_j = log(j+1) e_j. Injectivity gives U e_j != 0.
The proposed equality would imply

```text
A(U e_j) = log(j+1) • U e_j
log(j+1) * norm(U e_j) <= norm(A) * norm(U e_j).
```

Hence log(j+1) <= norm(A). `separatedCenterBlock_no_injective_finiteClock_intertwiner`
proves the contradiction when log(j+1)>norm(A). No bound on U, isometry, source
norm, moments, or positivity is used. The fact that U is only linear makes the
obstruction stronger than an isometric-intertwiner test.

`separatedCenterBlock_exists_excluded_baseTwo_cutoff` constructs a certified
excluded synchronized cutoff using `exists_nat_gt (exp(norm(A)))`. Choose such
N and j=N in Fin(4N+1); strict log monotonicity gives log(N+1)>norm(A). This is
an exact existence proof, with no decimal estimate of norm(A) or eigenvalues.
It does **not** assert that this is the first/smallest failing cutoff.

The seed/gradient theorem transports this obstruction through the existing
linear equivalence. The completed boundary theorem additionally composes U
with the existing graph embedding, whose left inverse is boundary-forget.
Thus it covers the **actual complete finite graph**, including its derived
boundary coordinate, not only raw samples or a physical projection.

New capstones:

- `separatedCenterBlock_no_injective_finiteClock_intertwiner`
- `separatedCenterBlock_no_injective_seedGradient_intertwiner`
- `separatedCenterBlock_exists_excluded_baseTwo_cutoff`
- `separatedCenterBlock_not_complete_materialClock_realization`
- `separatedCenterBlock_not_completedBoundaryClock_realization`

The last theorem refutes the statement that for **every** N there is an
injective U_N from the genuine finite completed boundary graph with
U_N L_N = A U_N. It does not claim that every individual finite cutoff fails.
No U_N is defined by moments or adjusted coefficients.

## Missing term, amplification and existing alternative

The necessary missing capacity is the material frequency action itself: log(n)
is unbounded as cutoffs grow, while A is a fixed bounded center-coupling block.
Its symmetry alone cannot supply that diagonal. This theorem does not prove
that adding a diagonal alone is sufficient, nor determine a minimal enlarged
carrier. Adding a fixed uniformly bounded collection of trace/adjoint blocks
cannot by itself justify an unbounded material-clock realization.

There is an **already local** finite alternative:
`finiteCompletedGreenIntertwiner N`, from `FiniteCompletedClockGreenIntertwiner`.
It is the precise composition

```text
finiteCompletedGraphDecode
  -> finiteMaterialGreenEmbedding
  -> greenParsevalAnalysis.
```

It is injective, takes values in the domain of the existing self-adjoint
`greenParsevalMaterialLogOperator`, and `_clock` proves its exact finite
intertwining with `finiteCompletedBoundaryClock`. Its energy on the existing
critical initial state is exactly the harmonic prefix sum over 4N+1 samples.
The already proved `_critical_energy_tendsto` and `_critical_no_limit` exclude
its infinite critical Hilbert limit. Enriching it with its clock step likewise
has a previously proved divergent energy. No nodal reconstruction or new metric
is introduced in the present proofs, and this known finite route is not sold
as a new infinite completed-state solution.

Any future candidate A_N must retain material frequency action (its norm must
at least reach its transported eigenvalues). An infinite candidate must address
operator domain and critical finite energy. The physical/residual, seed and
boundary channels above must also be explicitly retained through actual
analysis/synthesis; no claim is made that the separated center sectors alone
do so. Constructing a minimal symmetric amplification is a subsequent gate,
not a theorem obtained here.

## Seed, first column and independence

The current A fails the prerequisite complete clock-realization test. Therefore
no new v_N is designated, and canonical first-column tests r=0,1,2,3 are **not
performed**. The historical finite initial state remains an existing input to
the known finite Green route; its divergent limit is not reinterpreted as
v_completed. The conditional first-column theorem from the prior round remains
conditional. No canonical moment, Hankel, Jacobi, height or Krylov independence
claim is added. All no-gos from the prior round remain intact.

## Provenance and validation

Proof inputs are exclusively current local finite-clock, finite-coordinate and
completed-graph declarations, the existing bounded center block and Mathlib
operator-norm/exp/log inequalities. No historical package or new operator,
metric, amplitude, moment or scalarized state is introduced. Foundation is
unchanged. Every public name is registered with `#assert_analysis_axioms` and
`#print axioms` in central and scoped audits. Allowed footprint is only
`[propext, Classical.choice, Quot.sound]` or a subset.

```bash
lake build --wfail GeometryOfNumbers.Analysis.SeparatedCenterClockObstruction \
  GeometryOfNumbers.Analysis.SeparatedCenterClockObstructionAudit \
  GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
bash scripts/audit-analysis.sh
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
git diff --check
git diff --cached --check
```

The four requested `--wfail` targets passed (exit 0). Analysis, Foundation and
Geometry audit scripts all passed (exit 0). Each of the five new capstones
printed exactly `[propext, Classical.choice, Quot.sound]`; Foundation retained
its empty footprint. The new Lean sources contain no placeholder or trust-escape
declarations. Working and staged whitespace checks passed.

This is one coherent increment, published under commit message
`audit: exclude bounded separated center block as complete material clock`.
The resulting commit SHA and verified remote references are reported in the
round delivery; no self-referential commit SHA is inserted into its own content.
