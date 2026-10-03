> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# C2 Green temporal-mean audit

## STATUS

**PASS — the global raw Green defect has strictly positive temporal mean on every nonzero C2 source state; hence the restricted raw Gram cannot equal the identity for all times.**

`FINITE_PHASE_MEAN_PASS` is also closed. The infinite passage is closed, without a finite-section fallback or an assumed tail estimate.

## Repositories and preservation

- Downstream worktree: `/home/thlinux/carry-c2-source-raw-green`.
- Branch: `canary-c2-source-raw-green`.
- Initial and final HEAD: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Upstream dependency: `/home/thlinux/geometry-of-numbers-phase-canary`, HEAD `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`, with its preexisting uncommitted canaries preserved byte for byte.
- GreenFrame dependency: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; Lean `v4.32.0`.
- The previously absent downstream `.lake` cache was restored from the pinned dependency manifest. Existing Mathlib/support packages at the same revisions were reused via cache links. No upstream source or preexisting configuration was edited.
- No commit, merge, push, whitening, numerical argument or spectral inference.

The input is literally `c2GlobalGreenInputIsometry t V`. Its existing material address, critical amplitude and real rotation are retained. No historical same-index weighted source is used.

## Exact event ledger

Write

$$
f_t=c2GlobalGreenInputIsometry(t)(V),\quad
\mu_e=greenEventMass(\omega,e),\quad q_e=carryRatio(e.1),
$$

with the existing canonical partition. Set

$$
x_e=f_0(current),\qquad y_e=-2q_e f_0(parent),\qquad
z_e=\begin{cases}q_e^2 f_0(grandparent),&HasGrandparent(e),\\0,&\text{otherwise}.\end{cases}
$$

The new definitions are

$$
\Delta_e(t)=|Green_e(f_t)|^2-|DirectGreen_e(f_t)|^2,
\qquad A_e=\mu_e(|y_e|^2+|z_e|^2).
$$

`eventDiagonalDefect_eq_explicit` proves exactly

$$
A_e=\mu_e\left(4q_e^2|f_0(parent)|^2+
\mathbf1_{gp}q_e^4|f_0(grandparent)|^2\right)\ge0.
$$

`eventGreenDefect_eq_diagonal_add_cross` proves

$$
\Delta_e(t)=A_e+C_e(t),
$$

where `eventCrossDefect` contains exactly the three real cross products, and no norm-square is hidden in it.

## Phase and frequencies

`realPlanePackaging_rotate` derives the coordinate crosswalk

$$
pack(R_\theta v)=e^{i\theta}pack(v)
$$

from the previously proved real packaging theorem. `c2Source_phase` then proves, for every positive material integer, including coordinates outside the odd sector,

$$
f_t(n)=e^{-it\log n}f_0(n).
$$

This is an equality for the existing source, not a new source definition. `c2Source_normSq_time` proves its norm profile is independent of time.

Let $\lambda_e=\log(baseReal(e.1))$. Since the physical base is at least two, `camera_log_frequency_pos` proves $\lambda_e>0$.

`eventCrossDefect_eq_frequencies` proves

$$
C_e(t)=2\mu_e\left[
\Re(e^{-it\lambda_e}x_e\overline{y_e})+
\mathbf1_{gp}\left(
\Re(e^{-2it\lambda_e}x_e\overline{z_e})+
\Re(e^{-it\lambda_e}y_e\overline{z_e})\right)\right].
$$

| Cross product | Frequency magnitude | Justification |
|---|---:|---|
| current–parent | $\log b$ | $current=b\,parent$ |
| current–grandparent | $2\log b$ | $current=b^2\,grandparent$ when the ancestor exists |
| parent–grandparent | $\log b$ | $parent=b\,grandparent$ |

No rational-independence assumption is used. There is no missing zero-frequency cross contribution.

## Basic and finite temporal means

For real functions,

$$
Mean_T(h)=T^{-1}\int_0^T h(t)\,dt.
$$

Only $T>0$ matters for the limit at infinity; the total Lean definition at $T=0$ uses the usual inverse-zero convention.

`phaseFactor_timeAverage` uses Mathlib `integral_exp_mul_complex` and the bound

$$
\left|\frac1T\int_0^T e^{i\omega t}\,dt\right|
\le\frac{2}{|\omega|T}\longrightarrow0\qquad(\omega\ne0).
$$

`oscillatoryCross_timeAverage` transports that limit through a fixed complex coefficient and the real-part continuous linear map.

The following are kernel checked:

- `eventCrossDefect_timeAverage`: $Mean_T(C_e)\to0$.
- `eventGreenDefect_timeAverage`: $Mean_T(\Delta_e)\to A_e$.
- `finiteGreenDefect_timeAverage`: for every finite event set $F$,

$$
Mean_T\left(\sum_{e\in F}\Delta_e\right)\longrightarrow\sum_{e\in F}A_e.
$$

## Infinite exchange: proved uniform summable bound

Let

$$
Q_e=greenCoordinateMajorant(\omega,f_0,e).
$$

The existing Green Bessel assembly proves $Q_e\ge0$ and $\sum_e Q_e<\infty$. `greenMajorant_c2Source_time` proves this same majorant profile works at every time.

The new bounds are

$$
|\Delta_e(t)|\le2Q_e,\qquad |A_e|\le2Q_e,\qquad |C_e(t)|\le4Q_e
\quad\text{for every real }t.
$$

Their summability is proved by `eventUniformBound_summable`, `eventDiagonalDefect_summable`, `eventGreenDefect_summable` and `eventCrossDefect_summable`.

The private general helper `temporalMean_tsum` uses:

1. event continuity, hence integrability on each finite time interval;
2. $\int_0^T|h_e(t)|dt\le T B_e$ and summability of $B$;
3. Mathlib `integral_tsum_of_summable_integral_norm` to exchange the integral and sum;
4. the same bound on each temporal mean.

Mathlib `tendsto_tsum_of_dominated_convergence` then exchanges limit and sum. No unproved uniformity assumption is supplied.

`rawGreenDefect_eq_tsum_event` identifies this event sum with the preexisting metric defect

$$
D_t(V)=\|concreteAnalysisOperator(\omega)(f_t)\|^2-\|V\|^2.
$$

The capstones are

$$
\boxed{Mean_T(D_\cdot(V))\longrightarrow L(V)=\sum_e A_e(V)}
$$

(`globalGreenDefect_timeAverage`) and

$$
\boxed{Mean_T\left(\sum_e C_e(\cdot,V)\right)\longrightarrow0}
$$

(`globalCrossDefect_timeAverage`). The exact identity

$$
D_t(V)=L(V)+\sum_e C_e(t,V)
$$

is `rawGreenDefect_eq_diagonal_add_cross_tsum`.

## Camera-two check and strict positivity

`eventCrossDefect_baseTwo_eq_zero` proves that every camera-two event has zero cross ledger on this odd-support source. The current coordinate is even; either the parent is even or the second ancestor is absent.

`eventDiagonalDefect_baseTwo_eq_green` identifies its diagonal with the actual Green coordinate energy. The direct channel vanishes by the previous ledger.

`baseTwoDefect_timeAverage` reproduces the previous time-independent camera-two defect. Its prior two-generation diagonal formula and positivity are reused, without reproving the dyadic arithmetic or energy series.

`baseTwoDefect_le_totalDiagonal` proves

$$
L(V)\ge D_{2,0}(V).
$$

The prior `baseTwoDefect_pos` therefore yields, for every $V\ne0$,

$$
\boxed{L(V)>0.}
$$

This is `totalDiagonal_pos`; `globalGreenDefect_timeAverage_positive` packages the positive global temporal mean.

## Uniform-isometry obstruction

`exists_time_rawGreenDefect_pos` proves for every $V\ne0$,

$$
\exists t\in\mathbb R:\quad D_t(V)>0.
$$

The proof is by contradiction: if every defect were nonpositive, every positive-time mean would be nonpositive, contradicting its strictly positive limit.

Also closed:

- `exists_time_rawGreenDefect_ne_zero`;
- `exists_time_restrictedGram_ne_identity`;
- `not_forall_restrictedGram_eq_identity`:

$$
\boxed{\neg\bigl(\forall t,\ c2GlobalRestrictedGreenGram(t)=I\bigr).}
$$

The final theorem uses a concrete nonzero input supported on odd core one with real unit direction $(1,0)$. It does not postulate a nonzero input or use a spectral witness.

**Not claimed:** $G_t\ne I$ at every individual time, a pointwise sign of the non-base-two remainder, or impossibility of cancellation at an isolated time.

## Axioms and validation

- New module and dedicated audit: `lake build CarrySelfAdjointOperator.C2GreenTemporalMeanCanary CarrySelfAdjointOperator.C2GreenTemporalMeanCanaryAudit` — PASS.
- All 52 public declarations have a rejecting axiom guard and `#print axioms` in the dedicated audit. Private helpers are included transitively in the capstone checks.
- Every new capstone footprint is within `[propext, Classical.choice, Quot.sound]`; exact per-declaration lists are in `AXIOMS.json`.
- No new trust escape or banned construction. No whitening.
- `git diff --check` — PASS.
- The inherited global static script still flags the same five matches in legacy comments; the baseline checker confirms zero additional matches. That unrelated inherited failure is not reported as a global static PASS.
- Hash/status preservation checks cover all preexisting tracked and untracked changes in the downstream worktree and the upstream checkouts. All remain intact. HEAD/branches are unchanged.
- The local elaboration option concerning definitional transparency only resolves the existing dependent `ℓ²` instance coercions; it does not change statements, proofs or kernel trust.

New worktree files only:

1. `CarrySelfAdjointOperator/C2GreenTemporalMeanCanary.lean`.
2. `CarrySelfAdjointOperator/C2GreenTemporalMeanCanaryAudit.lean`.
3. `docs/C2_GREEN_TEMPORAL_MEAN_AUDIT.md`.

The local evidence bundle `c2_green_temporal_mean_work` contains mirrored sources, reports, build attempts, kernel prints, public-name/axiom lists, preservation snapshots and exact reference hashes. Failed intermediate elaborations are retained as logs and are superseded by the final successful build; no unfinished proof remains in the delivered module.

## Semantic conclusion

The negative compensation required for global raw isometry cannot hold throughout the entire temporal orbit for a nonzero C2 input. Its oscillatory cross ledger vanishes in the proved global temporal mean, leaving a sum of nonnegative diagonal energies with a strictly positive camera-two contribution. Thus uniform raw restricted-Gram identity in time is ruled out. This result does not classify any particular fixed time and makes no spectral claim.
