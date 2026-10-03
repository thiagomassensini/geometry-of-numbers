> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# C2 metric genealogy and nontrivial canonical Green normalization

## STATUS

**PASS — the raw concrete Green analysis has a nonidentity frame operator witnessed on the provenance-correct C2 source, while the pre-stencil chain is isometric and the canonical inverse-square-root normalization restores identity Gram; the whitening is therefore nontrivial and acts only after the vertical stencil.**

Here “after the stencil” describes the derivation and provenance of the normalization: the raw operator determines its frame, and only then is its canonical normalization constructed. The literal operator formula is $P=T\circ Q$, so $Q$ acts on the input State before applying $T$. It is not an output-side postcomposition or a change to the upstream C2 source.

## REPOSITORY

- Worktree: `/home/thlinux/carry-c2-source-raw-green`.
- Branch: `canary-c2-source-raw-green`.
- Initial/final HEAD: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Upstream geometry dependency: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`, including its existing uncommitted canaries, all preserved.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; Lean `v4.32.0`.
- No commit, merge or push. No upstream edit, arithmetic extension, new source definition, temporal proof repetition or new functional-calculus proof.

Throughout, $V_0$ denotes a real core input and $P$ denotes the normalized analysis, avoiding a conflict between the two uses of the letter V.

## RAW T

`canonicalRawGreenAnalysis` is only an abbreviation for

```lean
concreteAnalysisOperator canonicalCarryInfinitePartition
```

Its type is

```lean
GreenFrame.Concrete.State →L[ℂ] ConcreteAnalysisSpace
```

The frame is exactly the existing `frameOperator canonicalRawGreenAnalysis`, namely $F=T^*T$. No second frame operator is introduced.

`canonicalRawGreenFrameBounds` reuses `(concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds`. Its positive lower bound is $1/2$ and its upper bound is $1+greenBesselConstant$.

These bounds supply the existing canonical normalization API. They are not used as a non-isometry witness.

## C2 WITNESS

The new explicit definition is

```lean
c2RawMetricWitness :=
  lp.single 2 (⟨1, ..., ...⟩ : PositiveOddCore)
    (realPlaneHilbertEquiv (1, 0))
```

It is supported only at positive odd core one and has first real quadrature one. Its definition uses no decomposition or witness selected by `Classical.choose`.

- `c2RawMetricWitness_ne_zero` proves $V_0\ne0$.
- `c2RawMetricWitness_norm` proves $\|V_0\|=1$.
- `c2RawMetricWitness_exists_time_defect_pos` applies the already proved `exists_time_rawGreenDefect_pos` from `C2GreenTemporalMeanCanary`:

$$
\exists t:\ D_t(V_0)>0.
$$

Let $S_t=JW_t=c2GlobalGreenInputIsometry(t)$. The theorem `c2RawGreenDefect_eq_material_norm_sq_sub` proves

$$
D_t(V)=\|T(S_tV)\|^2-\|S_tV\|^2,
$$

using the existing isometry $\|S_tV\|=\|V\|$.

The new witness theorems are:

- `exists_c2_time_rawGreen_norm_sq_gt`;
- `exists_c2_time_rawGreen_norm_gt`;
- `exists_c2_state_rawGreen_norm_gt`;
- `exists_c2_unit_state_rawGreen_norm_gt`.

The last states explicitly

$$
\boxed{\exists(t,f):\ f=S_tV_0,\quad \|f\|=1,\quad \|Tf\|>1.}
$$

Thus the witness belongs to the range of the actual provenance-correct C2 source. Its time is existentially obtained by the previously checked temporal theorem, with no numerical time search.

## RAW ISOMETRY

`canonicalRawGreenAnalysis_not_isometry` proves

$$
\boxed{\neg Isometry(T).}
$$

The proof compares the distance of the witness to zero under a hypothetical isometry. Since $T0=0$, that would preserve its norm and contradict the strict norm increase above.

## RAW FRAME OPERATOR

`canonicalRawGreen_frameOperator_ne_identity` proves

$$
\boxed{F=T^*T\ne I.}
$$

The proof uses Mathlib `ContinuousLinearMap.isometry_iff_adjoint_comp_self`. Assuming $F=I$ would make $T$ an isometry and contradict the authorized C2 witness. There is no coordinate Gram calculation or inference from frame bounds.

No sign is asserted for $F-I$.

## RESTRICTED GRAM

The original restricted Gram is retained:

$$
G_t=(T S_t)^*(T S_t).
$$

`rawGreen_realGram_eq_frameOperator_restrictScalars` proves that the real Gram appearing in the previous bridge is the real restriction of the same complex frame:

$$
(T|_{\mathbb R})^*(T|_{\mathbb R})=F|_{\mathbb R}.
$$

Its private compatibility proof uses the existing real and complex polarization identities and adjoint uniqueness. This deals explicitly with the distinct real/complex inner-product instance presentations; it does not assume complex linearity of CoreState.

Reusing the previous compression and source-factor theorems then gives:

- `c2RestrictedGreenGram_eq_source_frame_compression`:

$$
G_t=S_t^*(F|_{\mathbb R})S_t;
$$

- `c2RestrictedGreenGram_eq_W_J_frame_J_W`:

$$
\boxed{G_t=W_t^*J^*(F|_{\mathbb R})JW_t.}
$$

Here $W_t$ is `globalCriticalPhysicalBranchIsometry t`, and $J$ is `oddMaterialToGreenState`. Both are real-linear isometries.

`c2RestrictedGreenGram_not_uniform_identity` directly reuses the temporal capstone:

$$
\boxed{\neg(\forall t,\ G_t=I).}
$$

No statement $G_t\ne I$ for every fixed time is added.

## PRE-STENCIL LEDGER

All these identity Grams are obtained from the previously constructed isometries or their existing adjoint theorems:

| Stage | New exposed theorem | Gram |
|---|---|---|
| Pure critical real branch | `criticalBranch_gram_identity` | $I$ |
| Global physical odd-core source | `globalPhysicalBranch_gram_identity` | $I$ |
| Real quadrature packaging + odd→PNat inclusion | `materialInclusion_gram_identity` | $I$ |
| Complete C2 input $JW_t$ | `c2GreenInput_gram_identity` | $I$ |
| Canonical elementary camera atlas | `elementaryAtlas_gram_identity` | $I$ |
| Conservative seed/residual/direct-Green analysis | `preStencil_gram_identity` | $I$ |
| Same pre-stencil analysis on the C2 input | `c2PreStencil_gram_identity` | $I$ |

The fixed-core physical construction is already the composition of `realCriticalBranchIsometry`, `physicalLegCorrection` and `branchIncidenceIsometry`; the existing `realCriticalPhysicalBranch_adjoint_comp_self` records its identity Gram. The existing global construction glues those physical fibers into `globalCriticalPhysicalBranchIsometry`.

No series, address arithmetic, conservation law or source norm is reproved.

`c2RawMetricDefect_is_stencil_defect` reuses the exact earlier localization:

$$
D_t(V)=\|G_{stencil}(S_tV)\|^2-\|G_{direct}(S_tV)\|^2.
$$

The raw operator changes the direct transmitted coordinate into the current/parent/grandparent stencil. The atlas and conservative Green/return mass split already preserve the metric. The existing GreenFrame crosswalk identifies this stencil with the normalized tower TFVD; no new TFVD is defined here.

## WHITENING

Use exactly the existing objects

$$
Q=inverseSqrtFrame(T)=F^{-1/2},\qquad
P=canonicalAnalysis(T)=T\circ Q.
$$

`canonicalRawGreen_inverseSqrt_normalization` is a direct instance of

```lean
inverseSqrt_frameOperator_inverseSqrt canonicalRawGreenFrameBounds
```

and proves

$$
QFQ=I.
$$

`canonicalRawGreen_inverseSqrtFrame_ne_identity` proves

$$
\boxed{Q\ne I.}
$$

If $Q=I$, the previous normalization identity becomes $F=I$, contradicting the C2-witnessed nonidentity frame. No spectral calculation or additional functional calculus is used.

## CANONICAL ANALYSIS

- `canonicalGreenAnalysis_eq_raw_comp_inverseSqrt` exposes the literal composition $P=T\circ Q$ by definition.
- `canonicalGreenAnalysis_gram_identity` directly reuses `canonicalAnalysis_adjoint_comp_self`:

$$
\boxed{P^*P=I.}
$$

- `canonicalGreenAnalysis_isometry` directly reuses `canonicalAnalysis_isometry`.
- `canonicalGreenAnalysis_norm` directly reuses `canonicalParseval_norm`:

$$
\boxed{\|Pf\|=\|f\|\quad\text{for every material State }f.}
$$

- `canonicalC2GreenAnalysis_norm` composes that identity with the existing C2 input isometry:

$$
\|P(JW_tV)\|=\|V\|.
$$

The inexpensive additional theorem `canonicalRawGreenAnalysis_ne_canonicalAnalysis` proves $T\ne P$: equality would transfer the canonical isometry property to the non-isometric raw operator. Injectivity of $T$ is not needed.

## METRIC GENEALOGY

$$
\boxed{
W_t^*W_t=I
\quad\longrightarrow\quad
\text{material inclusion, atlas and pre-stencil Gram}=I
\quad\longrightarrow\quad
F=T^*T\ne I
\quad\longrightarrow\quad
Q=F^{-1/2}\ne I
\quad\longrightarrow\quad
(TQ)^*(TQ)=I.
}
$$

These arrows express the proved construction and obstruction ledger, not an implication that an arbitrary isometric branch would force an arbitrary later analysis to be non-isometric. The middle obstruction is specifically supplied by the concrete raw Green stencil and the existing temporal C2 witness.

## AXIOMS / VALIDATION

- All 33 public declarations are checked by rejecting guards and `#print axioms` in `C2GreenWhiteningGenealogyAudit.lean`.
- Every capstone footprint is within `[propext, Classical.choice, Quot.sound]`. Exact lists are in `AXIOMS.json`.
- Private compatibility helpers are audited transitively through the compression capstones.
- The module and audit compile under Lean `v4.32.0` using the remote worktree.
- The new source contains no trust escape. The existing functional-calculus proofs are imported and reused, not restated as assumptions.
- `git diff --check` and the new-file whitespace checks pass.
- The inherited repository-wide static script still has the same five legacy comment matches; the baseline check confirms zero additional matches. This is recorded as an inherited static failure, not a global static PASS.
- Hash/status snapshots confirm that all preexisting tracked and untracked worktree files, both geometry checkouts, and the original carry checkout remain unchanged. The GreenFrame dependency remains at its pinned revision with a clean source tree.
- The local elaboration transparency option only resolves dependent instance presentations. It does not relax kernel checking.

## FILES

New worktree files only:

1. `CarrySelfAdjointOperator/C2GreenWhiteningGenealogy.lean`.
2. `CarrySelfAdjointOperator/C2GreenWhiteningGenealogyAudit.lean`.
3. `docs/C2_GREEN_WHITENING_GENEALOGY.md`.

The `c2_green_whitening_genealogy_work` evidence directory contains identical source/report copies, successful build and kernel-print logs, intermediate elaboration logs, public declaration and axiom lists, preservation snapshots and exact consulted source hashes. The final delivered Lean module has no unfinished proof.

## SEMANTIC CONCLUSION

The canonical normalization does not create the C2 geometric isometry: branch, physical incidence, global source, packaging, atlas and conservative pre-stencil analysis already have identity Gram. The vertical Green stencil produces the nonidentity raw frame, witnessed on that same authorized C2 source. The existing, demonstrably nontrivial $T(T^*T)^{-1/2}$ normalization restores Parseval after that frame has been constructed.

This closes only the metric genealogy. It asserts neither a fixed sign of $D_t$ or $F-I$, nor nonidentity of every restricted $G_t$ at each individual time.
