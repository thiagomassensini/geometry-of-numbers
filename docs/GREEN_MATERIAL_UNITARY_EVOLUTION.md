> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# Material unitary evolution and exact Parseval transport

## STATUS

**PASS_C2_ORBIT.**

The material phase defines a strongly continuous unitary group on `GreenFrame.State`. Its strong derivative is `-i L_mat` on the maximal logarithmic domain. Its Parseval transport is a strongly continuous ambient unitary group, satisfying `U_H(s) P = P U_L(s)` on the FULL Hilbert spaces and acting identically on the gauge complement.

**The historical C2 phase parameter is exactly the material unitary-group orbit parameter after provenance-correct embedding:** `U_s f_t = f_(t+s)` for every `CoreState`, without a logarithmic moment hypothesis.

## REPOSITORY / PRESERVATION

- Worktree on `llm`: `/home/thlinux/carry-c2-source-raw-green`.
- Branch: `canary-c2-source-raw-green`.
- Initial/final HEAD: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Geometry: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`; no changes.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; Lean `v4.32.0`.
- No commit, merge or push. The previous material-generator and Parseval-operator PASS sources are preserved, verified against their existing artifact manifests.
- The final validation bundle is `/home/thlinux/green-material-unitary-evolution-artifacts-2026-10-02`. Its `SOURCE_MANIFEST.json` records the checked source hashes, repository revisions and preservation checks. The temporary evidence folder cited before the interrupted session was not recovered; final validation logs are regenerated in this persistent bundle.

## MATERIAL PHASE

Definition:

```lean
greenStateMaterialPhase s n :=
  Complex.exp (-(((s * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))
```

Thus the sign is literally the historical negative convention:

$$
\phi_s(n)=e^{-is\log n}.
$$

The phase reads the MATERIAL integer `n : PNat`, and no branch-depth index replaces it.

Proved:

- `greenStateMaterialPhase_eq_native`: the historical phase at `j=n-1` is exactly this phase;
- `greenStateMaterialPhase_norm`: modulus is 1;
- `greenStateMaterialPhase_zero`: phase at 0 is 1;
- `greenStateMaterialPhase_add`: `phi_(s+r) = phi_s phi_r`;
- `greenStateMaterialPhase_neg`: phase at `-s` is the inverse phase;
- `greenStateMaterialPhase_eq_phaseFactor`: exact crosswalk to the previous C2 phase notation.

## MATERIAL EVOLUTION

The preexisting historical `infiniteRealSpectralEvolution` actually exists as a full infinite `LinearIsometryEquiv`. It is not invented from the finite construction.

Define by exact reindexing conjugation:

```lean
(nativeLogHilbertEquivGreenState.symm.trans (infiniteRealSpectralEvolution s)).trans
  nativeLogHilbertEquivGreenState
```

`greenStateMaterialEvolution s : State ≃ₗᵢ[ℂ] State` is a unitary equivalence on ALL State.

- `greenStateMaterialEvolution_apply`:

$$
(U_s f)(n)=\phi_s(n)f(n).
$$

- `greenStateMaterialEvolution_norm`: exact norm preservation.
- `greenStateMaterialEvolution_zero`, `..._add`, `..._neg`: identity, group law and inverse. The first two are stated pointwise for every Hilbert vector; the inverse is equality of equivalences.
- `greenStateMaterialEvolution_basis`: `U_s e_n = phi_s(n) • e_n`.
- `greenStateMaterialEvolution_native_intertwining`:

$$
U\,U_s^{old}=U_s^{mat}\,U.
$$

### Strong continuity

`greenStateMaterialEvolution_stronglyContinuous` proves `Continuous (fun s => U_s f)` for every `f : State`, at every time. `..._stronglyContinuous_at_zero` records the norm-limit form.

The private `state_tendsto_of_dominated_coordinates` applies Mathlib's `tendsto_tsum_of_dominated_convergence` to squared coordinate errors, then takes the square root using the actual ℓ² norm identity.

For continuity:

$$
|(U_s f)(n)-(U_r f)(n)|\le2|f(n)|,
\qquad B(n)=4|f(n)|^2.
$$

The bound is summable for every State. No logarithmic moment is used.

## MATERIAL GENERATOR

The generator is the SAME previously closed `greenStateMaterialLogGenerator`, with its maximal domain:

$$
Dom(L)=\{f:(n\mapsto\log n\,f(n))\in\ell^2\}.
$$

`greenStateMaterialEvolution_hasDerivative_zero` proves:

$$
\boxed{
HasDerivAt\bigl(s\mapsto U_sf,\,-iLf,\,0\bigr)
\quad(f\in Dom(L)).
}
$$

Equivalently, with `h → 0`, `h ≠ 0`:

$$
\frac{U_hf-f}{h}\longrightarrow-iLf
$$

in the Hilbert norm, not merely coordinatewise.

Proof:

1. reuse the previous coordinate derivative `materialLogPhase_hasDerivAt`;
2. use Mathlib's global inequality `Real.norm_exp_I_mul_ofReal_sub_one_le`;
3. obtain `|(phi_h(n)-1)/h| ≤ |log n|` (the bound is also valid for the totalized inverse at h=0);
4. dominate the squared derivative error by

$$
4(\log n)^2|f(n)|^2;
$$

5. apply counting-measure dominated convergence using exactly the previous domain criterion.

### Exact necessity of the domain

`greenStateMaterialEvolution_mem_domain_of_hasDerivative_zero` proves that any strong derivative at zero forces membership in Dom(L). Evaluation at n is a bounded linear functional, so uniqueness of scalar derivatives gives `d(n) = -i log n f(n)`. Multiplication of the derivative vector by i then supplies the required ℓ² logarithmic multiplier.

`greenStateMaterialEvolution_differentiableAt_zero_iff` proves:

$$
\boxed{
DifferentiableAt_{\mathbb R}(s\mapsto U_sf,0)
\iff f\in Dom(L).
}
$$

Thus the strong infinitesimal generator has exactly the maximal material-log domain, with action `-i L`; L is its self-adjoint clock convention. No abstract Stone or new functional-calculus theorem is needed for this identification.

## AMBIENT EVOLUTION

Reuse the previous canonical `P`, closed range R, range unitary U_P, and orthogonal decomposition:

$$
D:K\simeq R\oplus_2R^\perp.
$$

`parsevalRangeMaterialEvolution s` is `U_P U_s U_P^-1` on R.

`greenParsevalMaterialEvolution s : ConcreteAnalysisSpace ≃ₗᵢ[ℂ] ConcreteAnalysisSpace` is defined by conjugating

$$
(U_PU_sU_P^{-1})\oplus I_{R^\perp}
$$

through the SAME `greenParsevalOrthogonalDecomposition`. The product is `WithLp 2`, and its unitary packaging comes from `LinearIsometryEquiv.withLpProdCongr`.

### Exact adjoint formula

`parsevalRange_inverse_projection_eq_adjoint` proves:

$$
U_P^{-1}(proj_R y)=P^*y.
$$

It uses the previous `P*P=I` and the canonical projection's inner-product identity.

`greenParsevalMaterialEvolution_apply_adjoint` therefore gives:

$$
\boxed{\mathcal U_s y=P U_s P^*y+proj_{R^\perp}y.}
$$

The last summand is the ambient extension of the identity on the gauge complement, not identity on all K.

### Unitarity, group law, gauge

- `greenParsevalMaterialEvolution_norm`: exact norm preservation;
- `..._zero`, `..._add`, `..._neg`: identity, group law, inverse;
- `..._eq_self_of_mem_orthogonal`:

$$
y\in R^\perp\Longrightarrow\mathcal U_s y=y.
$$

- `..._stronglyContinuous`: `Continuous (fun s => U_H(s)y)` for every ambient vector, from the adjoint formula and material strong continuity.

## PARSEVAL INTERTWINING

`greenParsevalMaterialEvolution_intertwining` proves:

$$
\boxed{\mathcal U_s(Px)=P(U_sx)\qquad\forall x:State.}
$$

There is NO domain hypothesis. The bounded evolution exists on the full Hilbert space.

## AMBIENT GENERATOR

`greenParsevalMaterialEvolution_hasDerivative_zero` proves, for `y ∈ Dom(H_Green)`:

$$
\boxed{HasDerivAt(s\mapsto\mathcal U_sy,\,-iH_{Green}y,\,0).}
$$

This is transported from the material derivative by a bounded complex-linear map on the range. The proof explicitly cancels the constant orthogonal component in the difference quotient. It performs no Green-coordinate calculation and introduces no second ambient operator or domain.

`greenParsevalMaterialEvolution_derivative_on_range` uses the previous typed intertwining `greenParsevalMaterialLogOperator_intertwining` to give:

$$
\partial_s\mathcal U_s(Px)|_{s=0}=-iP(Lx),\qquad x\in Dom(L).
$$

It is literally consistent with the previously proved `HP=PL`.

## C2 SOURCE

For every `V : CoreState`, `f_t = c2GlobalGreenInputIsometry t V` is a State.

`greenParsevalMaterialEvolution_c2Source` proves the full bounded transport:

$$
\mathcal U_s(Pf_t)=P(U_sf_t).
$$

`c2GlobalGreenInput_evolution_add` proves directly from the existing exact `c2Source_phase` and the phase-addition law:

$$
\boxed{U_s f_t=f_{t+s}.}
$$

`greenParsevalMaterialEvolution_c2Source_add` composes these:

$$
\boxed{\mathcal U_s(Pf_t)=P f_{t+s}.}
$$

All three hold for every CoreState with no logarithmic moment hypothesis.

The parameters s and t remain distinct in the theorem. Their additive relationship is proved, not assumed. t is an evolution parameter, not an eigenvalue.

No source amplitude or provenance changes: the amplitude remains `2^(-k/2)` at the recovered C2 depth k; phase reads the material integer n. The source is not the old weighted diagonal `q^n psi_t(n)`.

## DOMAIN GATE

$$
\sum_n(\log n)^2|f(n)|^2<\infty.
$$

Required for:

- f ∈ Dom(L), applying L;
- strong differentiation of the material orbit (necessary and sufficient, proved);
- differentiating the transported orbit using H on its previous domain.

NOT required for:

- U_s f or U_H(s) y to be defined;
- norm preservation, group law or strong continuity;
- the all-vector Parseval intertwining;
- either of the C2 orbit-shift identities.

The prior classification `C2_SOURCE_LOG_DOMAIN_REQUIRES_EXTRA_MOMENT` for applying the unbounded clock to arbitrary CoreState remains unchanged. It does not obstruct bounded dynamics.

## HEIGHT OPERATOR

Identified? **NO.** L and H_Green are the material log clock and its Parseval transport. No height operator, Zeta, zeros, Jacobi or moment construction is used.

## AXIOMS / VALIDATION

All 40 public declarations are checked by rejecting guards and `#print axioms` in `GreenMaterialEvolutionAudit.lean`. Private analytic helpers are audited transitively. Footprints are contained in `[propext, Classical.choice, Quot.sound]`.

The two new modules and the audit build under Lean v4.32.0. Successful build/print logs, exact footprints, scope checks and preservation snapshots are recorded in the evidence bundle.

No new axiom, sorry, admit or unsafe is introduced. The existing static audit's five historical comment matches remain unchanged; it is an inherited static failure, not a repository-wide static PASS. New-file source hygiene and rejecting kernel guards pass independently.

## FILES

New worktree files:

1. `CarrySelfAdjointOperator/GreenStateMaterialEvolution.lean`;
2. `CarrySelfAdjointOperator/GreenParsevalMaterialEvolution.lean`;
3. `CarrySelfAdjointOperator/GreenMaterialEvolutionAudit.lean`;
4. `docs/GREEN_MATERIAL_UNITARY_EVOLUTION.md`.

Exact copies of the new files, final build and direct kernel-audit logs, source provenance, and checks against the previous PASS manifests are in `/home/thlinux/green-material-unitary-evolution-artifacts-2026-10-02`. Intermediate logs from the interrupted session are not included.

## SEMANTIC CONCLUSION

**YES.** Material phase gives a global strongly continuous unitary dynamics, transported exactly by the SAME canonicalAnalysis on every Hilbert vector. The logarithmic moment is required for the strong derivative and unbounded generator, and is unnecessary for bounded evolution. The provenance-correct historical C2 phase parameter is now formally the orbit parameter through the proved time-shift identities.
