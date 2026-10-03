> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# Self-adjoint ambient Green material clock via canonical Parseval range

## STATUS

**PASS — the self-adjoint material log generator transports unitarily through the canonical Parseval range and extends by zero on its orthogonal complement to a self-adjoint ambient Green operator satisfying H P = P L on the maximal material-log domain.**

This closes the operatorial extension gate identified in the previous round. The separate C2-source logarithmic moment gate remains unchanged.

## REPOSITORY / PRESERVATION

- Worktree: `/home/thlinux/carry-c2-source-raw-green`.
- Branch: `canary-c2-source-raw-green`.
- Initial/final HEAD: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Geometry dependency: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`, including its existing canaries; no edit.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; Lean `v4.32.0`.
- Exact consulted sources and hashes are recorded in `SOURCE_MANIFEST.json`.
- No commit, merge or push. No change to upstream geometry, previous modules, project dependencies or existing canary semantics.

## P

`greenParsevalAnalysis` is only an abbreviation for the SAME existing operator:

```lean
canonicalAnalysis canonicalRawGreenAnalysis
```

where `canonicalRawGreenAnalysis` is exactly

```lean
concreteAnalysisOperator canonicalCarryInfinitePartition
```

It has type `State →L[ℂ] ConcreteAnalysisSpace`.

`greenParsevalAnalysis_gram_identity` and `greenParsevalAnalysis_isometry` reuse the previous checked identities:

$$
P^*P=I,\qquad Isometry(P).
$$

`parsevalRange_isClosed` derives closed range from completeness of State and the isometry's closed-embedding theorem. No frame or alternative normalization is introduced.

## PARSEVAL RANGE

Definitions:

```lean
parsevalRangeSubmodule := greenParsevalAnalysis.toLinearMap.range
ParsevalRange := ↥parsevalRangeSubmodule
ParsevalOrthogonal := ↥parsevalRangeSubmoduleᗮ
```

`parsevalRange_completeSpace` is the closed-subspace completeness instance.

`parsevalRangeUnitary : State ≃ₗᵢ[ℂ] ParsevalRange` uses exactly

```lean
(canonicalParseval canonicalRawGreenFrameBounds).equivRange
```

whose underlying map is P. `parsevalRangeUnitary_apply` proves literally

$$
(U_Px:\ ConcreteAnalysisSpace)=Px.
$$

The inverse $U_P^{-1}$ is defined only on the range, with no fictitious inverse of P on the full ambient carrier.

## RANGE LOG GENERATOR

The existing `greenStateMaterialLogGenerator` is denoted by L.

`parsevalRangeMaterialLogGenerator` is

$$
L_P=U_P L U_P^{-1}
$$

as a partial complex-linear operator on ParsevalRange. Its domain is the preimage of the SAME maximal material-log domain.

`parsevalRangeMaterialLogGenerator_domain_iff` proves

$$
y\in Dom(L_P)\iff U_P^{-1}y\in Dom(L).
$$

`parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff` specializes to

$$
U_Px\in Dom(L_P)\iff x\in Dom(L).
$$

`parsevalRangeMaterialLogGenerator_isSelfAdjoint` proves $L_P^*=L_P$ by the prior unitary transport lemma and `greenStateMaterialLogGenerator_isSelfAdjoint`.

The private unitary-transport helpers from `GreenStateMaterialLogGenerator.lean` are reused exactly using Batteries `open private ... from ...`. Their definitions and proofs are not copied or modified; this command resolves their existing compiled names and does not change the trust model. The axiom guards audit these dependencies transitively.

`parsevalRangeMaterialLogGenerator_intertwines` proves for `hx : x ∈ Dom(L)`:

$$
\boxed{L_P(U_Px)=U_P(Lx).}
$$

This is equality of domain-typed output vectors, not merely equality of scalar products.

## ORTHOGONAL DECOMPOSITION

Let $R=range(P)$ and $K=ConcreteAnalysisSpace$.

`greenParsevalOrthogonalDecomposition` reuses `Submodule.orthogonalDecomposition`:

$$
D:K\simeq_{unitary}WithLp\ 2\ (R\times R^\perp).
$$

Its two components are the existing canonical orthogonal projections onto R and $R^\perp$. Its inverse sums the two inclusions.

The product is explicitly the L² product, not the ordinary maximum-norm product. No arbitrary complement or newly chosen Gram is used.

## GENERIC ZERO EXTENSION

No ready-made self-adjoint direct-sum extension API was found in the consulted partial-operator files. The new minimum generic layer is in `CarrySelfAdjointOperator.UnitaryZeroExtension`.

`hilbertPartialProdZero A` constructs the partial operator B on `WithLp 2 (R × S)`:

$$
Dom(B)=Dom(A)\times S,\qquad B(r,s)=(Ar,0).
$$

Its domain is implemented by `Submodule.comap` of the existing first-projection linear map. Its action is ordinary linear-map composition and product with the zero map.

- `hilbertPartialProdZero_mem_domain_iff` gives the exact first-slot domain criterion.
- `hilbertPartialProdZero_apply` gives the literal vector formula.
- `hilbertPartialProdZero_dense_domain` uses density of Dom(A), `Dense.prod`, and the existing product homeomorphism.
- `hilbertPartialProdZero_isSelfAdjoint` proves that self-adjoint A yields self-adjoint B.

The generic adjoint proof uses the two-slot product inner-product identity and adjoint maximality. Testing the first slot recovers membership in the original adjoint domain; the dense-domain uniqueness of the adjoint determines the complete output. There is no material-coordinate or logarithmic computation and no additional hypothesis replacing self-adjointness.

For a subspace Q admitting its canonical orthogonal projection:

$$
selfAdjointZeroExtension(Q,A)=D_Q^{-1}(A\oplus0)D_Q.
$$

The public theorems are:

- `selfAdjointZeroExtension_domain_iff`:

$$
y\in Dom(A\oplus0)\iff proj_Q(y)\in Dom(A);
$$

- `selfAdjointZeroExtension_apply`:

$$
(A\oplus0)y=\iota_Q\bigl(A(proj_Q y)\bigr);
$$

- `selfAdjointZeroExtension_isSelfAdjoint`:

$$
A=A^*\Longrightarrow selfAdjointZeroExtension(Q,A)=selfAdjointZeroExtension(Q,A)^*.
$$

The last is directly unitary transport of the product self-adjointness theorem. Completeness of the closed range and its orthogonal subspace supplies the generic Hilbert assumptions in the actual Parseval instance.

## AMBIENT GREEN LOG OPERATOR

Definition:

```lean
greenParsevalMaterialLogOperator :=
  selfAdjointZeroExtension parsevalRangeSubmodule parsevalRangeMaterialLogGenerator
```

Thus

$$
\boxed{H_{Green}=(U_P L U_P^{-1})\oplus0.}
$$

`greenParsevalMaterialLogOperator_isSelfAdjoint` proves

$$
\boxed{H_{Green}=H_{Green}^*.}
$$

`greenParsevalMaterialLogOperator_domain_iff` describes its full ambient domain:

$$
Dom(H)=\{y:proj_R(y)\in Dom(L_P)\}.
$$

No maximal-domain condition is required for the orthogonal component.

`greenParsevalMaterialLogOperator_P_mem_domain_iff` proves

$$
\boxed{Px\in Dom(H)\iff x\in Dom(L).}
$$

`greenParsevalMaterialLogOperator_intertwining` proves

$$
\boxed{H(Px)=P(Lx)\quad(x\in Dom(L)).}
$$

The range projection fixes Px. This reduces the equality to the already proved range intertwining.

## ZERO ON THE COMPLEMENT

`greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal` proves

$$
R^\perp\subseteq Dom(H).
$$

`greenParsevalMaterialLogOperator_eq_zero_of_mem_orthogonal` proves

$$
\boxed{y\in R^\perp\Longrightarrow Hy=0.}
$$

Both use the canonical range projection's vanishing on the orthogonal subspace. This is the literal full-domain zero operator on the complement.

## TRANSPORTED BASIS

For each `n : PNat`, `greenMaterialBasisVector n` is the previous material delta $e_n$.

`greenParsevalMaterialLogOperator_transported_basis` composes exact intertwining with the previous material basis law:

$$
\boxed{H(Pe_n)=(\log n)Pe_n.}
$$

`greenParsevalMaterialLogOperator_transported_basis_ne_zero` proves $Pe_n\ne0$ using injectivity of P and the nonzero delta coordinate.

Thus each $\log n$ has a genuine nonzero eigenvector in the transported range. The complement is annihilated. No exhaustion of the ambient spectrum is asserted.

## C2 SOURCE

Full domain membership for every `CoreState`: **OPEN**.

The previous classification remains **C2_SOURCE_LOG_DOMAIN_REQUIRES_EXTRA_MOMENT**.

`greenParsevalMaterialLogOperator_c2Source_mem_domain` and `greenParsevalMaterialLogOperator_c2Source_intertwining` are conditional on

$$
JW_tV\in Dom(L).
$$

They prove

$$
P(JW_tV)\in Dom(H),\qquad
\boxed{HP(JW_tV)=PL(JW_tV).}
$$

`greenParsevalMaterialLogOperator_c2Source_domain_iff_log_moment` reuses the exact previous gate:

$$
P(JW_tV)\in Dom(H)\iff
Summable\bigl(n\mapsto(\log n)^2\operatorname{normSq}(JW_0V(n))\bigr).
$$

No new estimate, universal membership claim or identification of material index with depth is added.

## UNITARY EVOLUTION

**UNITARY_EVOLUTION_PACKAGING_OPEN.** No ambient evolution or functional calculus is constructed in this round. The source phase parameter t remains only the parameter of the previously defined source; no separate evolution parameter is identified with it by assumption.

## HEIGHT OPERATOR

Identified? **NO.** H is the transported MATERIAL LOG CLOCK. Its basis eigenvalues are $\log n$, not zero heights. No identification with any reciprocal, signed, Jacobi or height operator is made.

## AXIOMS / VALIDATION

All 37 public declarations and named instances are checked by rejecting guards and `#print axioms` in `GreenParsevalMaterialLogOperatorAudit.lean`. The inherited private helper dependencies are audited transitively.

The range self-adjointness certificate is a named proof definition with an inferred proposition, obtained directly from the previous unitary-transport theorem. This retains its exact standard Hilbert instances; it is neither a hypothesis nor a new adjoint convention. Only the cosmetic `defProp` linter is disabled for that declaration. The ambient capstone is an explicit `IsSelfAdjoint` theorem.

All footprints lie within `[propext, Classical.choice, Quot.sound]`. The new module and audit compile under Lean v4.32.0. Exact footprints and successful logs are saved in `AXIOMS.json` and the evidence bundle.

No trust escape is introduced. The elaboration transparency option only handles dependent instance presentations, and `open private` only resolves names; kernel verification remains unchanged.

The inherited static baseline retains five old comment matches and zero new matches. It is an inherited static failure, not a repository-wide static PASS. Whitespace/diff checks and preservation snapshots are recorded independently.

## FILES

New worktree files only:

1. `CarrySelfAdjointOperator/GreenParsevalMaterialLogOperator.lean`;
2. `CarrySelfAdjointOperator/GreenParsevalMaterialLogOperatorAudit.lean`;
3. `docs/GREEN_PARSEVAL_MATERIAL_LOG_OPERATOR.md`.

Local exact mirrors, intermediate and successful logs, API probes, source hashes and preservation records are in `green_parseval_material_operator_work`.

## SEMANTIC CONCLUSION

**YES.** The self-adjoint material clock transports through the SAME canonical Parseval analysis onto its closed range. Its orthogonal direct sum with the zero operator then yields a self-adjoint operator on the full ambient Green analysis carrier with exact $HP=PL$ on the transported maximal domain.

Self-adjointness is inherited from the material generator, the unitary range equivalence, and the orthogonal sum with zero. The C2-source logarithmic moment remains an independent domain condition. No height or spectral-exhaustion conclusion is added.
