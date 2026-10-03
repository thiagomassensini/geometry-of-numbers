> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# Native logarithmic clock → exact positive-material Green State

## STATUS

**PASS_DOMAIN_GATE_OPEN — the material log generator is transported self-adjointly to GreenFrame.State, but membership of the full C2 source in its maximal domain requires an additional logarithmic moment bound.**

The generator identification and self-adjoint transport close. The separate claim that every `CoreState` input meets the logarithmic domain criterion is not assumed or proved here. This status does not assert a counterexample to that universal claim.

## REPOSITORY

- Worktree `/home/thlinux/carry-c2-source-raw-green`.
- Branch `canary-c2-source-raw-green`.
- Initial/final HEAD `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Geometry dependency `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f` with its existing canaries, preserved.
- GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- CPFormal `65d50f6db1208708e109982ba97e1d51d3039956` (native maximal generator).
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; Lean `v4.32.0`.
- Exact consulted source hashes are recorded in `SOURCE_MANIFEST.json`.
- No commit, merge or push; no geometry edit, new arithmetic, replacement source, Parseval generator transport or height construction.

## INDEX EQUIVALENCE

`natEquivPNat : ℕ ≃ PNat` is constructed explicitly:

$$
j\mapsto\langle j+1,\ j+1>0\rangle,\qquad
n\mapsto n.val-1.
$$

Exact theorems:

- `natEquivPNat_val`: `(natEquivPNat j : ℕ) = j+1`;
- `natEquivPNat_symm`: `natEquivPNat.symm n = n.val-1`;
- `natEquivPNat_symm_add_one`: `natEquivPNat.symm n+1 = n.val`.

No address is selected by choice. Both indices are MATERIAL coordinates of the same positive integer. Neither one is a branch depth, camera code, core or TFVD order.

## L2 UNITARY

`nativeLogHilbertEquivGreenState` has type

```lean
NativeLogHilbert ≃ₗᵢ[ℂ] GreenFrame.Concrete.State
```

Its coordinate formulas are:

$$
(Ux)(n)=x(n.val-1),\qquad
(U^{-1}f)(j)=f(\langle j+1,\ldots\rangle).
$$

The corresponding public theorems are `nativeLogHilbertEquivGreenState_apply` and `nativeLogHilbertEquivGreenState_symm_apply`.

`nativeLogHilbertEquivGreenState_norm` proves $\|Ux\|=\|x\|$.

The available lp API did not provide a ready-made reindexing equivalence in the consulted files. A minimal local linear equivalence uses `Equiv.summable_iff`, and its unitary packaging uses `LinearEquiv.isometryOfInner`, `lp.inner_eq_tsum` and `Equiv.tsum_eq`. There is no new manual norm-series calculation or Hilbert construction.

## BASIS CROSSWALK

`greenMaterialBasisVector n := lp.single 2 n 1` is only the usual delta at material $n$.

`nativeLogHilbertEquivGreenState_basisVector` proves

$$
U e_j=e_{j+1}.
$$

No new basis theory is introduced.

## MATERIAL LOG GENERATOR

`greenStateMaterialLogGenerator : State →ₗ.[ℂ] State` is exactly the conjugation

$$
L_{mat}=ULU^{-1},\qquad L=nativeLogGenerator.
$$

The minimal private `unitaryTransport` uses the preexisting `Submodule.comap` for its domain and ordinary linear-map composition for its value:

$$
Dom(L_{mat})=U^{-1}_{\text{preimage}}(Dom(L)),\qquad
L_{mat}f=U(L(U^{-1}f)).
$$

Here preimage means $\{f:U^{-1}f\in Dom(L)\}$. The original maximal domain is transported, rather than recreated from a new assumption.

`greenStateMaterialLogGenerator_mem_domain_iff` proves the exact domain crosswalk. `greenStateMaterialLogGenerator_domain_iff_memℓp` derives:

$$
\boxed{f\in Dom(L_{mat})\iff
Mem\ell^2\bigl(n\mapsto(\log n)f(n)\bigr).}
$$

`greenStateMaterialLogGenerator_apply` proves for a domain element:

$$
\boxed{(L_{mat}f)(n)=(\log n)f(n).}
$$

`greenMaterialBasisVector_mem_domain` transports existing native basis membership.

`greenStateMaterialLogGenerator_basisVector_log` transports the existing `nativeLogGenerator_basisVector_log`, proving:

$$
\boxed{L_{mat}e_n=(\log n)e_n.}
$$

## SELF-ADJOINTNESS

`greenStateMaterialLogGenerator_isSelfAdjoint` proves

$$
\boxed{L_{mat}^*=L_{mat}.}
$$

The existing Mathlib partial-operator API has adjoints and partial composition, but no ready-made unitary conjugation/self-adjoint transport theorem was found. The private minimal transport proof applies to an arbitrary self-adjoint partial operator and a unitary equivalence. It uses:

1. the native self-adjoint operator's dense domain;
2. density under the unitary homeomorphism;
3. preservation of inner products;
4. `LinearPMap.adjoint_isFormalAdjoint`;
5. `LinearPMap.mem_adjoint_domain_of_exists` and maximality/uniqueness of the adjoint.

It contains no logarithmic coordinate calculation. Thus the analytic self-adjointness proof of the native generator is inherited, not repeated.

The additional consequences `greenStateMaterialLogGenerator_dense_domain` and `greenStateMaterialLogGenerator_isClosed` reuse the existing self-adjoint API.

## C2 SOURCE DOMAIN

Classification: **C2_SOURCE_LOG_DOMAIN_REQUIRES_EXTRA_MOMENT**.

The existing source remains $f_t=c2GlobalGreenInputIsometry(t)V$, with its preserved material address, critical DEPTH amplitude and MATERIAL phase. The previous `c2Source_phase` is reused; no old diagonal source is used.

`materialLogPhase_hasDerivAt` proves the coordinate derivative:

$$
\frac d{dt}\bigl(e^{-it\log n}a\bigr)
=-i(\log n)e^{-it\log n}a.
$$

`c2Source_materialLog_hasDerivAt` specializes that derivative to each actual source coordinate. This is coordinatewise differentiability, not a claimed Hilbert derivative or unrestricted application of the unbounded operator.

`greenStateMaterialLogGenerator_domain_iff_log_moment` proves:

$$
f\in Dom(L_{mat})\iff
\sum_n(\log n)^2\|f(n)\|^2<\infty
$$

where the formal right side is `Summable` of the displayed nonnegative sequence.

`c2Source_log_domain_iff` gives the exact additional condition:

$$
\boxed{f_t\in Dom(L_{mat})\iff
Summable\bigl(n\mapsto(\log n)^2\operatorname{normSq}(f_0(n))\bigr).}
$$

`c2Source_log_domain_time_independent` proves that domain membership is equivalent at all times. It follows from the already proved invariant coordinate norms, not from a newly assumed moment estimate.

The source isometry controls the unweighted sum. It does not by itself supply this log-weighted bound over all cores. No theorem applying $L_{mat}$ to the full source for arbitrary $V$ is added. No counterexample or replacement source is constructed.

## PARSEVAL TRANSPORT READINESS — AUDIT ONLY

Let $P=canonicalAnalysis(canonicalRawGreenAnalysis)$ from the previous round.

- **Range closed: YES.** Existing `canonicalGreenAnalysis_isometry` plus completeness of State gives `Isometry.isClosedEmbedding`, hence a closed range. An audit-only kernel example checks the exact statement.
- **Unitary onto its range: YES.** The existing `canonicalParseval` packages P as a linear isometry; `LinearIsometry.equivRange` packages it as `State ≃ₗᵢ[ℂ] range(P)`. The audit checks this type.
- **Unbounded conjugation: minimal local construction now kernel checked.** The private transport lemma here suffices for unitary conjugation of partial self-adjoint operators. There is still no stock bundled Mathlib conjugation theorem in the consulted version; using the local helper downstream would require making that small API reusable.
- **Zero-complement extension: building blocks, not a completed theorem.** `Submodule.orthogonalDecomposition` provides the unitary product decomposition for a closed Hilbert subspace, and `LinearPMap.coprod` provides partial product composition. No bundled self-adjoint zero-complement extension theorem was found. Its exact missing obligation is self-adjointness/domain transport for $L_{range}\oplus0$ on $Dom(L_{range})\times range(P)^\perp$.

Classification: **UNBOUNDED_TRANSPORT_API_GAP**, specifically the still-unimplemented zero-complement self-adjoint packaging and public reusable conjugation API. The index/unitary material bridge is closed; no $P L_{mat} P^*$ operator or extension is defined in this round.

## HEIGHT OPERATOR

Identified with this generator? **NO.** This is the clock/material log generator. Its eigenvalue on the material delta is $\log n$. No height labels, height operator, moment or Jacobi construction appears.

## AXIOMS / VALIDATION

All 24 new public declarations are checked by rejecting guards and `#print axioms` in `GreenStateMaterialLogGeneratorAudit.lean`. Private transport helpers are covered transitively by the self-adjoint capstone.

The maximum allowed footprint is `[propext, Classical.choice, Quot.sound]`; exact lists, successful build logs and final validation are saved in the evidence bundle. No trust escape is introduced.

The repository-wide static baseline retains its five old comment matches, with zero new matches. This is an inherited static failure, not a global static PASS. Preservation snapshots verify existing worktree files and geometry remain unchanged.

## FILES

New worktree files:

1. `CarrySelfAdjointOperator/GreenStateMaterialLogGenerator.lean`;
2. `CarrySelfAdjointOperator/GreenStateMaterialLogGeneratorAudit.lean`;
3. `docs/GREEN_STATE_MATERIAL_LOG_GENERATOR.md`.

Local evidence is in `c2_material_log_transport_work`, with exact source copies, source manifests, proof/build logs, axioms and preservation snapshots.

## SEMANTIC CONCLUSION

**YES:** the historical maximal multiplier by $\log(j+1)$ is exactly the maximal MATERIAL multiplier by $\log n$ on GreenFrame.State under the canonical unitary address $n=j+1$. Self-adjointness and the maximal domain are transported without changing the operator. The C2 source's log-domain moment and the later Parseval/range-complement transport are separate gates.
