# C2: incidência material e correção física exata das pernas

## STATUS

**PASS — the critical branch isometry extends canonically to a provenance-preserving physical C2 material source by coordinatewise leg-phase correction and injective address reindexing.**

Branch `canary-c2-physical-material`, checkout llm
`/home/thlinux/geometry-of-numbers-phase-canary`, base
`93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`. Sem commit, merge ou push.

## Referência histórica e limite do porte

Única referência histórica para a construção aritmética:
`formalizacao_C2/LeanC2/Foundations/Dyadic.lean`, commit
`dc35555879e3c0f188508c729c4a0ea31be246fb`.

O arquivo consultado está **modificado** no checkout. SHA256 do conteúdo:
`a7b17be4ee2a41064886ef4179495aa229c3ee73da8e5028f382e9a717944c98`.
A diferença em relação ao commit troca o import `Basic` por `BasicCore`.
As duas versões e o diff estão arquivados; nenhuma foi alterada ou importada
como dependência. As provas novas foram verificadas no projeto novo.

| Histórico consultado | Recuperação local |
|---|---|
| `BranchSign`, `toInt` | `C2BranchDirection` e `c2BranchDirectionSign` preexistentes: 0 → −1, 1 → +1 |
| `natDescendant` | `c2BranchMaterialNat`, com depth explícito `j+2` |
| `natDescendant_address_unique` | Injetividade e unicidade no range para core fixo; prova local por resíduos mod 4 e injetividade da potência |
| `keff_left_leg`, `keff_right_leg` | Equivalência de todos os thresholds de carry dos dois vizinhos com `r ≤ k`, sob core ímpar |
| `bracket_bijection_odd_ge_three` | Consultado para genealogia; não foi necessário portar a cobertura global de todos os cores |

Não se definiu profundidade por valuation. O threshold relacional local
`Geometry.HasCarryDepthAtLeast` continua sendo a referência.

## ADDRESS

~~~lean
C2BranchAddress := C2BranchDirection × ℕ
c2BranchDepth i := i.2 + 2
c2BranchMaterialNat m i :=
  if i.1 = 0 then 2^(c2BranchDepth i)*m - 1
  else 2^(c2BranchDepth i)*m + 1
~~~

Para `m>0`, os endereços são naturais ≥3 e são empacotados como `PNat` em
`c2BranchMaterialAddress m hm`. O domínio não é um sample material arbitrário:
o endereço causa o ponto material.

`c2BranchMaterialAddress_injective` prova a injetividade para core fixo
positivo. Oddness não é necessária para essa injetividade; ela é necessária
para identificar o depth endereçado com o depth intrínseco efetivo.

### Recuperação

- **Sign:** `c2BranchMaterialNat_sign_mod_four`: resíduo 3 para −1, resíduo 1 para +1.
- **Depth:** `c2BranchMaterialAddress_depth_recovery`, sob `Odd m`, prova para todo `r`:

$$
\bigl(DepthAtLeast_2(n-1,r)\lor DepthAtLeast_2(n+1,r)\bigr)
\iff r\le k.
$$

  A perna é ímpar; esse é seu depth **efetivo**, lido nos vizinhos.
  Não se afirma que a profundidade de carry da própria perna seja k.
- **Core:** `c2BranchMaterialNat_core_recovery` prova a recuperação por
  `(n+1)/2^k` no ramo negativo ou `(n-1)/2^k` no positivo.
- **Unicidade:** `c2BranchMaterialAddress_eq_iff` e
  `c2BranchMaterialAddress_range_unique` recuperam o endereço único no range.

Não foi definida uma inversa arbitrária sobre todos os positivos.

## REAL MATERIAL STATE

~~~lean
RealMaterialState := ℓ²(PNat, RealPlaneHilbert)
RealPlaneHilbert := EuclideanSpace ℝ (Fin 2)
~~~

As duas quadraturas e a energia euclidiana são as da rodada anterior.
O material integer n é o índice de saída; o depth k continua no endereço.

## INCIDENCE ISOMETRY

`branchIncidenceIsometry m hm` tem tipo:

~~~lean
C2BranchCarrier →ₗᵢ[ℝ] RealMaterialState
~~~

É a extensão por zero `Function.extend` da Mathlib ao longo da injeção
de endereços. Cada preimagem no range é única; não há seleção de uma nova
decomposição geométrica. O `Classical.choice` da implementação não
acrescenta liberdade ao endereço. Fora do range o vetor é zero.

`branchIncidenceIsometry_norm` prova conservação de norma por reindexação
da soma quadrática. `branchIncidenceIsometry_coordinate_roundtrip` prova
o roundtrip de todas as coordenadas do carrier de ramo.
Nenhuma rotação participa dessa prova.

## PURE BRANCH PHASE

Reindexing the pure branch operator onto material addresses does not yet make
its phase equal to the physical phase of `2^k m ± 1`.

O ramo puro conserva `R_(-kt log2)` nesta etapa. A fase física é obtida por
uma operação separada e explicitamente provada abaixo.

## PHYSICAL LEG CORRECTION

`c2PhysicalLegCorrectionAngle` conserva o defeito exato:

$$
\alpha_{m,t}(a,k)=-t\left(\log m+
 \log\left(1+\frac{a}{2^k m}\right)\right).
$$

`c2PhysicalLegPhase_factorization` reutiliza
`c2FiberPoint_log_eq_depth_core_defect` e prova:

$$
\boxed{R_{\alpha_{m,t}(a,k)}R_{-kt\log2}
 =R_{-t\log(2^km+a)}.}
$$

Não há aproximação ou eliminação vetorial do log-defect.
`physicalLegCorrection m t` é uma `LinearIsometry` no branch carrier:
rotações coordenadas preservam exatamente as normas dos termos de ℓ².

`physicalLegCorrection_norm` prova preservação da norma;
`physicalLegCorrection_neg_comp` prova que a correção em `-t` desfaz
a correção em `t`. O theorem universal também fornece a ordem reversa
ao substituir t por −t.

## PHYSICAL SOURCE

`physicalBranchOperator sigma t hsigma m hm` é ℝ-linear e definido por:

$$
PhysicalW=Incidence_m\circ Correction_{m,t}\circ W_{\sigma,t}.
$$

Para `sigma>0`, `m>0`, `k=j+2`,
`physicalBranchOperator_apply_address` prova:

$$
\boxed{(PhysicalW_{\sigma,t,m}v)(2^km+a)
 =2^{-k\sigma}R_{-t\log(2^km+a)}v.}
$$

A igualdade usa o readout `realPlaneHilbertEquiv.symm` para exibir literalmente
o `RealPlaneState` original. Não há alteração da energia ou de suas instâncias.

`physicalBranchOperator_apply_off_range` prova zero fora dos endereços
desse core. Isso inclui todos os pontos não alcançados pelo ramo, inclusive
material 1 e os pares. Não se afirma uma completion global da source.

`physicalBranchOperator_norm` conserva a norma do ramo original para toda
a família positiva em sigma. `physicalBranchOperator_norm_sq` conserva
literalmente o fator `c2BranchOrbitMass` anterior, sem nova série geométrica.

## CRITICAL ISOMETRY

`realCriticalPhysicalBranchIsometry m hm t` é a composição das três isometrias:

~~~lean
RealPlaneHilbert →ₗᵢ[ℝ] RealMaterialState
~~~

`realCriticalPhysicalBranchIsometry_eq_operator` identifica seu mapa linear
com o `physicalBranchOperator` em sigma=1/2.
`realCriticalPhysicalBranchIsometry_norm` prova:

$$
\boxed{\|PhysicalW_{1/2,t,m}v\|=\|v\|.}
$$

## ADJOINT

**PROVED:** `realCriticalPhysicalBranch_adjoint_comp_self`:

$$
\boxed{PhysicalW_t^*PhysicalW_t=I.}
$$

Aplicação direta de `LinearIsometry.adjoint_comp_self`; sem cálculo
coordenado de adjunto. Não implica sobrejetividade no material ℓ².

## PROVENANCE / SEMANTIC_DIAGONAL_GAP

**PROVENANCE_GAP_CLOSED_FOR_FIXED_C2_CORE.**

`physicalBranchOperator_nonzero_provenance` prova que cada coordenada
material não nula tem exatamente um endereço no core fixo. Os theorems
de resíduos, thresholds e divisão recuperam sign, depth e core;
o material integer é o próprio endereço de saída. O roundtrip da incidência
preserva ambas as quadraturas, inclusive as coordenadas iniciais j=0.
`physicalBranchOperator_branch_coordinate_roundtrip` lê a source nos
endereços e desfaz a rotação, recuperando todas as coordenadas do ramo original.

Esta source não recupera nem assume a antiga `q^n ψ_t(n)`.
A cadeia formal é `depth k → (a,k,m) → n=2^k m+a`, e a fase usa `log n`.
A amplitude usa k. A identificação sample=depth continua proibida.

O fechamento é do ramo de core fixo solicitado, não de uma união de todos
os cores, dados de bordo de outra teoria, head/tail ou reconstrução TFVD.

## GREEN FRAME READINESS — somente auditoria

**READY_FOR_GREEN_ANALYSIS_INPUT**, quanto a índice e carrier material.

- `GreenFrame.Concrete.State := ℓ²(PNat, ℂ)` usa exatamente o mesmo índice
  material `PNat`. A nova source real usa R² euclidiano por coordenada.
- A source de core fixo tem suporte restrito; isso é um elemento válido
  do carrier material completo, estendido por zero. Não há index mismatch.
- A identificação usual `(x,y) ↔ x+i y` seria empacotamento coordenado
  das quadraturas com a mesma energia. Não foi implementada nesta rodada,
  e nenhum complexo foi usado nas novas definições/provas.
- Não existe theorem encontrado que conecte **esta nova source** ao
  `concreteAnalysisOperator`. Aplicação/realificação e qualquer transporte
  posterior não foram implementados. A classificação READY não fecha
  Green, naturalidade, Parseval ou uma identificação de sources históricas.

Auditados somente os tipos/definições de `GreenStencilComplex.lean:16` e
`ConcreteSplitOperators.lean:50–65`, na dependência GreenFrame do checkout
histórico, SHA `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
Nenhum desses módulos foi importado no projeto novo.

## AXIOMS / VALIDATION

Os 39 nomes públicos novos têm guards e `#print axioms` no Audit.
Os capstones de incidência, fase física, source, norma crítica e adjunto
têm footprint `[propext, Classical.choice, Quot.sound]`.
O footprint por declaração está em `AXIOMS.json`.

Builds do módulo, Analysis e Audit; três scripts de auditoria; busca de
placeholders; `git diff --check`; preservação por SHA256 dos arquivos anteriores
e guard dos módulos congelados. Logs e resultados em `c2_physical_branch_work`
local e `c2-physical-branch-artifacts` no llm.

Exemplos formais: endereços 3 e 5, depth efetivo dois da perna 3,
norma da incidência, correção invertida por −t, fase física `log 3`,
zero fora do range em material 2, norma crítica e identidade do adjunto.

## FILES

Novos:

- `GeometryOfNumbers/Analysis/C2PhysicalBranchCanary.lean`;
- `docs/C2_PHYSICAL_BRANCH_CANARY.md`.

Adições em:

- `GeometryOfNumbers/Analysis.lean`;
- `GeometryOfNumbers/Analysis/Audit.lean`;
- `docs/SOURCE_PROVENANCE.md`.

R2, Foundation, Geometry, os canários anteriores e alterações paralelas
permanecem preservados. Sem commit, merge ou push.

## SEMANTIC CONCLUSION

**SIM.** Para core C2 ímpar positivo fixo, o operador de ramo crítico
foi promovido a uma source material fisicamente faseada e isométrica,
por correção angular exata das pernas e incidência injetiva de endereços.
Não há colagem de índices, e o log-defect permanece na fase vetorial.
