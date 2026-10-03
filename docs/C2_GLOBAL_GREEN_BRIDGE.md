> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# C2 global source → raw concrete Green analysis

## STATUS

**PASS_RESTRICTED_GRAM — the provenance-correct global C2 source embeds canonically into the concrete Green analysis; exact split/frame identities close, but the raw restricted Gram is not proved to be identity.**

Verificado com Lean 4.32.0 no servidor `llm`, sem commit, merge ou push.
Não há afirmação de que o Gram bruto seja diferente da identidade; tampouco
há prova de que seja igual. A questão métrica restante é isolada exatamente.

## REPOSITORY / DEPENDENCY

Worktree downstream: `/home/thlinux/carry-c2-source-raw-green`.
Branch: `canary-c2-source-raw-green`.
HEAD inicial/final: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.

O carry não tinha dependência de `geometry-of-numbers`. A única adição de
configuração ao `lakefile.toml` foi:

```toml
[[require]]
name = "geometry-of-numbers"
path = "../geometry-of-numbers-phase-canary"
```

`lake update geometry-of-numbers` atualizou o manifest local: entrada de path,
reordenação das dependências e `inputRev` de Mathlib. Os pins efetivos das
dependências git anteriores não mudaram. GreenFrame já era dependência transitiva.
O probe importa diretamente os dois projetos e checa os tipos da source, de T
e dos bounds. Não houve cópia de definições ou teoremas upstream na implementação.

Upstream consumido: `/home/thlinux/geometry-of-numbers-phase-canary`, branch
`canary-c2-global-odd-source`, HEAD `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`.
Seu canário é **não commitado**; portanto HEAD sozinho não identifica o PASS.
SHA256 exato de `C2GlobalPhysicalBranchCanary.lean` consumido:
`264cb62f13fb8510d99817c5e251847c1e7cdf641f4828860fd04b9044a546ac`.
A dependência desta rodada é local; as referências e hashes do bundle tornam
explícito qual conteúdo foi verificado.

Mathlib, igual nos dois projetos: `81a5d257c8e410db227a6665ed08f64fea08e997`.
GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.

**geometry-of-numbers remains real; complex packaging begins only at this bridge.**
Nenhum arquivo upstream foi alterado. R2 permanece intacto.

## R2→C PACKAGING

```lean
realPlaneToComplexIsometry : RealPlaneHilbert →ₗᵢ[ℝ] ℂ
```

Avalia `v ↦ ⟨v 0,v 1⟩`, isto é, `x+iy`. O domínio é o EuclideanSpace real
já existente, não o produto com sua norma máxima.

- `realPlaneToComplexIsometry_re` e `_im`: preservam literalmente as coordenadas;
- `realPlaneToComplexIsometry_normSq`: normSq complexo = energia real anterior;
- `realPlaneToComplexIsometry_coordinate_roundtrip`: recupera o par real;
- `realPlaneToComplexIsometry_scale_rotate`: packaging da escala/rotação reais.

A norma usa a identidade coordenada de `Complex.normSq` e o theorem upstream
`realPlaneHilbert_energy_eq_norm_sq`. Não se deriva energia ou amplitude a
partir de complexos; a invariância angular já foi provada upstream.

Referência histórica de leitura:
`primos/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean`,
HEAD `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`, arquivo limpo,
SHA256 `4d5927ced40621df0e87002ce1242c139fd43bf264a3b6d1a88b4c2cbfb45ffe`.
Consultados `nativeCarryRealPlaneComplexPackaging`, suas coordenadas e
`normSq_nativeCarryRealPlaneComplexPackaging`. Esse módulo não é importado
pela ponte; somente o mínimo compatível com o EuclideanSpace foi construído.

## ODD→PNAT INCLUSION

```lean
oddMaterialToGreenState : OddMaterialState →ₗᵢ[ℝ] GreenFrame.Concrete.State
```

Extensão por zero ao longo da inclusão injetiva de `OddMaterialIndex` em PNat:

$$
(Jx)(n)=
\begin{cases}
\operatorname{pack}(x(\langle n,h\rangle)),&n\text{ ímpar},\ n\ge3,\\
0,&\text{fora desse setor}.
\end{cases}
$$

Theorems: `oddMaterialToGreenState_apply`, `_apply_off_sector`, `_one`, `_even`,
`_norm`. A somabilidade e a norma seguem da injetividade do índice, da
isometria coordenada e da soma quadrática ℓ². Não se descarta quadratura.

$$\boxed{\|Jx\|=\|x\|.}$$

## C2 GREEN INPUT

```lean
c2GlobalGreenInputIsometry (t : ℝ) : CoreState →ₗᵢ[ℝ] State
```

Composição direta de `oddMaterialToGreenState` com
`GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry t`.
Nenhuma amplitude nova é introduzida.

Se `oddMaterialC2Address n=(m,(a,j))` e `k=j+2`, a igualdade pointwise é:

$$
(JW_tV)(n)=2^{-k/2}
\left(\cos(-t\log n)+i\sin(-t\log n)\right)\operatorname{pack}(V(m)).
$$

Essa é a interpretação coordenada de `e^{-it log n}` solicitada: o código
prova o packaging da rotação real, sem usar exponencial complexo para
justificar a source. Theorems: `c2GlobalGreenInput_apply`, `_closed_form`.

Amplitude = **`2^(-k/2)`** no depth C2 recuperado, sem substituição por
`n^(-1/2)`. Fase = **`−t log n`** no material. `_one` e `_even` certificam
zero no seed e nos pares do **input**, sem afirmar zero nas linhas Green.

Proveniência:

- `c2GlobalGreenInput_provenance` mantém o mesmo material e o roundtrip de
  endereço completo `oddMaterialC2Address (globalC2OddMaterialAddress i)=i`;
- `c2GlobalGreenInput_quadrature_roundtrip` recupera o par real em cada material;
- o decoder upstream continua recuperando separadamente core, sinal e depth.

A source histórica diagonal não foi usada. O índice de eventos/row-depth do
Green é próprio de T; não foi identificado com o depth C2 dos vizinhos de n.

## RAW GREEN COMPOSITION

Fixada a escolha formal existente `canonicalCarryInfinitePartition`.
Sua definição está em `GreenFrame/Concrete/Analysis/InfinitePartition.lean`
e usa os pesos carry já certificados como partição admissível.

```lean
c2GlobalGreenAnalysis (t : ℝ) : CoreState →L[ℝ] ConcreteAnalysisSpace
```

$$A_t=T_{\mathbb R}\circ J\circ W_t,$$

onde `Tℝ=(concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ`.
O domínio permanece real. Não foi alegada linearidade complexa de CoreState.
`c2GlobalGreenAnalysis_apply` identifica a composição com o T original em cada input.

## FRAME BOUNDS

`c2GlobalGreenAnalysis_norm_sq_bounds` reutiliza literalmente
`concreteAnalysisOperator_norm_sq_bounds` e `c2GlobalGreenInput_norm`:

$$
\boxed{\tfrac12\|V\|^2\le\|A_tV\|^2
\le(1+\mathrm{greenBesselConstant})\|V\|^2.}
$$

Não se rederivam estimativas Green nem se recebem bounds como hipóteses novas.

## SPLIT ENERGY

Os três canais concretos são mantidos. Foram provadas as identidades:

$$\|A_tV\|^2=\|\mathrm{SeedResidual}(JW_tV)\|^2+\|\mathrm{Green}(JW_tV)\|^2,$$

$$\|A_tV\|^2=\|\mathrm{External}(JW_tV)\|^2+\|\mathrm{Bulk}(JW_tV)\|^2,$$

$$\|A_tV\|^2=\|\mathrm{SeedResidual}(JW_tV)\|^2+
\|G_1(JW_tV)\|^2+\|G_{\ge2}(JW_tV)\|^2.$$

O seed do input é zero. `c2GlobalGreenInput_seedResidual_eq_residual` permite
portanto obter exatamente:

$$\boxed{\|A_tV\|^2=\|\mathrm{Residual}(JW_tV)\|^2+
\|G_1(JW_tV)\|^2+\|G_{\ge2}(JW_tV)\|^2.}$$

Nomes públicos: `c2GlobalGreenAnalysis_split_seedResidual_green`,
`_split_external_bulk`, `_split_three`, `_split_residual_depthOne_bulk`.
As provas são composição dos splits existentes de ConcreteSplitOperators.

## RAW ISOMETRY TEST

**RAW_GREEN_ISOMETRY_NOT_DERIVED.**

A auditoria procurou identidade do Gram/isometria no split concreto, em
ConcreteSplitBounds, FrameOperator, CanonicalParseval e nos usos existentes
da partição canônica no carry. Não foi identificado theorem que faça o Gram
bruto virar identidade no range desta source C2 global.

A evidência encontrada é distinta:

- ConcreteSplitOperators: identidades de split exatas;
- ConcreteSplitBounds: bounds quantitativos;
- FrameOperator: positividade/invertibilidade do Gram;
- CanonicalParseval: identidade Gram para **canonicalAnalysis**, com
  `inverseSqrtFrame`, e não para T bruto;
- os carriers existentes do carry que anunciam preservação métrica usam
  transporte Parseval; não consomem esta source upstream nem identificam seu
  Gram bruto com I.

Esses módulos downstream foram somente lidos; nenhum theorem Parseval foi
importado ou aplicado na construção principal. O log de busca e os snapshots
permitem inspecionar os tipos/definições correspondentes.

Foi definido, sem assumir zero:

$$D_t(V)=\|A_tV\|^2-\|V\|^2.$$

`c2GlobalRawGreenDefect_split` exibe o split exato do defeito; `_bounds` prova

$$-\tfrac12\|V\|^2\le D_t(V)\le\mathrm{greenBesselConstant}\|V\|^2.$$

`_zero` prova `D_t(0)=0`. Não se produziu witness não nulo nem se provou
necessidade de whitening. A ausência de uma ponte encontrada é resultado
da auditoria do corpus, não um theorem Lean sobre ausência de theorems.

## RESTRICTED GRAM

**Definido:**

```lean
c2GlobalRestrictedGreenGram (t : ℝ) : CoreState →L[ℝ] CoreState
```

$$G_t=A_t^*A_t.$$

- `_inner`: $\langle G_tV,V\rangle_{\mathbb R}=\|A_tV\|^2$;
- `_positive`: `IsPositive`;
- `_bounds`: lower `1/2`, upper `1+greenBesselConstant` na forma quadrática;
- `_isUnit`: invertível no Banach algebra;
- `_bijective`: bijetivo;
- `_strictlyPositive`: positivo e invertível.

A invertibilidade usa diretamente a coercividade herdada e a API genérica
real `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`; não utiliza CFC
nem square root. Não foi construído um inverso para normalizar A.

**Identidade:** ainda não provada. Foi provado o critério exato:

$$G_t=I\iff(\forall V,\ \|A_tV\|=\|V\|)
\iff(\forall V,\ D_t(V)=0).$$

Theorems `_eq_one_iff_norm` e `_eq_one_iff_defect_zero` são equivalências,
não afirmações da identidade ou hipóteses artificiais na construção de A.

### Relação com a isometria crítica upstream

`c2GlobalSource_adjoint_comp_self`,
`oddMaterialToGreenState_adjoint_comp_self` e
`c2GlobalGreenInput_adjoint_comp_self` provam respectivamente:

$$W_t^*W_t=I,\qquad J^*J=I,\qquad(JW_t)^*(JW_t)=I.$$

`c2GlobalRestrictedGreenGram_compression` e `_source_factors` provam:

$$\boxed{G_t=W_t^*J^*T_{\mathbb R}^*T_{\mathbb R}JW_t.}$$

`c2GlobalRawGreenDefect_eq_gram_defect` prova:

$$D_t(V)=\langle(G_t-I)V,V\rangle_{\mathbb R}.$$

Assim, a métrica adicional vem exclusivamente do T bruto comprimido ao range
do input isométrico; não do packaging, do índice ou da amplitude crítica.

## WHITENING

**used? NO.**

Nenhum uso de `inverseSqrtFrame`, `canonicalAnalysis` ou `canonicalParseval` nos
dois arquivos Lean novos. CanonicalParseval foi auditado somente como referência.
O restricted Gram fica visível antes de qualquer normalização.

## FIRST GAP

Proposição ainda aberta:

```text
∀ t : ℝ, c2GlobalRestrictedGreenGram t = 1
```

Equivalentemente, zerar `c2GlobalRawGreenDefect t V` para todos os inputs.
Não existe uma declaração nova postulando isso. Se a igualdade falhar,
um witness específico ainda terá de ser provado; nenhum foi inventado.
Não há gap técnico na composição source → Green ou no Gram restrito.

## AXIOMS

Todos os **48** nomes públicos têm guard e `#print axioms` em
`C2GlobalGreenBridgeAudit.lean`. Cada um tem exatamente:

```text
[propext, Classical.choice, Quot.sound]
```

Incluem packaging, inclusão, input, A, bounds, splits, Gram, invertibilidade,
fatoração e critérios. A auditoria rejeita qualquer dependência adicional.
`AXIOMS.json` registra cada nome individualmente; `kernel-prints.log` guarda
as saídas literais. Nenhum novo escape de confiança.

## BUILDS / VALIDATION

Builds com `--wfail` da ponte e do audit passaram. O audit executado diretamente
com `lake env lean` também passou, incluindo nove exemplos formais. Probe de
dependência, checks de escopo, JSONs, sintaxe dos scripts e `git diff --check`
passaram. A cobertura kernel desta rodada é a ponte e seu audit dedicado;
não se anuncia rebuild/audit completo das camadas legadas.

### Falha estática herdada registrada

`scripts/static_audit.sh` retorna **1** no checkout inicial: seu regex também
lê comentários. Os mesmos cinco hits permanecem no HEAD inicial e na worktree:

- `CompletedNativePrimosProjectiveMassCrosswalkAudit.lean:55–56`;
- `CompletedNativeCameraVerticalHorizontalEnergyCrosswalkAudit.lean:8`;
- `CompletedNativeFirstSecondLayerAudit.lean:716`;
- `CompletedNativeTfvdSixSourceGammaEscapeRadialAuditAxioms.lean:8`.

Todos são comentários negando o uso desses escapes. Não são declarações ou
provas com placeholders. `STATIC_BASELINE_COMPARISON.json` registra igualdade
exata dos hits; o check dedicado confirma **zero hits novos** nos arquivos da
ponte. Os módulos legados e o script global não foram alterados para apagar a
falha. Logs da primeira tentativa e da validação final ficam preservados.

## FILES

Novos, exclusivamente na worktree downstream:

- `CarrySelfAdjointOperator/C2GlobalGreenBridge.lean`;
- `CarrySelfAdjointOperator/C2GlobalGreenBridgeAudit.lean`;
- `docs/C2_GLOBAL_GREEN_BRIDGE.md`;
- `audit/C2GlobalGreenDependencyProbe.lean`;
- `audit/check_c2_global_green_static_baseline.py`.

Modificados: `lakefile.toml`, `lake-manifest.json` (dependência local mínima).
Nenhum módulo matemático anterior, root import ou registry anterior foi editado.

Preservação verificada: HEAD/status/conteúdo de todas as alterações anteriores
nos checkouts carry (23 entradas), geometry (20), GreenFrame (limpo) e primos
(2 entradas); source global upstream com o mesmo SHA256. Nenhum commit,
merge ou push. As compilações escrevem apenas artefatos de build/cache.

### Artifact bundle

Local: `/home/thlinux/Downloads/FORMALIZANDO/c2_green_bridge_work`.
Remoto: `/home/thlinux/c2-global-green-bridge-artifacts`.

Contém arquivos finais, configurações, sources consultadas por leitura,
manifest de hashes, diffs, logs, lista pública, resultados de axiomas,
validação, baseline estático e snapshots de preservação. Os snapshots são
artefatos de auditoria; não substituem o import da dependência upstream.

## SEMANTIC CONCLUSION

A source C2 global correta chega isometricamente ao estado material complexo
PNat e entra nos canais concretos do Green bruto com proveniência intacta.
O Gram induzido é positivo e invertível, mas sua igualdade com I **não foi
provada**. Portanto esta rodada não permite eliminar a normalização métrica
nem afirmar que ela seja necessária. O elo exato restante é `G_t=I` no range
isométrico desta source; qualquer defeito adicional está em T, não em J ou W.
