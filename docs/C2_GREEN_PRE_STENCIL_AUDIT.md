> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# C2 / Green: localização exata do defeito métrico

## STATUS

**PASS — the branch/source, atlas, and conservative Green/return split are all isometric; the restricted Green Gram defect is localized exactly to replacement of the direct transmitted coordinate by the vertical TFVD/Green stencil.**

Este PASS é uma identidade estrutural. Não afirma que o defeito seja diferente de zero, que tenha um sinal, ou que o Green bruto deixe necessariamente de ser isométrico em alguma source específica.

## Repositório e proveniência

- Worktree downstream: `/home/thlinux/carry-c2-source-raw-green` no servidor `llm`.
- Branch preservada: `canary-c2-source-raw-green`.
- HEAD preservado: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- GreenFrame consultado: `/home/thlinux/carry-self-adjoint-operator/.lake/packages/GreenFrame`, commit `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Upstream real: `/home/thlinux/geometry-of-numbers-phase-canary`, HEAD `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`, dependência local já configurada.
- `C2GlobalPhysicalBranchCanary.lean` upstream: SHA-256 `264cb62f13fb8510d99817c5e251847c1e7cdf641f4828860fd04b9044a546ac`. O PASS upstream está em arquivos de trabalho; o HEAD isolado não identifica todo o conteúdo usado.
- A entrada desta rodada é exclusivamente o `c2GlobalGreenInputIsometry` já existente em `C2GlobalGreenBridge.lean`.

A fundação e R2 permanecem reais e intactos. Este canário vive na camada downstream já complexificada. Não usa a source diagonal antiga.

## ELEMENTARY ATLAS

**Isometric = YES.** Reutilizados, sem modificar suas definições ou reescrever suas provas:

- `GreenFrame.Concrete.elementaryAtlas_norm_sq_eq`
- `GreenFrame.Concrete.elementaryAtlas_isometry`
- `GreenFrame.Concrete.elementaryAtlasLinearIsometry`
- `GreenFrame.Concrete.canonicalCarryElementaryAtlas_isometry`

A prova nova de conservação usa a identidade de componentes do atlas e o teorema de norma já fechado. Não deriva novamente a partição de unidade.

## GREEN/RETURN MASS SPLIT

**Conservative = YES.** O histórico formal já prova:

```lean
GreenFrame.Concrete.greenMass_add_residualMass
```

A API aritmética desse teorema usa `AdmissiblePartition`, base natural `b` e número natural `n`. A API analítica usa `AdmissibleInfinitePartition`, código `r`, `baseReal r` e `PNat`.

O novo `canonicalDirectGreenMass_add_residualEventMass` é literalmente a especialização do teorema existente em `carryPartition (baseNat r) n`, por simplificação das definições. O auxiliar geral `directGreenMass_add_residualEventMass` registra a mesma identidade para qualquer partição infinita admissível:

$$
\frac{\omega_r(n)}{b_r}+\omega_r(n)\left(1-\frac1{b_r}\right)=\omega_r(n).
$$

Não há outra escolha de massa nem renormalização. O canal de retorno aqui é exatamente `residualAnalysis` do GreenFrame existente.

## DIRECT GREEN COORDINATE

Definição nova, namespace `CarrySelfAdjointOperator.C2GreenPreStencilCanary`:

```lean
directGreenCoordinate omega e f :=
  (greenAmplitude omega e : ℂ) * f (eventNumber e)
```

Com `e=(r,parent)` e `n=eventNumber e=b_r parent`:

$$
D_e(f)=\sqrt{\mu_G(e)}f(n),\qquad
\mu_G(e)=\omega_r(n)/b_r.
$$

**Energia exata**: `directGreenCoordinate_normSq_eq`:

$$
\operatorname{normSq}(D_e(f))=\mu_G(e)\operatorname{normSq}(f(n)).
$$

`directGreenAnalysis` é um elemento de `ℓ²(GreenEvent, ℂ)`. A somabilidade é obtida por dominação pela energia do atlas já somável e pela injeção `eventDivisibilityEquiv`. A identidade de energia global usa a reindexação existente `tsum_greenEvent_reindex`, com o suporte aritmético da partição.

`directGreenAnalysis_norm_sq_eq`:

$$
\|D_\omega f\|^2=
\sum_{(n,r)}\frac{\omega_r(n)}{b_r}|f(n)|^2.
$$

Também foram construídos `directGreenAnalysisLinearMap` e `directGreenAnalysisOperator`, com `directGreenAnalysis_norm_le`.

## PRE-STENCIL ANALYSIS

Carrier:

```lean
PreStencilSpace := WithLp 2 (SeedResidualSpace × ℓ²(GreenEvent, ℂ))
```

Definição:

```lean
preStencilAnalysis omega f :=
  WithLp.toLp 2 (seedResidualAnalysis omega f, directGreenAnalysis omega f)
```

Portanto contém, literalmente, o seed existente, as coordenadas residual/return existentes e o canal Green direto. Não separa G1 e G≥2.

**Conservação das câmeras** — `directGreen_add_residual_eq_elementaryCamera`:

$$
\|D_\omega f\|^2+\|R_\omega f\|^2=
\|\operatorname{elementaryAtlasCamera}_\omega f\|^2.
$$

**Norm identity** — `preStencilAnalysis_norm_sq_eq`, `preStencilAnalysis_norm`:

$$
\|\operatorname{Pre}_\omega f\|^2=\|f\|^2,
\qquad \|\operatorname{Pre}_\omega f\|=\|f\|.
$$

**LinearIsometry = YES**:

- `preStencilLinearIsometry : State →ₗᵢ[ℂ] PreStencilSpace`;
- `preStencilRealLinearIsometry : State →ₗᵢ[ℝ] PreStencilSpace`.

Não foi construída uma equivalência de carriers entre o atlas e o pré-stencil: a identidade conservativa de energia é suficiente, sem identificar o range com todo o novo contradomínio.

## C2 PRE-STENCIL

```lean
c2GlobalPreStencilIsometry t : CoreState →ₗᵢ[ℝ] PreStencilSpace
```

É a composição da restrição real da isometria pré-stencil canônica com `c2GlobalGreenInputIsometry t`.

**Norm preservation = YES** — `c2GlobalPreStencil_norm`:

$$
\|\operatorname{Pre}_{\mathrm{canonical}}(JW_tV)\|=\|V\|.
$$

O teorema `c2GlobalPreStencil_apply` identifica exatamente essa composição. A proveniência da source não é alterada.

## ACTUAL GREEN / STENCIL CORRECTION

`greenCoordinate_eq_direct_add_ancestorCorrection`:

$$
G_e(f)=D_e(f)+C_e(f).
$$

`greenStencilCorrection_eq`, com $q_r=\operatorname{carryRatio}(r)$:

$$
C_e(f)=\sqrt{\mu_G(e)}
\left[-2q_r f(parent)+
\begin{cases}
q_r^2 f(grandparent),&\operatorname{HasGrandparent}(e),\\
0,&\text{caso contrário}.
\end{cases}\right].
$$

A condição do segundo ancestral é exatamente a original. Não existe extensão fictícia de profundidade um.

A correção também existe globalmente em ℓ²:

```lean
greenStencilCorrectionAnalysis omega f :=
  greenAnalysis omega f - directGreenAnalysis omega f
```

`greenStencilCorrectionAnalysis_apply` prova a fórmula coordenada-a-coordenada. `greenStencilCorrectionOperator` é um mapa contínuo linear, definido como a diferença dos dois operadores limitados. Não requer uma nova estimativa de Bessel.

## GRAM DEFECT

**General identity** — `concreteAnalysis_norm_sq_sub_preStencil_norm_sq`:

$$
\|T_\omega f\|^2-\|\operatorname{Pre}_\omega f\|^2
=\|G_\omega f\|^2-\|D_\omega f\|^2.
$$

Usa somente a decomposição exata existente
`concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green`
e a decomposição dos componentes pré-stencil. O seed e o residual cancelam literalmente.

`concreteAnalysis_norm_defect_eq_stencil_defect`:

$$
\boxed{\|T_\omega f\|^2-\|f\|^2
=\|G_\omega f\|^2-\|D_\omega f\|^2.}
$$

**C2 specialization** — `c2GlobalRawGreenDefect_eq_stencil_defect`, escrevendo $f_t=JW_tV$:

$$
\boxed{D_t(V)=\|G_{\rm canonical}f_t\|^2-
\|D_{\rm canonical}f_t\|^2.}
$$

**Restricted Gram** — `c2GlobalRestrictedGreenGram_stencil_defect`:

$$
\boxed{\langle(G_t-I)V,V\rangle_{\mathbb R}
=\|G_{\rm canonical}f_t\|^2-\|D_{\rm canonical}f_t\|^2.}
$$

O corolário usa o teorema da rodada anterior `c2GlobalRawGreenDefect_eq_gram_defect`. Não reconstrói adjoints ou o Gram.

## FIRST NON-ISOMETRIC STEP

A primeira etapa em que uma alteração de métrica pode aparecer é a substituição:

$$
f(n)\longmapsto f(n)-2q_r f(parent)+q_r^2f(grandparent),
$$

com o terceiro termo condicionado como acima. Todas as etapas anteriores listadas são isométricas/conservativas.

Esta rodada **não prova que essa substituição seja efetivamente não isométrica no range C2**, nem que $D_t(V)\ne0$. Localiza exatamente qualquer defeito que exista. Uma correção vetorial não nula, por si só, não estabelece uma diferença de energias: termos cruzados podem cancelar sua contribuição quadrática.

## TFVD CROSSWALK

Foram auditados e reutilizados como identificação existente:

```lean
verticalGreenStencil_eq_canonicalNormalizedTowerTFVD
greenCoordinate_eq_canonicalNormalizedTowerTFVD
```

O passo responsável pela diferença de energias é exatamente o já identificado com a TFVD de torre normalizada. Não há uma nova TFVD nem mudança em R2.

## WHITENING

**Used? NO.** Nenhuma prova nova utiliza `inverseSqrtFrame`, `canonicalAnalysis` ou `canonicalParseval`. A eventual normalização posterior atua sobre o Gram da análise que já aplicou o stencil; não se demonstrou aqui que seja necessária ou trivial no range C2.

## AXIOMS / validação

- Todas as 40 declarações públicas novas possuem guard `#assert_pre_stencil_axioms` e impressão `#print axioms` no audit dedicado.
- Todas usam exatamente `[propext, Classical.choice, Quot.sound]`.
- Os sete resultados existentes explicitamente pedidos também têm guard e impressão no mesmo audit.
- Build remoto isolado do módulo e do audit: **PASS**.
- Reexecução direta do audit pelo Lean: **PASS**.
- `git diff --check`: **PASS**.
- Busca no código novo: nenhum `sorry`, `admit`, novo `axiom` ou `unsafe`; nenhum uso de whitening.
- `scripts/static_audit.sh` global: **FAIL herdado**, por cinco ocorrências textuais em comentários de módulos antigos. A comparação com HEAD e o estado anterior confirma exatamente os mesmos cinco matches, sem acréscimo do canário. Os arquivos antigos não foram modificados para silenciar esse audit.
- Hashes/estado: todos os arquivos dirty preexistentes da worktree e dos checkouts upstream foram preservados; nenhuma alteração em `geometry-of-numbers`, em R2 ou no GreenFrame.

Os outputs completos e hashes estão em `AXIOMS.json`, `PUBLIC_NAMES.json`, `SOURCE_MANIFEST.json`, `VALIDATION.json`, `PRESERVATION_BEFORE.json`, `PRESERVATION_AFTER.json` e `logs/` no bundle da rodada.

## FILES

Apenas três arquivos novos na worktree downstream:

1. `CarrySelfAdjointOperator/C2GreenPreStencilCanary.lean`;
2. `CarrySelfAdjointOperator/C2GreenPreStencilCanaryAudit.lean`;
3. `docs/C2_GREEN_PRE_STENCIL_AUDIT.md`.

Nenhum arquivo anterior foi editado. A configuração local de dependências anterior foi preservada. Sem commit, merge ou push.

Cópia local fiel e evidências: `/home/thlinux/Downloads/FORMALIZANDO/c2_pre_stencil_work`.

## SEMANTIC CONCLUSION

O Gram adicional não vem da source C2, da incidência material, do packaging real→complexo, da partição por câmeras ou da divisão conservativa Green/return. A diferença métrica da análise concreta é **exatamente** a diferença entre o canal Green que aplica o stencil vertical e o canal que transmite diretamente os mesmos dados com a mesma massa.

Portanto qualquer Gram adicional surge somente nessa substituição pelo stencil. Permanecem fora desta conclusão sua existência efetiva, seu sinal e sua eventual anulação no range da source C2.
