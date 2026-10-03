# Auditoria/canário: fase sintetizada e defeito centro–pernas

## STATUS

**PARTIAL — local no-cancellation is closed, synthesis→rotation bridge still open.**

Checkpoint consultado: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`, igual a
`main` e `origin/main` após fetch. Branch de trabalho isolada:
`audit-synthesized-phase-canary`.

**NÃO ficou provado que a fase sintetizada apenas gira uma configuração já
determinada.** O objeto global pós-síntese com evolução angular não existe nesta
árvore. Além disso, as famílias de ângulos permitidas na câmera/atlas não estão
restritas a uma rotação comum: um contraexemplo vetorial foi certificado.
Isso NÃO refuta a ausência de cancelamento das energias locais já formalizadas.

## 1. Objetos efetivamente encontrados

| Objeto preexistente | Tipo/construção | Resultado da inspeção |
| --- | --- | --- |
| `realCriticalDepthState` | `(b,k,hb,theta) → ℝ × ℝ` | Rotação da semente crítica; ângulo livre, sem lei de evolução selecionada |
| `centerLegForm` | `q → theta → RealPlaneState → RealPlaneState` | Três posições construídas antes do readout; uma rotação compartilhada LOCALMENTE |
| `centerLegCameraEnergy` | `half → (ℕ→ℝ) → (ℕ→ℝ) → (ℕ→RealPlaneState) → ℝ` | `theta r` livre por canal; soma de energias locais |
| `centerLegAtlasEnergy` | `P → half → (AtlasBase→ℕ→ℝ) → (AtlasBase→ℕ→ℝ) → (ℕ→RealPlaneState) → ℝ` | `theta b r` livre por base e canal; soma de energias de câmeras |
| `realCarryTfvdSynthesis` | `(ℓ²(ℕ,ℝ) × (ℝ×ℝ)) →L[ℝ] ℓ²(ℕ,ℝ)` para eta admissível | Green causal + retorno afim; nenhum argumento angular, nenhuma saída no plano |

O par de bordo da TFVD contém valor e inclinação. Ter o tipo `ℝ×ℝ` não o
identifica com o estado radial/angular `RealPlaneState`. Seu retorno é
`eta^n(a+n slope)`, não uma ação angular. Não foi feita tal identificação.

`realCarryTfvdSynthesis_comp_analysis` prova exatamente `S_eta ∘ T_eta = I`
no espaço ESCALAR vertical. Não seleciona fases de câmeras, não identifica
o índice vertical com o raio horizontal e não produz um intertwiner de rotações.

A busca cobriu os arquivos Lean de Foundation/Geometry/Analysis, seus imports,
usos de `RealPlaneState`, trigonometria, rotações e análise/síntese. Os únicos
objetos angulares pertinentes são os acima. `FORMALIZATION_PLAN.md` registra
R3/R4 como não iniciadas e a lei de fase/globalização como aberta. Não há um
objeto preexistente `synthesizedPhase` ou equivalente tipado sobre o carrier R2.
Nenhuma definição com esse papel foi criada nesta auditoria.

## 2. Fatos anteriores preservados e reutilizados

Consultados nos módulos `RealQuadraticPlane`, `RealCriticalDepthState`,
`CenterLegForm`, `CenterLegCameraForm`, `AtlasEnergyPartition`,
`CenterLegAtlasForm`, `RealCarryL2`, `RealCarryTfvd` e `Analysis/Audit`:

- `rotateRealPlane_energy`, `rotateRealPlane_zero`, `rotateRealPlane_add`;
- `centerLegForm_eq_closed`, `centerLegForm_eq_factor`;
- `centerLegForm_energy_angle_independent`, `centerLegForm_energy_zero_iff`;
- `centerLegCameraEnergy_angle_independent`,
  `centerLegCameraEnergy_zero_iff_local_zero`, `centerLegCameraEnergy_zero_iff`;
- `centerLegAtlasEnergy_angle_independent`,
  `centerLegAtlasEnergy_zero_iff_local_zero`, `centerLegAtlasEnergy_common_zero_iff`.

Todos continuam com a semântica anterior; não foram reprovados ou modificados.
Também foram consultados `AGENTS.md`, `HUMAN_THEORY.md` (§§34–39),
`FORMALIZATION_PLAN.md`, `SOURCE_PROVENANCE.md`,
`R2_TFVD_GREEN_VALVE_ROUTE.md` e `R2_IMPLEMENTATION_AUDIT.md`.
Nenhum resultado de outro repositório foi importado.

A fatoração existente é

$$
D(q,\theta,v)=(q+q^{-1}-2)R_\theta v
=\frac{(q-1)^2}{q}R_\theta v\quad(q\ne0).
$$

Assim, a energia é `(q−1)^4/q² × E(v)` e independe do ângulo. O zero local
equivale a `q=1` sob `q>0` e `E(v)>0`. Na câmera/atlas de defeito comum,
bastam `q≠0` e energia inicial total positiva. Entrada nula ou resolução
vazia não selecionam `q`. Essas são condições anteriores, não novas hipóteses
substitutas da ponte procurada. Não se introduziu sigma.

## 3. Cinco teoremas novos, sem definições novas

Todos em `GeometryOfNumbers.Analysis`, no arquivo-canário:

| Nome | Enunciado/resposta |
| --- | --- |
| `rotateRealPlane_neg_comp` | `R_(-theta)(R_theta v)=v`, por composição das leis existentes |
| `rotateRealPlane_eq_zero_iff` | `R_theta v=0 ↔ v=0` |
| `centerLegForm_eq_rotate_zero` | `D(q,theta,v)=R_theta(D(q,0,v))`, usando a fatoração anterior |
| `centerLegForm_zero_iff_zero_angle` | `D(q,theta,v)=0 ↔ D(q,0,v)=0`, sem hipótese sobre q/v |
| `centerLegForm_independent_angles_not_common_rotation` | Dois canais permitidos com ângulos 0 e pi não admitem uma rotação comum de seus estados com ângulo zero |

Cadeia vetorial efetivamente provada:

```text
forma local preexistente
→ rotação do defeito em ângulo zero
→ rotação invertível
→ preservação exata do zero vetorial local
```

Cadeia energética já existente, apenas reutilizada:

```text
formas locais resolvidas
→ fator radial × energia inicial
→ independência de TODOS os ângulos locais
→ ausência de cancelamento da soma de energias
→ zero iff q=1 no defeito comum, sob as condições anteriores
```

Nenhuma cadeia partindo de uma fase pós-síntese foi provada.

## 4. Obstáculo angular certificado

Use dois canais ativos com o mesmo `q=2` e a mesma semente `v=(2,0)`.
Os vetores da configuração com ângulos ambos zero são `(1,0),(1,0)`.
Os ângulos independentes `0,pi` produzem `(1,0),(-1,0)`.
Uma mesma rotação aplicada a dois vetores iguais produz dois vetores iguais;
portanto nenhuma rotação comum transforma a primeira configuração na segunda.
O quinto theorem prova exatamente essa impossibilidade, sem definir uma
nova fase ou síntese. Os dados são admissíveis nos canais 1 e 2 da câmera.

Isso refuta a identificação universal das famílias angulares livres com
uma órbita diagonal da sua configuração em ângulo zero. Cada canal continua
individualmente na órbita da mesma ação real. A obstrução é a diferença dos
ângulos entre canais, não uma falha de ortogonalidade local.

As duas energias locais do exemplo continuam iguais a 1; o total é 2.
A energia de uma eventual SOMA VETORIAL seria zero, mas essa soma não é
o readout definido por `centerLegCameraEnergy`/`centerLegAtlasEnergy`.
O audit anterior já contém um contraexemplo a identificar esses observáveis.
Não foi criada uma scalarização nova nem atribuída essa leitura à síntese R2.

| Grau de liberdade/componente | Auditoria |
| --- | --- |
| Fases independentes por canal/base | PRESENTES nos parâmetros `theta r` / `theta b r`; não commonizadas |
| Quadraturas/sinais livres adicionais | Nenhum parâmetro independente além dos estados/ângulos já recebidos foi encontrado |
| Termos cruzados de fases relativas | AUSENTES nas energias definidas, que somam quadrados locais; uma soma vetorial criaria outro observável |
| Fontes novas após scalarização | Nenhum objeto pós-scalarização pertinente encontrado |
| Transporte angular do interior/bordo R2 | NÃO DEFINIDO; o carrier é escalar real, sem mapa ao carrier angular resolvido |

Após identificar os ângulos independentes, nenhuma commonização foi
postulada, nenhuma interface foi corrigida e nenhuma prova global foi tentada
usando o no-cancellation como hipótese.

## 5. Primeiro gap restante

**Fronteira exata:** saída de `realCarryTfvdSynthesis` em
`RealCarry.CarryVerticalL2`, em `Analysis/RealCarryTfvd.lean`, para um carrier
angular resolvido do tipo usado por `CenterLegCameraForm`/`CenterLegAtlasForm`.
Falta a construção com proveniência desse carrier e de sua evolução após a
síntese; em seguida, falta provar que a evolução é uma ação angular comum
ou obter seu intertwiner com a síntese. Não há um nome de theorem global
preexistente a preencher, porque esses objetos ainda não foram definidos.

Classificação do gap:

- [ ] Apenas uma prova Lean faltante entre objetos já construídos.
- [x] Interface/proveniência entre carriers distintos.
- [x] Definição pós-síntese ainda incompleta/ausente.
- [x] Obstrução matemática à identificação UNIVERSAL das famílias livres
  atuais com uma rotação comum, certificada pelo quinto theorem.

Essa última obstrução não prova que uma evolução futura, legitimamente
derivada, escolherá fases independentes; tampouco que só poderá escolher uma
fase comum. Essa escolha não está determinada nesta árvore.

## 6. Axiomas, validação e alterações

Cada um dos cinco nomes novos tem `#assert_analysis_axioms` e `#print axioms`
em `Analysis/Audit.lean`. A impressão individual de TODOS os cinco é
`[propext, Classical.choice, Quot.sound]`. Nenhum axioma adicional.

Validações: **TODAS PASSARAM**. Logs e `VALIDATION.json` em
`/home/thlinux/phase-canary-artifacts` no servidor; cópia local em
`/home/thlinux/Downloads/FORMALIZANDO/phase_canary_work`. A primeira compilação
isolada do novo módulo levou 3,2 s no Lean; a tabela inclui repetições com cache,
medidas de ponta a ponta via SSH.

| Verificação | Segundos | Exit code |
| --- | ---: | ---: |
| Build isolado do canário | 2,871 | 0 |
| Build Analysis | 3,990 | 0 |
| Build Audit | 3,427 | 0 |
| audit-foundation.sh | 9,301 | 0 |
| audit-geometry.sh | 12,636 | 0 |
| audit-analysis.sh | 19,470 | 0 |
| git diff --check | 0,309 | 0 |
| Busca de placeholders/trust escapes | 0,319 | 0 (nenhuma ocorrência) |
| Diff das camadas congeladas | 0,301 | 0 |

O patch paralelo do usuário manteve o mesmo SHA256 antes e depois:
`8e19cecb62de62c6cc2ea0f542caed234706bbb9fa7557a58a3cc93b24efa058`.
As referências main/origin/main continuam no checkpoint inicial.

Arquivos da árvore alterados nesta rodada, exclusivamente:

1. Novo: `GeometryOfNumbers/Analysis/SynthesizedPhaseCenterLegCanary.lean`.
2. Modificado: `GeometryOfNumbers/Analysis.lean` (import do canário).
3. Modificado: `GeometryOfNumbers/Analysis/Audit.lean` (dez comandos de audit).
4. Novo: `docs/SYNTHESIZED_PHASE_CENTER_LEG_CANARY.md` (este relatório).

Foundation, Geometry, definições R2 e teoremas anteriores permanecem intactos.
Os edits paralelos em `.gitignore` e `docs/HUMAN_THEORY.md` permanecem no
checkout original. Não houve commit, merge ou push nesta rodada.

**Conclusão semântica:** o defeito LOCAL apenas gira e não pode ganhar ou
perder seu zero. As energias resolvidas existentes não sofrem cancelamento,
mesmo com ângulos independentes. A identificação de uma fase GLOBAL
pós-síntese com uma única rotação real NÃO foi provada.
