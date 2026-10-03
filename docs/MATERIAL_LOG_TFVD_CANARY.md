# Canário: órbita logarítmica material × TFVD vertical

## STATUS

**PASS — material log phase admits a real one-parameter lift and intertwines with lifted TFVD synthesis.**

PASS no carrier-canário finito material × vertical solicitado. Não identifica
uma fonte histórica com esse carrier, não fecha R3/R4 e não deriva uma nova
lei física de fase a partir da Foundation.

Base nova: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`.
Branch: `audit-material-log-tfvd`, worktree
`/home/thlinux/geometry-of-numbers-phase-canary` no servidor llm.
Os arquivos não commitados do canário anterior foram preservados.

## ÍNDICES — respostas à etapa A

1. **Material histórico:** `n : ℕ` em `NativeLogHilbert = ℓ²(ℕ,ℂ)`;
   `n` enumera o ponto positivo `n+1`. `nativeLogGenerator_basisVector_log`
   aplica `log(n+1)` à coordenada/base canônica n, não à profundidade.
2. **Vertical R2:** `k : ℕ` em `RealCarry.CarryVerticalL2 = ℓ²(ℕ,ℝ)`.
   Os shifts mudam k e o Green/trace/retorno/TFVD atuam nessa coordenada.
3. **Ambos no projeto novo antes desta rodada:** a torre DISCRETA já retém
   quantidade e profundidade em `emergentResidualTower b depth quantity`;
   `emergentResidualTower_value` reconstrói a quantidade. Porém não havia um
   carrier real de quadraturas materiais com uma fibra vertical ℓ² por material.
4. **Ponte existente:** SIM para quantidade↔torre/depth:
   `hasCarryDepthAtLeast_eq_scaled_tail` mantém quantidade, tail e depth;
   `primeResidualDepth_iff_le_factorization` representa os thresholds e
   `primeCarryVoice_eq_of_residual_thresholds` lê a voz logarítmica.
   NÃO há encoder dessas construções para o carrier ℓ² material/vertical da
   fase histórica. Esses resultados não identificam n com k e não o selecionam.
5. **R2 não esqueceu um label:** `realCarryTfvdAnalysis`/`Synthesis` nunca
   receberam material n. Seu par `ℝ×ℝ` é valor/inclinação do bordo; não são
   quadraturas. O lift retém DOIS pares de bordo, um por quadratura.

```text
n : Fin N  ─── frequência log(n.val+1) ─── U_t na fibra material n
    |
    └── (x_n, y_n) : CarryVerticalL2 × CarryVerticalL2
             |
             └── k : ℕ ─── TFVD vertical, componente a componente
```

Nenhuma identificação material=depth foi encontrada nos módulos auditados
do novo projeto, nem foi introduzida. Raio de câmera também não foi identificado
com k. No carrier novo os dois índices são argumentos separados; a fórmula
do ângulo usa SOMENTE `n.val`, nunca k.

## FONTES HISTÓRICAS — somente auditoria

carry-self-adjoint-operator: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
Sua dependência CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.

Existência e definições consultadas dos quatro fatos solicitados em
`CarrySelfAdjointOperator/NativeLogEvolution.lean`:

- `nativeLogGenerator_isSelfAdjoint`;
- `nativeLogGenerator_basisVector_log`;
- `nativeRealSpectralState_eq_logOrbit_zero`;
- `nativeFiniteRealSpectralState_eq_logEvolution_zero`.

O clock vem de `CpInfiniteRealSpectralGenerator.infiniteRealSpectralFrequency`:
`Real.log ((n+1:ℕ):ℝ)`. Sua `infiniteRealSpectralPhase` usa o sinal negativo
`exp(-i t log(n+1))`. `CpRealSpectralGenerator.finiteRealSpectralEvolution`
usa a mesma fase no cutoff. `CpNativeCarryLogPhaseOrbit` prova a fatoração
da semente e a igualdade entre fases finitas/infinitas. `CpRealSpectralOperator`
identifica o argumento material do estado como o vértice positivo n+1.

Referências para distinguir coordenadas:

- `PositionalDepthRefinement.positionalDepthRefinement_reconstructs` retém
  quantidade n e profundidade k em charts diferentes da mesma quantidade;
- `FinitePositionalObservableShift.no_positionalObservable_eq_depth` impede
  extrair depth arbitrário apenas de charts estabilizados de um número fixo;
- `C2FiberDepthLogTransport.c2FiberPoint_centered_log` registra
  `log(2^k m)=k log 2+log m` para centro/core; o log da perna tem correção
  distinta, registrada em `c2FiberPoint_log_increment_defect`;
- `C2OddCorePushforward` distingue core m, depth k e os pontos `2^k m ± 1`.

**Cuidado:** uma fibra C2 crescente MUDA a amostra material conforme k.
Nenhuma dessas fórmulas foi usada para definir uma fase vertical `log(k+1)`.
Nenhuma equivalência dessa fibra com o carrier-canário foi presumida.

Esta é auditoria de declarações históricas; não foi repetido um build de todo
o repositório histórico. Nenhum módulo histórico é importado no canário novo,
e nenhum resultado espectral/downstream é premissa de suas provas reais.
`SOURCE_SHA256.txt` nos artefatos registra os nove arquivos históricos consultados.

## REAL LOG ORBIT

`materialLogAngle t n := -(t * Real.log ((n+1:ℕ):ℝ))`.
`materialLogRotate` aplica a rotação real existente a esse ângulo.

Teoremas, todos em `GeometryOfNumbers.Analysis`:

| Grupo | Teoremas novos |
| --- | --- |
| Rotação material em R² | `materialLogRotate_zero`, `materialLogRotate_add`, `materialLogRotate_energy`, `materialLogRotate_neg_comp`, `materialLogRotate_eq_zero_iff` |
| Quadraturas reais em um módulo | `realQuadratureRotate_zero`, `realQuadratureRotate_add`, `realQuadratureRotate_neg_comp`, `realQuadratureRotate_eq_zero_iff`, `realQuadratureRotate_eq_rotateRealPlane` |
| Naturality ℝ-linear | `realQuadratureMap_rotate` |
| Órbita material | `materialLogPhase_zero`, `materialLogPhase_add`, `materialLogPhase_neg_comp`, `materialLogPhase_eq_zero_iff` |
| Lift da reconstrução | `materialTfvdSynthesis_comp_analysis` |
| Intertwining | `materialTfvdAnalysis_phase`, `materialTfvdSynthesis_phase`, `materialTfvdSynthesis_phase_zero_iff` |
| Órbita sintetizada | `materialTfvdSynthesized_logOrbit` |
| Avaliação/energia | `materialLogPhase_planeAt`, `materialLogPhase_planeEnergy`, `materialLogPhase_finiteEnergy` |
| Centro–pernas por coordenada | `materialLogPhase_centerLeg_orbit`, `materialLogPhase_centerLeg_zero_iff`, `materialTfvdSynthesized_centerLeg_zero_iff` |

São **26 theorems e 10 definições/aliases**, todos auditados. O auxiliar
`realQuadratureRotate` é a combinação linear real
`(cosθ • x − sinθ • y, sinθ • x + cosθ • y)`; sua especialização escalar
coincide com `rotateRealPlane`, por theorem. A lei de grupo é provada, não
posta como campo ou hipótese. Não se usa Euler complexo.

`materialLogPhase t X n` tem um único t global e o clock fixo de n.
Não recebe uma família `theta n`. Em particular, o material n=0 tem log 1=0
em TODA profundidade; isso é testado no Audit.

## TFVD LIFT E INTERTWINING — PASS

Carriers:

```lean
MaterialVerticalCarrier N :=
  Fin N → (CarryVerticalL2 × CarryVerticalL2)

MaterialVerticalAnalysisCarrier N :=
  Fin N → ((CarryVerticalL2 × (ℝ × ℝ)) ×
           (CarryVerticalL2 × (ℝ × ℝ)))
```

`materialTfvdAnalysis` aplica `(T x_n,T y_n)`; `materialTfvdSynthesis` aplica
`(S a_n,S b_n)`. Ambos deixam n fixo. O roundtrip usa unicamente
`realCarryTfvdSynthesis_comp_analysis`, com `0<eta<1` já requerido em R2.
A comutação da síntese vale para quaisquer dados Y, inclusive fora da imagem
da análise, sob `0≤eta<1`, domínio anterior do retorno R2.

O único argumento do intertwining é `realQuadratureMap_rotate`: um mapa
ℝ-linear transporta as duas combinações lineares com os mesmos coeficientes.
O interior e TODOS os dados de bordo entram nesse mapa. Não se omite trace,
não se descarta o retorno, não se mistura material labels.

Identidades provadas:

$$
U_0=I,\quad U_{t+s}=U_tU_s,\quad U_{-t}U_t=I,
$$
$$
S_{mat}T_{mat}=I,\quad T_{mat}U_t=U_tT_{mat},\quad
S_{mat}U_t=U_tS_{mat},
$$
$$
\boxed{S_{mat}(U_t(T_{mat}X))=U_tX.}
$$

Preservação de energia foi provada para cada `(n,k)` e para qualquer bloco
finito de coordenadas. Não se afirmou que a norma padrão do produto de dois
ℓ², que usa outra convenção, seja a energia quadrática somada.

## ZERO PRESERVATION — PROVADO no alcance tipado

`materialTfvdSynthesis_phase_zero_iff` prova `S(U_t Y)=0 ↔ S(Y)=0`.
Não requer injetividade de S: usa seu intertwining e a inversa de U_t.

O mapa `materialVerticalPlaneAt X n k := ((X n).1 k,(X n).2 k)` é a avaliação
coordenada canônica dos ℓ² existentes, realizada por `carryVerticalL2Eval k`.
Ele entrelaça U_t com `materialLogRotate t n.val` no plano. Portanto há uma
ponte TIPADA para aplicar o `centerLegForm` preexistente a essa coordenada.
Isso não transforma a profundidade k em raio horizontal.

O readout centro–pernas nessa avaliação satisfaz

$$
D_q(\operatorname{eval}_{n,k}(U_tX))
=R_{-t\log(n+1)}D_q(\operatorname{eval}_{n,k}X).
$$

Sua nulidade é preservada, também após a síntese de dados de análise evoluídos.
Nenhum `Defect` global foi inventado. O resultado é para a aplicação existente
de `centerLegForm q 0` a uma coordenada avaliada. Não identifica esse readout
com uma energia de câmera/atlas global. O critério anterior `q=1` continua
com suas condições anteriores de energia positiva; nenhuma foi removida.

## PRIMEIRO GAP

**Nenhum gap nos intertwining do carrier-canário.**

Para identificar esta construção com a fonte nativa do corpus, falta um
encoder com proveniência da fonte/torre residual para
`MaterialVerticalCarrier N`, preservando a amostra material n+1 e definindo
sua sequência vertical ℓ² e suas duas quadraturas. A torre discreta existente
não fornece esse encoder analítico. Uma fibra C2 crescente também não pode
substituí-lo por identificação de índices.

Assim, o PASS não afirma que o carrier histórico e o carrier-canário são iguais,
nem que a globalização R3/atlas esteja concluída. O canário anterior sobre
ângulos arbitrários permanece verdadeiro; ele não refuta esta órbita de um
parâmetro, cujos ângulos dependem de velocidades materiais diferentes.

## AXIOMS E VALIDAÇÃO

`#assert_analysis_axioms` e `#print axioms` cobrem todos os 36 nomes novos.
Cada impressão contém somente `[propext, Classical.choice, Quot.sound]`.
`AXIOMS.json` registra cada nome individualmente; os capstones são
`materialTfvdSynthesized_logOrbit`, `materialTfvdSynthesis_phase_zero_iff` e
`materialTfvdSynthesized_centerLeg_zero_iff`, com esse mesmo footprint.

Build isolado, Analysis/Audit, três scripts de auditoria, busca de placeholders,
diff-check e preservação das camadas congeladas **PASSARAM**, todos com
exit code 0, registrados em `VALIDATION.json` e logs. Artefatos locais:
`/home/thlinux/Downloads/FORMALIZANDO/material_log_canary_work`.
Artefatos no servidor: `/home/thlinux/material-log-tfvd-artifacts`.


| Validação final via SSH | Segundos | Exit code |
| --- | ---: | ---: |
| module-build | 3.353 | 0 |
| analysis-build | 3.524 | 0 |
| audit-build | 3.495 | 0 |
| foundation-audit | 9.217 | 0 |
| geometry-audit | 13.512 | 0 |
| analysis-audit | 20.135 | 0 |
| diff-check | 0.310 | 0 |
| placeholder-check | 0.303 | 0 |
| frozen-layers | 0.306 | 0 |

## ARQUIVOS E PRESERVAÇÃO

Alterações DESTA rodada:

- Novo `GeometryOfNumbers/Analysis/MaterialLogTfvdCanary.lean`.
- `GeometryOfNumbers/Analysis.lean`: import do novo canário.
- `GeometryOfNumbers/Analysis/Audit.lean`: guards, impressões e três exemplos.
- Novo `docs/MATERIAL_LOG_TFVD_CANARY.md` (este relatório).
- `docs/SOURCE_PROVENANCE.md`: fonte auditada do clock e limites do porte.

O canário Lean e relatório da rodada anterior permanecem não commitados,
com os cinco theorems anteriores intactos. Foundation, Geometry e TODOS os
módulos R2 permanecem intactos. O checkout main conserva os edits paralelos
em `.gitignore`/`HUMAN_THEORY.md`. Nenhum commit, merge ou push foi feito.

## SEMANTIC CONCLUSION

**SIM, no carrier-canário finito construído:** t determina uma única órbita
logarítmica real, e a análise/síntese levantada preserva separadamente material
n e vertical k. Cada fibra gira com sua própria frequência fixa; não existe
entrada de ângulos arbitrários na evolução. A síntese comuta com essa ação.

Essa é uma compatibilidade algébrica exata do lift de R2. A identificação com
uma fonte histórica completa continua dependendo do encoder especificado
acima. Não há conclusão espectral.
