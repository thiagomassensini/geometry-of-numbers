# Fonte ponderada histórica: gate de proveniência material/vertical

## STATUS

**SEMANTIC_DIAGONAL_GAP — the historical weighted source identifies
material/sample and vertical coordinates without a theorem deriving that
identification.**

Classificação da leitura diagonal: **DIAGONAL_ONLY_REPRESENTATION**.

A fonte histórica é uma sequência ponderada unidimensional bem definida.
Não ficou demonstrado que seu eixo de amostragem é a profundidade posicional
intrínseca de suas quantidades materiais. A identificação universal com essa
profundidade é refutada pelos dois certificados Lean desta rodada.
Isso não é uma prova de inexistência de qualquer encoder possível.

O gate foi concluído antes de qualquer definição nova. Não foi criado um
objeto X(n,k), encoder, decode, fonte bidimensional ou hipótese de transporte.
A tabela completa está em [WEIGHTED_SOURCE_GATE_ZERO.md](WEIGHTED_SOURCE_GATE_ZERO.md).

## Checkpoints e escopo

Rodada: 2026-10-02. Trabalho exclusivamente downstream de R2, sem commit,
merge ou push.

| Repositório | Checkout/SHA consultado |
| --- | --- |
| geometry-of-numbers | 93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f |
| carry-self-adjoint-operator | cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa |
| primos | 8c4b7fdf65a49d1d0febe8193d56e2cfb2191260 |
| CPFormal fixado no carry | 65d50f6db1208708e109982ba97e1d51d3039956 |

Worktree no servidor llm:
/home/thlinux/geometry-of-numbers-phase-canary.
Branch: audit-weighted-source-diagonal, derivada da cópia de trabalho do
canário material. Todas as alterações anteriores foram preservadas.

O arquivo CpNativeCarryWeightedSpectralState.lean é idêntico nos dois
snapshots de CPFormal auditados; SHA256:
ede53efc04e972b04d80178e23ad41b6fc552b2e68f8e15b4dd7a1b542ab24bc.
O manifesto SOURCE_MANIFEST.json e as cópias de referência nos artefatos
registram os demais conteúdos consultados.

## HISTORICAL INDEX AUDIT

| Objeto | Papel do índice | Classificação |
| --- | --- | --- |
| realSpectralState t n | Sample do ponto material positivo n+1 | DEFINITIONAL |
| q^n na fonte ponderada | Expoente do mesmo sample/slot n | DEFINITIONAL |
| Interpretar esse n como profundidade posicional de n+1 | Não há theorem de identificação recuperado | DOCUMENTED-ONLY |
| CarryVerticalL2 no projeto novo | Slot vertical k de shifts, bracket, Green e trace | DEFINITIONAL |
| positionalDepth b N | Máximo expoente de divisibilidade, para b>1 e N>0 | DERIVED |
| C2 fiber depth k | Escala do centro 2^k m; profundidade intrínseca quando o core é ímpar | DERIVED |
| C2 core m | Core canônico ímpar para os centros alinhados; parâmetro livre na fórmula de fibra genérica | DERIVED para a seleção canônica |
| materialLogPhase outer index | Material Fin N, relógio log(n.val+1); independente do slot vertical k | DEFINITIONAL |

**NO_THEOREM_IDENTIFIES_MATERIAL_INDEX_WITH_POSITIONAL_DEPTH**

Essa é uma conclusão da busca nos snapshots e interfaces auditados, não um
metateorema Lean sobre a ausência de declarações.

No primos, CpNativeCarryWeightedSpectralState.lean define um estado
CarryVerticalL2 histórico sobre ℂ, com coordenada exatamente:

\[
x_{q,t}(n)=(q:\mathbb C)^n\,\psi_t(n).
\]

nativeCarryWeightedRealSpectralState_apply prova essa igualdade por rfl.
O n de ψ é o sample de n+1, como mostram CpRealSpectralOperator,
CpReflectedEndpoint e a origem do relógio em NativeLogEvolution.
Nenhum cálculo de profundidade ocorre nessa definição.
primeCarryWeightedRealSpectralState apenas especializa a razão de amplitude
a uma base pelo menos 2; sua igualdade de coordenadas também é rfl.
Isso determina q, mas não transforma o expoente n em depth(n+1).

NativeLogEvolution contém literalmente nativeLogGenerator_isSelfAdjoint,
nativeLogGenerator_basisVector_log,
nativeRealSpectralState_eq_logOrbit_zero e
nativeFiniteRealSpectralState_eq_logEvolution_zero. Sua existência foi
confirmada somente para genealogia do relógio; nenhum desses resultados
é importado ou usado como premissa dos certificados novos.

### Certificados negativos locais

HistoricalWeightedSourceIndexAudit.lean reutiliza somente o crosswalk local
primeResidualDepth_iff_le_factorization:

~~~lean
sampleTwo_materialThree_binaryDepth_iff (k : ℕ) :
  Geometry.HasCarryDepthAtLeast 2 (2 + 1) k ↔ k = 0

materialSampleIndex_not_intrinsicBinaryDepth :
  ¬ ∀ n : ℕ, Geometry.HasCarryDepthAtLeast 2 (n + 1) n
~~~

O sample 2 aponta para 3, cuja profundidade binária intrínseca é zero.
Essa afirmação trata dos resíduos iniciais nulos/depth intrínseco.
Ela não proíbe escolher uma janela de coordenadas posicionais de tamanho 2
para representar 3, nem confunde profundidade de uma perna C2 com
profundidade de seu centro adjacente.

## POSITIONAL DECOMPOSITION

Há construções canônicas suficientes para decompor quantidades discretas:

- No projeto novo, emergentResidualTower b depth N preserva resíduos e tail.
  emergentResidualTower_value reconstrói N; residualTower_unique e
  residualTower_eq_canonical dão unicidade. emergentResidualTower_expansion
  registra prefix + tail * b^depth. depth é uma janela explícita.
- HasCarryDepthAtLeast e hasCarryDepthAtLeast_iff_dvd_pow distinguem uma
  janela arbitrária de um prefixo residual nulo. O crosswalk primo local
  liga esse critério à fatorização.
- No primos, positionalDecompositionAtDepth_existsUnique usa o quotient e
  residue canônicos, N = r + b^k m, 0≤r<b^k. positionalDepth_spec e
  positionalDepth_factorization_existsUnique isolam a profundidade máxima
  e o core não divisível por b, sob b>1,N>0.
- No C2 histórico, c2AlignedIndexDepth j =
  positionalDepth 2 (j+1) + 2 e c2AlignedIndexCore j =
  (j+1)/2^positionalDepth 2 (j+1). c2AlignedIndex_factorization,
  c2AlignedIndexCore_pos, c2AlignedIndexCore_odd e
  c2AlignedCenter_padicDepth_eq_fiberDepth
  provam a reconstrução do centro 4(j+1) = 2^k m.
- C2Adjacent fornece oddLegEquivIncidence e seus round-trips: para uma
  perna ímpar N≥3, o centro adjacente e a incidência preservam qual perna
  foi escolhida. C2Depth prova effectiveDepth_eq_centerDepth.

Não foi encontrada uma bijeção irrestrita de todos os samples positivos
com triplas C2 arbitrárias. O domínio de centros/pernas e suas condições
de incidência precisam ser preservados.

Um diagnóstico direto das fórmulas recuperadas: o centro 4 tem k=2 e m=1;
as pernas 3 e 5 têm samples 2 e 4 na fonte antiga. Seu depth efetivo C2 é
o mesmo, mas os expoentes históricos são 2 e 4. Essa observação aritmética
não foi adicionada como terceiro theorem Lean nesta rodada.

Reindexar uma quantidade central N=2^k m preservando literalmente a fonte
antiga tornaria seu dressing q^(2^k m-1), pois o sample é N-1. Não o
transformaria em q^k. A amplitude crítica local realCriticalDepthSeed b k
é indexada pela profundidade derivada; não existe um theorem que permita
substituir o dressing antigo por essa amplitude na fonte.

## LOG FACTORIZATION

**Provada historicamente; não portadas novas identidades R² nesta rodada.**

Arquivos PrimeDepthTfvdLogJetCrosswalk e C2FiberDepthLogTransport:

- primeDepthLogLedger_eq_log;
- c2Fiber_centeredLog_eq_depth_add_primeCoreLedger;
- c2Fiber_center_log_eq_depth_add_primeCoreLedger;
- c2AlignedCenter_log_eq_currentDepth_add_primeCoreLedger.

Para o centro e sob as hipóteses de positividade presentes nos enunciados:

\[
\log(2^k m)=k\log 2+\operatorname{primeDepthLogLedger}(m).
\]

Isso decompõe o relógio de uma quantidade material. Não identifica sample
com k. Para as pernas 2^k m+ε, o arquivo C2FiberDepthLogTransport preserva
a correção log(1+ε/(2^k m)), via c2FiberPoint_log_center_defect e
c2FiberPoint_log_increment_defect; ela não pode ser removida usando o centro.

Uma órbita obtida reindexando quantidades por core/depth terá ângulo
-t(k log 2 + log m) no centro. Para um core fixo, esse ângulo muda com k.
Portanto o resultado anterior do canário, cujo ângulo fica constante na
vertical de cada material label, não se aplica automaticamente a essa
reindexação. Nenhum FAIL da fonte completa é inferido daqui.

## ENCODER

**Type: não definido. Definition origin: ponte ausente.
Injective/roundtrip: não aplicável.**

Os round-trips posicionais e de incidência acima são legítimos.
Eles não constituem ainda um encoder da fonte ponderada para
Fin N → (CarryVerticalL2 × CarryVerticalL2) do projeto novo.
Faltam uma identificação da fonte, o tratamento de amplitude, o readout
e o bordo no carrier tipado. Não foi usada escolha clássica para fabricar
essa seleção.

## HISTORICAL SOURCE CROSSWALK

**OPEN. Leitura universal sample = profundidade intrínseca: REFUTED.**

PrimeDepthTfvdLogJetCrosswalk substitui log(N) por uma soma de profundidades
primas no mesmo estado amostrado. Os theorems
finitePrimeDepthGeneratedLogSlopePrefixState_eq_nativeLogSlope e
finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix
mantêm os slots de sample. Não reindexam o estado por depth.

MultibaseCameraLogTfvdChannelTransport define
CameraResolvedCarryVertical := ℕ →₀ CarryVerticalL2.
Seu índice externo é a câmera/primo p e o interno armazena samples de
log-slope. finiteCameraResolvedLogSlopePrefixState_synthesis_eq_primeDepth
soma as câmeras para recuperar o prefixo anterior.
cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes e
cameraChannelSynthesis_tfvdReconstruction_commutes são naturalidade de
mapas lineares com soma de canais; não são uma identificação da fonte
ponderada com o carrier material×depth.

## LOG ORBIT CROSSWALK / TFVD TRANSPORT

**Ponte da fonte histórica: não provada; transporte bloqueado no gate zero.**

O PASS anterior de MaterialLogTfvdCanary permanece disponível:
materialTfvdAnalysis_phase, materialTfvdSynthesis_phase,
materialTfvdSynthesis_comp_analysis e materialTfvdSynthesized_logOrbit.
Ele atua sobre um carrier já separado e prova a comutação para relógio
fixo por material label. Não contém encodeHistoricalSource.
Não foram refeitas essas provas nem alterada a reconstrução R2.

## BOUNDARY PROVENANCE

Sob 0<q<1, o theorem histórico
carryWeightedVerticalTrace_nativeSpectralState fornece:

\[
\operatorname{Tr}_q x_{q,t}
  =(1,\psi_t(1)-1).
\]

O theorem carryWeightedVerticalCenteredBracket_nativeSpectralState_succ
fornece:

\[
(B_qx_{q,t})_{n+1}
 =q^{n+1}\bigl(\psi_t(n+2)-2\psi_t(n+1)+\psi_t(n)\bigr).
\]

São identidades algébricas corretas da sequência histórica.
O trace usa dois samples materiais distintos; o bracket usa três.
No canário separado, trace e bracket atuam em slots verticais de UMA
fibra material e seu relógio é constante nesses slots.
Nenhuma ponte preservando esse bordo foi demonstrada.
Não foi declarado PASS de bulk ou de boundary.

## CENTER-LEG COMPOSITION

**Blocked; intentionally not attempted after gate zero.**
Não há encoder equivariante para compor com o no-cancellation local.
Nenhuma conclusão de zero-confinement para a fonte histórica foi produzida.

## FIRST GAP

O primeiro elo ausente já está em nativeCarryWeightedRealSpectralState:
justificar geometricamente o papel vertical do expoente sample n, ou
fornecer uma reconstrução da fonte por coordenadas posicionais que preserve
material, depth, core/incidência, amplitude e bordo sem usar essa igualdade.
O arquivo histórico não computa essa decomposição.

## AXIOMS

Os dois nomes públicos novos estão em Analysis/Audit.lean com
#assert_analysis_axioms e #print axioms:

| Theorem | Footprint impresso |
| --- | --- |
| sampleTwo_materialThree_binaryDepth_iff | propext, Classical.choice, Quot.sound |
| materialSampleIndex_not_intrinsicBinaryDepth | propext, Classical.choice, Quot.sound |

Nenhum axioma, sorry, admit ou unsafe novo. Nenhuma construção nova usa
Classical.choose. As fontes históricas não são imports dos certificados.

## Build e preservação

Executados no servidor llm com o toolchain do worktree:

| Verificação | Resultado | Segundos da passagem final |
| --- | --- | --- |
| módulo HistoricalWeightedSourceIndexAudit | PASS | 2.251 |
| lake build GeometryOfNumbers.Analysis | PASS | 3.645 |
| lake build GeometryOfNumbers.Analysis.Audit | PASS | 3.582 |
| audit-foundation.sh | PASS | 9.469 |
| audit-geometry.sh | PASS | 13.331 |
| audit-analysis.sh | PASS | 22.120 |
| git diff --check | PASS | 0.311 |
| busca de placeholders/trust escapes | PASS | 0.324 |
| diff dos módulos Foundation/Geometry e R2 vertical | sem alterações | 0.317 |

VALIDATION.json/logs preservam comandos, status e tempos. A passagem final
repetiu as verificações depois de escrever a documentação; ajustes editoriais
posteriores receberam novamente git diff --check.

Os hunks paralelos de .gitignore e docs/HUMAN_THEORY.md do main foram
preservados (hash do patch registrado em REPOSITORY_STATE.json).
Main, HEAD e origin/main continuam no checkpoint inicial; o trabalho
permanece não commitado na branch de canário.

## FILES

Novos nesta rodada:

- GeometryOfNumbers/Analysis/HistoricalWeightedSourceIndexAudit.lean;
- docs/WEIGHTED_SOURCE_GATE_ZERO.md;
- docs/HISTORICAL_WEIGHTED_SOURCE_DIAGONAL_AUDIT.md.

Modificados nesta rodada, preservando os hunks dos canários anteriores:

- GeometryOfNumbers/Analysis.lean — import do certificado;
- GeometryOfNumbers/Analysis/Audit.lean — guards/prints dos dois theorems;
- docs/SOURCE_PROVENANCE.md — registro desta auditoria.

R2, Foundation, Geometry e os arquivos dos canários anteriores permaneceram
sem alterações desta rodada. Artefatos reproduzíveis:
/home/thlinux/Downloads/FORMALIZANDO/weighted_source_audit_work e
/home/thlinux/weighted-source-diagonal-artifacts no servidor.

## SEMANTIC CONCLUSION

q^n ψ_t(n) é uma representação unidimensional legítima, mas **não ficou
provado que represente a geometria material×vertical separada**.
Seu expoente e sua fase usam o mesmo sample; promovê-lo a profundidade
posicional exigiria uma identificação que o corpus auditado não fornece
e cuja versão intrínseca universal é falsa.

A diagonal abstrata é apenas uma representação possível de qualquer
sequência, sem proveniência geométrica recuperada aqui.
O próximo elo necessário é um encoder/fonte derivado da geometria e um
theorem independente identificando sua relação com a fonte histórica,
preservando também o bordo. Nenhum substituto foi definido nesta rodada.
