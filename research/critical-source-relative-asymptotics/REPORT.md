# Fonte crítica nativa: cancelamento conjunto e escala do déficit relativo

**Classificação: PARTIAL.** A investigação continua a recomendação final da PR
[#41](https://github.com/thiagomassensini/geometry-of-numbers/pull/41).
A fonte completada original foi mantida. Demonstramos um limite **vetorial
conjunto**, sua versão polarizada, a impossibilidade de uma margem relativa
fixa e a escala exata do déficit que precisa ser controlado. No primeiro caso
par, obtivemos uma contração relativa decrescente a partir de `h₀ > 0`, já
provado pela fonte. Não demonstramos o sinal de todos os pivôs.

## A — O que já estava demonstrado

A base desta branch é `ee56930a2c30456cfbd214a29bb31b12d3977204`, cabeça da
PR #41, sobre `origin/main` em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
A nova branch é `agent/critical-source-relative-asymptotics`. A PR é empilhada
sobre #41; não foi pressuposta sua integração à `main`. Nenhuma PR anterior
foi alterada ou mesclada.

No repositório `carry-self-adjoint-operator`, em
`bfeb10fd2425400fa38139903d12bf0599f02e53`, reutilizamos:

| Declaração existente | Função nesta investigação |
| --- | --- |
| `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` | Identifica os dois vetores com a síntese incidente e o retorno originais. |
| `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` | Transporta o balanço completo para a energia de bordo canônica, com os cruzamentos. |
| `radialIncidentSynthesis_injective` | Impede tratar o vetor dominante não nulo como redundância. |
| `inner_completedNativeChiralCauchyFeature` | Mantém a métrica Cauchy original e fornece a calibração de ordem zero. |
| `hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw` | Fornece continuidade do quociente completado no centro, onde vale −1. |
| `canonicalCompletedNativeLogDerivativeMoment_zero_pos` | Descarrega o sinal no primeiro caso, sem hipótese Stieltjes. |

Da PR #41 usamos `sourceMomentSchur_critical_direction_of_isUnit` e
`native_inverseSchur_boundary_energy`: a identificação algébrica do residual
exige inversibilidade do bloco antigo, não seu sinal. A base polinomial
assinada e a existência de whitening positivo continuam sendo fatos distintos.

De `research/critical-source-return/CriticalSource.lean` reutilizamos as
**mesmas** `criticalCoordinates`, `criticalIncident`, `criticalReturned` e
`criticalBalance`. Não foram construídos novos estados a partir de uma
fatoração positiva dos momentos.

A PR #33 já havia refutado uma margem absoluta fixa sobre todas as ordens e
mostrado a insuficiência de seu orçamento absoluto de caudas. O NO-GO abaixo
é diferente: fixa uma ordem e uma direção e faz tender o índice radial.

## B — O que foi demonstrado agora

### 1. Objetos e índices preservados

Escrevemos `s ∈ Fin 2`, `n` para a dimensão do bloco anterior e
`m = 2n+s` para a maior ordem de jet da direção crítica. O índice `k` é o
índice da regularização radial existente; não é profundidade Carry, índice
material ou ordem da Hankel.

Sejam `Iₖ` e `Rₖ` os vetores incidente e retornado da fonte original nessa
direção. Sua métrica continua a do carrier
`CanonicalCompletedNativeChiralCauchyCarrier`. O passo é
`δₖ = i/(k+1)`, herdado de `canonicalCompletedC3RadialSecondStep`.
A amplitude é a original

\[
 A(z)=\frac{E_+(z)}{\sqrt2\,F(z)},\qquad
 A(0)=\frac{i}{\sqrt2}.
\]

`amp_zero` e `amp_zero_norm_sq` provam essa constante e `|A(0)|²=1/2`.
Não se ajustou a normalização. `F` e `E₊` são os objetos completados
preexistentes, com suas correções.

### 2. Limite dos dois vetores antes do readout

Defina a observação complexa `aₖ = δₖ^m/√(k+1)`. Provamos

\[
 a_k (I_k,R_k)\longrightarrow (w_m,-w_m),\qquad w_m\ne0.
\]

O vetor dominante tem fórmula explícita na síntese física existente:

\[
 w_m=\operatorname{radialIncidentSynthesis}_{0,\,2(n+1)}
 \left(r\mapsto \frac{A(0)}{m!}\,
       \operatorname{completedGreenForwardWeight}(m,r)\right).
\]

A fase da coordenada crítica mais alta cancela exatamente a fase do jet:
`criticalCoordinates_top_phase`. Os coeficientes inferiores não foram
apagados da fonte: desaparecem apenas neste limite dominante, e continuam
no balanço finito e no seu termo residual.

[SourceLeading.lean](SourceLeading.lean) demonstra a convergência dos coeficientes para qualquer
vetor de jets com maior coeficiente não nulo. [WholeSourceLimit.lean](WholeSourceLimit.lean)
transporta isso para os dois vetores físicos. [CriticalRelative.lean](CriticalRelative.lean)
especializa às coordenadas críticas canônicas:

- `critical_pair_exact` — igualdade dos dois vetores com a fonte original;
- `critical_whole_source_tendsto` — limite conjunto;
- `criticalLeadingState_ne` — não degenerescência do vetor dominante.

A multiplicação por `aₖ` é uma observação **depois** da síntese completa.
Não define outra fonte, métrica, operador ou sequência de momentos. No
quociente entre energias ela cancela exatamente.

O par limite é não nulo e tem forma quiral assinada nula. Portanto, seu
cancelamento energético não autoriza eliminá-lo como informação redundante.
Os dois canais permanecem presentes.

### 3. Cruzamentos polarizados

[PolarizedLimit.lean](PolarizedLimit.lean), teorema `critical_scaled_cross_tendsto_zero`, prova,
para quaisquer setores e ordens, o limite da **diferença dos dois pareamentos
complexos**, depois das respectivas observações vetoriais. Ele decorre do
limite conjunto: os pareamentos dominantes de `w` e de `−w` coincidem.
Isso conserva as duas quadraturas reais e os cruzamentos; não se infere a
identidade bilinear de uma comparação de diagonais.

Esse limite dominante nulo não diz que o pareamento canônico finito ou seu
limite sem a observação seja zero.

### 4. Crescimento e déficit relativo

Defina

\[
 g_k=(k+1)^{2m+1}=(k+1)^{4n+2s+1},\quad
 C_{s,n}=\|w_m\|^2>0,\quad
 \varepsilon_k=1-\frac{\|R_k\|^2}{\|I_k\|^2}.
\]

`observationScale_norm_sq` prova `|aₖ|²=1/gₖ`.
Sem hipótese de positividade de momento, provamos

\[
 \frac{\|I_k\|^2}{g_k}\to C_{s,n},\qquad
 \frac{\|R_k\|^2}{g_k}\to C_{s,n},\qquad
 \|I_k\|^2\to+\infty,
 \qquad\frac{\|R_k\|^2}{\|I_k\|^2}\to1.
\]

Os nomes são `critical_incident_growth`, `critical_returned_growth`,
`critical_incident_diverges` e `critical_energy_ratio_tendsto_one`.
O vetor incidente é eventualmente não nulo, de modo que o quociente tem a
interpretação usual na cauda.

Em [RelativeDeficit.lean](RelativeDeficit.lean),
`critical_boundary_of_isUnit` e `critical_balance_tendsto_of_isUnit`
retiram a hipótese de positividade do bloco anterior da identificação
física herdada. Para `σₛ,ₙ = sourceMomentSchur h s n`, sob **apenas inversibilidade do bloco
anterior**, o balanço completo original tende a `2σₛ,ₙ`. Segue

\[
 \boxed{g_k\varepsilon_k\longrightarrow
 L_{s,n}=\frac{2\sigma_{s,n}}{C_{s,n}}.}
\]

`critical_scaled_relative_deficit` é a fórmula, e
`critical_relative_corridor` fornece, para cada `η>0`, eventualmente,

\[
 \frac{L_{s,n}-\eta}{g_k}<\varepsilon_k<
 \frac{L_{s,n}+\eta}{g_k}.
\]

Não há cutoff numérico explícito nem uniformidade em `n`.
O novo pivô pode ter qualquer sinal nesta identidade. A equivalência
`critical_gap_coefficient_pos_iff` é apresentada como equivalência: ela
**não** demonstra o sinal do coeficiente.

### 5. Primeiro caso descarregado pela fonte

Em [InitialSource.lean](InitialSource.lean):

\[
 C_{0,0}=\tfrac14,\qquad
 (k+1)\varepsilon_k\to8h_0.
\]

São `first_leading_energy` e `first_scaled_relative_deficit`.
Usando o teorema original `h₀>0`, sem pressuposto de sinal de pivô, obtemos
`first_source_relative_contraction`:

\[
 \boxed{\|R_k\|^2\le
 \left(1-\frac{4h_0}{k+1}\right)\|I_k\|^2
 \quad\text{eventualmente}.}
\]

A existência de sinal positivo nessa ordem já era conhecida; a novidade é
sua realização como estimativa relativa na fonte original, com a taxa
forçada pelo crescimento dos canais. Não se anuncia um novo certificado de
positividade all-order.

## C — O que foi refutado

`critical_no_fixed_relative_contraction` prova, sem hipótese de sinal de
pivô, que para todo `ρ<1` é falsa a afirmação

\[
 \|R_k\|^2\le\rho\|I_k\|^2
 \quad\text{para todo }k\text{ suficientemente grande}.
\]

Isso já falha com `s,n` fixados. A razão tende a 1. A obstrução não depende
de aumentar o cutoff, da quantidade de algarismos ou de uma escolha nova de
vetor para o clock material.

O alcance é específico: exclui a **margem relativa fixa** aplicada aos dois
canais originais dessa síntese. Não exclui margens que tendem a zero, o sinal
positivo do balanço finito, outra identidade física legítima ou a
positividade dos momentos canônicos. O primeiro caso acima exemplifica uma
margem decrescente válida.

Também não se pode obter o sinal do limite finito comparando apenas as duas
energias dominantes positivas: elas têm o mesmo termo principal. O dado
canônico fica no cancelamento subdominante. Esse é o motivo concreto para
não escalarizar nem descartar os cruzamentos antes de completar a síntese.

## D — O que permanece aberto

Ainda não provamos, a partir de uma desigualdade independente da fonte,
`Lₛ,ₙ>0` em toda ordem. O sinal restante continua exatamente o de `σₛ,ₙ`;
a fórmula assintótica não o cria.

Nenhuma equivalência Stieltjes foi usada como prova incondicional de seus
lados. Nenhum vetor foi produzido por Cholesky dos momentos desejados.
Não se inferiu isometria da injetividade de câmeras, nem se projetou fora
do domínio físico. Não se construiu aqui a ponte C2 → Green completado
all-order: trabalhamos na síntese completada nativa já identificada.

As certificações finitas H6/K6 e de doze fontes continuam sendo resultados
finitos. Não demonstram, por si, a existência de uma Gram positiva infinita
coerente. A regressão pertinente foi recompilada.

## E — Próximo passo mínimo

A estimativa relativa seguinte deve respeitar a escala `gₖ⁻¹`. Procurar
`ρ<1` fixo encerraria uma rota agora refutada. O próximo trabalho útil é
controlar o **primeiro termo não cancelado do balanço completo**, a partir
explicitamente de `F`, `F′`, amplitude, retorno e seus restos polarizados.

Um teste concreto é obter um desenvolvimento com resto controlado dos dois
vetores até a ordem que sobrevive no balanço `‖Iₖ‖²−‖Rₖ‖²`, conservando
os termos mistos. Deve-se então demonstrar o sinal desse coeficiente por
uma propriedade independente da fonte. A positividade de
`lim gₖ εₖ`, isoladamente, seria apenas outra forma do pivô desejado;
introduzi-la como hipótese não resolveria a lacuna.

O menor dado que esta investigação acrescenta para esse trabalho é a taxa
forçada e o stencil físico dominante, não uma nova hipótese equivalente a
Stieltjes. As ordens finitas já certificadas servem de regressão. A campanha
do sétimo pivô da PR #32 permanece separada.

## Validação e reprodução

A validação é feita no host `llm`, sem alterar dependências:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/critical-source-relative-asymptotics/generate_audit.py
python3 research/critical-source-relative-asymptotics/validate.py
```

`compile_module.sh` usa o toolchain e o ambiente do checkout irmão
`carry-self-adjoint-operator`, com os caches de pesquisa predecessores
indicados explicitamente. São pré-requisitos os checkouts nos commits
registrados e seus módulos predecessores compilados. O validador recompila
os módulos nativos importados, a identificação crítica herdada e cada módulo
novo; não confia no build raiz para descobrir arquivos de pesquisa fora da
biblioteca.

Resultados e comandos completos ficam em `evidence/`. Os logs maiores
`root-build.log.gz` e `analysis-audit.log.gz` estão comprimidos sem perda;
use `gzip -dc` para lê-los. Apenas espaços no fim das linhas são removidos
na preparação dos logs para publicação. `generate_audit.py`
enumera todos os teoremas, definições e abreviações públicos novos.
`Audit.lean` executa `#print axioms` e percorre transitivamente **tipos e
corpos**, permitindo apenas `propext`, `Classical.choice` e `Quot.sound`.
As hipóteses matemáticas dos teoremas condicionais continuam visíveis nos
enunciados; ausência de axiomas novos não as descarrega.

São executados builds focados e raiz com `lake build --wfail`, compilação
explícita dos módulos com `-DwarningAsError=true`, auditorias de Foundation,
Geometry e Analysis e a regressão H6/K6/doze fontes. O validador também
verifica ausência de escapes de confiança, alterações históricas e mudanças
nos pins. Preserva os dois arquivos de pesquisa não rastreados do operador
com seus hashes originais. Não foi criada worktree nem feito merge automático.

### Resultado registrado

- **PASS:** build focado do operador nativo com `--wfail`.
- **PASS:** build focado e build raiz de `geometry-of-numbers` com `--wfail`.
- **PASS:** auditorias de Foundation, Geometry e Analysis.
- **PASS:** regressão de `research/sixth-odd-twelve-sources/Regression.lean`.
- **PASS:** sete módulos de pesquisa, incluindo `Audit.lean`, compilados
  explicitamente com warnings tratados como erros.
- **PASS:** 49 teoremas, 8 definições e 2 abreviações novos; 62 raízes
  auditadas contando três declarações herdadas, com fechamento de 6.010
  constantes em tipos e corpos. Apenas os três axiomas fundacionais
  permitidos apareceram.
- **PASS:** alterações restritas à pasta desta tarefa; `main`, pins e arquivos
  do usuário no operador preservados.

A rodada completa está em `evidence/checks.json` e
`evidence/native-source-build.log`. Após enfraquecer o bloco anterior de
positivo definido para invertível, recompilamos as duas dependências de
pesquisa e todos os módulos novos; a rodada final está em
`evidence/checks-research.json`. A biblioteca, os pins e os módulos históricos
não mudaram entre essas rodadas. `evidence/source-sha256.json` identifica os
scripts e fontes Lean da versão final. Esses são resultados locais de Lean;
não são uma declaração sobre CI remoto.
