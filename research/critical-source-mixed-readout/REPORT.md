# Orientação do pareamento nativo: cancelamento exato e primeira correção

**Resultado: PARTIAL.** Continuamos a investigação da PR
[#42](https://github.com/thiagomassensini/geometry-of-numbers/pull/42)
no pareamento entre o valor completado e o companheiro literal `−F′`.
A novidade concreta é uma expansão **da fonte completa**, com resto conservado,
para a segunda direção crítica par. Seu primeiro coeficiente de correção é
estritamente negativo por novas desigualdades verificadas nas caixas theta
originais. O balanço, entretanto, é eventualmente estritamente positivo.

Também identificamos uma contribuição não linear positiva nessa direção,
além do primeiro termo de Euler. Não foi demonstrada uma lei de sinal em
toda ordem, nem se construiu uma Gram positiva auxiliar.

## A — O que já estava demonstrado

Base exata: `3e267bffdc238c82b89577cb16190d2f54cefe05`, cabeça da PR #42.
Branch nova: `agent/critical-source-mixed-readout`, empilhada sobre #42.
`origin/main` consultada: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
As PRs #41 e #42 permanecem preservadas e sem merge automático.

O operador consultado continua em
`bfeb10fd2425400fa38139903d12bf0599f02e53`, no host `llm`.
Não alteramos seus arquivos, os pins ou os dois módulos de pesquisa não
rastreados do usuário.

Reutilizamos declarações atuais, não apenas relatórios:

| Declaração existente | Papel |
| --- | --- |
| `incident_synthesis_eq_source`, `returned_synthesis_eq_source` | Identidades vetoriais `I=C+iV`, `R=C−iV` na fonte original. |
| `storage_re_eq_source_cross` | O balanço é `4 Im ⟨V,C⟩`, com todos os cruzamentos. |
| `storage_one_eq_euler_boundary_add_remainder` | Separa o termo de Euler e o resto vetorial completo, sem afirmar seu sinal. |
| `storage_one_eq_odd_green_tower_and_remainder` | Torre de bordo assinada já existente, com resto exato. |
| `radialEulerPower_firstSurviving_boundary` | Primeiro cruzamento observável em setores de cancelamento; não é novo resultado desta branch. |
| `nativeSourceTransverseSlope_exact_remainder` | Taylor local do próprio `−F′/F` até grau sete, com resto analítico de ordem oito. |
| `material_theta_integral_input`, `mem_logMomentBox` | Inclusões dos integrais theta originais e sua propagação pela recorrência nativa. |
| `critical_balance_tendsto_of_isUnit` | Identifica o limite físico com `2σ`, exigindo apenas inversibilidade anterior. |

A decomposição de completion em `nativeDressedCompanion` e
`completionCompanion`, bem como sua orientação assinada, já existe em
`CompletedNativeChiralReturnCompletionSplit.lean`. Ela não foi substituída
por uma norma positiva. Aqui o companheiro utilizado é o completo `−F′`,
que conserva ambas as parcelas.

## B — O que foi demonstrado agora

### 1. Coordenadas da mesma fonte, antes do readout

Em [SourceCoordinates.lean](SourceCoordinates.lean), `jetStencil` é o mapa
original de diferenças finitas depois de explicitar seu fator de amplitude:

\[
 \beta_{k,r}(x)=\sum_a
 \frac{\operatorname{phase}(a)\,W(a,r)}{a!\,\delta_k^a}\,x_a,
 \qquad \delta_k=\frac{i}{k+1}.
\]

`nativeInput_factor` prova que a entrada física original é exatamente
`A(zₖ,ᵣ) βₖ,ᵣ`, com `A=E₊/(√2 F)`. Nos pontos regulares, os fatores de
valor cancelam algebricamente:

\[
 \frac{A(z)F(z)}{E_+(z)}=\frac1{\sqrt2}.
\]

Os teoremas `valueCoefficients_eq_stencil`, `sourceValue_eq_stencil` e
`sourceCompanion_eq_stencil` demonstram, nos vetores já sintetizados,

\[
 V_k=\frac1{\sqrt2}\,S_k\beta_k,\qquad
 C_k=\frac{i}{\sqrt2}\,S_k(\beta_k\,\ell_k),
 \quad \ell_k(r)=-i\frac{-F'(z_{k,r})}{F(z_{k,r})}.
\]

`Sₖ` é a **mesma** `radialIncidentSynthesis`, com sua métrica Cauchy
original. Assim `storage_eq_stencil_slope` fornece o readout exato

\[
 D_k=2\operatorname{Re}\langle S_k\beta_k,
                                  S_k(\beta_k\ell_k)\rangle.
\]

Isso não cria uma fonte sem amplitude: identifica as coordenadas da fonte
original, com os fatores já determinados por ela. A regularidade necessária
é fornecida eventualmente pelos teoremas preexistentes em toda família
finita. O índice radial `k` continua distinto da profundidade Carry.

[MixedCritical.lean](MixedCritical.lean) conserva também a polarização:

\[
 \langle C+iV,D+iW\rangle-\langle C-iV,D-iW\rangle
 =2i(\langle C,W\rangle-\langle V,D\rangle).
\]

Os dois cruzamentos ordenados complexos estão presentes.
`critical_mixed_tendsto` liga o pareamento original ao pivô, sob inversibilidade
anterior, sem lhe atribuir sinal.

### 2. Família de teste e direção crítica original

Em [SecondEvenReadout.lean](SecondEvenReadout.lean), tomamos as coordenadas
originais de quatro jets

\[
 x(a)=(a,0,-1,0),\quad a\in\mathbb R,
 \qquad K=k+1,\quad \tau=K^{-1}.
\]

`second_stencil_exact` prova, sem aproximação,

\[
 \beta_k=(a-K^2/2,\ K^2,\ -K^2/2,\ 0).
\]

A quarta coordenada é exatamente zero nessa direção específica. Não foi
removido um canal independente de uma fonte arbitrária.

`second_balance_three_slopes` reduz o pareamento completo a três valores da
**inclinação completa**, depois de computar todos os cruzamentos Cauchy.
Os coeficientes são os forçados pelo stencil, não ajustes a momentos.

Defina `bⱼ = nativeSourceOddBoundaryCoefficient j`, a derivada ímpar de
`−F′/F` dividida pelo fatorial. Sua identificação preexistente com a resposta
normalizada dá `bⱼ=2hⱼ`. A aplicação nova explicita esse fator em
`sourceCoefficient_eq_canonical`.

### 3. Expansão exata com resto da fonte conservado

Existe um resto analítico da fonte que fornece, eventualmente, para todo
`a` fixado:

\[
\begin{aligned}
 D_k(a)={}&B_0(a)+\tau^2 B_2(a)+\tau^4 B_4(a)
               -\tau^6 b_3a^2+\tau^3\mathcal R_a(\tau),\\
 B_0(a)={}&b_0a^2+2b_1a+b_2,\\
 B_2(a)={}&-b_1a^2-40b_2a-14b_3,\\
 B_4(a)={}&b_2a^2+462b_3a.
\end{aligned}
\]

`second_balance_exact_source_remainder` é uma igualdade do balanço
original, não uma substituição da fonte por seu polinômio. A fórmula explícita
de `normalizedSourceRemainder` retém as avaliações do mesmo resto analítico
nos três pontos radiais. [SecondEvenLimit.lean](SecondEvenLimit.lean) demonstra
sua continuidade e controla sua contribuição no limite, obtendo

\[
 K^2(D_k(a)-B_0(a))\longrightarrow B_2(a).
\]

Nenhum sinal de pivô foi usado nessa expansão ou no controle do resto.

### 4. Primeiro coeficiente de correção com sinal certificado

Para a segunda direção crítica par, **índice `n=1` do setor `s=0`**,

\[
 a_*=-\frac{h_1}{h_0},\qquad
 p=h_2-\frac{h_1^2}{h_0}.
\]

[CriticalOrientation.lean](CriticalOrientation.lean) prova
`second_critical_coordinates`: `x(a*)` é exatamente
`criticalCoordinates 0 1`. Também prova a igualdade de seu balanço com
`criticalBalance 0 1 k`. Não é apenas um vetor com a mesma norma ou o mesmo
observável escalar. A família física existe para todo `a` antes de escolher
a direção crítica; essa escolha usa `h₀,h₁`, sem usar o sinal de `h₂`
ou o coeficiente novo que se pretende investigar.

Temos `B₀(a*)=2p` e

\[
 A:=B_2(a_*)=
 -\frac{2h_1^3-80h_0h_1h_2+28h_0^2h_3}{h_0^2}.
\]

[IntegralOrientation.lean](IntegralOrientation.lean) certifica, das caixas
**já provadas para os integrais theta originais**,

\[
 \boxed{h_0h_2-2h_1^2>0},\qquad
 \boxed{2h_1^3-80h_0h_1h_2+28h_0^2h_3>0}.
\]

São `source_nonlinear_margin_pos` e `source_correction_numerator_pos`.
As verificações inteiras usam `decide +kernel`, não `native_decide`.
Nenhum valor decimal de checkpoint entra na prova.

Consequentemente, `second_correction_neg` demonstra **`A<0`** e
`second_critical_correction_tendsto` demonstra

\[
 \boxed{K^2(D_k-2p)\longrightarrow A<0.}
\]

O teorema `second_critical_between_zero_and_limit` conclui:

\[
 \boxed{0<D_k<2p\quad\text{eventualmente}.}
\]

O balanço positivo aproxima seu limite **por baixo**. Não foi provada
monotonicidade nem calculado um cutoff numérico.

### 5. Orientação positiva do resto não linear original

Em [EulerOrientation.lean](EulerOrientation.lean), `secondNonlinearReadout`
é literalmente o pareamento com
`radialCompletedRemainderSynthesis`, na métrica original. A contribuição de
Euler se simplifica exatamente, em cada ponto regular:

\[
 D_k(a)=b_0a^2+\texttt{secondNonlinearReadout}(a,k).
\]

Na direção crítica,

\[
 \texttt{secondNonlinearReadout}(a_*,k)
 \longrightarrow 2h_2-\frac{4h_1^2}{h_0}>0.
\]

`second_critical_nonlinear_eventually_pos` certifica seu sinal positivo na
cauda. A desigualdade de fonte que o fornece é **mais forte** que a simples
positividade do segundo pivô; foi demonstrada, não recebida como premissa.
A contribuição continua sendo um pareamento assinado, não uma norma definida
retroativamente para representar seu valor.

## C — O que foi refutado ou delimitado

Não surgiu um novo NO-GO da geometria. O sinal negativo de `A` é o sinal da
**correção ao limite**, enquanto o balanço completo é positivo. Confundi-los
produziria uma conclusão falsa sobre a fonte.

Também não se podem misturar as escalas: nessa direção as energias de cada
canal crescem como `K⁵`, o déficit relativo da PR #42 é de ordem `K⁻⁵`, e a
correção nova ao balanço finito é de ordem `K⁻²`. São quantidades diferentes.
O NO-GO para uma margem relativa fixa continua com o alcance específico de #42.

A positividade de normas, a injetividade das câmeras e o cone nulo dominante
não foram usados como provas do sinal dessas correções. Os sinais finitos
novos vêm de desigualdades adicionais verificadas na fonte theta.

## D — O que permanece aberto

Não demonstramos o sinal da orientação completa em toda ordem. A fórmula de
primeira correção foi provada na família de jets `0,2`, não em todas as
direções nem em toda a matriz de quatro fontes. O sinal de `A` não foi
universalizado a outras ordens.

O segundo pivô já tinha positividade certificada anteriormente. Aqui não o
anunciamos como um novo avanço de ordem: obtivemos a aproximação por um lado,
a fórmula de sua primeira correção com resto controlado e uma margem
separada para o canal não linear original.

Não há prova de que somente a norma geométrica crítica obrigue os sinais
all-order. Uma realização positiva infinita ou uma propriedade de passividade
que implicasse esses sinais ainda precisaria ser demonstrada com proveniência.

## E — Próximo passo mínimo

Generalizar a extração direta do pareamento misto para a direção crítica de
ordem `m`, usando `nativeInput_factor` e os pesos de diferenças finitas,
com o resto analítico de `F` conservado. A meta concreta é uma fórmula do
primeiro coeficiente de correção em termos dos coeficientes críticos e dos
jets da própria fonte, acompanhada de um limite para o resto.

Em paralelo, procurar uma desigualdade da fonte que controle o termo não
linear nessa direção. A condição "o pareamento é positivo" isolada é apenas
a obrigação antiga renomeada. O exemplo finito acima oferece duas
combinações explícitas que a fonte realmente satisfaz; investigar sua
estrutura é mais informativo que postular um sinal para todo resto.

Esta tarefa não altera a campanha do sétimo pivô da PR #32. Mantemos a
classificação **PARTIAL**, com avanços formais efetivos na orientação da fonte.

## Validação e reprodução

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/critical-source-mixed-readout/generate_audit.py
python3 research/critical-source-mixed-readout/validate.py
```

O ambiente é o mesmo Lean 4/Mathlib dos repositórios, sem atualização de pins.
Os caches predecessores explicitados em `compile_module.sh` devem estar
compilados nos commits registrados. A pesquisa não está implicitamente
incluída no build raiz: o script compila cada módulo novo com
`-DwarningAsError=true`.

O validador executa os builds focados do operador e de `geometry-of-numbers`,
o build raiz com `lake build --wfail`, as auditorias de Foundation, Geometry
e Analysis e a regressão H6/K6/doze fontes.

`Audit.lean` imprime os axiomas e percorre tipos **e corpos** transitivos.
Permite somente `propext`, `Classical.choice` e `Quot.sound`. Além disso,
rejeita dependências dos certificados de positividade dos blocos mistos,
H6/K6 e dos prefixos de quatro ordens listados no guard, para conferir que os
novos sinais vieram das inclusões theta, não desses resultados posteriores.
A auditoria não elimina hipóteses explícitas dos teoremas condicionais.

Os comandos, resultados, estado inicial, hashes e logs completos estão em
`evidence/`; os dois logs maiores são comprimidos sem perda (`gzip -dc`).
Somente espaços finais de linhas são removidos na preparação dos logs.
Nenhuma worktree nova foi criada e não há merge automático.

### Resultados registrados

- **PASS:** build focado do operador nativo com `--wfail`.
- **PASS:** build focado e build raiz de `geometry-of-numbers` com `--wfail`.
- **PASS:** auditorias Foundation, Geometry e Analysis.
- **PASS:** regressão H6/K6/doze fontes recompilada.
- **PASS:** oito módulos de pesquisa, incluindo `Audit.lean`, com warnings
  tratados como erros.
- **PASS:** 37 teoremas, 12 definições e uma abreviação novos; 53 raízes
  contando três declarações herdadas; fechamento de 6.186 constantes em tipos
  e corpos, somente com os axiomas fundacionais permitidos.
- **PASS:** guard contra as dependências de positividade finita listadas.
- **PASS:** alterações restritas à pasta da tarefa; pins, `main`, arquivos
  históricos e arquivos do usuário no operador preservados.

`evidence/checks.json` registra as 16 verificações sequenciais; o build nativo
adicional está em `evidence/native-source-build.log`.
`evidence/source-sha256.json` identifica os scripts e fontes Lean validados.
Esses são resultados locais de Lean no host de pesquisa; não são uma afirmação
sobre CI remoto.
