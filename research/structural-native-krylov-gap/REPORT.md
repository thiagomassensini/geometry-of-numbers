# Ataque estrutural à positividade Hankel canônica — fonte e clock de Krylov

## Resultado

**NO-GO específico da realização canônica pela família Krylov de paridade do clock material original.** A obstrução é nova em relação aos testes de massa e incidência: vale para **qualquer vetor fonte**, mesmo se sua massa central já tiver sido calibrada, e sobrevive ao transporte isométrico Green/Parseval. Falha já nas diagonais que representam `h₁` e `h₂`, antes de qualquer argumento de cauda ou independência all-order.

**PARTIAL na identificação da fonte:** foi provada explicitamente, em toda ordem, a igualdade entre `BaseTwoCompletion.baseTwoCanonicalMomentSequence` e `canonicalCompletedNativeLogDerivativeMoment`, derivada da identidade do response completado e da unicidade da recorrência. Isso não é uma representação Gram.

**A positividade canônica all-order permanece OPEN.** Não há `PASS_ALL_ORDER`, nem foi encontrado um mecanismo positivo novo para a síntese quiral completa. Os NO-GOs desta rodada não excluem outra realização legítima dos mesmos momentos, derivada dos bordos/retorno/completion originais. O encerramento desta rota não encerra a pesquisa nem demonstra falha da geometria original; a obstrução atinge a identificação dos momentos com as energias das potências deste clock e seus transportes isométricos.

## Base e escopo

Repositório editado: `geometry-of-numbers`, base `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, `origin/main` verificado antes de iniciar e antes de publicar. Branch: `agent/structural-native-krylov-gap`. Nenhum worktree criado. Sem merge automático.

A referência do pedido a “PR #32” corresponde atualmente à **issue #32**, “Sétimo Schur par theta e lei geral de coordenadas/resíduo”, com **PR #34 aberto**. Não foi alterado, incorporado ou duplicado. O PR #35 da auditoria anterior também permanece separado. Não se recalculou o sétimo pivô.

Consultas sem alterações de fontes:

| Repositório | Estado consultado e papel |
| --- | --- |
| carry-self-adjoint-operator | `main` em `045369f...`; checkout `bfeb10f...` da auditoria anterior. Response nativo, recorrência, theta e identidades Gamma existentes; dois arquivos de usuário não rastreados preservados |
| quantity-representation-foundations | `main` `66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`, lido pela API GitHub; conservação/escape de informação não são uma lei de sinal Hankel |
| carry-geometry | checkout `1f85b8c...`, fonte `QuadraticAmplitude.lean`; rigidez da amplitude quadrática, sem inferir Gram canônica |
| momentos | `a54f267365d5d8c965376734b17b10ae89ed3f74`; somente três valores `canonical_h` existentes para diagnóstico, sem recalcular momentos |

Dependências, pins, fontes, pesos, métricas, dressing, amplitudes e operadores não foram alterados. Novos resultados em módulos separados, com apenas registro de imports/auditoria nos pontos de entrada. Nenhum vetor foi escolhido a partir dos momentos, de Cholesky, de zeros ou de alturas.

## A. Qual objeto físico existente produz os momentos?

O objeto efetivo é a fonte completada real `baseTwoCompletedBoundaryHilbertState t`, denotada `Y(t)`, no carrier existente com **seed, gradiente material e retorno global**. O readout `ℓ = baseTwoCompletedBoundaryHilbertReadout` e o dressing canônico `D(t)` dão

\[
S(t)=\ell(Y(t)),\qquad F(t)=D(t)S(t)=\texttt{baseTwoCanonicalResponse}(t).
\]

`carryMaterialDressedCompanion` constrói o companheiro da mesma fonte no domínio do clock de bordo existente. Seu readout é exatamente `−F′(t)`, por `carryMaterialDressedCompanion_source_readout`. Depois da síntese e do dressing, o readout normalizado é

\[
Q(t)=-\frac{F'(t)}{2F(t)}.
\]

`carryMaterialNormalizedResponse_connection` retém a contribuição do clocked return e a conexão do dressing:

\[
Q(t)=\frac{i\,R_L(t)}{2S(t)}-\frac{D'(t)}{2D(t)},\qquad S(t)\ne0.
\]

Esses são teoremas **já existentes**, conferidos nas declarações atuais. O quociente é não linear na fonte. Não é automaticamente um produto interno `⟨v,L^rv⟩`. O clock de bordo transportado também não é simétrico na métrica produto original, por `completedBoundaryTransportedClock_not_standard_symmetric`; a hipótese do teorema genérico de Krylov não está disponível para esse clock de bordo.

O novo `CarryStructuralKrylov.canonical_phi_eq_native` usa `CarryMaterialCanonicalComparison.material_response`, que identifica o response inteiro em cada parâmetro real, e o transporte real/complexo de suas derivadas. Prova

\[
\texttt{baseTwoCanonicalPhi}(n)=\texttt{completedNativeRealEvenCharacteristicCoefficient}(n).
\]

`canonical_moments_eq_native` então usa a **recorrência division-free já demonstrada**, seu coeficiente constante não nulo e unicidade. Não recebe um Gram, um sinal Hankel, um readout postulado ou uma hipótese de primeira coluna. Não cria outra sequência: identifica as duas definições originais a partir da mesma fonte completada.

## B. Qual igualdade falta para uma Gram canônica?

Para um operador simétrico e vetor previamente construídos, `firstColumn_of_symmetric_implies_hankelGram` continua correto. A escolha fisicamente compatível com a paridade dos jets temporais do clock material usa a sequência auxiliar **já existente**

\[
\mu_r(v)=\langle v,L^rv\rangle_\mathbb R,\qquad q_n(v)=\mu_{2n}(v),
\]

onde `L = finiteMaterialClock` é o multiplicador original `log(j+1)`. Não se identifica `L` com um operador de alturas. A família de `finiteClockParityKrylov` é

\[
J_{2i}=L^{2i}v,\qquad J_{2i+1}=-iL^{2i+1}v.
\]

Os produtos pares, ímpares e mistos dessa família são provados pelo arquivo original `FiniteClockKrylovHankel.lean`. A identidade de primeira coluna que permitiria usar o teorema genérico para essa família é `h_n = μ_{2n}(v)`. **Essa igualdade é impossível para todo vetor material finito**, como demonstrado nesta rodada. Não há uma obrigação residual legítima de simplesmente prová-la para essa construção.

Para a fonte completada efetiva `Y,D,Q`, continua faltando uma família física de jets com igualdade bilinear ao kernel canônico, incluindo retorno, completion, Gamma e todos os cruzamentos. O readout escalar completo já está identificado. Uma representação vetorial positiva desses coeficientes ainda não está estabelecida. Não se introduziu uma estrutura que receba essa igualdade como campo e depois a anuncie como prova.

## C. Identidade nova e obstrução concreta

### Ruler geométrico independente dos momentos

As frequências originais são `λ_n=log(n+1)`. A frequência `n=0` é zero. Para toda outra coordenada, `λ_n ≥ log 2 > 1/2`, usando o bound formal de `log 2` de Mathlib. Logo, coordenada a coordenada,

\[
\frac14|\lambda_n v_n|^2\le |\lambda_n^2 v_n|^2.
\]

Somando **depois** de considerar a fonte inteira, obtém-se, para qualquer vetor finito,

\[
\boxed{\quad\|L^2v\|^2\ge\tfrac14\|Lv\|^2.\quad}
\]

`finite_clock_energy_gap` prova essa desigualdade. A simetria e a identidade Krylov existentes dão `finite_even_first_column_gap`:

\[
\mu_4(v)\ge\tfrac14\mu_2(v).
\]

A frequência zero pode modificar a massa `μ₀`; ela não modifica essa restrição. Por isso ajustar apenas a massa da fonte não remove o problema. Nenhuma hipótese `‖v‖=1`, incidência ortogonal ou coercividade de Hankel foi usada.

### Os fatores originais de Taylor também foram testados

Não se apagou o fatorial para esconder uma incompatibilidade. Os jets temporais normalizados **originais** satisfazem, pelos crosswalks existentes,

\[
j_1=-iLv,\qquad j_2=-\tfrac12L^2v.
\]

O novo `finite_normalized_jet_energy_gap` conserva o `2!` e demonstra

\[
\boxed{\quad\|j_2\|^2\ge\tfrac1{16}\|j_1\|^2.\quad}
\]

Trocar somente fases de módulo um não muda nenhuma dessas diagonais. Também não se introduziu um fator de escala temporal/frequencial para ajustar o teste.

### A fonte canônica viola ambos os rulers

As caixas theta originais já certificadas em `OddSourceBoxes.mem_compactMomentBox`, nas ordens **1 e 2 somente**, provam no kernel:

\[
h_2<h_1/16<h_1/4.
\]

As duas desigualdades de comparação são provadas separadamente a partir das caixas existentes, sem quadratura nova e sem hipótese de positividade all-order. Nomes: `native_two_lt_one_quarter`, `canonical_two_lt_one_quarter`, `canonical_two_lt_one_sixteenth`.

O diagnóstico separado, com `Fraction` dos decimais armazenados do checkpoint, dá `h₂/h₁ ≈ 0.00387850013647`. Seu CSV tem SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc8e1833`. Esse diagnóstico **não entra em nenhuma prova Lean**. Os intervalos usados na prova vêm dos integrais theta com as caudas já certificadas, e não desse CSV.

### Origem e escopo das constantes

O `1/4` do limite de energia vem da lacuna das frequências não nulas, `log 2 > 1/2`. Nos jets temporais normalizados, o fator `1/2!` em `j₂` divide sua energia por quatro, produzindo o limite `1/16`. Separadamente, a desigualdade canônica **relativa** `h₂ < h₁/16` vem das caixas theta, sem usar esse argumento do clock.

A cota histórica **absoluta** `h₀ < 1/16`, já provada por `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` em `CompletedC3KernelMetricCalibration.lean`, trata de outro momento e de outra comparação. A repetição da constante não identifica essas duas obstruções nem demonstra uma relação histórica entre suas derivações.

Consequências novas, para qualquer cutoff e fonte:

- `finite_clock_not_canonical_firstColumn`: rejeita a primeira coluna `h_r = μ_(2r)`.
- `finite_clock_not_canonical_logDerivative_recurrence`: a recorrência canônica não pode ser satisfeita por esses momentos auxiliares, pois unicidade forçaria a primeira coluna impossível.
- `finite_clock_not_canonical_parityGram`: rejeita a Gram de paridade canônica para essa família.
- `finite_clock_not_H6_K6`: a realização falha nas entradas exatas dos blocos 6×6. São necessárias apenas a diagonal even `(1,1)=h₂` e a diagonal odd `(0,0)=h₁`.
- `finite_normalized_jets_not_canonical_diagonals`: mantém os fatoriais originais e rejeita também a atribuição das duas diagonais aos jets normalizados.

### Clock infinito e transportes

`infinite_clock_energy_gap` prova a mesma desigualdade no domínio maximal do operador ℓ² original, com **exatamente** `v ∈ Dom L` e `Lv ∈ Dom L`. Não se aplica `L⁴` fora de seu domínio, nem se presume regularidade all-order.

`infinite_clock_isometric_energy_gap`, `green_clock_energy_gap` e `parseval_clock_energy_gap` conservam a desigualdade sob os transportes existentes. `infinite_clock_not_canonical_diagonals` exclui as duas energias canônicas no clock infinito já com esses dois domínios. Provar regularidade adicional não resolveria essa incompatibilidade.

O resultado para Parseval utiliza sua isometria demonstrada. **Não se aplica à análise Green bruta `T` como se `T*T=I`**: ali o defeito do frame permanece. Não se afirmou que esse defeito ou o residual Gamma tenham sinal favorável.

### Regressões finitas e coerência

`regression_H6_K6` transporta os certificados originais H6/K6 para o nome local da mesma sequência, usando a igualdade de momentos recém-provada. Não escolhe vetores com esses blocos.

`regression_twelve_nested` reutiliza a família física já certificada de doze fontes e conserva **dois argumentos independentes e todos os prefixos** na mesma escolha física. Seu carrier é o Cauchy/retorno original, com a recomposição de `fullSourceJet`; não é o vetor do clock material que foi excluído.

Não se extrapola essa família de doze para uma família infinita coerente. A incompatibilidade do candidato já ocorre no teste H2/K1, portanto não foi necessário recalcular H6/K6, o sétimo pivô ou milhares de momentos.

## D. O que está provado e o que não está

**Kernel novo:** igualdade all-order das duas sequências originais pela fonte; rulers finito e infinito do clock; seus transportes Green/Parseval; incompatibilidade com a recorrência, primeira coluna e diagonais canônicas; regressões H6/K6 e doze fontes. São 22 teoremas públicos novos, todos com `#print axioms` e guard transitivo de tipos e corpos, permitindo apenas `propext`, `Classical.choice`, `Quot.sound`.

**Fatos anteriores reutilizados:** simetria/Krylov do clock finito, fonte completada e companheiro, recorrência e caixas theta, positividade H6/K6, família física finita aninhada. Não foram anunciados como novos sinais all-order.

**Teste numérico finito:** leitura dos três primeiros `canonical_h` existentes, sem recalcular a fonte; registrado separadamente em `evidence/preflight.json`.

**OPEN:** realização Gram positiva dos jets da síntese completada; PSD canônica em toda ordem; independência para obter PD all-order; controle relativo de Gamma/retorno em toda direção e ordem. Não foi encontrado contraexemplo aos momentos canônicos.

A identidade existente

\[
\operatorname{storage.re}=2\|\Gamma(c)\|^2-2\operatorname{Im}(\operatorname{rawGammaWronskianBalance}(c,c))
\]

conserva as correções completas. Nem positividade do primeiro quadrado nem Parseval determina o sinal da diferença. Receber como hipótese a dominância quiral estrita all-order ou o kernel positivo desejado apenas recolocaria a obrigação como premissa. Não foi usado esse caminho circular. O orçamento absoluto de cauda do PR #33 foi consultado e não foi repetido como se fornecesse controle relativo.

## E. Próximo passo matemático mais curto

Encerrar a tentativa de identificação literal da primeira coluna com os momentos quadráticos do **mesmo clock material**. Ela agora está refutada sem depender da escolha da fonte, e não precisa de mais precisão ou regularidade.

A frente que permanece legítima usa os objetos já construídos `Y`, seu companheiro, o retorno Cauchy e as correções de completion. O primeiro trabalho útil seria derivar uma identidade de energia para o **quociente completado** que explique como o termo de conexão e os termos de retorno alteram o ruler do clock. A identidade deve ser vetorial/polarizada antes do readout, com Gamma e cruzamentos presentes. Então confrontar suas diagonais e primeira coluna com as caixas e a família física de doze fontes existentes.

Não basta impor a mesma recorrência como hipótese, declarar um novo operador ajustado, reescalar `log n`, inverter frequências para fazê-las caber nos momentos, ou fabricar estados via H6/K6. Se a proposta continuar sendo apenas um transporte isométrico das potências do clock original, os teoremas desta rodada já a excluem. Se incluir o readout de bordo/completion efetivo, a igualdade e seu sinal ainda precisam ser demonstrados da fonte; esta rodada não os encontrou.

## Validação e reprodução

Arquivos novos de biblioteca: `MaterialClockKrylovGap.lean` e sua auditoria. Pesquisa: `CanonicalClockGap.lean`, `Regression.lean`, `Audit.lean`. Inventário de raízes em `public-roots.json`; hashes de fontes novas e reutilizadas em `source-manifest.json`.

`validate.py` executa os builds focados `lake build --wfail`, a compilação explícita dos três módulos de pesquisa com `-DwarningAsError=true`, o build de raiz e os scripts Foundation/Geometry/Analysis. Os módulos de pesquisa reutilizam o ambiente cruzado **já existente**, por `compile_module.sh`, sem acrescentar dependências ou pins. Não se recompilou toda a campanha theta: seus certificados existentes foram importados.

`check_sources.py` confere o registro de todos os novos teoremas, os pontos permitidos de alteração, preservação de módulos históricos/pins e dos arquivos de usuário do operador. Logs, comandos, saídas e SHA256 em `evidence/validation.json`; resumo final em `VALIDATION.md`.

A publicação é por commit/PR da branch identificada, **sem merge**, conforme solicitado. Os SHAs e a URL finais constam do arquivo de entrega local `DELIVERY.json`.
