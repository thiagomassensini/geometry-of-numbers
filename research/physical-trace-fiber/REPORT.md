# Fibra física do traço e kernel canônico completado

**Resultado: PARTIAL.** A passagem do estado físico ao traço foi explicitada como uma decomposição ortogonal exata, na métrica original. Uma componente invisível ao traço é comprovadamente não nula na própria fonte central e persiste no limite do cutoff. A funcional simplética completada recupera o kernel canônico em dois argumentos, com todos os fatores originais. Nenhuma dessas identidades transforma essa funcional em uma Gram positiva.

Repositório de entrega: `geometry-of-numbers`. Branch: `agent/physical-trace-fiber`, criada independentemente a partir de `origin/main`, commit `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Não depende das branches das PRs #41–45 e não as modifica. Fontes nativas inspecionadas e compiladas em `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. O estado e os hashes das dependências estão em `evidence/preflight.json`. Não há alteração de pins, fonte, amplitudes, pesos ou métrica. Sem merge automático.

## A — O que já estava demonstrado

A cadeia escalar tem proveniência geométrica exata. `projectiveValveMass_canonicalCpLogBlock_eq_mul` transporta a soma das curvaturas nativas ao produto das massas formais. `canonicalC3BracketTfvdMoment_eq_canonical` identifica os momentos TFVD/Wronskianos com os canônicos em toda ordem. `canonicalCompletedNativeMoment_eq_primeDepthMaterialResponse` fornece sua genealogia material por profundidades primas. Estas identidades não são representações de Gram.

A reconstrução `DiscreteProjective.eq_iff_boundary_and_stateMass_eq` mantém valor inicial, inclinação e massa. A não injetividade de `stateMass` não deve ser atribuída à válvula sobre curvaturas, que é injetiva.

A resposta `DividedVectorResponse.sourceVector` conserva quatro rótulos estruturais: cabeça, cauda, completion e correção da carta. `polarizedResponse_readout_local` recupera o kernel dividido nativo com dois argumentos. A definição de seu carrier usa `CanonicalCompletedC3FullWronskianOperatorCarrier`, que já é posterior à projeção de traço. Quatro rótulos conservados não tornam essa projeção injetiva no carrier físico anterior.

O objeto anterior existe: `CanonicalCompletedC3AllCutoffOnePointHilbert`. Ele retém três vetores Naimark — direto, refletido e refletido com quarto de volta — e quatro coordenadas escalares separadas. `canonicalCompletedC3AllCutoffOnePointState_tendsto_completed` prova convergência vetorial ao estado completado `canonicalCompletedC3CompletedOnePointState`.

A projeção existente é

`canonicalCompletedC3OnePointCompletedTraceProjection`.

Ela é real-linear e retorna o par companheiro/valor depois de somar cabeça e cauda. O código que produz `sourceVector` usa essa projeção antes de construir o readout dos quatro setores. Isso localiza uma redução real de coordenadas; não demonstra perda de informação independente na família física admissível.

A representação theta permanece uma identidade analítica do mesmo objeto. Não foi desfeita nem usada para construir outro conjunto de momentos nesta investigação.

## B — O que foi demonstrado agora

Todos os nomes novos estão no namespace `CarryTraceFiber`, em três módulos de pesquisa. São 46 teoremas públicos e dez definições/abreviações. O lema privado auxiliar também é verificado pelo kernel e pela auditoria transitiva.

### B.1 — Pareamento físico antes da projeção

Para um estado `x` do carrier EXISTENTE, escrevemos

\[
H_x=(i\ell_{H,x},v_{H,x}),\qquad
T_x=(i\ell_{T,x},v_{T,x}),\qquad
P x=H_x+T_x,\qquad D x=H_x-T_x.
\]

`P` é exatamente a projeção original. `D` é apenas a diferença entre coordenadas já presentes. Se `B(x,y)` é a soma dos três pareamentos Naimark, então `physical_inner_fiber` prova, para quaisquer duas entradas independentes,

\[
\boxed{\langle x,y\rangle_{\mathbb R}
=B(x,y)+\tfrac12\langle Px,Py\rangle_{\mathbb R}
+\tfrac12\langle Dx,Dy\rangle_{\mathbb R}.}
\]

Não são somente normas diagonais. `physical_eq_iff` prova que os três vetores Naimark, `P x` e `D x` determinam exatamente `x`. `head_reconstruction` e `tail_reconstruction` recuperam as duas pernas por soma e diferença.

O coeficiente `1/2` é forçado pela identidade de soma/diferença de duas pernas. Não é uma normalização escolhida para ajustar `h0`.

### B.2 — Fibra ortogonal sem mudar a fonte

`balancedLift t` coloca metades iguais do traço nas duas pernas, com os três vetores Naimark nulos. É uma seção AMBIENTE de comparação, não uma nova fonte física. Não reivindicamos que pertença ao domínio de um clock nem que satisfaça as relações que caracterizam os estados admissíveis.

Os teoremas `projection_balancedLift`, `balancedLift_inner` e `balancedLift_minimum` provam que essa seção é determinada pela projeção e pela métrica ambiente existente. Definimos a componente de comparação

\[
I_x=x-\operatorname{balancedLift}(Px).
\]

`projection_invisible`, `invisible_orthogonal`, `physical_reconstruct` e `physical_inner_visible_invisible` dão

\[
P I_x=0,\qquad
x=\operatorname{balancedLift}(Px)+I_x,
\]

\[
\boxed{\langle x,y\rangle_{\mathbb R}
=\tfrac12\langle Px,Py\rangle_{\mathbb R}
+\langle I_x,I_y\rangle_{\mathbb R}.}
\]

A componente `I_x` é conservada integralmente na identidade. Seu quadrado da norma é exatamente a soma das energias Naimark mais metade da energia de `D x`, por `invisible_norm_exact`. `trace_energy_preserved_iff` identifica a condição precisa de igualdade energética: `I_x=0`.

`finite_synthesis_pairing` e `finite_synthesis_energy_defect` aplicam as identidades SOMENTE DEPOIS de sintetizar duas famílias finitas completas, com coeficientes reais independentes. Os vetores continuam com suas quadraturas internas; não se apagam os cruzamentos ordenados.

### B.3 — Aplicação à própria fonte completada

Se `X_z` é `canonicalCompletedC3CompletedOnePointState z hz`, então sua cauda escalar completada é zero, mas

\[
D X_z=P X_z.
\]

Logo `native_pairing_exact` prova

\[
\langle X_z,X_w\rangle_{\mathbb R}
=B(X_z,X_w)+\langle PX_z,PX_w\rangle_{\mathbb R}.
\]

Isto NÃO diz que todos esses canais sejam fisicamente independentes: há relações entre eles. É a decomposição da métrica do carrier original, sem quociente adicional.

`native_center_trace_ne_zero` usa o valor nativo central e o fator da carta não nulos, sem positividade de Hankel. Daí:

\[
\boxed{\|I_{X_0}\|^2>0.}
\]

Isso é `native_center_invisible_energy_positive`. O estado central real da fonte não coincide com a seção ambiente de energia mínima (`native_center_not_minimum_energy_lift`).

`native_invisible_tendsto` e `native_invisible_pairing_tendsto` transportam os limites VETORIAIS e polarizados dessa componente. `native_center_invisible_energy_eventually` fornece uma margem eventual estrita: a energia ao cutoff `M` fica acima de metade da energia limite positiva. `M` é cutoff do carrier; não é a profundidade vertical nem o índice radial das PRs #42–45.

### B.4 — Readout e kernel canônico nos mesmos objetos

`completed_readout_trace` identifica o readout Wronskiano original com o pareamento do traço mediante sua rotação simplética existente. `completed_readout_invisible_left/right` prova que ele não vê `I_x`, inclusive em cruzamentos com qualquer outra entrada.

Na fonte central há, portanto, uma componente não nula no radical dessa forma puxada para o carrier físico. Isso não é apenas isotropia diagonal e não é o radical da métrica Hilbert positiva. O teorema exato é `native_center_invisible_boundary_radical`.

A completação e a correção de carta continuam no bloco arquimediano original. `normalized_functional_state_from_physical` abre sua definição, mostrando a projeção de `X_z` e esse bloco sem substituir nenhum dos dois.

Se `F` é a característica original, `Q=-F'/(2F)` e

\[
K_Q(z,w)=\operatorname{dslope}Q(\bar z,w),
\]

então `physical_functional_native_kernel` prova

\[
\boxed{\Omega(Z_z,Z_w)
=2\overline{F(z)}F(w)(w-\bar z)K_Q(z,w).}
\]

`Z_z` é o estado funcional normalizado EXISTENTE; `Omega` é sua funcional simplética EXISTENTE. Hipóteses exatas: os dois parâmetros estão no strip nativo, `F(z)` e `F(w)` não se anulam, e `w≠conj(z)`. Não há `PosDef`, `PosSemidef`, independência linear ou hipótese de Gram.

`native_kernel_from_physical_functional` dá a divisão pelos fatores comprovadamente não nulos. A diagonal é tratada separadamente por `native_kernel_center_diagonal`: seu valor é `h0`, usando a continuação derivativa de `dslope`, não o quociente totalizado `0/0`.

Estas duas últimas identidades compõem resultados existentes no nível do kernel; não reivindicamos uma descoberta de novos momentos ou uma prova nova de sua positividade.

## C — O que foi refutado, e o alcance exato

`not_physical_norm_factors_through_trace` prova que a norma quadrática do carrier físico inteiro não pode ser uma função somente de seu traço. O testemunho é a componente central `I_X0`, com traço zero e norma estritamente positiva.

Isso refuta a identificação da norma ambiente inteira com uma leitura apenas do traço PARA TODOS OS VETORES desse carrier. Não refuta a existência de uma representação positiva para uma família nativa distinta, nem prova não injetividade de `P` restrita à órbita canônica. Também não demonstra que `I_X0` seja uma direção física livre, separável das demais pelas relações Carry.

A substituição do estado canônico pela seção de energia mínima já falha como igualdade vetorial no centro. Preservar o readout não autoriza essa substituição da fonte.

O contraexemplo anterior `c3RawProjectiveValveShiftResidual_eq_neg_six` continua específico da realização C3 bruta. Não foi convertido em obstrução contra a síntese completada.

## D — O que permanece aberto e certificação

Não demonstramos que `Omega`, dividida pelos fatores da fonte e pela separação, seja um kernel positivo. Nem a injetividade da codificação enriquecida nem a positividade da métrica ambiente fornecem esse sinal automaticamente.

A conclusão kernel-checked desta rodada é uma decomposição sem perda das coordenadas AMBIENTES, sua especialização não trivial à fonte original e a identificação exata do readout nativo. Não há experimento numérico nem conjectura convertida em premissa.

A auditoria enumera 56 declarações públicas e percorre 6.273 constantes transitivas de tipos e corpos. Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos. Um guard rejeita os certificados de sinal finito explicitamente nomeados no auditor, inclusive a positividade central dos momentos. Esse guard nomeado não substitui a inspeção semântica das hipóteses.

Os comandos, resultados e hashes estão em `evidence/checks.json`, `evidence/kernel-Audit.log` e `evidence/source-sha256.json`. A validação concluiu **14 checks com código zero**. Inclui os módulos nativos importados com `lake build --wfail`, todos os módulos novos com warnings como erros, build focado e raiz, auditorias Foundation/Geometry/Analysis, regressão H6/K6 e doze fontes, e preservação dos arquivos históricos e dos dois arquivos nativos não rastreados do usuário.

Reprodução no host `llm`:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/physical-trace-fiber/validate.py
```

Não foram adicionados axiomas matemáticos, placeholders ou alterações de dependências. A branch de entrega parte da main indicada, enquanto o script de compilação usa o checkout nativo explicitamente registrado. Não afirma que uma instalação remota arbitrária contenha automaticamente esse mesmo checkout/cache.

## E — Próximo passo mínimo

A igualdade do readout com o kernel não deve ser listada novamente como a lacuna: ela está explícita, em duas entradas, com completion e carta.

O primeiro ponto ainda aberto é o transporte POSITIVO dessa funcional na família física correta. Agora é possível formular um teste mais restrito: para o transporte nativo candidato, calcular sua ação tanto na parte `balancedLift(Px)` quanto em `I_x`, antes de tomar jets ou normas. Isso deve determinar quais direções da fibra são dependências físicas legítimas e quais contribuições entram no balanço com o retorno. Não basta definir um transporte que descarte `I_x`, pois seu desaparecimento energético já foi refutado na fonte central.

O teste mínimo deve apresentar a imagem vetorial dessas duas parcelas para o mesmo transporte, seus dois cruzamentos ordenados e a identidade resultante para `Omega/(2 conj(Fz) Fw (w-conj(z)))`. Uma eventual forma complementar positiva já existente só pode ser aplicada depois de demonstrada essa identificação de domínio e pareamentos. Declarar a igualdade com uma Gram como hipótese seria apenas repetir o problema.

Se esse transporte não for construído, o estado correto continua **PARTIAL**, com NO-GO somente para a substituição ambiente pelo traço/seção mínima. Não há positividade all-order nem impossibilidade geral da geometria.
