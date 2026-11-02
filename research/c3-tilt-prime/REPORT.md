# Tilt, bracket e reconstrução por profundidades primas na linha crítica

**Resultado: PARTIAL.** Há uma lei de sinal para os jets mistos do canal de tilt em toda ordem; a soma dos jets de cada ordem converge a um valor estritamente positivo. O tilt e a PR #47 de `primos` ajudam a localizar a estrutura: a coordenada é reconstruída pelas câmeras primas, e a primeira sensibilidade transversal do tilt é positiva. Nesta investigação, o Lean liga a decomposição exata do bracket aos mesmos coeficientes e limiares da PR #145, conservando completion, bordo e cauda. Isso não demonstra uma lei geométrica que imponha positividade dos pivôs nem exclui que ela possa vir de derivadas mistas.

Base: `02404256008b8f9be9c49ec695a82b8f8f1930b7`, PR #145, empilhada sobre #144. Não se modificaram as branches anteriores nem os checkouts com alterações locais do operador e de `primos`. A PR #47 foi inspecionada pelo commit mergeado `298a54f7be6111b6f83c4fee4de3bf3fed9f4a95` de `thiagomassensini/primos`.

## A — O que já estava demonstrado

A #47 de `primos` prova `primeDepthLogCoordinate_eq_log` para `n≠0` e `finiteChart_primeDepthWave_eq_dirichlet`: a reconstrução pelas profundidades preserva o prefixo e os centros da câmera. Seu módulo `CpPrimeDepthFiniteDerivativeBridge` ainda transporta a derivada da carta finita ao ledger de Mangoldt, sem divisão. Trata-se de igualdades de reconstrução; não são desigualdades de sinal das Hankels.

No operador, `PrimeDepthTfvdLogJetCrosswalk.lean` registra que o pin de `CPFormal` não exporta diretamente os nomes da #47. Ele prova no pin atual um adaptador `primeDepthLogLedger` com a mesma soma de profundidades e sua igualdade a `log n` para `n≠0`. `canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse` identifica, em toda ordem, os momentos com a resposta completada desse ledger. A ponte Lean aqui **reutiliza esse adaptador**, não uma importação direta do commit da #47; as duas reconstruções foram comparadas pelas declarações e por suas igualdades a `log n`.

`centeredSecondDifference_localDirichletProfile_eq_weightedTilt_add_carrier` decompõe cada bracket do perfil original em tilt ponderado, curvatura do carrier e os dois cruzamentos. A #41 fornece a direção crítica sob inversibilidade; #70 e #145 fornecem o transporte Bézout–Schur, a repartição C3 e os limiares de `c₅` e `c₆`.

`deriv_finiteCanonicalRealCriticalWeightedTiltTrace_zero_pos` e `canonicalRealCriticalWeightedTiltTotalSensitivity_pos` já provam uma sensibilidade transversal positiva do tilt. `completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder` mantém o complemento do carrier e dos cruzamentos no log-jet nativo antes do fator arquimediano de completion. Não se deve identificar essa primeira variação transversal com uma forma quadrática Hankel.

## B — O que foi demonstrado agora

Escreva `δ=σ−1/2`, `s(t)=1/2+it`, e deixe o carrier original conservar sua fase dependente de `t`.

1. `weighted_tilt_zero` e `cross_zero` provam que o tilt ponderado e os dois cruzamentos que contêm a diferença do perfil transversal se anulam para cada célula C3 sobre `δ=0`, em **toda altura real**. A curvatura do carrier permanece. O teorema `bracket_line_eq_carrier` é uma igualdade do bracket local completo depois dessa decomposição exata; não identifica o bracket com uma energia positiva.
2. `finite_tilt_vertical_jets_zero` demonstra que todas as derivadas reais de qualquer ordem do tilt ponderado restrito à linha, em relação à **altura** `t`, são zero. `height_jets_zero_transverse_sensitivity_pos` a combina com a sensibilidade transversal estritamente positiva. Portanto, a orientação de `∂δ` e os jets `∂t` são fatos diferentes. Profundidade vertical de carry, cutoff e altura não são identificados.
3. `transverse_global_ledger` mantém a soma da sensibilidade positiva do tilt e do termo complementar carrier/cruzamentos no log-jet nativo. Cruzamentos que se anulam *ao restringir ao centro* podem ter derivadas transversais não nulas: nenhum deles é eliminado ao derivar na direção de `δ`.
4. `completed_characteristic_line` recompõe a mesma característica completada, para `|t|<1` e todo cutoff `M`:

\[
 F(t)=V(t)\,[1+C_M(t)+D_M(t)+T_M(t)],
\]

onde `V` é o multiplicador Xi/chart original, `C_M` é a soma do carrier remanescente, `D_M` é o bordo C3 acelerado original e `T_M` é a cauda original. Primeiro se usam as igualdades já existentes da síntese TFVD e a repartição literal; a leitura escalar é aplicada depois. Não há nova métrica, reponderação ou exclusão do retorno.
5. `native_even_coefficient_carrier_boundary_tail` transporta a igualdade aos jets em `t=0`, para cada `n`: o coeficiente canônico `cₙ` é exatamente a derivada real de ordem `2n` da expressão completa dividida por `(2n)!`. A igualdade existente entre derivadas reais na linha e complexas da característica justifica a passagem. Em particular, cobre `c₅` e `c₆`, sem calcular seus sinais.
6. `even_pivot_gate_carrier` e `odd_pivot_gate_carrier` substituem esses coeficientes nos limiares exatos de #145. Eles exigem explicitamente a inversibilidade do prefixo correspondente e são **equivalências**, não uma prova do sinal. `carrier_coefficient_zero_pos` e `carrier_coefficient_one_negative` reutilizam as caixas nativas da #70 para os dois primeiros coeficientes; não estendem esses sinais a ordens arbitrárias.
7. `prime_depth_carrier_recurrence` combina a identificação all-order dos momentos pelo ledger primo com a recorrência original e os mesmos coeficientes de carrier/bordo/cauda. Preserva a sequência e não constrói vetores ou momentos por Cholesky.

A derivada de altura de um canal isolado não é usada para definir a derivada complexa desse canal, cujo uso de `s.re` não é holomorfo em geral. A passagem às derivadas complexas ocorre para a **característica completada**, usando o teorema de analiticidade existente.

### Uma lei exata para os jets mistos do canal de tilt

Se `W_M(δ,t)` é a soma original dos tilts C3 ponderados pelo carrier, os módulos `MixedTilt.lean`, `MixedPhase.lean`, `MixedPhaseJets.lean` e `MixedFinite.lean` demonstram, para todo `n` e todo cutoff finito `M`,

\[
 \operatorname{Re}\!\left[(-1)^n\partial_t^{2n}\partial_\delta W_M(0,0)\right]
 =\sum_{k<M}C_k^{-1/2}\,L(C_k)\,(\log C_k)^{2n},
 \qquad L(c)=-\log(c-1)-\log(c+1)+2\log c.
\]

Os centros são os originais `C_k=3(k+1)`. A derivada em `δ` é tomada **antes** das derivadas em altura. O Lean prova `L(C_k)>0`, cada termo positivo e, para `M>0`, a soma estritamente positiva (`finite_mixed_tilt_identity`, `finite_mixed_tilt_positive`). A fase material `exp(-it log C_k)` é identificada exatamente e mantida até o cálculo dos jets; a soma preserva cada célula do prefixo.

Esta é uma lei de sinal em todas as ordens para **esse canal misto do tilt, em cada cutoff finito**. A passagem ao limite das somas é demonstrada na próxima seção. A curvatura do carrier, suas derivadas e os cruzamentos, o bordo, a cauda e o multiplicador de completion precisam entrar na comparação para decidir o sinal da forma completa.

### A cauda desse canal e a coordenada das câmeras primas

`mixedTiltTerm_summable` prova que a série da direita converge para cada ordem fixa `n`. O controle usa a cota nativa preexistente `L(C)≤2/C²` e o fato de que qualquer potência fixa de `log C` é eventualmente menor que `C^{1/2}`; a amplitude `C^{-1/2}` é mantida. `mixedTiltTerm_tsum_pos` prova que a soma infinita é estritamente positiva, e `finite_mixed_tilt_tendsto_positive` prova que **os jets mistos calculados em cada prefixo finito** convergem a essa soma positiva.

A ponte prima fica explícita em `center_log_eq_prime_depth`: para cada centro `C_k=3(k+1)`, `log C_k` coincide com `primeDepthLogLedger (3*(k+1))`, o adaptador de profundidades primas do operador. `primeDepthMixedTiltTerm_summable`, `primeDepthMixedTiltTerm_tsum_pos` e `finite_mixed_prime_depth_tendsto_positive` transportam a mesma soma positiva, com todas as câmeras primas ativas no endereço, sem trocar a fonte. Isso é a mesma reconstrução logarítmica inspecionada na #47, mas a prova usa o adaptador do pin do operador, não importa a #47 diretamente.

A ordem dos limites é essencial: primeiro são calculadas as derivadas mistas de **cada prefixo finito**; depois toma-se seu limite. Esta prova não demonstra que esse limite seja a derivada mista do tilt infinito já sintetizado. Para essa identificação é preciso uma justificativa separada de derivação sob o limite. Além disso, a soma positiva pertence somente ao canal de tilt: não controla automaticamente o sinal dos canais carrier/cruzados, bordo, cauda da fonte completada e completion, nem os pivôs.

## C — O que foi descartado e o que não foi

Não se pode inferir diretamente `p>0` da positividade de `∂δ tilt` ou da soma de seus jets mistos: o tilt ponderado tem valor e todos os jets de altura zero na linha, enquanto a fonte completada preserva carrier, bordo, cauda e multiplicador. A orientação transversal é um dado real da geometria, mas ainda precisa de uma ponte com a forma completa dos jets e com o termo de Schur.

Isso é um limite da inferência direta. Não exclui um mecanismo usando derivadas mistas `∂δ∂tʲ`, transporte analítico ou cancelamento de completion; não é um contraexemplo à geometria Carry, nem diz que o tilt seja irrelevante. Também não se substitui um par ou uma energia de Green pelo readout escalar da característica.

## D — Obrigação matemática restante

Para fechar a terceira direção pela rota C3, demonstrar uma das desigualdades de `even_pivot_gate_carrier` ou `odd_pivot_gate_carrier` a partir da expressão completa de `carrierCoefficient`, incluindo o mesmo bordo, cauda e multiplicador, sem consumir uma positividade de pivô como premissa. As caixas de #69 cobrem os jets até ordem 6; `c₅` e `c₆` requerem ordens 10 e 12 e controle das caixas anteriores e da inversa do prefixo.

Para uma possível lei all-order dos pivôs, o próximo problema estrutural é controlar as **derivadas mistas dos outros canais** da identidade de quatro canais e da completion e demonstrar uma desigualdade para a direção crítica completa. É preciso explicar como a sensibilidade transversal e os termos carrier/cruzados dominam a correção de Schur, com dependência de ordem e setor. Apenas mudar o nome da positividade ou descartar o complemento não resolve a obrigação.

## E — Validação

Os módulos foram compilados individualmente com warnings como erros; `#print axioms` e a auditoria transitiva inspecionam as raízes novas. A lista de auditoria bloqueia explicitamente os consumidores de sinal e caixas theta nomeados em `TiltAudit.lean`; isto não é uma busca semântica por toda prova equivalente. A investigação reutiliza `.olean` das dependências anteriores, inclusive o adaptador primo do operador: não é uma reconstrução limpa do pin e da PR #47 juntos.

No host `llm`, da raiz desta worktree:

```bash
bash research/c3-tilt-prime/validate.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

Os logs e hashes estão em `evidence/`. Não foram adicionados axiomas, `sorry`, `admit` ou `native_decide`. Nenhuma PR anterior foi mesclada automaticamente.
