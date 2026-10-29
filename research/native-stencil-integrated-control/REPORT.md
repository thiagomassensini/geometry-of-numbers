# Stencils ímpares em toda ordem e integração do erro radial

**Classificação geral: PARTIAL.** A identidade combinatória de `Lambda` e seu transporte ao par nativo completado foram demonstrados em Lean para quaisquer duas ordens ímpares. A cota de erro também foi integrada entre passos da grade para combinações finitas arbitrárias dos jets originais. A integrabilidade da cota foi demonstrada para as combinações finitas de jets; ainda não foi provado um orçamento somável e dominado pelo saldo crítico em todas as ordens, nem positividade Hankel all-order.

## A — O que já estava demonstrado

A base é `9425c30b975b6a7135c111a7f5e05a0c85b5826c`, cabeça da PR #132, sobre `agent/native-jet-variation-budget`. A #132 prova uma cota pontual da diferença entre a derivada do pareamento completado e a variação do prefixo, incluindo as duas velocidades e o resto completo da resposta. O estado, métricas, fases, câmera, pesos e momentos originais não foram modificados.

Duas declarações anteriores reduziram a obrigação que a #132 deixou em aberto: `CarrySpatialCorrection.difference_power_stirling` fornece as diferenças finitas e os coeficientes de Stirling em toda ordem; `CarryOddEnergy.normalized_odd_pair_expansion` já transporta um coeficiente chamado `spatialCorrection` à expansão do par nativo, com resto. `finite_odd_energy_correction_tendsto`, `finite_odd_source_original` e `finite_odd_green_recomposition` conservam, para cada família finita, as duas pernas, os cruzamentos e a recomposição física. Eles não afirmam sinal da correção.

A prova variacional da PR #41 continua pertinente para identificar o residual crítico; não supomos seu sinal. Os controles de fonte e a não anulação local vêm dos teoremas anteriores, não de uma Gram definida a posteriori.

## B — O que foi demonstrado agora

### B.1 — Soma combinatória e ponte à fonte

Se `m=2r+1`, `n=2s+1`, os pesos são os `completedGreenForwardWeight` originais e o denominador é o de Cauchy `i+j+2`. `physical_stencil_cauchy_beta` obtém a soma beta a partir de `raw_stencil_complement` e `complement_row_factorial`: a síntese vetorial precede a leitura do par. `stencil_pair_physical_reduction` mantém as duas pernas ordenadas e reduz a soma dupla a duas somas fatoriais. `shifted_factorial_binomial`, `centered_odd_split` e `odd_stencil_pair_eq_centered` provam, em Lean e em todas as ordens ímpares, a reindexação e os sinais que unem essas somas à diferença finita centrada.

`centered_difference_stirling` e `centered_correction_eq_lambda` avaliam essa diferença usando Stirling. Consequentemente, `odd_stencil_correction_all_order` demonstra a igualdade completa

$$\frac1{m!n!}\sum_{i=0}^m\sum_{j=0}^n(-1)^{m+n-i-j}\binom mi\binom nj\frac{(i+1)^{m+n+3}+(j+1)^{m+n+3}}{i+j+2}=-\Lambda_{m,n},$$

$$\Lambda_{m,n}=\frac{(m+1)(m+2)(2m+3)}{12}+\frac{(n+1)(n+2)(2n+3)}{12}+\frac12\left(\frac{(m+1)(m+2)-(n+1)(n+2)}2\right)^2.$$

`existing_spatial_coefficient_eq_lambda` identifica essa expressão com o `spatialCorrection` já usado pela fonte. `original_odd_pair_expansion_lambda` transporta a identidade à expansão do par ímpar nativo completo e mantém o resto analítico. Na normalização **existente** `normalizedOddPair`, para `h_k=radialStep k` e para todo k suficientemente grande:

$$P_{r,s,k}=h_{r+s+1}-h_k^2\Lambda_{2r+1,2s+1}h_{r+s+2}+h_k^4R_{r,s}(h_k).$$

Aqui `h_j` são os momentos canônicos originais e `R` é o pareamento dos restos originais nomeado no teorema. A normalização `P` é a do código citado; não se substitui um fator por outro para reproduzir uma convenção diferente. `original_finite_odd_energy_correction_lambda` fornece a passagem à energia assinada da combinação finita original, com todos os pares `r,s`. A identidade não recebe positividade canônica como hipótese.

### B.2 — Integração entre passos radiais

`physical_curve_exact_prefix_and_tail` preserva, para quaisquer entradas materiais finitas independentes, a igualdade exata entre o pareamento completado e seu prefixo **mais** o pareamento da cauda. `source_error_hasDerivAt_and_bound` usa a cota pontual da #132 após essa síntese.

`integrated_native_grid_jets` toma duas combinações finitas independentes de jets literais, qualquer dimensão N e qualquer truncamento M. Quando `N h_k<1/4`, denotando por `F` a forma física completa, `P_M` seu prefixo da mesma fonte e `B_{N,M}` o orçamento explícito da #132, o Lean prova

$$\left\|[F-P_M](h_k)-[F-P_M](h_{k+1})\right\|
\le \int_{h_{k+1}}^{h_k} B_{N,M}(t)\,dt,$$

O teorema geral `integrated_native_grid_jets` explicita inicialmente a hipótese de integrabilidade de `B_{N,M}`. `native_jet_budget_interval_integrable` a demonstra por continuidade para as combinações literais dos jets, e `integrated_native_grid_jets_unconditional` a descarrega: na grade, basta o corte `N h_k<1/4`. A integrabilidade da derivada do erro também é derivada por dominação, não recebida separadamente. Ordens abaixo de N permitem usar `radial_jet_curve_complete_jet` para identificar o prefixo com cada jet físico inteiro. Coeficientes arbitrários incluem uma direção crítica fixa de qualquer ordem finita, mas o teorema não constrói seus coeficientes nem estabelece dominância do saldo. `integrated_original_jet_combinations` oferece também a variante com primitiva W que domina a cota.

## C — O que foi refutado ou delimitado

`lambda_real_positive` mostra `Lambda_{m,n}>0` para cada par de ordens naturais. Entretanto, `lambda_crossing_negative` verifica que a matriz dos coeficientes para ordens 1 e 3 tem a direção `(1,-1)` com valor `5-2·42+30=-49`. Isso não determina o sinal da correção canônica, que inclui momentos diferentes em cada cruzamento; demonstra apenas que positividade entrada a entrada não pode substituir a análise do pareamento.

O contraexemplo de dois átomos da #132 permanece válido e não é fonte Carry. A identidade de Lambda não prova que todos os pivôs sejam positivos, não constrói uma Gram infinita e não estabelece que todas as correções críticas tenham o mesmo sinal. O controle finito em `centered_identity_probe.py` é diagnóstico adicional, não premissa dos teoremas.

## D — O que permanece aberto

Para uma direção crítica de ordem arbitrária, a integrabilidade em cada intervalo já está demonstrada; ainda falta calcular uma cota somável dos incrementos em função de seus coeficientes, levando em conta o crescimento dos stencils e o fator radial. Depois é preciso uma desigualdade da fonte, independente da positividade desejada, que prove na mesma escala que o saldo crítico domina a cauda. A fórmula de Lambda preserva os cruzamentos, mas não escolhe o sinal de sua soma ponderada por momentos e coeficientes da direção.

A expansão física anterior é eventual em k para cada par ou família finita; não foi estabelecido um corte uniforme para todas as ordens. Nada aqui prova um operador infinito ou resultados sobre zeros.

## E — Próximo passo mínimo e reprodução

Para a família crítica ímpar arbitrária, usar `native_jet_velocity_size` e os coeficientes binomiais originais para obter uma primitiva explícita ou cota de potência de `B_{N,M}` quando o passo tende a zero. Em seguida somar os orçamentos a partir de uma escala determinada e compará-los com o saldo da **mesma** fonte. Essa comparação é a obrigação de sinal, não uma consequência automática da lei combinatória.

Em `llm`, com as dependências originais e a base acima:

```bash
python3 research/native-all-order-radial-tail/restore_verified_cache.py
bash research/native-stencil-integrated-control/validate.sh
```

Validação local no `llm`: os nove módulos da primeira etapa foram recompilados com warnings como erros, seguidos de `BudgetContinuity`; `lake build --wfail` e as auditorias Foundation, Geometry e Analysis passaram. As versões finais têm `#print axioms` para 45 teoremas e auditoria transitiva de tipos e corpos de 55 declarações, percorrendo 58.488 dependências e bloqueando os consumidores enumerados de certificados finitos de positividade. Somente `propext`, `Classical.choice` e `Quot.sound` aparecem. Os 200 objetos ancestrais foram verificados e reutilizados; #131, #132 e os módulos novos foram compilados. A checagem de 81 pares e 200 camadas adicionais é independente e não é premissa Lean.

O cache ancestral de 200 objetos exige `.cache/input-cache.tar.gz` dentro de `research/native-all-order-radial-tail`, SHA256 `d374041b5b017e2541039b6993ed3f53b244f20a1dd8c2e7bb851ba09eca288a`. A rotina verifica fontes, toolchain e dependências antes de restaurar; #131, #132 e os módulos novos são compilados explicitamente. `centered_identity_probe.py` é um controle racional independente, não usado como premissa Lean. Logs e hashes ficam em `evidence/` e `SHA256SUMS`; não há alegação de CI externa.

Fim do relatório — combinatória e transporte ímpar all-order verificados; orçamento total e sinal crítico all-order permanecem abertos.
