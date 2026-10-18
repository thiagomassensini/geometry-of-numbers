# Ataque all-order: cauda polarizada da fonte e escala da margem

## Resultado matemático

Foi obtido um controle **incondicional e uniforme no número de colunas restantes** da forma da fonte canônica. A positividade em todas as ordens continua aberta. O novo controle limita quanto uma energia pode ficar abaixo de zero; não prova que esse erro tenha sinal favorável.

A fonte, os momentos, os pesos, o dressing, as métricas, os pins e os operadores históricos não foram alterados. Nenhum estado foi construído por fatoração de uma matriz-alvo. A norma euclidiana dos coeficientes aparece somente no orçamento de erro; não substitui a norma física.

## Proveniência

- Investigação iniciada no merge do PR #29, `76fead5cbc40c350449966a5f5c89ff8ea47d234`, em `geometry-of-numbers`. O checkout principal continha o trabalho de outra sessão no sexto setor ímpar. Ele foi preservado integralmente.
- Worktree própria: `/home/thlinux/geometry-of-numbers-all-order-tail`, branch `agent/all-order-polarized-tail`. Durante a investigação o PR #31 foi integrado por outra sessão. A worktree foi atualizada por fast-forward até `1490fd5`, sem incorporar alterações próprias naquela sessão.
- Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Seus dois arquivos C2 não rastreados foram preservados.
- O majorante usado é o já demonstrado `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_sharp_decay`. Ele é derivado da fonte theta infinita e da recorrência logarítmica; não pressupõe positividade dos momentos.
- Os prefixos positivos usados são `CarryCriticalSource.even_source_five_posDef` e `CarryThetaPattern.odd_source_five_posDef`, já disponíveis antes desta rodada. Não foi necessário certificar outro pivô finito.
- `CarryCriticalSource.criticalBalance_tendsto` conserva a identificação entre a direção crítica e o limite incidente menos retorno. `sourcePair_boundary` reutiliza literalmente o fator 4, os sinais e as fases da decomposição canônica existente.

## Pareamento antes da diagonal

Escrevendo `h_j` para o momento logarítmico canônico efetivo, definimos apenas sua contração retangular:

\[
P_s(x,y)=\sum_{i,j}h_{i+j+s}\,\overline{x_i}y_j.
\]

Isto é o pareamento assinado já existente, após a síntese da fonte. Não é uma realização positiva nova nem uma fonte material substituta.

Para cabeças `x,y` com N entradas e caudas `a,b` de comprimentos independentes M,L, o Lean demonstra

\[
P_s(x\oplus a,y\oplus b)
=P_s(x,y)+P_{s+N}(x,b)+P_{s+N}(a,y)+P_{s+2N}(a,b).
\]

As quatro parcelas ordenadas permanecem complexas. Suas duas quadraturas são transportadas explicitamente:

\[
\Re P_s(x,y)=B_s(x_R,y_R)+B_s(x_I,y_I),\qquad
\Im P_s(x,y)=B_s(x_R,y_I)-B_s(x_I,y_R).
\]

`B_s` é a mesma soma real com os mesmos momentos. A ordem da conjugação está fixada no primeiro argumento. O primeiro cruzamento, a avaliação central e o caso de cauda vazia são regressões formais. Não houve identificação nova entre tempo material e parâmetro espectral, profundidade e jet, ou carriers físicos distintos.

## Estimativa de todas as ordens

Seja `r=22/175`, exatamente o majorante anterior da fonte, e `E(x)=Σ|x_i|²`. Cauchy–Schwarz e a soma geométrica fornecem, para qualquer N,M e quaisquer coeficientes complexos,

\[
\left|P_s(x\oplus a,x\oplus a)-P_s(x,x)\right|
\le \delta_{s,N}\bigl(E(x)+E(a)\bigr),
\qquad
\delta_{s,N}=\frac{r^{s+1}(r^N+r^{2N})}{1-r^2}.
\]

O bound estima os cruzamentos; não os remove da identidade. `uniform_cutoff_accuracy` prova que, para todo erro positivo, existe um cutoff a partir do qual esse bound vale simultaneamente para todos os comprimentos restantes e todos os inputs. Não há troca não justificada de somas infinitas, limites de jets ou derivadas globais.

Se o prefixo retido é positivo semidefinido, então

\[
\Re P_s(x\oplus a,x\oplus a)\ge-\delta_{s,N}(E(x)+E(a)).
\]

Com N=5, ambos os setores já certificados tornam essa conclusão incondicional em toda ordem restante. As constantes racionais verificadas no kernel são

\[
\delta_{0,5}<1/240000,\qquad \delta_{1,5}<1/1900000.
\]

`boundary_all_order_lower_bound` transporta o resultado ao readout Green canônico:

\[
\mathrm{Boundary}_{2(5+M)}
\ge-4\delta_{0,5}E_{\rm even}-4\delta_{1,5}E_{\rm odd}.
\]

Cada energia de coeficientes inclui sua cabeça e sua cauda. O gráfico inverso de paridade já existente cobre todos os inputs desse readout. Esse orçamento não é uma igualdade com a energia de Hilbert física e não demonstra contração do retorno em ordem arbitrária.

## Por que ainda não fecha a positividade

1. O erro é estritamente positivo. Um limite inferior negativo, mesmo pequeno, não decide o sinal.
2. Fazer `δ(s,N)` tender a zero muda o prefixo N. Não podemos presumir que esses novos prefixos sejam positivos. O resultado não autoriza concluir positividade global a partir de um único prefixo finito.
3. A estimativa absoluta é grosseira precisamente nas direções de cancelamento. `cutoff_budget_exceeds_last_native_diagonal` prova, para N≥2, que esse orçamento já excede a última diagonal nativa do prefixo. Portanto ele não fornece uma margem abaixo da coercividade bruta desse prefixo. É uma limitação deste orçamento, não uma direção negativa da fonte.
4. `physical_critical_margin_upper` demonstra, supondo somente a positividade do prefixo antigo, que uma margem `ε` persistente no balanço físico satisfaz

\[
\varepsilon\le 2\sigma_{s,n}\le 2r^{2n+s+1}.
\]

`no_fixed_physical_critical_margin` exclui uma margem positiva fixa em todas as ordens nessa escala original. Não exclui margens positivas dependentes de n.

O PR #31 já exclui coercividade uniforme dos blocos nas coordenadas originais (`CarryResidualObstructions.no_uniform_native_coercivity`). Esse resultado foi conferido; não o apresentamos como descoberta desta rodada. Aqui a nova comparação quantitativa é com o orçamento de cutoff e com a margem do balanço físico na direção crítica.

## Obrigação exata restante

A identidade residual do PR #29, para o prefixo antigo invertível, continua sendo uma forma concreta de atacar o sinal:

\[
\sigma=E_{\rm trial}(z)-r_z^TA^{-1}r_z,\qquad r_z=b-Az.
\]

O critério suficiente já demonstrado é `r_zᵀr_z < α E_trial(z)`, onde `α>0` é uma coerção demonstrada do prefixo antigo. Continua faltando derivar da fonte uma família de estimativas que satisfaça esse critério, ou outro controle relativo dos canais, para cada ordem e setor. A desigualdade nova desta rodada controla o tamanho da cauda; não fornece esse controle relativo. Não foi demonstrado que aumentar os modos theta, sozinho, resolva o cancelamento.

O próximo alvo sugerido é uma estimativa da fonte para o residual na direção crítica, com a dependência da ordem explícita e todos os acoplamentos conservados. Não escolher outra normalização para obter o sinal.

## Status

| Status | Resultado |
|---|---|
| Provado | Expansão polarizada retangular com quatro blocos e caudas de comprimentos independentes. |
| Provado | Reconstrução das partes real e imaginária pelas duas quadraturas. |
| Provado | Bound explícito de cutoff uniforme em toda ordem restante e todos os inputs. |
| Provado | Limite inferior global a partir dos prefixos reais já certificados, incluindo o readout Green com seu fator 4. |
| Provado | Escala superior das margens críticas físicas e limitação do orçamento absoluto. |
| Condicional | Bound a partir de qualquer outro prefixo positivo semidefinido; sua positividade não é fornecida pelo teorema. |
| Aberto | Desigualdade relativa da fonte, positividade de todos os pivôs, retorno contrativo em todas as ordens e realização física positiva infinita. |
| Obstruído | Margem crítica positiva fixa em todas as ordens na escala original; uso direto deste orçamento absoluto como margem coerciva do prefixo. |

## Validação e reprodução

Comando no `llm`:

```bash
bash research/all-order-polarized-tail/audit-all-order-polarized-tail.sh
```

O runner compila os sete módulos explicitamente com `-DwarningAsError=true`, incluindo as regressões e a auditoria das 41 raízes públicas por tipos e corpos. Executa também `lake build --wfail` e as auditorias Foundation, Geometry e Analysis. A verificação transitiva permite somente `propext`, `Classical.choice` e `Quot.sound`. Não há obrigações admitidas, axiomas novos ou atalhos de confiança.

Dependências compiladas anteriores são reutilizadas e registradas por hash, com fontes e pins conferidos. As novas fontes são recompiladas explicitamente; o build raiz sozinho não compila os módulos em `research`. A worktree reutiliza o cache `.lake` do checkout canônico. Os dois pacotes mais antigos, anteriores ao formato `source-manifest.json`, são conferidos contra o commit base e registrados separadamente. `evidence/validation.json` só é produzido após todos os comandos terminarem com sucesso; `evidence/source-manifest.json` registra hashes de fontes, dependências e caches.
