# Margem da cabeça TFVD e orçamento completo da cauda

**Resultado: PARTIAL.** Há agora uma margem rigorosa para a cabeça literal C3 na segunda direção par, válida para uma família de direções e cortes suficientemente grandes. O orçamento completo de cauda também ganhou uma cota explícita na ordem e no corte. A origem da margem finita é o certificado C3 anterior da PR #70 para a **fonte completa**; essa rota não fornece uma explicação independente do sinal do pivô nem uma lei all-order.

## A — Base e fonte

Base inicial `87bafb893ce0d4e54ce74e0ad18c0e5a569dc051`, PR #146, branch `agent/c3-critical-tilt-prime`, empilhada na #145. Durante a investigação, o commit paralelo `91a4ca70663e93d4a8fdde8f9f6319ad913d0dea` foi integrado à mesma branch. São preservados os estados de cabeça e cauda literais, a decomposição TFVD completa, a métrica, completion, bordo e os cruzamentos. O arquivo `CompletedFirstVariation.lean`, inicialmente não rastreado e depois integrado pelo commit paralelo, foi preservado e não é dependência da prova nova.

São reutilizados:

- `native_regrouped64_total_lower` (PR #70), que obtém de caixas da fonte C3 e da cauda original uma cota inferior para a forma **completa** em toda direção `z(t)=(t,1)`, `|t|≤1`, sem hipótese de sinal de pivô. A margem é `κ=10⁻⁸−10⁻¹³`.
- `literal_error_bound` e `literalErrorBudget_normed` (PRs #70 e #143), que preservam HT, TH e TT e limitam a diferença entre o pareamento completo e a cabeça literal.
- `normalizedError_tendsto_zero` (PR #143), que demonstra a convergência do orçamento normalizado para cada dimensão e setor fixos.
- `literal_product_critical` da continuação da #146 e a direção mônica da PR #41, com prefixo anterior invertível.

A fonte C3 da PR #70 já estabelece uma desigualdade sobre a **forma completa** que, para a direção crítica, implica o sinal finito. Logo, empregá-la para obter sinal da cabeça e voltar ao pivô é um transporte quantitativo legítimo, mas **não é uma origem geométrica independente** para o sinal daquele pivô.

## B — Margem efetivamente demonstrada

`c3_original_pair_lower` transporta exatamente a cota fonte da PR #70 para o mesmo bloco Bézout nativo, sem mudar a fonte e sem assumir sinal de pivô. `c3_literal_monic_margin_eventually` prova que, para todo corte `M` suficientemente grande e uniformemente em `|t|≤1`,

\[
 H_M(0)\ne0,\qquad
 \operatorname{Re}HH_M(z(t),z(t))>9\cdot10^{-9},\qquad
 20 E_M(z(t),z(t))<\operatorname{Re}HH_M(z(t),z(t)).
\]

`E_M` é a soma original dos três orçamentos não negativos HT, TH e TT, não apenas a norma da sua soma. A propriedade é demonstrada antes de selecionar a direção crítica. O resultado é para a **cabeça literal bruta** do corte `M`, e não para a cabeça com bordo reorganizado em `M=64`; não há contradição com a falha numérica daquele teste até `M=4096`. A demonstração estabelece um corte eventual, sem apresentar valor numérico dele.

`c3_literal_critical_product_margin_eventually` especializa à direção crítica verdadeira da PR #41/#70, usando `native_even_one_isUnit_from_source`, descarregada das caixas da própria fonte. Nessa direção ele retém as duas parcelas do produto e a igualdade com `nativeC 0 * nativeSourceSchurRemainder 0 1`. Trata-se do segundo pivô par já conhecido, não de uma nova ordem.

## C — Dependência explícita da ordem e do corte

`literal_full_budget_explicit_order_rate` fortalece, para o orçamento **em si**, a taxa antes disponível para a norma do erro final. O Lean demonstra uma constante `C>0` da envoltória da fonte tal que, para todo corte `M`, tamanho `r`, setor e par de vetores reais `x,y`,

\[
E_M(x,y)\le 4r^2(2A_r\rho_{M,r}+3\rho_{M,r}^2)\|x\|_1\|y\|_1,
\quad
A_r=\sum_{k=0}^{2r}|c_k|,\quad
\rho_{M,r}=\frac{C16^{2r}}{M+1}.
\]

A cota conserva as contribuições HT, TH e TT separadamente durante sua obtenção. A constante `C` é garantida pelo teorema `literal_tail_jet_envelope` da fonte original, mas não foi reduzida aqui a uma caixa racional ou número calculável. A taxa não dá coercividade relativa nem uniformidade em `r`.

Para a regressão par de dimensão dois, `c3_monic_margin_of_explicit_budget` usa

\[
U_M=64(2A_2\rho_{M,2}+3\rho_{M,2}^2).
\]

Se `C/(M+1)<c₀` e `21U_M<κ`, ele prova que a cabeça é invertível e que `20E_M<Re HH_M` para todos os `|t|≤1`. `c3_explicit_source_cutoff_exists` demonstra, para a mesma constante da fonte, que ambas as condições são satisfeitas eventualmente. É um **critério simbólico em M**, não um inteiro de corte calculado.

## D — O que não foi demonstrado

Não se provou uma margem para a terceira direção ou para ordens arbitrárias a partir da cabeça geométrica. A PR #144 já demonstrou sinal da terceira direção nos dois setores com caixas theta; usá-lo para estabelecer primeiro o sinal completo e depois voltar à cabeça não resolveria a busca de origem independente. A PR #145 identifica exatamente as desigualdades nos coeficientes `c₅` e `c₆` que faltam para esse próximo teste diretamente na fonte. A #69/70 certifica apenas os quatro coeficientes `c₀,…,c₃`; para a terceira direção são necessárias caixas independentes suficientemente precisas até `c₅` no par e `c₆` no ímpar, incluindo Gamma, chart, cabeça C3 e cauda.

A taxa de cauda não demonstra que a margem da cabeça exceda o orçamento em ordem arbitrária. A afirmação de que existe algum corte com tal margem, sem um mecanismo anterior independente, pode apenas reformular a positividade desejada. Nenhuma Gram física Green foi identificada com a Hankel pela presente prova.

## E — Validação e próximo passo mínimo

As novas provas estão em `NativeBudgetRate.lean`, `NativeFiniteHeadMargin.lean`, `NativeExplicitHeadMargin.lean` e `NativeHeadMarginAudit.lean`. `#print axioms` aponta apenas `propext`, `Classical.choice` e `Quot.sound`. A auditoria transitiva exige as raízes originais da fonte e bloqueia caixas theta e consumidores de sinal explicitamente nomeados; isso não é auditoria semântica de todas as equivalências. A prova finita **usa** a cota da fonte completa da PR #70, conforme descrito acima.

```bash
bash research/c3-tilt-prime/validate_native_head_margin.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

Os logs estão em `evidence/`; os caches de dependências anteriores foram reutilizados. O próximo avanço não circular é certificar, para `r=3`, as caixas C3/Gamma/chart dos coeficientes até `c₅`/`c₆` e provar o limite inferior da cabeça com seus cruzamentos, comparando-o com a cauda original. Para all-order é necessária uma propriedade que controle essa margem e a direção crítica em função da ordem; a taxa absoluta acima sozinha não a fornece.
