# Quatro caixas da característica original pela cauda C3 acelerada

**PASS no alvo finito das quatro caixas.** `canonical_four_source_boxes` demonstra, sem hipóteses de inclusão ou de sinal, as quatro caixas dos coeficientes completos da característica original F exigidas pela PR #67. A rota usa Gamma original, fatores Xi/chart, prefixo C3 e toda a cauda acelerada. **A positividade all-order continua aberta.**

Base: `383c4b5a58d009062233bc588ff60670f64e2839`, HEAD da PR #68.
Branch: `agent/c3-fourteenth-tail`, empilhada sobre `agent/c3-gamma-jet-enclosures`, sem merge automático.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
Operador consultado, sem alterações: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

- A PR #67 identifica, na fonte original, os quatro coeficientes fatoriais f₀,f₂,f₄,f₆ e prova que erro absoluto ≤10⁻¹² nos centros racionais documentados basta para `h₀h₂−h₁²>0`. O teorema consumidor é `CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes`.
- A mesma PR fornece `completedTrace_head_tail`, `full_even_jets_head_tail`, `odd_jets_head_tail_cancel` e o ledger conjunto de quatro slots. Estado enriquecido, traços, caudas e todos os termos mistos permanecem nos teoremas de origem.
- A PR #68 certifica os sete jets da Gamma **original** Γ(1/4+iw/2), com erro absoluto ≤10⁻¹⁸. `CarryC3Gamma.native_gamma_seven_boxes` não recebe momentos, sinais Hankel ou valores numéricos não certificados como premissas.
- As identidades originais da característica com a continuação Genuine e a carta C3 já estão em `nativeScalar_eq_genuineContinuation_unconditional`. Esta igualdade é reutilizada; não se redefine a característica por um avaliador finito.
- A PR #41 separa ortogonalização algébrica e sinal. O residual da segunda direção par é `h₂−h₁²/h₀` quando h₀≠0. A nova avaliação não pressupõe seu sinal.
- Os certificados H6/K6 e a realização física das doze fontes são regressões posteriores, preservados e bloqueados nas dependências das novas provas de inclusão. Não são entradas deste avaliador.

O alvo é finito: quatro caixas de F, não uma hipótese de Gram e não positividade em toda ordem. A fonte C3 original, a unidade semente, os endereços, as duas pernas, as fases, o argumento Gamma, o fator polinomial, a exponencial com π e o chart continuam os mesmos.

## B — Identidades e estimativas da mesma fonte

### 1. Aceleração exata na malha C3

Escreva Δf(a)=f(a+1)−f(a) e defina o polinômio de bordo

$$\begin{aligned}
B(\Delta)={}&-\Delta/3+\Delta^2/3-2\Delta^3/9+\Delta^4/9-\Delta^5/27\\
&+\Delta^7/81-\Delta^8/81+2\Delta^9/243-\Delta^{10}/243+\Delta^{11}/729.
\end{aligned}$$

`CarryC3Tail.c3_acceleration_cell` demonstra, para **qualquer** sequência complexa, a identidade exata

$$\boxed{\Delta^2f(a)=Bf(a)-Bf(a+3)+\Delta^{14}f(a)/729.}$$

Os coeficientes resultam da divisão algébrica de −D por 3+3D+D²; não foram escolhidos a partir de momentos ou de um sinal desejado. `c3_acceleration_finite` conserva ambos os bordos e cada parcela do resto em qualquer janela finita.

O crosswalk físico é separado dessa álgebra. `native_c3_cell_fd` identifica **literalmente**

$$\operatorname{realCpSaturatedBracket}(3,m,s(w))
=f_w(3m+2)-2f_w(3m+3)+f_w(3m+4),\qquad f_w(n)=n^{-s(w)},\quad s(w)=1/2+iw.$$

Portanto, a janela começa em a=3M+2 e avança de três em três. Não se transporta uma envoltória da malha base dois por semelhança de stencil. `c3_sample_eq_generic_power` confere a igualdade da onda genérica antes de reutilizar sua regularidade; os endereços C3 têm prova própria.

### 2. Todo o resto infinito e os sete jets

`fd_norm_le` prova uma estimativa complexa a partir da cadeia inteira de derivadas. Ela usa uma desigualdade de norma, sem alegar um teorema do valor médio escalar para funções complexas.

`native_fd_bound` fornece, no disco |w|≤1/2 e para a≥1,

$$\|\Delta^n f_w(a)\|\le n!/a^n.$$

A potência relevante é 14. `c3_power14_tail` demonstra na malha original

$$\sum_{k\ge0}\frac1{(3(k+M)+2)^{14}}
\le\frac1{(3M-1)^{13}},\qquad M\ge1.$$

`c3_boundary_at_infinity` prova que o bordo distante desaparece. Só depois `native_c3_tail_acceleration` passa a identidade finita ao limite:

$$\operatorname{realCpBracketCutoffTail}(3,M,s(w))
=Bf_w(3M+2)+\frac1{729}\sum_{k\ge0}\Delta^{14}f_w(3(k+M)+2).$$

Definimos H_M como o prefixo literal, com sua semente, acrescido desse bordo; T_M é a cauda original menos o mesmo bordo. `native_c3_head_tail` conserva a identidade **S=H_M+T_M**. Isso é uma divisão de avaliação do mesmo sinal; não constitui outra fonte física.

`accelerated_c3_tail_bound` e a estimativa de Cauchy dão

$$\|T_M(w)\|\le\frac{14!}{729(3M-1)^{13}},\qquad
\left\|T_M^{(r)}(0)/r!\right\|\le\frac{14!\,2^r}{729(3M-1)^{13}}.$$

`native_c3_seven_jet_error_at64` especializa, para r=0,…,6:

$$\boxed{\left\|S^{(r)}(0)/r!-H_{64}^{(r)}(0)/r!\right\|\le10^{-19}.}$$

O índice 64 conta células C3. A ordem 14 é a ordem da diferença finita. Nenhum desses índices é profundidade vertical ou ordem Hankel.

### 3. Completion e avaliação dos valores finitos

`characteristic_c3_formula` reutiliza a característica original:

$$F(w)=A(w)S(w),\qquad A(w)=\frac{\Xi(w)}{1-3^{1-s(w)}}.$$

`height_parameter_crosswalk` confere a igualdade exata dos parâmetros antes de reutilizar as cotas dos fatores polinomial e exponencial já existentes. O chart C3 recebe sua própria separação em `c3_chart_inverse_bound`. No disco |w|≤1/4:

$$\|1/Q_3(w)\|\le4,\qquad \|\Xi(w)/\Gamma(s(w)/2)\|\le3,\qquad \|A(w)\|\le96.$$

O quociente sem Gamma aqui é escrito pelos fatores originais em `xiBeforeGamma`; nenhuma divisão em um zero é presumida. A regularidade e os não anulamentos necessários são provados nas declarações correspondentes.

O prefixo acelerado satisfaz |H₆₄|≤4. Defina a parte esquerda da avaliação

$$L_{64}(w)=\frac{\Xi_{\mathrm{antes\ de\ Gamma}}(w)}{Q_3(w)}H_{64}(w).$$

`finite_left_jet_bound` fornece |jet_r L₆₄|≤64·4ʳ. A substituição dos **sete coeficientes Gamma**, com o erro já demonstrado na #68, é apenas uma aproximação de avaliação. `finiteCompletedJet` registra a convolução finita com esses centros Gamma e `gamma_jet_replacement_error` conserva seu erro.

O erro completado da cauda é controlado separadamente, por Cauchy aplicado a A·T₆₄, sem aproximar duas energias divergentes. `completed_jet_evaluator_error` combina as duas parcelas para cada r=0,…,6:

$$\boxed{|\operatorname{jet}_rF-\operatorname{finiteCompletedJet}_r|\le4\times10^{-13}.}$$

Os erros utilizados, antes do arredondamento final, são

$$E_r^{\mathrm{cauda}}=\frac{96\,14!\,4^r}{729\,191^{13}},\qquad
E_r^{\mathrm{Gamma}}=\frac{64\sum_{j=0}^r4^j}{10^{18}}.$$

### 4. Intervalos racionais dos fatores elementares e dos endereços

`RationalBoxes.lean` demonstra as inclusões para soma, subtração, produto, inverso separado de zero e arredondamento dirigido. O grid de avaliação é 10⁻³⁰. Ele não altera a métrica física; serve apenas para armazenar envoltórias racionais com tamanho controlado.

`unit_log_box` usa a série de logaritmo com resto explícito. `rational_log_box` reduz os argumentos racionais a [1/2,1] por potências de dois **somente para avaliar logaritmos**. Essa redução numérica não troca a câmera C3 nem o índice material. A avaliação de log π usa as desigualdades rigorosas `Real.pi_gt_d20` e `Real.pi_lt_d20` de Mathlib, monotonicidade do log e os mesmos intervalos racionais.

`exp_box` usa o polinômio de Taylor da exponencial com 64 termos e um resto demonstrado para argumentos de módulo ≤4. Não recebe decimais de mpmath.

`SamplePrimitiveBoxes` verifica no kernel os logaritmos e amplitudes dos endereços 1,…,205. São exatamente os endereços necessários ao prefixo de 64 células e ao bordo de 12 amostras. `CompletionPrimitiveBoxes` certifica os fatores envolvendo log π, exp(−log π/4), log 3 e exp(log 3/2).

`boundary_stencil`, `sample_jet_formula` e `accelerated_head_jet_formula` identificam os coeficientes avaliados com os da fonte literal. Cada jet conserva a fase iʳ. O prefixo finito não é declarado par: os jets ímpares não são zerados para facilitar as contas.

`phased_product` e `phased_reciprocal` demonstram as convoluções e a recorrência inversa do chart. A inversão exige o seu não anulamento no centro; nenhum sinal de Hankel entra nessa construção. `finite_left_jet_formula` e `finite_completed_jet_formula` ligam as tabelas racionais ao avaliador dos mesmos fatores originais.

### 5. Quatro inclusões finais

Os centros da #67 são preservados exatamente:

| Coeficiente | Centro racional decimal finito |
|---|---:|
| f₀ | 0.497120778188314 |
| f₂ | −0.011485972157573 |
| f₄ | 0.000123452018070 |
| f₆ | −0.000000832355481 |

`four_finite_evaluator_checks` verifica as quatro inclusões do avaliador finito em caixas de raio 10⁻¹³. A interpretação desses cálculos é demonstrada em `finite_completed_reference_error`.

O teorema que descarrega a obrigação completa é

**`CarryC3Boxes.canonical_four_source_boxes (j : Fin 4)`**:

$$\boxed{\left|F^{(2j)}(0)/(2j)!-q_j\right|\le10^{-12}.}$$

O orçamento é 4·10⁻¹³ da avaliação analítica, mais 10⁻¹³ da inclusão racional finita; a margem resultante cabe na tolerância original. As normas são complexas, portanto não se apaga uma componente imaginária para produzir o certificado.

Por aplicação do teorema da #67, **`canonical_two_even_determinant_pos_from_c3`** fornece

$$h_0h_2-h_1^2>0.$$

Esse é um sinal de uma seção finita, agora obtido por esta rota C3 com todos os seus erros. O sinal finito já possuía certificados por outra rota; a novidade é a inclusão efetiva a partir da avaliação nativa pedida aqui.

## C — O que foi refutado ou evitado

Não foi demonstrada uma obstrução nova da geometria. O resultado não generaliza os sinais de uma seção para toda ordem.

Foram evitadas três identificações indevidas: a malha de quatro passos não é a malha C3; um prefixo sem cauda não é F; uma aproximação Gamma não é um fator físico redefinido. Cada aproximação tem identidade de proveniência e erro na característica verdadeira.

A correspondência entre resultados Python de alta precisão não é utilizada como intervalo. Os scripts novos usam somente `Fraction` para propor e conferir testemunhos racionais. A validade matemática vem das inclusões e restos compilados em Lean.

Não se criou uma nova Gram, fonte, métrica, normalização, operação de whitening ou operador de alturas. Nada disso é necessário para descarregar as quatro caixas. A ortogonalização da #41 continua downstream da sequência canônica original.

## D — Validação, axiomas e reprodução

São **133 teoremas, 74 definições e 2 abreviações, em 209 raízes matemáticas explícitas**, distribuídas por 16 módulos, mais Regression e Audit. A estrutura auxiliar de intervalos `Box` e sua instância de decidibilidade são percorridas transitivamente nas dependências. As raízes estão em `public-roots.json`. `generate_audit.py` inclui os nomes de teoremas dentro do namespace `Box`, imprime `#print axioms` e audita transitivamente tipos e corpos. Os únicos axiomas permitidos são `propext`, `Classical.choice`, `Quot.sound`. Os consumidores posteriores de sinais de momentos e de positividade H6/K6/H7 especificados no guard são rejeitados.

As contas fechadas usam `decide +kernel`. Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos novos. `check_intervals.py` é uma regressão racional independente; seus resultados não são recebidos como prova. Os fechamentos transitivos por grupo visitaram 1.762, 2.477, 2.458, 3.331, 1.134, 1.693, 4.772, 3.379, 1.725, 1.743, 5.165, 3.406, 1.897, 818, 1.890 e 5.324 constantes, com sobreposição entre os grupos; esses números não devem ser somados como constantes distintas.

**Validação final: 28/28 verificações locais passaram**, com código de saída zero: geração da auditoria, 18 módulos explícitos com `warningAsError`, regressão racional, builds focado e raiz com `lake build --wfail`, três auditorias de camadas, regressão das doze fontes, preservação histórica e diff check. Os comandos e resultados efetivos ficam em `evidence/checks.json`, com logs dos módulos, builds focado e raiz com `--wfail`, auditorias Foundation/Geometry/Analysis e regressão das doze fontes. O manifesto `source-sha256.json` registra os arquivos entregues. O build do pacote raiz, isoladamente, não compila estes módulos de pesquisa; por isso eles têm comandos explícitos próprios. Durante a validação, a regressão Python ainda procurava uma tabela no arquivo anterior à separação dos módulos. O caminho foi corrigido para `HeadEvaluatorData.lean` e o check foi repetido. As 18 compilações Lean já concluídas foram conservadas, sem alteração das fontes; `validation-recovery.json` registra seus hashes, os checks preservados e a tentativa anterior. `checks.json` consolida os resultados finais.

Reprodução no host llm, com os ancestrais preparados conforme seus relatórios:

```bash
cd /home/thlinux/geometry-of-numbers
git switch agent/c3-fourteenth-tail
python3 research/c3-fourteenth-tail/validate.py
```

`compile_module.sh` declara os caches ancestrais. Não se reivindica bootstrap de clone vazio sem esses módulos. Main, PRs anteriores, dependências, pins, métricas, câmeras e arquivos não rastreados preexistentes são preservados. Não se criou worktree nova e não se realiza merge automático.

## E — Próximo passo mínimo

A inclusão `canonical_four_source_boxes` foi compilada e auditada: **a obrigação das quatro caixas está resolvida**. Não é necessário repetir avaliação Gamma ou assumir a cauda C3 como entrada livre.

Para reutilização quantitativa em outras seções finitas, o avaliador pode ser ampliado com o orçamento de jets e diferenças correspondente. Isso é avaliação da mesma fonte; não produz uma lei de sinal universal por si só.

Para positividade all-order, continua faltando uma propriedade independente que controle o sinal do resto conjunto nas direções nativas. O ledger de cabeça+cauda da #67 permanece válido, com todos os cruzamentos. Estas quatro caixas não resolvem esse problema global e não fornecem uma realização Gram infinita por retroajuste dos momentos.

**PASS:** quatro caixas da fonte original certificadas e transportadas ao determinante finito. Não há conclusão de positividade em toda ordem.
