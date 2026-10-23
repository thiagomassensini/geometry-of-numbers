# Caixas dos sete jets Gamma da característica nativa

**PARTIAL.** Foi resolvida a parte Gamma da obrigação de avaliação da PR #67: para os sete coeficientes fatoriais da **Gamma original**, o Lean demonstra caixas complexas com erro absoluto de até **10⁻¹⁸**. A prova vem da integral de Euler, de uma aproximação finita explícita e de aritmética racional reduzida pelo kernel.

**As quatro caixas da característica completa F ainda não foram demonstradas.** Não há novo sinal canônico, nova positividade Hankel all-order ou identificação positiva de kernels. A novidade é uma avaliação incondicional de um fator original que antes só tinha cotas superiores largas.

Base: `d9801859b15ae0daf4723e8b3e3b4de556d34b4e`, HEAD da PR #67.
Branch: `agent/c3-gamma-jet-enclosures`, empilhada sobre `agent/tfvd-two-even-jet-determinant`, sem merge automático.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
Operador consultado, sem alterações: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

- `CarryTwoEvenJets.completedTrace_head_tail` conserva os dois traços do estado TFVD enriquecido antes da observação: `(F,-F') = headTrace + tailTrace`.
- `full_even_jets_head_tail`, `odd_jets_head_tail_cancel` e `native_two_even_tfvd_ledger` conservam cabeça, cauda e os cruzamentos originais. Não autorizam declarar uma cabeça par nem apagar sua cauda.
- `canonical_two_even_det_pos_of_four_jet_boxes` demonstra que caixas absolutas 10⁻¹² para os quatro coeficientes completos f₀,f₂,f₄,f₆, nos centros racionais da #67, bastam para `h₀h₂−h₁²>0`. A inclusão da fonte verdadeira nessas caixas continuava aberta.
- `CarryReadoutBounds.complex_gamma_norm_le_real` e `real_gamma_le_inverse` já controlavam o tamanho da Gamma. Não localizavam seus valores ou derivados em intervalos estreitos.
- A PR #41 identifica a ortogonalização algébrica e o residual de Schur sem pressupor seu sinal. Esta etapa não utiliza seus pivôs positivos como premissas.

O argumento Gamma é literalmente o de `nativeXiCompletionFactor`: se s(w)=1/2+iw, então

$$G(w)=\Gamma(s(w)/2)=\Gamma(1/4+iw/2).$$

Não se usou uma Gamma de outra câmera por analogia. `native_xi_gamma_factorization` e `c3_value_multiplier_gamma_factorization` conferem essa proveniência por igualdade com as definições existentes, conservando o fator polinomial, a exponencial com log π e o chart C3.

## B — O que foi demonstrado agora

Todos os nomes novos pertencem a `CarryC3Gamma`.

### 1. Avaliador finito da própria integral de Euler

`EulerGamma.lean` mantém a integral original da Gamma. Em `gamma_tail_bound`, para T≥1 e Re z≤1, toda a cauda satisfaz

$$\left\|\int_T^\infty e^{-x}x^{z-1}\,dx\right\|\le e^{-T}.$$

O majorante vem de x^(Re z−1)≤1 para x≥T≥1. A cauda não é omitida.

`exp_head_error` usa o resto complexo certificado da exponencial. `gamma_compact_error` integra o erro na parte compacta, incluindo a singularidade integrável em zero. Para 0<Re z≤1, T≥1 e T/(N+1)≤1/2, `gamma_integral_approx_error` fornece

$$\|\Gamma(z)-P_{N,T}(z)\|
\le \frac{2T^{N+1}}{N!\operatorname{Re}z}+e^{-T}.$$

`gamma_head_integral_formula` avalia exatamente a integral do polinômio:

$$P_{N,T}(z)=T^z\sum_{k=0}^{N-1}\frac{(-T)^k}{k!(z+k)}.$$

`euler_term` prova a igualdade termo a termo antes da integração. `gamma_finite_error` transporta o mesmo erro à fórmula finita. Não há aproximação numérica recebida como hipótese.

### 2. Erro uniforme e erro de todos os jets normalizados

Escolhemos T=81 e N=512 somente como parâmetros de avaliação da integral. **T não é profundidade vertical, endereço material ou cutoff C3; N não é ordem Hankel.** A escolha 81=3⁴ permite avaliar exatamente o prefator no centro: 81^(1/4)=3.

`exp_neg_eighty_one_bound` e a desigualdade racional do resto dão

$$e^{-81}\le10^{-33},\qquad 16\,81^{513}/512!\le10^{-100}.$$

Logo `gamma_finite_512_error` prova, em toda a faixa 1/8≤Re z≤1,

$$\|\Gamma(z)-P_{512,81}(z)\|\le10^{-32}.$$

`native_gamma_argument` confere que o argumento original pertence a essa faixa no disco |w|≤1/4. `native_gamma_uniform_error` aplica o resultado ao mesmo G(w), sem alterar seu argumento.

As regularidades de G e do avaliador finito no disco aberto |w|<1/2 são provadas em `native_gamma_analytic` e `finite_gamma_analytic`. Cauchy fornece `native_gamma_jet_error`, para todo r fixo:

$$\left\|\frac{G^{(r)}(0)}{r!}-\frac{P^{(r)}(0)}{r!}\right\|
\le4^r\,10^{-32},\quad P(w)=P_{512,81}(1/4+iw/2).$$

É controle de erro analítico, sem hipótese de sinal dos momentos.

### 3. Avaliação racional efetiva dos sete valores

`native_gamma_power_formula` prova o prefator exato

$$81^{1/4+iw/2}=3\exp(2iw\log3).$$

Defina as somas finitas racionais

$$R_l=\sum_{k<512}\frac{(-81)^k}{k!(k+1/4)^{l+1}}.$$

`finite_native_gamma_coefficient` demonstra, sem diferenciar uma aproximação flutuante,

$$\frac{P^{(r)}(0)}{r!}=3i^r\sum_{j=0}^{r}
\frac{(2\log3)^j}{j!}\left(-\frac12\right)^{r-j}R_{r-j}.$$

As grandes parcelas alternadas são combinadas em aritmética racional antes do arredondamento. `rational_coefficient_boxes` verifica as sete somas exatas. `log_three_box` certifica log 3 por sua série com resto explícito; não recebe um decimal da biblioteca numérica.

`gamma_rational_boxes` verifica os centros finais. `real_gamma_polynomial_error` controla conjuntamente a propagação do erro em log 3 e nos R_l. As fases i^r e as duas quadraturas são conservadas até a norma complexa final.

O resultado incondicional principal é:

`native_gamma_seven_boxes (r : Fin 7)`

$$\boxed{\left\|G^{(r)}(0)/r!-i^r q_r\right\|\le10^{-18}.}$$

Os centros reais q_r, multiplicados pela fase i^r, são os seguintes decimais finitos exatos:

| r | q_r |
|---:|---:|
| 0 | 3.6256099082219083119306851 |
| 1 | −7.6635487085783518164820007 |
| 2 | 15.8931748887619764984312977 |
| 3 | −31.9492391787097771150216316 |
| 4 | 63.9802931920930082298478094 |
| 5 | −127.9918916464207390365214969 |
| 6 | 255.9967530306344417982917702 |

Esses são coeficientes **Gamma**, não os quatro coeficientes f₂ⱼ de F. Os números não redefinem a fonte. Os centros exatos e as tolerâncias estão em `LogGammaData.lean` e `GammaValueBoxes.lean`.

## C — O que foi refutado ou delimitado

Não há novo no-go físico. Não foi refutada a positividade dos momentos, a síntese TFVD ou uma realização Gram completada.

Também não se demonstrou que a positividade das normas, da Gamma real central ou dessas caixas determine o sinal do balanço Green. O balanço completo continua contendo os cruzamentos, o retorno e as correções originais.

Uma caixa de G não é uma caixa de F: faltam a composição com a exponencial envolvendo π, o chart C3 e a soma completa das células. Não se usaram números mpmath, um resto Taylor/EM não demonstrado, caixas theta, zeros, alturas ou uma Hankel-alvo como entradas da prova nova.

Não se transportaram as envoltórias base dois para a câmera C3 sem igualdade. A prova do avaliador Gamma é independente de câmera; a identidade de seu argumento com o fator nativo é conferida separadamente.

## D — Kernel, dependências e reprodução

São **33 teoremas e 15 definições, em 48 raízes públicas**, distribuídos por oito módulos matemáticos, mais `Regression.lean` e `Audit.lean`. A auditoria gerada inventaria todas as declarações públicas, imprime `#print axioms` e percorre tipos e corpos transitivamente. O guard permite somente `propext`, `Classical.choice`, `Quot.sound` e rejeita os consumidores posteriores de positividade especificados no código. Os fechamentos por grupo visitaram 4.642, 4.642, 5.021, 3.135, 633, 1.674, 5.043 e 4.645 constantes. Há sobreposição entre eles; esses números não devem ser somados como constantes distintas.

As reduções das somas finitas usam `decide +kernel`, sem avaliação nativa como atalho de confiança. Os resultados Python `Fraction` são regressões independentes; não são importados como provas.

**Validação final: 20/20 verificações locais passaram**, com código de saída zero: geração da auditoria, dez módulos explícitos com `warningAsError`, regressão racional, builds focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/Analysis, regressão das doze fontes, preservação histórica e `git diff --check`. Comandos e tempos: `evidence/checks.json`. Logs ficam em `evidence/`. O manifesto `source-sha256.json` registra os hashes dos arquivos publicados. Não se confunde essa validação no host llm com um resultado de CI externo.

Reprodução no ambiente preparado dos ancestrais, host llm:

```bash
cd /home/thlinux/geometry-of-numbers
git switch agent/c3-gamma-jet-enclosures
python3 research/c3-gamma-jet-enclosures/validate.py
```

`compile_module.sh` explicita os caches ancestrais. Não se reivindica bootstrap de clone vazio com esses caches ausentes. `check_rationals.py` reproduz exatamente as somas, os centros e os orçamentos, sem produtor transcendental de momentos.

Main, refs anteriores, módulos históricos, fontes, métricas, amplitudes, câmeras, pins, worktrees e arquivos não rastreados preexistentes são preservados. Nenhuma worktree nova foi criada. A branch é entregue sem merge automático, conforme a orientação do usuário.

## E — Próximo passo mínimo

O componente **Gamma e seus sete valores 0…6 já tem caixas rigorosas**. Não é mais necessário recebê-los como hipóteses nem refazer sua avaliação por mpmath.

A obrigação restante da #67 continua sendo a inclusão do mesmo F nas quatro caixas. Para concluí-la:

1. Certificar os sete jets dos fatores elementares restantes de Xi/chart: o polinômio original, a exponencial com log π e o inverso do chart C3, com seus não anulamentos já existentes.
2. Avaliar os sete jets do prefixo literal C3 e provar o resto acelerado da **mesma cauda C3**. A aproximação Taylor/EM do experimento anterior ainda precisa de seu certificado analítico; a concordância numérica entre cutoffs não o substitui.
3. Combinar esses intervalos e as caixas Gamma por convolução finita na identidade completa de cabeça+cauda da #67. Só então aplicar `canonical_two_even_det_pos_of_four_jet_boxes`.

A menor etapa de análise infinita que permanece é uma **cota certificada para os sete jets do resto C3 acelerado** no cutoff escolhido. Os parâmetros precisam ser selecionados pelo orçamento das quatro caixas, sem apagar a cauda ou tratá-la como livre.

Mesmo quando essa seção finita for fechada, continuará aberta uma propriedade independente da fonte que oriente o sinal em toda ordem. Esta etapa fornece avaliação rigorosa de um fator original; não transforma uma condição de sinal em lei geométrica.

**PARTIAL:** sete caixas Gamma incondicionais demonstradas; quatro caixas de F e positividade all-order continuam abertas.
