# Jets nativos: recombinação positiva e residual variável

**Resultado: PARTIAL.** O próximo passo da PR #47 foi executado e ligado formalmente à PR #41: a identidade completa foi transportada aos stencils, à síntese canônica dos jets e às mesmas direções residuais da ortogonalização algébrica, com os dois argumentos independentes e todos os cruzamentos. Uma recombinação exata produz uma parte positiva determinada pelos pareamentos físicos existentes. O defeito restante não foi apagado: na primeira direção ele tem limite estritamente negativo, identificado com uma obstrução ambiente já provada. A positividade da soma em toda ordem continua aberta.

Branch `agent/native-jet-overlap-budget`, baseada em `cbedeeff67ffa8ec453ef7e28b7b799be4642dce`, da PR #47. A main consultada, depois de `git fetch origin`, permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Fonte nativa: `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. Alterações restritas a `research/native-jet-overlap-budget/`, sem merge automático.

## A — O que já estava demonstrado

A PR #47 fornece `CarryFiberTransport.radial_four_channel_overlap_identity` e `finite_radial_overlap_transport`: o defeito original de quatro canais, depois do Cauchy original, separa-se no defeito do consumidor com dois parâmetros e na correção de overlap. A identidade ainda precisava ser aplicada aos coeficientes físicos dos jets.

**A PR #41 é a camada algébrica desta linha de prova.** Foi consultada no commit `ee56930a2c30456cfbd214a29bb31b12d3977204`, branch `agent/native-moment-orthogonalization-audit`, ainda aberta e não integrada à main. Nela, `NativeMomentOrthogonalization.nativeResidualBoundary_energy` identifica a energia do bordo original com quatro vezes o pivô da eliminação polinomial, sem hipótese de sinal. `native_inverseSchur_boundary_energy` fornece a identidade correspondente para o vetor `(-A⁻¹b,1)`, exigindo somente `IsUnit A`. A base mônica existe sem positividade; ortogonalidade efetiva exige os pivôs anteriores não nulos. Whitening real para a identidade e alturas positivas são etapas posteriores, com suas obrigações próprias.

Nesta continuação os cinco módulos originais necessários da #41 são extraídos, sem alterações, desse objeto Git e recompilados por `prepare_pr41.py` em cache local. A PR #41 não foi modificada ou mesclada. O commit e os hashes dos cinco arquivos ficam em `evidence/pr41-source.json`. Não houve alteração de versões ou pins das bibliotecas.

O operador já fornece:

- `nativeSourceChiralJetInput` e `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`: a mudança de coordenadas e a igualdade dos DOIS canais completos antes de normas ou readouts;
- `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto`, `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` e `nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control`: limites polarizados e controle absoluto em cada dimensão finita, sem hipótese de sinal;
- `primeDepthGeometricMoment_eq_canonical`: igualdade em toda ordem com os momentos canônicos originais;
- `polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance`: comparação com a síntese de câmera existente, conservando o defeito;
- `radialDifferenceSource_pair`: os coeficientes de diferença recuperam o par incidente/retorno original;
- `canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess` e `canonicalCompletedC3NormalizedAmbientCentralExcess_pos`: o excesso central do candidato ambiente já era conhecido.

Os blocos H6/K6 e a realização de doze fontes já estão certificados no projeto. Sua positividade não é usada para demonstrar a identidade estrutural desta rodada.

## B — O que foi demonstrado agora

### B.1 — O overlap não diminui com a malha

Sejam `z_i` os pontos radiais antigos, `U_i` os vetores Cauchy antigos e

\[
a_i=\sqrt{2\operatorname{Im}z_i},\quad
C_{ij}=\langle U_i,U_j\rangle,\quad O_{ij}=a_i a_j C_{ij}.
\]

`observedCauchy_eq`, `radialOverlap_independent` e `radialOverlap_closed` provam

\[
a_iU_i=\sqrt{2(i+1)}\,u_i,
\qquad
\boxed{O_{ij}=\frac{\sqrt{2(i+1)}\sqrt{2(j+1)}}{i+j+2}.}
\]

Aqui `u_i` é a feature Cauchy preexistente em L²[0,1]. O índice radial desaparece exatamente. Trata-se da observação de comparação já determinada pelo consumidor, não de uma substituição da fonte ou de seus pesos.

Para coeficientes complexos independentes `c,d`, `complement_pairing` prova, depois da síntese,

\[
\sum_{i,j}\bar c_i d_j(1-O_{ij})
=\overline{\sum_i c_i}\sum_jd_j
-\left\langle\sum_i c_i a_iU_i,\sum_j d_j a_jU_j\right\rangle.
\]

`observedSynthesis_eq_zero_iff` conserva a injetividade dos coeficientes. Portanto `complement_zero_sum_strict` e `forwardStencil_complement_strict` provam que a forma `1-O` é estritamente negativa em todo stencil binomial antigo de ordem positiva. No primeiro stencil,

\[
\boxed{(-1,1)^*(1-O)(-1,1)=-2+\frac{4\sqrt2}{3}<0.}
\]

Este é um teste do kernel de overlap. Não determina sozinho o sinal da correção completa, que também contém os pesos de fonte e os pareamentos Gamma.

### B.2 — Transporte pelo MESMO mapa dos jets

Escrevemos `Γ_i` para a saída ambiente da fonte enriquecida original, `G_ij=<Γ_i,Γ_j>` e `d_ij` para o defeito do consumidor com seus dois parâmetros corretos. Para a entrada física `c`, o peso continua sendo exatamente

\[
\beta_i=\frac{c_i}{E_+(z_i)}.
\]

Definimos apenas as duas somas de contabilidade da identidade existente:

\[
\Delta(c,d)=\sum_{i,j}\bar\beta_i\gamma_j C_{ij}d_{ij},
\qquad
\mathcal E(c,d)=\sum_{i,j}\bar\beta_i\gamma_j(1-O_{ij})G_{ij}.
\]

`four_channel_split` e `source_balance_budget` identificam o balanço original, sem impor sinal a essas somas. Aplicando literalmente `c=nativeSourceChiralJetInput n k x` e o mesmo mapa a `y`, obtemos `jetBudget_eq_original_pairing`: o orçamento é exatamente a forma projetiva assinada dos dois vetores de jets completos.

`jetBudget_eventually_close` transporta o limite polarizado para

\[
\sum_{i,j}\bar u_i h_{i+j}v_j+
\sum_{i,j}\bar u'_i h_{i+j+1}v'_j,
\]

com as fases pares/ímpares já fixadas pela síntese nativa. Os cruzamentos mistos permanecem no cálculo finito e só desaparecem no limite provado. A formulação mantém explicitamente o domínio físico, em vez de inventar uma fonte fora do strip para totalizar a função.

`jetBudget_eventually_energy_control` prova, para toda dimensão finita fixa e todo `η>0`, eventualmente e uniformemente em `x`,

\[
\left|4\operatorname{Re}\mathcal Q_k(x,x)-
\operatorname{nativeSourceFiniteBoundaryEnergy}(2n,x)\right|
\le\eta\|x\|^2.
\]

Esse controle absoluto é transportado do teorema preexistente. Não é apresentado como novo mecanismo de sinal nem como coerção uniforme em toda ordem.

### B.3 — Uma recombinação positiva efetiva

`camera_sub_overlap_eq_damped` prova a operação exata

\[
G-(1-O)\odot G=O\odot G,
\]

incluindo todos os pesos e cruzamentos nas duas somas. `overlapMatrix_eq_gram` e `ambientMatrix_posSemidef` identificam os dois fatores como Grams de estados físicos já existentes. Pelo teorema de Schur, `dampedCameraMatrix_posSemidef` prova

\[
\boxed{O\odot G\succeq0.}
\]

Nenhum momento desejado determina esses vetores ou essa métrica. A positividade é desta parte identificada da expressão, não de outra Hankel escolhida para substituí-la.

Finalmente, `jetBudget_eq_damped_add_defect` e `dampedCameraBalance_self_nonneg` dão

\[
\boxed{\mathcal Q_k(x,y)=P_k(x,y)+\Delta_k(x,y),
\qquad P_k(x,x)\ge0.}
\]

O limite canônico está estabelecido para a SOMA. Não provamos convergência separada desses dois termos em todas as ordens, nem convergência de uma família infinita de vetores.

### B.4 — O teste central do residual

`CentralResidual.lean` usa uma única fonte verdadeira, com os coeficientes antigos do jet de ordem zero. O índice `4k+3` seleciona uma subsequência cofinal da malha ORIGINAL; `central_point_eq` prova que ela coincide com a malha ambiente antiga de uma fonte. Nenhum ponto ou peso foi ajustado.

`centralResidual_eventually_eq_negative_old_defect` identifica exatamente

\[
\Delta_k=-\operatorname{RegularizedAmbientRadialDslopeDefect}_k.
\]

Assim `centralResidual_tendsto_negative_excess` e `centralResidual_eventually_negative` provam

\[
\boxed{\Delta_k\longrightarrow h_0-
\|\operatorname{NormalizedAmbientResponseState}(0)\|^2<0,}
\]

e o residual é eventualmente estritamente negativo. A desigualdade do excesso central é reutilizada, não anunciada como descoberta desta rodada. O avanço é sua identificação com o residual que resta depois da nova recombinação.

### B.5 — Ligação formal com os resíduos da PR #41

`PR41Bridge.lean` importa as declarações originais recompiladas da #41. Para `x_(s,n)=nativeResidualBoundary s n`, `pr41_residual_exact_budget` substitui a mesma direção polinomial no orçamento completo. `pr41_residual_budget_eventually_close` prova, nos dois setores e em toda ordem,

\[
\boxed{\operatorname{Re}\,[P_k(x_{s,n},x_{s,n})+\Delta_k(x_{s,n},x_{s,n})]
\longrightarrow d_{s,n}.}
\]

Não há hipótese de sinal ou inversibilidade nessa identidade. Ela permanece válida para pivôs nulos ou negativos; isso não torna a família efetivamente ortogonal quando um pivô anterior é nulo.

`pr41_inverseSchur_budget_eventually_close` recupera analogamente `sourceMomentSchur` na direção crítica original por inversa. Sua única hipótese matricial é `IsUnit` do bloco antigo. Não se pressupõe prefixo positivo para justificar uma mera identidade.

Há duas quantidades distintas: `d_(s,n)` é o residual algébrico da ortogonalização; `Delta_k` é o defeito físico variável de transporte. O primeiro é o limite da SOMA `P_k+Delta_k`, não do defeito isolado. Assim, `Delta_k<0` no teste central não demonstra pivô negativo: nesse teste o limite da soma é `d_(0,0)=h0>0`.

A direção polinomial depende dos momentos já globais porque é uma leitura algébrica posterior à sua extração, como na #41. Ela é usada aqui como entrada de teste no mapa físico preexistente. Não é uma família de vetores construída retroativamente para fornecer uma Gram positiva dos próprios momentos.

## C — O que foi refutado

1. A correção `1-O` não pode ser descartada como erro que desaparece com a malha. O kernel é independente da escala e detecta estritamente todos os stencils binomiais de ordem positiva.
2. A estratégia de fechar esta decomposição provando `Δ>=0` em toda a família falha na própria fonte de ordem zero. O residual necessário é negativo nesse teste.
3. A parte positiva `P` não pode ser identificada sozinha com o alvo canônico: há uma correção efetiva já na primeira direção.

Nada disso demonstra uma direção negativa da Hankel canônica. No centro, a soma continua sendo `h0>0`, já certificado. A contribuição negativa retira o excesso do candidato ambiente, enquanto a positividade da soma em ordens arbitrárias permanece uma questão adicional.

## D — Kernel, regressões e lacuna atual

São **41 teoremas públicos e 15 definições/abreviações** novos, em seis módulos: `OverlapGeometry`, `JetBudget`, `DampedCamera`, `StencilObstruction`, `CentralResidual` e `PR41Bridge`. Os módulos originais reutilizados da #41 não entram nessa contagem de resultados novos.

A auditoria separa **47 raízes estruturais**, com 7.822 constantes transitivas de tipos e corpos, de **9 raízes do teste central**, com 6.662 constantes. Todos os resultados permitem apenas `propext`, `Classical.choice` e `Quot.sound`. O núcleo estrutural, incluindo a ponte com a #41, também rejeita dependência dos certificados finitos nomeados de positividade e de contratividade de sete fontes. O teste central reutiliza explicitamente o resultado de excesso ambiente, com suas comparações finitas já provadas.

As fixtures N4/N6 fornecidas pelo usuário são preservadas byte a byte, com hashes. `check_finite_regression.py` refaz as fatorações racionais exatas dos decimais e reproduz os cálculos de ponto flutuante nos mesmos parâmetros. A positividade racional refere-se aos decimais; o cálculo flutuante não fornece uma inclusão intervalar dos momentos verdadeiros.

As identidades de fonte e os testes estruturais novos são provas Lean. As matrizes e alturas N4/N6 são regressões finitas. Não há teorema de positividade canônica em toda ordem nesta entrega.

Os comandos e resultados de validação ficam em `evidence/checks.json`; a auditoria completa está em `evidence/kernel-Audit.log`. O procedimento recompila os módulos herdados necessários, os cinco arquivos originais da #41 e os módulos novos, executa `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e a regressão H6/K6/doze fontes, além dos testes numéricos e das verificações de preservação de arquivos e pins.

A rodada final concluiu **29 checks com código de saída zero**, incluindo a preparação da #41 e a compilação explícita da nova ponte. Os hashes em `evidence/source-sha256.json` identificam as fontes novas efetivamente validadas.

```bash
cd /home/thlinux/geometry-of-numbers
git fetch origin ee56930a2c30456cfbd214a29bb31b12d3977204
python3 research/native-jet-overlap-budget/validate.py
```

O fetch apenas disponibiliza o objeto imutável da PR #41 para checkouts que ainda não o tenham; não muda a branch nem faz merge. Os logs são escritos temporariamente fora do checkout e normalizados antes de entrar nas evidências, para que as próprias auditorias de whitespace não leiam um log parcialmente escrito.

## E — Próximo passo mínimo e resposta à pergunta principal

**Ainda não resolvemos a positividade canônica em toda ordem.** O transporte pedido pela PR #47 está concluído, a expressão positiva parcial foi identificada e a ponte com os resíduos da #41 foi formalizada. O sinal que falta está no balanço entre essa energia e a parte negativa do defeito variável, nas mesmas direções residuais.

A próxima obrigação é uma estimativa independente da fonte que controle essa subtração relativa a `P`, com os parâmetros variáveis e o Cauchy completo. Apenas assumir `Δ>=-P` não seria um mecanismo geométrico novo: pela identidade demonstrada, seria reafirmar o sinal desejado.

Também não basta restringir a linguagem a “coordenadas de jets”. O teorema preexistente `nativeSourceChiralJetInput_eventually_bijective` mostra que essa carta cobre todos os coeficientes originais em cada dimensão fixa. E `radialReturnTransfer_norm_le_one_iff_storage` identifica a contratividade com o sinal do storage. Reintroduzir uma dessas condições sem demonstrá-la seria circularidade, não solução.

A PR #41 permite focalizar o próximo teste: controlar a combinação completa **na direção residual canônica de cada setor e ordem**, em vez de exigir de início uma estimativa uniforme sobre todos os coeficientes físicos. Com um prefixo positivo já certificado, uma margem estrita nessa direção permite avançar pelo Schur. A identidade por inversa precisa somente da inversibilidade; o sinal continua sendo a obrigação a demonstrar.

Um candidato concreto seria uma cota de fonte `Delta_k(x_n,x_n) >= -P_k(x_n,x_n) + m_n - e_(n,k)`, com `m_n>0` obtido independentemente do pivô e `e_(n,k)->0` controlado a partir dos canais originais. Não demonstramos essa cota e não a recebemos como hipótese para anunciar sucesso. Uma margem relativa fixa não é exigida, preservando a distinção assintótica da PR #42.

Esse é o teste mais curto de uma futura lei física capaz de explicar por que o defeito NEGATIVO não consome toda a energia positiva. Ele deve ser derivado do transporte/retorno, não dos pivôs ou das alturas. Os blocos N4/N6 permanecem disponíveis como regressões dessa lei; aumentar sua ordem, isoladamente, não a demonstra.

Não foi alterada a fonte, a métrica, a câmera, o dressing, a normalização, os pins ou os arquivos históricos. Nenhuma worktree nova foi criada. As PRs anteriores permanecem intactas; esta continuação fica em branch e PR próprias, sem merge automático.
