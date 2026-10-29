# Jets físicos com duas regularizações: limite polarizado e teste da torre prima

**Classificação: PARTIAL na ponte canônica; NO-GO para a união radial bruta.**
24/10/2026. Repositório `thiagomassensini/geometry-of-numbers`.
Branch `agent/mixed-radial-jet-limit`, baseada exatamente no commit
`8a287232a55709fb79847033143978f555fa10b4` da PR #79.
A PR #79 e suas dependências continuam em branches próprias. A `main`
verificada foi `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Nenhum merge automático foi feito.

O alvo imediato do relatório anterior foi resolvido: calculamos o limite
**polarizado** do jet físico zero, com duas regularizações independentes.
Ele depende do caminho. A igualdade das diagonais não produz uma única
Gram positiva para a união dos estados radiais originais.

A nota nova das potências primas foi examinada em paralelo. Sua soma
positiva é um modelo auxiliar matematicamente legítimo, mas as fórmulas
literais propostas já falham nas entradas canônicas de ordens 1 e 2.
Esse teste foi formalizado sem modificar a fonte original.

## A — O que já estava demonstrado

1. `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`:
   a síntese dos jets é exatamente o par incidente/retornado original,
   com o mesmo mapa de coeficientes nos dois canais.
2. `projectiveChiralDifferenceJet` e
   `canonicalCompletedNativeProjectiveChiralForm`:
   jet por diferenças finitas e forma assinada nativos. O fator `1/2`
   da forma já existia; não foi escolhido nesta investigação.
3. PR #79, `CarryCompletedTrace.native_kernel_cross_factor`:
   comparação exata do pareamento entre duas grades com o kernel nativo,
   mantendo o fator geométrico misto `crossRadialFactor`.
4. `completedGreenDslope_tendsto_prod_of_analyticAt`:
   limite conjunto da diferença dividida de uma resposta analítica.
   É mais forte que a continuidade em cada argumento isolado.
5. `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical`:
   identifica a derivada central da resposta completada com o momento
   canônico. Não requer positividade all-order.
6. `canonicalCompletedNativeLogDerivativeMoment_zero_pos`:
   sinal de `h₀` demonstrado independentemente. Só os lemas tardios de
   obstrução utilizam esse sinal.
7. `CarrySixthOdd.mem_compactMomentBox`: caixas racionais já certificadas
   da mesma fonte theta, reutilizadas apenas no canário da nota prima.
8. PR #41, branch independente, head
   `ee56930a2c30456cfbd214a29bb31b12d3977204`, ainda draft aberta:
   energia do bordo residual original = quatro vezes o pivô de Schur,
   identidade **assinada**. Essa branch não foi importada implicitamente.
9. `primos` PR #47, merge
   `298a54f7be6111b6f83c4fee4de3bf3fed9f4a95`:
   `primeVerticalScale_prime_pow`, `vonMangoldt_prime_pow`,
   `sum_vonMangoldt_primeTower_eq_verticalScale` e
   `primeDepthLogCoordinate_eq_log`. São identidades aritméticas e de
   coordenadas; não identificam uma energia canônica com a soma positiva
   de potências primas da nota.

Foram consultadas as declarações originais, não apenas relatórios.
Os checkouts compartilhados do operador e de `primos` foram preservados,
inclusive seus arquivos modificados/não rastreados preexistentes.

## B — O que foi demonstrado agora

Todos os novos nomes abaixo pertencem a `CarryMixedRadial`.

### B.1 — O mesmo jet físico, com a normalização original

Definimos apenas abreviações/readouts dos objetos existentes:

\[
Z_k=\operatorname{projectiveChiralDifferenceJet}(k,0),\qquad
Q_{k\ell}=\tfrac12\bigl(\langle I_k,I_\ell\rangle
                      -\langle R_k,R_\ell\rangle\bigr).
\]

`zero_jet_original` identifica `Zₖ` com a primeira amostra projetiva
original. `zero_jet_boundary` prova que ele também é exatamente
`nativeSourceProjectiveBoundaryJetSynthesis 1 k ![1,0]`.
Portanto, não é um vetor reconstruído de `h₀` ou de uma fatoração Hankel.

`original_zero_balance_eq_twice_pairing` registra a conversão para a
convenção anterior sem `1/2`: o balanço polarizado incidente−retorno é
`2 * Q`. Assim, o limite diagonal desse balanço será `2 h₀`, como antes.

Sejam `κ=k+1`, `λ=ℓ+1`, `zₖ=i/κ`, `zℓ=i/λ`.
`zero_pairing_original` preserva a amplitude completada, o quociente de
retorno e o produto interno Cauchy originais. Sob a regularidade nativa
explícita — strip no primeiro ponto, `F` e coordenada chiral positiva não
nulas nos dois pontos — `zero_pairing_factor_kernel` demonstra:

\[
\boxed{Q_{k\ell}=\rho_{k\ell}\,K(z_k,z_\ell)},\qquad
\rho_{k\ell}=\frac{\sqrt\kappa\sqrt\lambda}{2}
              \left(\frac1\kappa+\frac1\lambda\right).
\]

`K` é **o** `canonicalCompletedNativePolarizedDslopeKernel`, da resposta
completada existente. Não é uma nova fonte. As condições de regularidade
são provadas eventualmente pelas declarações nativas já existentes.

### B.2 — Limite com duas entradas independentes

`native_kernel_limit` prova, para quaisquer sequências de índices `u,v`
que tendam ambas a infinito, inclusive sobre um filtro arbitrário:

\[
K(z_{u(a)},z_{v(a)})\longrightarrow h_0.
\]

A prova usa a analiticidade da resposta e o limite **conjunto** de
`dslope`. Não substitui a segunda entrada pela primeira.

`zero_pairing_limit_of_factor` então demonstra:

\[
\rho_{u(a),v(a)}\to\rho
\quad\Longrightarrow\quad Q_{u(a),v(a)}\to\rho h_0.
\]

A hipótese de convergência de `ρ` é geométrica, não um sinal presumido
para momentos. Nos dois testes concretos ela é descarregada exatamente:

| Caminho | Fator exato | Limite de `Q` |
| --- | --- | --- |
| `ℓ=k` | `1` | `h₀` |
| `ℓ=2k+1` | `3√2/4` | `(3√2/4)h₀` |

Teoremas: `diagonal_zero_limit`, `doubled_zero_factor`,
`doubled_zero_limit`. `doubled_zero_factor_gt_one` prova `3√2/4>1`.
Os índices aqui são de **regularização radial**, não câmeras, profundidades
Carry, ordens de jet ou níveis de uma torre prima.

### B.3 — Todos os cruzamentos e a diferença física

`difference_pairing_four_crosses` mantém os quatro termos ordenados:

\[
Q(Z_k-Z_\ell,Z_k-Z_\ell)
 =Q_{kk}+Q_{\ell\ell}-Q_{k\ell}-Q_{\ell k}.
\]

`zero_pairing_conj` prova a simetria hermitiana. Daí
`doubled_difference_limit` demonstra:

\[
\boxed{Q(Z_k-Z_{2k+1},Z_k-Z_{2k+1})
 \longrightarrow\left(2-\frac{3\sqrt2}{2}\right)h_0<0.}
\]

O sinal estrito e sua validade eventual são provados separadamente em
`doubled_difference_negative_eventually`, usando o sinal já conhecido
de `h₀`. As duas quadraturas complexas e os dois canais foram mantidos
até completar o pareamento; somente depois foi tomada a parte real.

### B.4 — Canário exato da nota prima

`native_two_lt_one_sixteenth` recompila das caixas existentes:

\[
h_2<h_1/16.
\]

Essa desigualdade já aparecia na PR #36. Sua reutilização não é anunciada
como uma nova descoberta. Não importamos o clock nem a branch da #36.

Para as fórmulas da nota, escreva `a=log p`, `0<q<1`:

\[
m_1=\frac{a^2q}{(1-q)^2},\qquad
m_2=\frac{a^3q(1+q)}{(1-q)^3}.
\]

`tower_closed_forms_gap` prova `m₂≥m₁/2` sempre que `a≥1/2`.
`prime_log_ge_half` descarrega esse requisito para todo primo, usando
`log p≥log 2>1/2`. Finalmente,
`prime_tower_closed_forms_not_native` demonstra, para **qualquer massa
positiva** `M`, que não podem valer simultaneamente:

\[
h_1=M m_1,\qquad h_2=M m_2.
\]

Isso é um teorema sobre as duas fórmulas literais fornecidas. Não foi
necessário criar outra sequência física nem formalizar uma medida
auxiliar infinita. A prova de soma positiva de toda ordem apresentada na
nota é um argumento matemático do modelo auxiliar; não foi apresentada
como nova formalização Lean nesta PR.

## C — O que foi refutado

**1. Limite conjunto bruto.** `no_joint_zero_limit` prova que não existe
`L` tal que `Qₖℓ→L` quando ambos os índices radiais tendem a infinito.
Ambos os caminhos usados na refutação são cofinalmente infinitos nas
duas coordenadas. A falha não depende de escolher um índice fixo.

**2. Gram positiva da união radial bruta.**
`no_hilbert_gram_for_raw_radial_union` exclui vetores em qualquer espaço
com produto interno complexo positivo cujos pareamentos sejam todos
esses `Qₖℓ`. A diferença física anterior teria norma quadrática negativa.
Equivalentemente, a matriz limite de dois estados é:

\[
h_0\begin{pmatrix}1&3\sqrt2/4\\3\sqrt2/4&1\end{pmatrix},
\qquad \det=-h_0^2/8<0.
\]

O coeficiente `1−(3√2/4)²=−1/8` foi provado em
`doubled_factor_determinant`. Trata-se de uma **forma assinada** de dois
canais, não de uma norma Hilbert negativa. O NO-GO refere-se à união sem
transporte dos estados radiais, não à Hankel canônica nem a todas as
realizações físicas possíveis.

**3. Identificação literal com a torre positiva da nota.** As entradas
`h₁,h₂` já impedem essa identificação; aumentar ordem, cutoff ou precisão,
ou multiplicar por uma massa positiva, não corrige o conflito. Isso não
refuta o papel aritmético das potências primas, nem um transporte original
que inclua Green, retorno, bordo e completion.

Nada disso contradiz os certificados finitos H6/K6 ou as realizações de
jets dentro de cada grade. Tampouco converte a identidade assinada da
PR #41 numa afirmação de sinal. Uma identificação entre diferentes
regularizações requer uma lei adicional comprovada.

## D — O que permanece aberto

Não foi construída uma Gram positiva all-order dos momentos canônicos.
Não foi demonstrado um transporte físico entre regularizações que
preserve a fonte completa e forneça os cruzamentos canônicos.
Não se provou que todas as energias residuais da PR #41 são positivas.

O primeiro defeito agora está determinado, já no jet zero:

\[
Q_{k\ell}-K(z_k,z_\ell)
 =(\rho_{k\ell}-1)K(z_k,z_\ell).
\]

No caminho duplo seu limite é `(3√2/4−1)h₀>0`. Não é um erro de
aproximação que desapareça. Dividir os cruzamentos por `ρ` produziria
outro pareamento sem uma justificação física; não fizemos essa operação.

A massa unitária auxiliar e a independência de polinômios numa torre
prima não descarregam esse defeito nem o sinal do bordo canônico.
O sinal all-order continua sendo uma obrigação da fonte completada.

## E — Próximo passo mínimo e validação

O próximo teste útil é buscar **no Green/TFVD original**, em seu domínio
físico, uma lei vetorial de transporte entre regularizações. Seu primeiro
caso obrigatório é explicar o defeito `(ρ−1)K` acima por uma identidade
original de interior/retorno/bordo, conservando o complemento. Deve
reproduzir o cruzamento `h₀` entre as duas regularizações antes de tentar
jets superiores. Uma identificação que preserve literalmente todos os
`Qₖℓ` brutos já foi refutada; não deve ser tentada novamente.

É preciso distinguir um transporte que atua em cada representação de
uma única isometria global que conservaria o pareamento bruto. A segunda
não pode remover a obstrução demonstrada. Qualquer candidato à primeira
deve ser derivado da geometria, e não definido multiplicando um kernel
pelo fator inverso desejado. Só depois dessa identidade cabe retomar os
jets `(0,1)` e `(1,1)` e o residual geral da #41.

**Resultado formal:** 25 teoremas, duas definições e uma abreviação, em
quatro módulos. As 28 raízes públicas foram auditadas por `#print axioms`
e pela inspeção transitiva de tipos **e corpos**: 5.572 dependências.
Somente `propext`, `Classical.choice`, `Quot.sound`; não se reivindica
footprint vazio na camada analítica.

A auditoria separa construção sem momentos (12 raízes), identificação
analítica sem sinais finitos (6), obstrução usando apenas o primeiro sinal
nativo (5) e canário das fórmulas primas/caixas theta (5). Os lemas de
construção não dependem de momentos definidos por uma Gram, Cholesky,
alturas, sinais H6/K6 ou da positividade all-order.

Validação: 15 comandos com saída zero, incluindo compilação explícita
dos quatro módulos e do audit, build de fontes usadas no operador,
recompilação de `OddSourceBoxes`, `lake build --wfail` na raiz e auditorias
Foundation/Geometry/Analysis. Oito módulos ancestrais foram recompilados
de fontes idênticas ao commit base. Não foram adicionados `sorry`,
`admit`, `native_decide` ou axiomas. Fontes, amplitudes, pins e arquivos
históricos foram preservados.

Reprodução no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

Os scripts usam os mesmos checkouts e dependências Lean já existentes;
não instalam bibliotecas nem alteram pins. Logs, comandos, códigos de
saída, hashes dos fontes e SHAs dos repositórios estão em `evidence/`.
`GOAL_STATUS.md` mantém explícita a obrigação global ainda aberta.

**FIM DO RELATÓRIO — PARTIAL; NO-GO da união radial bruta e do modelo primo literal, não da geometria Carry.**
