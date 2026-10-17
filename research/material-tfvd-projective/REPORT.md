# TFVD e válvula projetiva na fonte material efetiva

## Resultado

A passagem aditiva → multiplicativa funciona exatamente nas fibras físicas
do Carry. Foi construída uma codificação fiel do carrier completado existente
por **bordos e massas projetivas de todas as fibras**, mantendo semente,
arestas residuais e retorno global. O produto interno real original pode ser
avaliado por essa codificação, com parâmetros independentes e todos os quatro
cruzamentos Green/retorno.

Isso é uma reconstrução em outras coordenadas. **Não identifica esse produto
interno com o kernel canônico e não resolve a positividade do residual.**

Há também um teste canônico exato: a massa da fibra real de núcleo 1 e direção
0, no tempo 0, não coincide diretamente com a massa canônica em altura ao
quadrado. A primeira curvatura dessa fibra é estritamente negativa, enquanto
o primeiro momento canônico é positivo. A obstrução se restringe à comparação
direta dessas duas séries; não exclui uma síntese conjunta das fibras.

## Fonte e proveniência

Base do trabalho: `geometry-of-numbers`, `main` em
`31e8ff082cccac2a881180eb3b079824591e22d3` (PR #16).
O operador foi consultado sem alterações em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

| Infraestrutura reutilizada | Declaração | Commit de proveniência |
| --- | --- | --- |
| TFVD real, com traços | `realCarryTfvdSynthesis_comp_analysis` | `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f` |
| Classificação por bordo e massa | `realDiscreteProjectiveReconstructionEquiv` | `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f` |
| Coordenadas físicas e quatro cruzamentos | `carryMaterialTfvd_coordinate`, `carryMaterialTfvd_edge_pairing` | `36718e438c1fa1d738ffa7e0c6ad6fd9310bf06f` |
| Ponte escalar dos momentos | `projectiveValveMass_nativeMoments_eq_reciprocal` | `643b917046891f9a119b2e05bd2ecb197bc4bce2` |
| Naturalidade C3 | `canonicalCompletedC3ValveNaturality` | `18cccf54effd8ab3ce99833507adcb7fcf934430` |

Os nomes de geometry acima pertencem a `GeometryOfNumbers.Analysis`, com
subnamespaces `DiscreteProjective` e `ProjectiveValve` quando indicados no
código. Os nomes do operador pertencem a `CarrySelfAdjointOperator`.
`new-roots.json` registra os nomes e posições dos resultados novos.

## 1. De onde vem a curvatura

Seja `g` o gradiente material já existente, reindexado pela incidência C2.
Para núcleo `m`, direção `a`, quadratura real `r` e profundidade coordenada `j`,
escrevemos

\[
x_j=(\operatorname{baseTwoPhysicalEdgeC2State}g)_{m,a,j,r},
\qquad v_j=\eta^{-j}x_j.
\]

O gauge inverso é **pontual**. Não se declara que ele seja limitado em ℓ²,
nem que a sequência `v` pertença a ℓ². A razão crítica permanece exatamente a
existente: `eta = criticalVerticalAmplitudeRatio 2 = 2^(-1/2)`.

A curvatura e a massa são

\[
C=\operatorname{toProjective}(\operatorname{mk}(\Delta^2 v)),
\qquad A=\mathcal V(C),\quad A(0)=1,\quad A'=CA.
\]

O novo teorema `carryMaterialProjective_bracket` verifica o índice:

\[
(B_\eta x)_{j+1}=\eta^{j+1}(\Delta^2v)_j.
\]

Assim, `C` é extraída do bracket TFVD da fibra efetiva, não de um Gram-alvo.
O índice `j` é profundidade coordenada da fibra; a profundidade física é `j+2`.
Ele não foi identificado com índice material, tempo ou ordem de jet.

## 2. A soma torna-se produto, sem perder o bordo

Para dois canais materiais `g,h`, os teoremas novos demonstram

\[
C(g+h)=C(g)+C(h),\qquad A(g+h)=A(g)A(h).
\]

São massas escalares reais por fibra e quadratura. Não é uma identidade
para matrizes não comutativas.

O TFVD dá `x=G+R`. Após retirar o gauge,

\[
\eta^{-j}R_j=x_0+j(\eta^{-1}x_1-x_0).
\]

Portanto a segunda diferença do retorno é zero e sua massa é **1**. A massa
da fibra completa coincide com a massa da parte Green, mas seus bordos não
podem ser descartados. O teorema
`carryMaterialProjective_source_return_invisible` comprova isso na própria
fonte: no núcleo 1, direção 0, quadratura real, tempo 0, a massa do retorno é
1 e seu valor no primeiro endereço é estritamente negativo.

Isso não significa energia nula do retorno. Significa que a válvula, sozinha,
não o observa. O retorno de traço TFVD continua distinto do retorno global.

## 3. Codificação fiel e pareamento completo

Cada fibra guarda o dado já existente

\[
d=(v_0,\ v_1-v_0,\ A),\qquad
\xi(d,j)=\eta^j\operatorname{reconstruct}(d)_j=x_j.
\]

`carryMaterialProjectiveEncode` guarda esses dados de **todas** as fibras e
duas quadraturas, além da semente, projeção residual e retorno global.
`carryMaterialProjectiveEncode_injective` prova sua injetividade para
`eta ≠ 0`. O espaço desses dados não recebe uma nova norma ou produto interno.
A codificação de massas é não linear.

Para os estados originais `y,z`, `carryMaterialProjective_full_pairing` prova

\[
\langle y,z\rangle_{\mathbb R}
=\langle s_y,s_z\rangle_{\mathbb R}
+\sum_i\sum_{r=0}^1\xi(d_y,i,r)\xi(d_z,i,r)
+\langle g_y^{res},g_z^{res}\rangle_{\mathbb R}
+\langle\beta_y,\beta_z\rangle_{\mathbb R}.
\]

A soma usa todos os endereços físicos já presentes no carrier ℓ². Sua
validade vem desse carrier original, sem completar um espaço artificial de
massas. `carryMaterialProjective_source_pairing` especializa a identidade a
`Y_t,Y_u` com tempos independentes.

`carryMaterialProjective_crossings` preserva, inclusive entre endereços e
quadraturas distintos,

\[
\xi_y(i,r)\xi_z(j,s)=GG+GR+RG+RR.
\]

O resultado é real. As duas quadraturas e seus cruzamentos permanecem
disponíveis; não foi substituído o estado por sua energia diagonal.

A compatibilidade com o relógio é demonstrada por
`carryMaterialProjective_profile_hasDerivAt`, em cada endereço fixo:

\[
\frac{d}{dt}v_j(t)=\eta^{-j}
  (\operatorname{baseTwoPhysicalEdgeC2State}(-i\,g^{clock}_t))_{m,a,j,r}.
\]

Usa-se o gradiente relógio existente, com sua conexão material. Não se
postula diferenciabilidade forte do estado global em ordens superiores.

## 4. Comparação canônica e defeito explícito

`real_valve_eq_operator_valve` prova, pela unicidade da mesma EDO normalizada,
que as válvulas dos dois repositórios são iguais sobre `PowerSeries ℝ`.

Sejam `Q=mk canonicalCompletedNativeLogDerivativeMoment` e
`B=normalizedCompletedNativeEvenFormalSeries⁻¹`. A ponte escalar existente dá
`B=V(Q)`. Para a comparação direta da massa de uma fibra:

\[
A=B\iff C=Q.
\]

Isso é um teste explícito de identificação entre o parâmetro projetivo de
profundidade e a variável de altura ao quadrado. Nenhum mapa geométrico entre
essas variáveis foi presumido.

Para `delta=A-B`, os novos teoremas fornecem

\[
\delta_0=0,\qquad
\delta'=C\delta+(C-Q)B,
\]

\[
\delta_1=\eta^{-2}x_2-2\eta^{-1}x_1+x_0-h_0.
\]

Esta `delta` é a **diferença de massas formais desta comparação**, não o kernel
`carryMaterialRealResidual` nem o defeito Green de quatro canais.

O canário usa a fonte efetiva: os endereços `j=0,1,2` da fibra de núcleo 1 e
direção 0 correspondem às arestas materiais `2,6,14`. Com o gauge crítico,
tempo 0 e quadratura real:

\[
C_0=\frac{2\sqrt2}{\sqrt7}-\frac2{\sqrt{15}}-\frac1{\sqrt3}<0<h_0.
\]

A prova do sinal usa limites racionais exatos, sem decimais:
`2 sqrt(2)/sqrt(7) < 15/14`, `2/sqrt(15) > 1/2` e
`1/sqrt(3) > 4/7`.

Logo a massa dessa fibra individual não é `B`, e seu primeiro coeficiente de
defeito é negativo. Não há mudança de constante que tenha sido aplicada para
fechar essa calibração. Nenhum sinal negativo foi atribuído à energia física.

## 5. Onde permanece a obrigação

**Fonte disponível → transformação existente → destino → igualdade ausente:**

`Y_t` completo → incidências C2 + TFVD + codificação fiel por bordo/massa →
todos os dados físicos reconstruíveis → identificação de seu balanço Green
completo com o pareamento normalizado que produz os momentos canônicos.

O readout escalar já está identificado: o resultado anterior
`CarryMaterialCanonicalComparison.material_response` iguala a resposta da
fonte completa à característica canônica. Esta rodada não apresenta essa
igualdade antiga como uma nova descoberta.

O que falta é a compatibilidade **bilinear** da síntese conjunta, com
normalização e correções existentes. A identificação direta de cada fibra
com a mesma série canônica é inadequada; o canário demonstra uma falha
específica dessa tentativa. Ainda não foi construído um transporte do
pareamento físico para o Gram canônico. A positividade do balanço normalizado
do PR #16 permanece aberta.

## Status e validação

| Status | Resultado |
| --- | --- |
| PROVADO EM LEAN | Curvatura efetiva, gauge e bracket com índice correto |
| PROVADO EM LEAN | Soma de canais → produto de massas |
| PROVADO EM LEAN | Retorno real não nulo com massa unitária |
| PROVADO EM LEAN | Codificação fiel do carrier completo e pareamento real |
| PROVADO EM LEAN | Quatro cruzamentos e derivada escalar por endereço |
| PROVADO EM LEAN | Mesma válvula nos dois repositórios e EDO do defeito |
| OBSTRUÍDO | Identificação direta da massa da fibra canário com a canônica |
| ABERTO | Transporte do pareamento conjunto para o Gram canônico |
| ABERTO | Positividade do residual normalizado e de toda a hierarquia |

Comandos e resultados finais constam em `validation.json`; os logs de sucesso
ficam em `evidence/`. As auditorias transitivas usam `Lean.collectAxioms`, por
declaração, e `#print axioms`; Analysis admite apenas `propext`,
`Classical.choice`, `Quot.sound`. Foundation mantém sua política vazia e
Geometry sua política própria. Não se introduziram `sorry`, `admit` ou axiomas.

Nenhuma métrica, peso, fonte, pin, operador, normalização canônica ou módulo
dos outros repositórios foi alterado. Esta rodada não usou experimentos
numéricos como entrada de prova.
