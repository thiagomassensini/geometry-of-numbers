# Retorno global polarizado nas coordenadas da válvula

## Resultado

A relação de grafo do retorno global foi transportada para as coordenadas da
válvula do PR #17, usando a mesma fonte e o domínio do relógio existente.
Também foram formalizados o retorno clockado, a polarização complexa finita,
os quatro termos de prefixo/cauda, a estimativa do erro de produto e o limite
bilinear com cutoffs independentes.

A reconstrução conjunta fornece a expressão Green completa de ordinary,
clock e dressing. Sua comparação com o residual do PR #16 conserva a
subtração do complemento oculto e todos os fatores assinados. Nenhum fator
que possa se anular foi dividido.

**O resultado é uma ponte bilinear de representação. Não é prova de
positividade, isometria com o Gram canônico ou construção de operador.**

Base: `geometry-of-numbers`, `main` após PR #17,
`4d84edfd53e7e6d5cd087c6b1c7c1349e99dce05`.
Operador consultado, sem alterações:
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

## A. Arestas e relação de grafo

Os módulos novos são:

- `GeometryOfNumbers/Analysis/CarryMaterialProjectiveGlobalReturn.lean`;
- `GeometryOfNumbers/Analysis/CarryMaterialProjectiveReturnGreen.lean`.

Todos os nomes abaixo, salvo indicação, pertencem a
`GeometryOfNumbers.Analysis`. O inventário `new-roots.json` registra seus
nomes completos, tipos de declaração e linhas.

`carryValveEdge eta y k s` é definido reconstruindo as duas quadraturas reais
em `baseTwoPhysicalEdgeC2Address (k,s)` e usando os mapas existentes
`realPlaneHilbertEquiv` e `realPlaneToComplexIsometry`.

Para `eta ≠ 0`, `carryValveEdge_eq` prova

\[
E_\eta(y,k,s)=g_y(\operatorname{baseTwoPhysicalEdgeIndex}(k,s)).
\]

Com `carryValveCell = E(k,1)-E(k,0)`, `carryValveCell_eq` identifica a função
inteira com `completedBoundaryCellReturnCoordinates y`.
`carryValveReturn_graph` transporta diretamente o `HasSum` já contido no
domínio original para `globalReturn (carryMaterialProjectiveEncode eta y)`.
Nenhuma condição foi acrescentada a um ledger arbitrário.

Na fonte efetiva `Y_t`, `carryValveCell_source` recupera a célula centro–pernas
original, e `carryValveReturn_source` fornece a soma do retorno ordinary
`carryValveBeta t = baseTwoCompletedBoundaryValue t`.

## B. Saída clockada

`carryValveReturn_clock_graph` usa
`completedBoundaryTransportedClock_image_boundary` para a saída `L y`.
Não afirma `L y ∈ domain L` e não itera o operador.

`carryValveReturn_clock_source` e `carryValveKappa_eq_tsum` identificam

\[
\kappa(t)=\operatorname{baseTwoCompletedBoundaryClockReturn}(Y_t)
=\sum_k c_\eta(LY_t,k).
\]

`carryValveEdge_clock` conserva a coordenada do relógio original. Em uma
aresta material `j`, ela contém exatamente

\[
\log(j+2)g_j+
\bigl(\log(j+2)-\log(j+1)\bigr)
\left(s+\sum_{r<j}g_r\right).
\]

Não foi substituída por uma multiplicação diagonal de `g_j`. Nenhuma derivada
forte adicional do estado global foi postulada.

## C. Polarização real e complexa

Para dois estados, inclusive `Y_t,Y_u` com tempos independentes,
`carryValveCell_polarized` prova

\[
\overline{c_k(y)}c_l(z)=
\overline{E_{k1}(y)}E_{l1}(z)
-\overline{E_{k1}(y)}E_{l0}(z)
-\overline{E_{k0}(y)}E_{l1}(z)
+\overline{E_{k0}(y)}E_{l0}(z).
\]

Cada aresta usa seu próprio endereço decodificado. Não se presume que as
duas arestas da célula pertençam à mesma fibra C2.

`carryValveRealCross` nomeia os quatro termos **existentes** GG, GR, RG e RR
para endereços e quadraturas independentes; `carryValveRealCross_eq` é o
crosswalk do teorema `carryMaterialProjective_crossings` do PR #17.
`carryValveEdge_polarized` conserva as duas partes do produto complexo:

\[
\operatorname{Re}(\bar E_yE_z)=C_{00}+C_{11},\qquad
\operatorname{Im}(\bar E_yE_z)=C_{01}-C_{10}.
\]

Cada `C_rs` contém GG + GR + RG + RR.
`carryValveCell_tfvd_polarized` junta os quatro sinais das arestas com essas
expansões completas. `carryValveReturnPrefix_tfvd` fornece o ledger finito
com todos os pares ordenados de células e cutoffs `M,N` distintos.

## D. Prefixos, caudas e limites

`carryValveReturnPrefix eta y M` soma as primeiras `M` células reconstruídas.
`carryValveReturnTail` é o retorno armazenado menos esse prefixo. Essa
diferença não substitui a definição geométrica do retorno: a relação de grafo
foi transportada antes.

`carryValveReturn_tail_ledger` prova, para estados completos `y,z`,

\[
\overline{\beta_y}\beta_z=
\overline{\beta_{y,M}}\beta_{z,N}
+\overline{\beta_{y,M}}\tau_{z,N}
+\overline{\tau_{y,M}}\beta_{z,N}
+\overline{\tau_{y,M}}\tau_{z,N}.
\]

`carryValveReturn_product_error` prova

\[
\left|\overline{\beta_y}\beta_z-
\overline{\beta_{y,M}}\beta_{z,N}\right|
\le |\beta_{y,M}||\tau_{z,N}|+
|\tau_{y,M}||\beta_{z,N}|+|\tau_{y,M}||\tau_{z,N}|.
\]

Os teoremas `carryValveReturn_prefix_tendsto` e
`carryValveReturn_clock_prefix_tendsto` reutilizam os `HasSum` transportados.
`carryValveReturn_tail_tendsto_of_hasSum` e
`carryValveReturn_error_tendsto_of_hasSum` dão os limites nulos respectivos.

O filtro bilinear é `atTop ×ˢ atTop` sobre `Nat × Nat`, sem impor `M=N`.
Há especializações para os quatro produtos ordinary/ordinary,
ordinary/clockado, clockado/ordinary e clockado/clockado. As hipóteses de
somabilidade dos lemas gerais são satisfeitas pelas provas da fonte e da
saída clockada; não são novas hipóteses físicas.

Nenhum passo separa as séries infinitas de Green e de retorno de traço.
Os limites utilizam as células completas. Não foi demonstrada nem usada uma
troca de soma infinita para cada uma das parcelas expandidas separadamente.
Também não se afirma convergência uniforme em tempo, dimensão ou ordem de jet.

## E. Expressão Green conjunta e comparação com PR #16

As novas leituras são construídas das somas de células reconstruídas:

\[
S_\eta(t)=1+\sum_k c_\eta(Y_t,k),\qquad
K_\eta(t)=\sum_k c_\eta(LY_t,k),
\]
\[
F_\eta=D S_\eta,\qquad
\Psi_\eta=iD K_\eta-D'S_\eta.
\]

`carryValveValueReadout_eq` e `carryValveCompanionReadout_eq` identificam
essas expressões com os readouts do mesmo par físico original. A igualdade
do readout escalar com a característica canônica já existia; o avanço aqui é
o ledger bilinear das incidências, retornos e caudas.

`carryValveReturnGreen` é a expressão explícita

\[
\begin{aligned}
\mathcal W_\eta(t,u)={}&i\bar D_tD_u
\bigl(\bar S_tK_u+\bar K_tS_u\bigr)\\
&+(\bar D'_tD_u-\bar D_tD'_u)\bar S_tS_u.
\end{aligned}
\]

`carryValveReturnGreen_eq` prova
`W_eta = conj(F_eta(t))*Psi_eta(u) - conj(Psi_eta(t))*F_eta(u)`.
`carryValveReturnGreen_physical_ledger` prova, com a mesma convenção
`G((c,v),(d,w))=<v,d>-<c,w>`,

\[
G(X_t,X_u)-G(HX_t,HX_u)=\mathcal W_\eta(t,u).
\]

O fator 1/2 do readout é compensado por o par original guardar **duas vezes**
o valor em sua segunda componente. Não houve alteração de normalização.
`H` continua sendo o complemento de `seed + globalReturn`, distinto do
complemento central `Q` do PR #16.

O par de prefixo guarda o valor e a companheira obtidos com os prefixos
ordinary e clockado. O par de cauda conserva
`D*tau` e `i*D*tau_clock-D'*tau`.
`carryValvePair_prefix_tail` e `carryValveReturnGreen_tail_ledger` dão os
quatro termos Green prefixo/prefixo, prefixo/cauda, cauda/prefixo e cauda/cauda.
`carryValvePrefixGreen_tendsto` prova o limite em dois cutoffs independentes.

Com a escala **já existente** `a = carryMaterialResponseScale`, defina

\[
\mathcal B_\eta(t,u)=a^2tu\,\mathcal W_\eta(t,u)
-\frac{a(u-t)}2\overline{\Psi_\eta(t)}\Psi_\eta(u).
\]

`carryValveReducedReturnBalance_physical` identifica essa expressão com o
Green do par reduzido menos o Green de seu complemento oculto. Portanto ela
é também a soma assinada dos cinco termos do PR #16 menos o sexto termo
oculto. Não foi apagada a parcela quadrática forçada nem qualquer cruzamento.

No arquivo de comparação externa, sem nova dependência Lake:

- `CarryMaterialValveGlobalReturnComparison.material_valve_return_green_wronskian`
  calibra a ordem literal `completedGreenWronskian F companion u t`.
- `...material_valve_global_residual_numerator` reutiliza **o ledger do PR #16**
  e prova, em uma vizinhança central comum,

\[
\mathcal B_\eta(t,u)=
2a^2tu\,\bar F(t)F(u)(u-t)\,R(t,u).
\]

- `...material_valve_global_central_row` prova `B_eta(0,u)=0` antes de
  normalizar, usando o readout central efetivo da companheira.
- `...material_valve_prefix_residual_limit` prova que o balanço de prefixos
  converge ao **mesmo numerador canônico completo** com `M,N` independentes.
  A escala, o dressing e a normalização são os da fonte completa durante
  todo o limite; não se recalcula uma resposta reduzida para cada truncamento.

Todas essas igualdades conservam `t=0`, `u=0` e `t=u` nos domínios declarados.
Não se dividiu pelo fator `2a²tu conj(F(t))F(u)(u-t)`.

## O que permanece aberto

O confronto bilinear pedido nesta rodada não exigiu hipótese física nova.
Seu numerador está identificado. O próximo obstáculo é uma propriedade de
sinal do balanço normalizado completo, equivalente ao enunciado já existente
`CarryRealKernelNonnegativeOn carryMaterialRealResidual U` para uma
vizinhança central apropriada.

Em termos concretos: para toda família finita de tempos e coeficientes reais,
provar que a forma quadrática do residual é não negativa. Uma decomposição
em quadrados ou uma dominância da correção oculta derivada da fonte poderia
resolver essa obrigação, mas nenhuma foi obtida nesta rodada.

O fator assinado entre `B_eta` e `R` impede concluir o sinal do kernel
normalizado apenas pelo sinal pontual de um numerador. Os limites de prefixos
não são estimativas uniformes da forma quadrática para todas as famílias ou
ordens. O valor zero da linha central do numerador também não permite apagar
os termos físicos, que podem cancelar-se.

| Status | Resultado |
| --- | --- |
| PROVADO EM LEAN | Arestas, células e grafo do retorno nas coordenadas da válvula |
| PROVADO EM LEAN | Fonte ordinary e saída clockada, sem segundo domínio |
| PROVADO EM LEAN | Polarização orientada, duas quadraturas e GG/GR/RG/RR |
| PROVADO EM LEAN | Caudas completas, erro de produto e limites independentes |
| PROVADO EM LEAN | Green conjunto, dressing derivativo e complemento oculto |
| PROVADO EM LEAN | Comparação literal com numerador do residual do PR #16 |
| ABERTO | Cancelamento estrutural, fatoração positiva ou dominância geral |
| ABERTO | Positividade do residual e do Gram canônico |

## Proveniência e validação

`provenance.json` registra commits de origem e hashes dos arquivos utilizados,
pins e arquivos de usuário preservados. `new-roots.json` registra as declarações
novas; `footprints.json` seus axiomas transitivos por tipos e corpos.
`validation.json` associa os comandos aos logs de sucesso em `evidence/`.

As auditorias usam `Lean.collectAxioms` e `#print axioms` por declaração.
Analysis admite somente `propext`, `Classical.choice` e `Quot.sound`.
Foundation conserva auditoria vazia; Geometry sua política discreta própria.
Não há `sorry`, `admit`, novos axiomas, métricas, operadores ou fontes.

Comandos principais:

```bash
lake build GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen --wfail
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
lake env lean -DwarningAsError=true research/projective-global-return/Regression.lean
bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator
bash scripts/audit-material-projective-comparison.sh /home/thlinux/carry-self-adjoint-operator
```

As regressões verificam o caso 72, a conexão material de uma aresta, o cutoff
zero com cauda inteira, cutoffs 1 e 2 distintos, o sinal da parte imaginária,
a fonte crítica, a saída clockada e as declarações dos no-gos anteriores.
Não se usaram experimentos numéricos como entrada de prova.
