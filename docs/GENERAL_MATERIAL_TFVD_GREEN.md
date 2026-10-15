# Transporte material geral e a primeira ponte real TFVD/Green

2026-10-15 — `thiagomassensini/geometry-of-numbers`.
Base: PR #2, `ab0c47651d414271cf6fda60c2d32fa2f2997927`.
Fonte externa consultada, sem alteração: `carry-self-adjoint-operator`,
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532` (PR #106).

## O avanço

A lei entre raios foi provada para duas células inteiras existentes que
compartilham o centro. Sua correção é exatamente a soma orientada das duas
faixas de gradientes materiais pedida na investigação. O caso 72 é corolário,
com os mesmos índices 79 e 62, e não uma segunda prova particular.

Há também uma ponte real concreta: recuperamos cada gradiente físico por
**Green mais retorno de traço**, no endereço C2 decodificado antes do TFVD.
Essa infraestrutura já existia; esta rodada a conecta aos novos readouts,
ao transporte de raios e aos pareamentos polarizados. Não foi construída
novamente a análise TFVD nem atribuída uma nova métrica ao seu alvo.

O primeiro teste de bordo mostra algo decisivo: no início da fibra unitária
esquerda, Green é zero, mas o retorno da fonte efetiva é negativo. Portanto,
eliminar o retorno falha já nessa coordenada concreta. A ponte completa não
sofre essa obstrução: ela conserva ambos os termos.

## 1. Inventário das interfaces reaproveitadas

Todos os nomes desta seção são anteriores à mudança. Os caminhos estão sob
`GeometryOfNumbers/Analysis`, exceto quando indicado. Nomes, hashes e commits
de proveniência estão no [inventário](../research/general-material-tfvd/provenance.json).

| Interface existente | Tipo e alcance efetivos |
|---|---|
| `Geometry/IntegerCameraIncidence.lean`: `integerCameraTowerCell`, `integerCameraTowerCell_center` | Centro reconstruído da cauda da torre original, com base positiva e testemunho `HasCarryDepthAtLeast`. Mantém base, profundidade, núcleo, raio e papel da incidência. |
| `CarryMaterialSourceRealization.lean`: `carryMaterialPointReadout` | Funcional contínuo complexo finito no Hilbert completado; recupera `f_t(n)` quando `n>0`. Não é uma isometria. |
| `CarryMaterialCameraTransport.lean`: `carryMaterialCameraReadout`, `carryMaterialCamera_clock_connection` | Readout `P_left-2P_center+P_right`; derivada finita com as diferenças dos logaritmos das pernas. |
| `BaseTwoCompletedBoundaryHilbert.lean` | `Y_t = seed ⊕ (gradient ⊕ boundaryReturn)` em um produto Hilbert já definido. O retorno vem do limite geométrico; seu readout global soma seed e retorno. |
| `BaseTwoCompletedVectorLiftGate.lean` | Dressing escalar canônico e sua regra de derivação, com hipóteses vetoriais explícitas. Não identifica a característica do carry. |
| `BaseTwoPhysicalEdgeC2Address.lean` | Decodifica a aresta material por seu extremo ímpar em núcleo, direção e profundidade C2 genuína. |
| `BaseTwoPhysicalEdgeTfvdBridge.lean`: `baseTwoPhysicalResidualTfvdAnalysis` | Aplicação real linear do gradiente em `(C2RealTfvdChannels × MaterialEdgeL2)`. O segundo fator retém o residual. Injetividade exige `0<eta<1`. |
| Mesmo arquivo: `baseTwoPhysicalTfvdChannel` | Aplicação real **contínua** em cada núcleo/direção/quadratura, com interior e dois traços. Não é afirmada continuidade em uma norma global da família inteira. |
| `C2RealFiberTfvdIncidence.lean` | `C2RealTfvdChannels` é uma família de canais, cada um `CarryVerticalL2 × (ℝ×ℝ)`. Síntese Green/retorno é inversa à esquerda da análise em cada fibra. |
| `RealCarryTfvd.lean`, `RealCarryWeightedValve.lean` | `GB + R Tr = I` em `CarryVerticalL2 = ℓ²(ℕ,ℝ)`. O parâmetro crítico já existente é `eta_b=b^(-1/2)`. |

No carry foram conferidos os contratos
`HasCompletedNativeRealAxisNormalizedGreenKernel`,
`HasCanonicalCompletedNativeTfvdGreenCenterLegReadout` e
`CompletedNativeRealHPCarrierCertificate`, além de `pack_inner`, complemento
prime-carry e a costura de três setores dos PRs #105/#106.

Os no-gos continuam respeitados: o certificado complexo antigo tem primeiro
jet ímpar nulo; o Gram de observação vertical não é automaticamente Hankel;
o bloco central limitado não representa fielmente todo o relógio material.
Nenhum desses resultados foi promovido a impossibilidade da fonte completa.

## 2. Lei geral sobre a mesma fonte

A fonte prescrita anteriormente é

\[
f_t(n)=n^{-1/2}e^{-it\log n},\qquad
g_t(j)=f_t(j+2)-f_t(j+1).
\]

O novo `carryMaterialIntervalReadout a b` é a soma finita dos funcionais
existentes de gradiente, nos índices `p-1`, para `p∈Ico a b`. Para `0<a≤b`,

\[
\sum_{p=a}^{b-1}g_t(p-1)=P_b(Y_t)-P_a(Y_t).
\]

A identidade é demonstrada primeiro no carrier inteiro, pela recorrência dos
readouts de ponto. A especialização não introduz um campo independente.

Se duas células existentes têm centro `c` e raios `h≤H<c`, então

\[
\boxed{B_H(t)=B_h(t)+\Delta_{h,H}(t)},
\]

\[
\boxed{\Delta_{h,H}(t)=
\sum_{p=c+h}^{c+H-1}g_t(p-1)
-\sum_{p=c-H}^{c-h-1}g_t(p-1)}.
\]

O teorema `carryMaterialCamera_general_transport` trabalha com as células
originais, sem impor uma bijeção entre pernas. Sua especialização
`carryMaterialTower_general_transport` recebe explicitamente os dois
testemunhos de profundidade nas torres originais e as bases positivas. Não
substitui essa proveniência por uma isometria postulada.

As hipóteses permitem raios iguais; nesse caso a correção é zero. O sentido
inverso usa `B_h=B_H-Delta`, com as mesmas hipóteses ordenadas. Não se declara
antissimetria de somas `Ico` invertidas, que são vazias por definição. A lei
não requer maximalidade ou primalidade; essas condições continuam nas APIs
que selecionam apresentações máximas. No regime pedido `0<h<H<c`, todas as
posições materiais são positivas.

Para 72, os intervalos são `Ico 80 81` e `Ico 63 64`, e o Lean obtém

\[
\Delta_{8,9}(t)=g_t(79)-g_t(62).
\]

O defeito não foi zerado: a prova do PR #2 de `Re Delta(0)>0` permanece.

## 3. Pareamento, quadraturas e defeito de energia

Com `t,u` independentes, foi formalizado

\[
\overline{B_H(t)}B_H(u)=
\overline{B_h(t)}B_h(u)+\overline{B_h(t)}\Delta(u)
+\overline{\Delta(t)}B_h(u)+\overline{\Delta(t)}\Delta(u).
\]

Os nove cruzamentos foram generalizados para quaisquer duas células com
posições positivas. Para `a=(1,-2,1)`, posições ordenadas `n_i,m_j`,

\[
\overline{B_a(t)}B_b(u)=
\sum_{i,j=0}^{2}a_i a_j\overline{f_t(n_i)}f_u(m_j).
\]

Os coeficientes são `((1,-2,1),(-2,4,-2),(1,-2,1))`. As partes real e
imaginária são exatamente `P(X,Y)` e `P(JX,Y)`, para o pareamento anterior
`P(X,Y)=X₁Y₁+X₂Y₂` e `J(X₁,X₂)=(-X₂,X₁)`. Ordem e sinal coincidem com
`CarrySelfAdjointOperator.RealQuadrature.pack_inner`. A fórmula de fase do
PR #2 continua: amplitude `1/(sqrt(n)sqrt(m))` multiplicando cosseno e seno de
`t log n-u log m`. A generalização do ledger não elimina essa dependência.

Somente após essa síntese, o novo teorema de energia dá

\[
E_H(t)-E_h(t)=2P(B_h^{real}(t),\Delta^{real}(t))
+E(\Delta^{real}(t)).
\]

Não foi imposto sinal a esse defeito, nem conservação entre raios distintos.
A derivada das leituras continua sendo a do PR #2, com os logaritmos de
**cada** perna. Raio não se transforma em ordem de jet ou frequência.

## 4. A ponte real concreta com Green e retorno

As arestas físicas históricas são `j=4k+2` e `j=4k+3`. O mapa anterior
`baseTwoPhysicalEdgeC2State` restringe a esses índices, decodifica o extremo
ímpar e realifica o valor complexo como duas quadraturas. Índices `0,1 mod 4`
permanecem no residual. Isso não identifica as células escaladas do PR #1
com as células C2 históricas de raio 1.

No endereço `i=(m,(direction,j))`, o índice vertical `j` significa profundidade
física **j+2**. Ele não é o índice da aresta material. Para cada quadratura,
seja `x` a sequência vertical efetivamente extraída. Usamos os operadores
anteriores para construir dois funcionais reais contínuos:

\[
G_i(g)=[Green_\eta(Bracket_\eta x)]_j,\qquad
R_i(g)=[Return_\eta(Trace_\eta x)]_j.
\]

`carryMaterialTfvd_coordinate` e `carryMaterialTfvd_edge_source` demonstram

\[
G_i(g_t)+R_i(g_t)=\operatorname{quadrature}(g_t(edge(i))).
\]

O retorno não foi escolhido para acertar o lado direito: é o operador de
traço/retorno existente. Sua fórmula, agora explicitamente conectada ao
readout, é

\[
R_j=\eta^j[x_0+j(\eta^{-1}x_1-x_0)].
\]

Todas as provas valem para `0<eta<1`; a regressão instancia o valor crítico
**já existente**, `eta_2=2^(-1/2)`. Não se seleciona `eta` pelo Gram-alvo.

No canário, as arestas são `(19,right)` e `(15,left)`. Seus endereços são
`(core=5,right,j=2)` e `(core=1,left,j=4)`: profundidades físicas 4 e 6,
associadas aos centros históricos 80 e 64. São diferentes dos raios 8 e 9
das células comparadas e das profundidades 3 e 2 do centro 72.

O novo teorema `carryMaterialTfvd72_correction` recupera **cada quadratura** de
`g_t(79)-g_t(62)` por `G_right+R_right-G_left-R_left` nesses endereços.

Para quaisquer duas arestas físicas e dois estados de gradiente, o pareamento
posteriormente empacotado como complexo foi provado como

\[
\overline{g_e}g_f=
\overline{G_e}G_f+\overline{G_e}R_f+
\overline{R_e}G_f+\overline{R_e}R_f.
\]

Cada `G` e `R` nessa notação reúne seus dois readouts **reais**. A fórmula
conserva ambas as partes do pareamento; não atribui um produto interno novo
ao espaço de canais TFVD. Os dois termos mistos não são supostos nulos.

Para raios gerais, a correção pode conter arestas residuais. O teorema
`carryMaterialRadiusCorrection_residual_ledger` mantém separadamente as duas
faixas físicas e as duas faixas residuais. Só a parcela física recebe o
readout C2 descrito acima. Não apagamos o restante para estender o canário.

## 5. Calibração efetiva e o termo que não pode desaparecer

Na fibra unitária esquerda, as coordenadas `j=0,1,2` correspondem aos
gradientes materiais `g_t(2),g_t(6),g_t(14)`. Foram verificados o início e o
primeiro nível em que Green pode contribuir:

\[
G_0=0,\quad R_0=x_0,\qquad
G_2=x_2-2\eta x_1+\eta^2x_0,\quad
R_2=2\eta x_1-\eta^2x_0.
\]

Os teoremas `carryMaterialTfvd_unit_samples` e `carryMaterialTfvd_unit_cross`
testam a fonte real efetiva, com parâmetros e quadraturas independentes:

\[
(G_0(t)+R_0(t))(G_2(u)+R_2(u))
=\operatorname{quad}_r(g_t(2))\operatorname{quad}_s(g_u(14)).
\]

Em fase zero, na primeira quadratura,

\[
R_0(0)=g_0(2)=\frac12-\frac1{\sqrt3}<0.
\]

Essa desigualdade foi provada em Lean por aritmética exata de raízes. Assim,
substituir a síntese por Green sozinho falha **nesta fonte e nesta coordenada**.
O cruzamento real inicial com `j=2`, em fase zero, é
`(1/2-1/sqrt(3))*(1/4-1/sqrt(15))`; ele inclui o retorno de maneira efetiva.
Não o identificamos com um momento canônico: coordenada vertical não é jet.

## 6. Estado completo, regularidade e pareamento preservado

O estado anterior continua sendo `Y_t=(f_t(1),(g_t,beta_t))`. Leituras finitas
não detectam `beta_t`; as segundas diferenças também cancelam a semente.
O fato de não a observarem não permite eliminá-la do estado.

O novo `carryMaterial_complete_real_pairing` prova, para `t,u` independentes,

\[
\langle Y_t,Y_u\rangle_\mathbb R=
\langle f_t(1),f_u(1)\rangle_\mathbb R+
\langle C2(g_t),C2(g_u)\rangle_\mathbb R+
\langle residual(g_t),residual(g_u)\rangle_\mathbb R+
\langle beta_t,beta_u\rangle_\mathbb R.
\]

Isso polariza a decomposição física/residual já provada: a ortogonalidade
vem de suportes disjuntos, não de uma independência postulada das câmeras.
O produto interno complexo completo do PR #2 também permanece disponível,
com gradiente complexo e retorno. A energia TFVD antes da reconstrução não
foi declarada igual a esse pareamento.

Os novos readouts reais são contínuos porque são composições de operadores
limitados existentes. Sua derivada escalar ao longo da fonte foi provada a
partir da derivada forte **já existente do gradiente material**:
`g'_t=-i*clockL2_t`. Esta contém as diferenças `log(n+2)-log(n+1)`; não é um
relógio diagonal de profundidade. Não se afirma derivada forte da família
global de canais numa norma não construída, nem jet holomorfo de `Y_t`.

`beta_t` é o retorno global de células completas; `R_i` é o retorno do traço
de uma fibra TFVD. São objetos distintos. A igualdade do retorno global com
uma soma de canais físicos já existe, mas é afirmada na órbita concreta
somável, não como um funcional limitado sobre um `ℓ²` arbitrário. O dressing
e seu termo derivativo seguem intactos; não foram substituídos por `R_i`.

Amplitude crítica e fase são as prescritas anteriormente. A torre e suas
incidências são aritméticas; isso não deduz a fase logarítmica só da
divisibilidade nem reabre a seleção da meia escala.

## 7. Diagnóstico da primeira ponte ainda ausente

| Fonte disponível | Transformação existente e agora testada | Destino | Igualdade e status |
|---|---|---|---|
| Gradiente de `Y_t` | Restrição física, endereço aritmético, realificação e análise TFVD | Canais por núcleo/direção/quadratura e residual separado | **Provado:** Green + retorno recupera a coordenada; cruzamentos são os quatro termos completos. |
| Duas leituras de células reais | Somas finitas dos gradientes da mesma fonte | Correção entre raios e pareamento de nove termos | **Provado:** lei geral, energias com defeito e regressão 72. |
| Estado completo `Y_t` | Decomposição física/residual sem apagar semente ou retorno global | Pareamento real completo | **Provado:** igualdade polarizada da seção 6. |
| Família TFVD física, residual, semente e `beta_t` | Falta uma realização no carrier canônico compatível com sua síntese e dinâmica | `CanonicalCompletedTfvdGreenHilbertCarrier` | **Aberto:** mapa efetivo da mesma fonte com o pareamento normalizado. Não foi encontrado nas interfaces consultadas. |
| Jets concretos desse eventual estado | Transporte de incidências centro–pernas | Interface real HP do PR #106 | **Condicional:** precisa do readout Green canônico dos mesmos jets, além das condições de independência da interface. |
| Fonte efetiva na fibra unitária esquerda | Candidata que remove o retorno TFVD | Green sozinho | **Obstruído:** `G_0=0` e `R_0(0)<0`, formalizados. A obstrução não vale contra Green + retorno. |

O contrato `HasCompletedNativeRealAxisNormalizedGreenKernel` pede

\[
\left\langle\frac{Z(x)}{\sqrt2 F(x)},
\frac{Z(u)}{\sqrt2 F(u)}\right\rangle
=\operatorname{dslope}\left(\frac{F_{comp}}{2F}\right)(x,u),
\]

em pontos reais onde `F` não zera. Não o preenchemos assumindo essa igualdade.
Mesmo para a candidata literal `Z(x)=D(x)Y_x`, que **não foi identificada**
com a fonte nativa do operador, a obrigação expandida seria

\[
\frac{\overline{D(x)}D(u)}{2\overline{F(x)}F(u)}
\left[\overline{f_x(1)}f_u(1)+\langle g_x,g_u\rangle_\mathbb C
+\overline{beta_x}beta_u\right]
=\operatorname{dslope}\left(\frac{F_{comp}}{2F}\right)(x,u).
\]

Não há aqui um teorema que identifique os readouts/dressing da geometria com
`F,F_comp` do carry, ou que produza essa igualdade de dois argumentos.
A calibração central necessária dessa candidata é

\[
\frac{|D(0)|^2}{2|F(0)|^2}
\left(1+\|g_0\|^2+|beta_0|^2\right)=h_0.
\]

Essa equação não foi demonstrada, nem imposta ajustando constantes. Para o
readout de jets, o próximo cruzamento exigiria, por exemplo,
`inner(jet(inl 0),jet(inl 1))=h_1`. A fórmula material verificada acima não é
essa igualdade: falta a identificação dos vetores e de suas ordens.

A família `C2RealTfvdChannels` é um tipo de funções em canais Hilbert locais;
isso não fornece por si um mapa global para o Hilbert canônico do contrato.
Injetividade da análise e reconstrução por fibra não suprem essa lacuna.

A forma complementar do PR #106 continua sendo
`C(x,y)=inner_R(x,y)-inner_R(Tx,Ty)`, na torre prime-carry concreta, com
empacotamento `C(x,y)+i C(Jx,y)`. Não há aqui um mapa tipado desses dados C2
para essa torre que permita aplicar `T`. Coincidência das convenções de
quadratura não identifica esse complemento com o pareamento material.

As identidades dos PRs #105/#106, incluindo `R=Gamma+Q`, escape e seus quatro
cruzamentos, continuam intocadas. Não se anulou `D_4` nem se dividiu por
`w-conj(z)` na diagonal. O certificado complexo obstruído não foi utilizado.

## 8. Código, provas e validação

Módulos novos: `CarryMaterialGeneralTransport.lean` e
`CarryMaterialTfvdGreenReadout.lean`. Há 37 raízes públicas: 32 teoremas e
5 definições. Todas são registradas no audit central, com guard transitivo
de axiomas e `#print axioms`. Analysis permite apenas os axiomas padrão;
Foundation e Geometry permanecem inalteradas e com seus guards anteriores.

Evidências em `research/general-material-tfvd/`: `public-roots.json`,
`provenance.json`, `validation.json`, `Regression.lean` e registros de build
e auditorias. A regressão usa o parâmetro crítico anterior e verifica os
índices, o pareamento literal do PR #2 e os no-gos pertinentes.

Foram exigidos build focado e completo `lake build --wfail`, os três scripts
de auditoria, regressão com warnings tratados como erros, e preservação dos
pins. Não há `sorry`, `admit`, axioma novo, métrica alterada ou fonte ajustada.
Os contratos canônicos citados nesta seção de diagnóstico permanecem abertos;
nenhum certificado de positividade geral ou de alturas foi construído.
