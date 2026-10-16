# Transporte material do par valor–companheira e do residual Green

## Resultado e limite

Foi formalizado um transporte do **par vetorial completo**, no carrier material
já existente, até o **numerador do residual canônico**. O resultado é uma
identidade de formas Green assinadas, com dois parâmetros independentes.
O complemento anulado pelo readout permanece explícito, com seus cruzamentos.
Não foi demonstrada uma realização do residual como Gram positivo.

O avanço em relação ao PR #7 é utilizar a companheira produzida pelo relógio
e pela derivada do dressing. A projeção ortogonal do estado normalizado,
estudada naquele PR, continua tendo o primeiro jet incompatível com o
residual canônico. Nenhuma constante, amplitude, fonte ou métrica foi alterada.

## Proveniência, tipos e convenções

Base: `geometry-of-numbers` em `5dcca37b088b3d1975d76f116b9e856a27fd6e19`
(merge do PR #7). Consulta externa, sem alterações:
`carry-self-adjoint-operator` em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
Os PRs #1–#7 de geometria e #105–#106 do operador são registrados com seus
SHAs no inventário `research/material-green-pair/provenance.json`.

Escrevemos:

- `E = MaterialCarrier`, alias do `BaseTwoCompletedBoundaryHilbertCarrier`;
- `Y(t) = baseTwoCompletedBoundaryHilbertState t = (a(t),g(t),beta(t))`;
- `ell = baseTwoCompletedBoundaryHilbertReadout`, com `ell(a,g,beta)=a+beta`;
- `K = completedBoundaryTransportedClock`, no seu domínio já construído;
- `D(t) = baseTwoCanonicalDressingScalar t`;
- `F(t) = baseTwoCanonicalResponse t = ell(D(t) • Y(t))`;
- `r0(t) = carryMaterialNormalizedResponse t = -F'(t)/(2 F(t))`;
- `alpha = carryMaterialResponseScale`, identificado com o momento nativo `h0`;
- `r1(t) = carryMaterialReducedResponse t`, com a extensão central anterior.

`D` contém **a completação arquimediana e a retirada do fator da câmera**.
Não é apenas o fator arquimediano `A` usado no mapa triangular escalar do
operador. Seus termos derivativos não podem ser intercambiados sem essa
retirada. Os hashes e os últimos commits dos módulos efetivamente usados
constam do inventário.

Cada `Y(t)` pertence ao domínio de `K`. A companheira é um vetor de `E`,
construído aplicando `K` uma vez. Não se presume que ela própria pertença ao
domínio de `K`, nem se postula um domínio para `K²`. A derivada forte do estado
vestido usada aqui já estava demonstrada no PR #5. Não se pressupõe uma
segunda derivada forte ou uma extensão vetorial holomorfa.

Os pares estão no produto algébrico `E × E`; a forma Green usa os produtos
internos originais de `E`, conjugados no primeiro argumento. Nenhuma norma
nova do par é usada para provar conservação. A escrita complexa representa
as duas quadraturas existentes. Os mapas de redução são complexo-lineares,
portanto reais lineares e compatíveis com a multiplicação por `I` (a rotação
`J`). Isso não identifica o carrier material com outro carrier do operador.

O parâmetro é o tempo material real. Sua comparação com as funções canônicas
é a identidade de funções já verificada no PR #5; não é uma identificação
entre o relógio material e o operador das alturas.

## 1. Par completo e conexão do dressing

Definimos no carrier original:

\[
 X_t=(P_t,Q_t),\qquad
 P_t=-[D_t(-i K Y_t)+D'_tY_t],\qquad Q_t=2D_tY_t.
\]

`carryMaterialCompanionValuePair_readout` prova
`ell(X_t)=(-F'(t),2F(t))`. A comparação externa prova literalmente a igualdade
com o par canônico `(-F',F)`, mantendo o fator dois no slot do valor.
Esse fator vem da resposta `-F'/(2F)` já fixada, não de uma calibração nova.

Para qualquer par, o dressing atua por

\[
 T_{D,t}(p,q)=(D_t p-(D'_t/2)q,D_tq),\qquad
 X_t=T_{D,t}(iKY_t,2Y_t).
\]

Com a convenção já existente
`G(x,y)=<x.2,y.1>-<x.1,y.2>`, provou-se:

\[
 G(T_{D,t}x,T_{D,u}y)=\bar D_tD_uG(x,y)
 +\frac{\overline{D'_t}D_u-\bar D_tD'_u}{2}\langle x_2,y_2\rangle.
\]

Ambas as orientações da correção ficam presentes. A igualdade literal da
forma local com `NativeCarrySpectralWeyl.Boundary.greenForm` foi verificada
no arquivo de comparação, sem acrescentar dependências ao Lake de geometria.

## 2. O complemento determinado pelo readout

O vetor médio do readout é `w=(1/2,0,1/2)`. Definimos
`P_ell y = ell(y) w` e `N y = y-P_ell y`. Assim:

\[
 N(a,g,\beta)=((a-\beta)/2,g,(\beta-a)/2),\quad
 \ell(Ny)=0,\quad P_\ell y+Ny=y.
\]

O coeficiente `1/2` é imposto pelo readout e pelo produto interno preexistentes.
A identidade polarizada, provada com argumentos independentes, é:

\[
 \langle x,y\rangle=
 \tfrac12\overline{\ell x}\ell y+\langle Nx,Ny\rangle,
\qquad
 \langle Nx,Ny\rangle=
 \langle g_x,g_y\rangle+
 \tfrac12\overline{(a_x-\beta_x)}(a_y-\beta_y).
\]

Logo, aplicando `N` aos dois slots do par:

\[
 G(x,y)=\tfrac12G(\ell x,\ell y)+G(Nx,Ny).
\]

O termo oculto é explicitamente o Green dos gradientes mais os dois
cruzamentos orientados dos contrastes semente–retorno. O retorno global
não foi confundido com o retorno de traço TFVD. `N` também não é o residual
espacial `Q_edge`, o complemento central do PR #7 ou o escape Naimark.

Para a fonte concreta, a auditoria externa fecha, para todos `t,u` reais:

\[
 G(X_t,X_u)=G(NX_t,NX_u)+W_F(u,t),
\]

onde `W_F` é exatamente `completedGreenWronskian` das característica e
companheira completadas existentes. A ordem `(u,t)` foi verificada no Lean.

## 3. Redução homogênea e conservação da informação

A transformação antes de qualquer quociente é

\[
 L_t(p,q)=(p-\alpha t q,\alpha t p),\qquad W_t=L_tX_t.
\]

É linear, comuta com `N` componente a componente e tem a lei exata:

\[
 G(L_tx,L_uy)=\alpha^2tuG(x,y)
 -\alpha(u-t)\langle x_1,y_1\rangle.
\]

Para `alpha*t != 0`, há reconstrução explícita do par original. No centro,
o mapa bruto perde o valor. Por isso o transporte fiel formalizado conserva
**também o valor original**:

\[
 \widetilde L_t(p,q)=(L_t(p,q),q),\qquad
 (p,q)=((\widetilde L_t(p,q))_{1,1}+\alpha t q,q).
\]

Essa aplicação é injetiva para todo `t`, inclusive zero. Não se afirma que
seja uma isometria. Não se introduz uma métrica para torná-la isométrica.

## 4. Identificação exata do numerador residual

Em uma vizinhança aberta real de zero, a comparação da fonte prova:

\[
 d_t:=\ell(W_t.2)=2\alpha tF_t r_0(t),\qquad
 \ell(W_t.1)=d_t r_1(t).
\]

Usando a realidade da resposta reduzida no eixo real e a identidade de
`dslope`, para quaisquer `t,u` dessa vizinhança, inclusive os coincidentes:

\[
 G(W_t,W_u)-G(NW_t,NW_u)
 =\tfrac12\bar d_t d_u(u-t)\operatorname{dslope}r_1(t,u).
\]

Consequentemente:

\[
 \boxed{G(W_t,W_u)=G(NW_t,NW_u)
 +2\alpha^2tu\,\bar F_tF_u(u-t)\,R(t,u)},
\]

\[
 R(t,u)=\overline{r_0(t)}r_0(u)\operatorname{dslope}r_1(t,u).
\]

`R` é **o mesmo residual ponderado canônico do PR #6**, sem substituição da
fonte ou fatoração escolhida de seu Gram. Os teoremas novos são
`material_reduced_pair_green_dslope` e
`material_reduced_pair_canonical_residual_numerator`, no namespace
`CarryMaterialGreenPairComparison`.

A fórmula não divide por `t`, `u` ou `u-t`. Na diagonal e nos eixos os fatores
podem anular: a identidade continua válida, mas por si só não determina um
valor diagonal de kernel através de divisão. Em particular, não prova
positividade do residual nem transforma uma forma Green assinada em norma.

## 5. O canal central não observado

Para a fonte efetiva, provou-se:

\[
 P_0\ne0,\qquad \ell(P_0)=0,\qquad NP_0=P_0,
 \qquad W_0=(P_0,0)\ne0,\qquad \ell(W_0)=0.
\]

Portanto, o zero escalar do par reduzido não é um zero vetorial. A forma Green
própria de `(P0,0)` vale zero, mas isso não autoriza eliminar seus cruzamentos.
Se `What_t = W_t-(P0,0)`, a centralização preserva o readout e satisfaz:

\[
 G(W_t,W_u)=G(\widehat W_t,\widehat W_u)
 +\langle W_t.2,P_0\rangle-\langle P_0,W_u.2\rangle.
\]

`What_0=0` e a reconstrução conserva `(P0,0)` separadamente. Não se provou
que esses dois termos mistos se anulem; tampouco uma extensão vetorial de
`W_t/t²`. O resultado pontual não é anunciado como um teorema sobre limites.

## 6. TFVD, testes e auditoria

O teste de regressão reaplica a reconstrução TFVD anterior às componentes
de gradiente da companheira reduzida oculta e do valor reduzido oculto,
com tempos independentes. Conserva as duas quadraturas e os quatro termos
`GG + GR + RG + RR`. Também testa a reconstrução do par fonte pelo mapa
com valor retido no parâmetro singular `t=0`.

Permanecem as regressões das câmeras de 72, índices 79/62, relógio e conexão,
domínio da fonte, retorno global, decomposição física/residual, no-gos do
Gram vertical e do relógio separado, e o primeiro jet da projeção anterior.
Não foram utilizados experimentos numéricos para certificar os resultados.

Foram acrescentados **24 teoremas e 12 definições públicas** no módulo
`CarryMaterialCompanionGreenTransport.lean`, e **11 teoremas** na comparação
externa. Todos os 47 novos roots têm auditoria transitiva por tipos e corpos.
A lista permitida na análise é `propext`, `Classical.choice`, `Quot.sound`;
não se anuncia footprint vazio para essa camada. A Foundation permanece
com auditoria vazia, e a Geometry mantém seu contrato distinto.

A validação registrada contém build focado `--wfail`, build completo
`lake build --wfail`, auditorias das três zonas, comparação externa com
`-DwarningAsError=true`, regressões e inventário de axiomas. Os comandos,
códigos de saída e logs estão em `research/material-green-pair/`.
Os pins Lean/Mathlib/GreenFrame e os arquivos preexistentes dos outros
repositórios foram preservados.

## Status e primeira obrigação restante

| Status | Resultado |
|---|---|
| **Provado em Lean** | Par completo da fonte, dressing com derivada, ledger polarizado do readout e Green oculto. |
| **Provado em Lean** | Redução homogênea, sua lei Green e transporte com valor retido, injetivo inclusive no centro. |
| **Provado em Lean** | Igualdade com o Wronskiano completado e, localmente, com o numerador do residual canônico. |
| **Provado em Lean** | Companheira central invisível e não nula; centralização com seus dois cruzamentos explícitos. |
| **Condicional ao domínio indicado** | Inversão do mapa bruto apenas para `alpha*t != 0`; as identidades com `r1` são locais. |
| **Obstrução específica** | O par reduzido bruto não se anula no centro; uma leitura escalar nula não permite descartá-lo. O no-go de Gram da projeção do PR #7 permanece. |
| **Aberto** | Realizar o residual como produto interno positivo de uma família derivada da fonte, com identificação de kernel e extensões diagonais justificadas. |
| **Aberto** | Controlar geometricamente o balanço Green oculto e os termos mistos centrais, ou convertê-los por uma identidade adicional em pareamento positivo. |
| **Não demonstrado** | Domínios de potências do relógio, jets vetoriais de ordem arbitrária, iteração positiva completa e consequências espectrais. |

**Fonte disponível → transformação existente → destino → igualdade provada
→ identidade ainda ausente:**

`Y(t)` no domínio de `K` → companheira com `D'` e valor `2DY` → par `X_t` →
redução `L_t` com valor original retido → `W_t` e seu complemento `NW_t` →
balanço Green igual ao numerador de `R(t,u)` → **falta uma identidade física
que realize o residual normalizado como um pareamento positivo**, preservando
o balanço oculto, os cruzamentos e as extensões onde o fator se anula.

O ledger localiza essa questão: não basta declarar `G(NW_t,NW_u)=0`, nem
identificar uma norma com a diferença assinada. Esta rodada não demonstra
que tal realização positiva exista ou seja impossível. Ela fornece o
transporte exato sobre o qual essa pergunta pode agora ser feita.
