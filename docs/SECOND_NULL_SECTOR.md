# Controle do setor que cancela o primeiro momento material

## Resultado

Foi demonstrada em Lean a positividade local da energia residual para
**qualquer família finita fixa** de coeficientes reais `c_i` e direções
materiais reais `a_i` que satisfaça

\[
 M_1:=\sum_i c_i a_i=0,\qquad M_2:=\sum_i c_i a_i^2\ne0.
\]

Escrevemos `h_n = canonicalCompletedNativeLogDerivativeMoment n`.
A energia é a do **mesmo residual normalizado** dos PRs #8 e #9:

\[
 E_R(\varepsilon)=\sum_{i,j}c_ic_jR(\varepsilon a_i,\varepsilon a_j).
\]

A fatoração é exata, em escalas suficientemente próximas de zero:

\[
 \boxed{E_R(\varepsilon)=\varepsilon^4 Q_2(\varepsilon)},\qquad
 Q_2(\varepsilon)\longrightarrow
 \gamma M_2^2,\qquad
 \gamma:=\frac{h_0h_2-h_1^2}{h_0}>0.
\]

Da continuidade segue uma margem inferior local explícita:

\[
 E_R(\varepsilon)\ \ge\ \frac{\gamma M_2^2}{2}\,\varepsilon^4.
\]

A constante `gamma` é imposta pelos coeficientes da fonte. O fator `1/2`
expressa apenas a margem obtida por continuidade; não altera nenhum kernel,
fonte, métrica ou normalização. Para `epsilon != 0`, a margem é positiva.

**Limite dos quantificadores:** a vizinhança depende da família fixa
(`n,c,a`). Não foi demonstrada uma vizinhança uniforme para todas as
combinações. O caso `M1=M2=0` conserva o resto exato, mas seu sinal não foi
fechado nesta rodada. Não há prova de Gram positivo em todas as ordens.

## Proveniência e interfaces preservadas

Base de geometria: `1e2c5f2463b5d61ed56bcc05f6cbc8c446fca833`, merge do PR #9.
Consulta externa: `carry-self-adjoint-operator`,
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, sem modificações.

Os objetos de partida continuam sendo:

- `Y(t) = baseTwoCompletedBoundaryHilbertState t`, com semente, gradiente e
  retorno global, no domínio do relógio material já construído;
- o dressing `D` e sua derivada, conservados no par valor–companheira;
- `r0(t) = carryMaterialNormalizedResponse t = -F'(t)/(2F(t))`;
- `A0(t) = carryMaterialResponseAxis t = dslope r0 0 t`;
- `r1(t) = carryMaterialReducedResponse t`;
- `R(t,u) = Re(conj(r0(t))*r0(u)*dslope r1 t u)`, a definição anterior.

A fonte completada e o kernel canônico já foram comparados literalmente nos
PRs anteriores. O PR #8 mantém o balanço Green do par completo e seu
complemento invisível ao readout; o PR #9 prova o termo principal
`h1*M1²` após remover `epsilon²`. Essa energia anterior não foi substituída.

Usamos as duas quadraturas reais já existentes; a notação complexa empacota
seus produtos apenas após a síntese. As partes reais têm proveniência na
realidade da resposta no eixo real, já formalizada. Não se identifica
profundidade vertical com ordem de jet, índice material com câmera ou
relógio material com operador das alturas.

O relatório de proveniência em
`research/material-second-null-sector/provenance.json` registra declarações,
hashes, pins e os últimos commits dos módulos reutilizados.

## 1. A próxima redução é a mesma, não uma fonte nova

Definimos no parâmetro real:

\[
 A_1(t)=\operatorname{dslope}r_1(0,t),\qquad
 b=A_1(0)=\frac{h_1}{h_0^2}>0,
\]

\[
 r_2(t)=\frac{\operatorname{dslope}A_1(0,t)}{b A_1(t)}.
\]

No código: `carryMaterialSecondAxis`, `carryMaterialSecondScale` e
`carryMaterialSecondReducedResponse`. A comparação externa demonstra que
esses objetos coincidem, como germes reais no centro, com os
`secondAxis`, `reducedSourceScale` e `secondReducedResponse` **já existentes**
no operador. Não se reconstruiu a cadeia canônica.

As hipóteses de regularidade, não anulação local e realidade são fornecidas
pela fonte. A fórmula é primeiro comparada fora da diagonal; a igualdade
na diagonal é demonstrada por continuidade de `dslope`, não por divisão em
`u=t`. A completação da fonte permanece na resposta usada pela redução.

`NativeCompletedSourceThirdPositiveChannel` já fornece:

\[
 r_2(0)=0,\qquad
 r'_2(0)=\frac{h_0(h_0h_2-h_1^2)}{h_1^2}.
\]

O sinal de `h0*h2-h1²` provém do teorema integral theta
`nativeSourceMixedDiscriminants_pos.1`, com o crosswalk literal dos momentos.
Este sinal foi reutilizado, não reapresentado como descoberta desta rodada.

A derivada material aqui é uma derivada do parâmetro real de respostas
escalares provenientes da fonte. Não foi presumida uma segunda derivada
forte do estado global em Hilbert nem holomorfia desse estado.

## 2. Identidade polarizada completa antes de decidir o sinal

Sejam

\[
 L(t)=A_0(t)A_1(t),\qquad H(t)=\frac{L(t)}{\sqrt b},
 \qquad v_1(t)=\frac{r_0(t)A_1(t)}{\sqrt b}=tH(t),
\]

\[
 C_2(t,u)=\operatorname{Re}
 \bigl(\overline{L(t)}L(u)\operatorname{dslope}r_2(t,u)\bigr).
\]

O módulo novo identifica, com dois parâmetros independentes e incluindo
coincidências, o residual anterior como:

\[
 \boxed{R(t,u)=\operatorname{Re}(\overline{v_1(t)}v_1(u))
                    +t^2u^2 C_2(t,u).}
\]

O novo `C2` é uma **função de dois parâmetros** com nome Lean
`carryMaterialSecondResidualCore`; não é uma fibra C2, um vetor TFVD ou uma
forma a que foi atribuído sinal positivo em todos os pontos.

A identidade preserva a resposta reduzida inteira. Consequentemente,

\[
 E_R(c,t)=\left|\sum_i c_i v_1(t_i)\right|^2+
 \sum_{i,j}c_ic_jt_i^2t_j^2 C_2(t_i,t_j).
\]

Todos os cruzamentos ordenados `i,j` são mantidos. Não se inferiu o sinal
da soma completa apenas porque seu primeiro termo é um quadrado.

## 3. Cancelamento exato e controle do resto

A derivada central de `H` vale zero: isso é transportado das derivadas
certificadas `A0'(0)=A1'(0)=0`. A identidade de diferenças divididas dá:

\[
 H(t)=H(0)+t\operatorname{dslope}H(0,t).
\]

Para `M1=0`, a síntese do canal extraído torna-se exatamente

\[
 \sum_i c_i v_1(\varepsilon a_i)
   =\varepsilon^2 S_2(\varepsilon),\qquad
 S_2(\varepsilon):=
 \sum_i c_i a_i^2\operatorname{dslope}H(0,\varepsilon a_i).
\]

Não foi feita divisão por `epsilon`; a igualdade também vale em zero.
Substituindo na energia completa:

\[
 Q_2(\varepsilon)=|S_2(\varepsilon)|^2+
   \sum_{i,j}c_ic_ja_i^2a_j^2C_2(\varepsilon a_i,\varepsilon a_j).
\]

Essa é a definição explícita `carryMaterialSecondNullEnergy`. Conserva o
quadrado do canal e todo o novo residual, com a orientação dos pareamentos.

A regularidade escalar fornece continuidade de `Q2` no centro, inclusive
para direções repetidas. Para reutilizá-la em `r2`, o lema anterior de
continuidade de `dslope f(e*a,e*b)` foi generalizado ao escalar `f`; o nome
e o enunciado anteriores permanecem como especialização. Não se mudou o
objeto material ao generalizar essa ferramenta.

As declarações que certificam essa etapa são
`material_second_reduced_hasDerivAt_zero`,
`material_second_reduced_deriv_continuous`,
`carryReal_scaledSlope_continuous` e
`carryMaterialSecondNullEnergy_continuous`. A primeira dá a derivada real
central de `r2`; a segunda fornece continuidade de sua derivada; as duas
últimas controlam diferenças divididas e a síntese finita completa.

Como `H'(0)=0`, temos `S2(0)=0`. A calibração do outro termo é:

\[
 L(0)=h_1/h_0,\qquad
 C_2(0,0)=\left(\frac{h_1}{h_0}\right)^2 r'_2(0)
          =\frac{h_0h_2-h_1^2}{h_0}=\gamma.
\]

Assim, `Q2(0)=gamma*M2²`. O teorema de limite é provado para qualquer
família fixa; o requisito `M1=0` entra na identificação de `epsilon⁴ Q2`
com a energia original. Se `M2!=0`, a positividade e a margem inferior
seguem da continuidade da expressão **completa**, sem eliminar o resto.

## 4. Regressões que distinguem os alcances

1. **Duas observações refletidas:** `c=(1,1)`, `a=(1,-1)`.
   Temos `M1=0`, `M2=2`. Essa é precisamente a combinação que o PR #9
   deixava sem decisão pelo termo de segunda ordem. Agora sua energia
   residual é estritamente positiva em pequenas escalas não nulas.
2. **Duplo cancelamento real:** `c=(3,-3,1)`, `a=(1,2,3)`.
   Aqui `M1=M2=0`, mas `M3=6`. O teste verifica que `Q2(e)` tende a zero;
   não afirma que a energia inteira seja zero nem decide seu sinal.
3. São preservadas as regressões das câmeras de 72, correção 79/62,
   quadraturas, domínio do relógio, dressing, retorno global e TFVD,
   quatro cruzamentos Green/retorno, reconstrução do par em zero e
   calibrações/no-gos anteriores. O exemplo `M1!=0` do PR #9 também permanece.

Não houve experimento numérico usado como certificado nesta rodada.

## Declarações novas e auditoria

- Módulo: `GeometryOfNumbers/Analysis/CarryMaterialSecondNullSector.lean`.
  Nove definições e oito teoremas públicos.
- Generalização conservativa no módulo anterior:
  `carryReal_scaledSlope_continuous` (um teorema público novo).
- Comparação externa: namespace `CarryMaterialSecondNullComparison`, com
  21 teoremas públicos, incluindo a margem inferior.
- Total: **30 teoremas novos, 9 definições, 39 roots públicos auditados**.

Os roots públicos têm guards transitivos sobre tipos e corpos e
`#print axioms`. A análise admite apenas `propext`, `Classical.choice` e
`Quot.sound`. A auditoria da Foundation permanece separada e vazia;
Geometry conserva seu próprio contrato de confiança. Não há novos axiomas,
`sorry`, `admit` ou escapes de confiança. A comparação externa usa pins
Lean/Mathlib/GreenFrame iguais, sem adicionar dependências ao Lake.

Build focado e completo com `--wfail`, auditorias das três zonas,
regressões e comparação externa com warnings como erros constam de
`research/material-second-null-sector/validation.json`, com logs e
`footprints.json`. Os pins e os arquivos preexistentes foram preservados.

## Status e próxima obrigação

| Status | Resultado |
| --- | --- |
| **Provado em Lean** | Transporte da segunda redução canônica para a mesma fonte material real, com regularidade e realidade explícitas. |
| **Provado em Lean** | Decomposição polarizada do residual anterior em canal positivo e residual completo, incluindo diagonais. |
| **Provado em Lean** | Fatoração exata de quarta ordem quando `M1=0`, calibração pelo discriminante e limite da energia rescalada. |
| **Provado em Lean** | Positividade e margem inferior para qualquer família fixa com `M1=0` e `M2!=0`. |
| **Com hipóteses explícitas** | Os lemas de infraestrutura recebem as identidades/regimes da fonte; a comparação externa verifica essas hipóteses para a fonte efetiva. |
| **Aberto** | Sinal no setor `M1=M2=0`, incluindo seus cruzamentos e o próximo resto. |
| **Aberto** | Controle uniforme em todas as famílias/ordens e realização positiva global do residual. |

**Fonte disponível → transformação existente → destino → identidade nova →
próxima lacuna:** fonte completada com relógio, retorno e dressing → resposta
real e segunda redução canônica já existente → residual polarizado e sua
síntese finita → fator `epsilon⁴`, coeficiente `gamma*M2²` e margem local →
**controlar o duplo cancelamento `M1=M2=0` sem apagar o próximo residual,
e distinguir esse controle por família de uma estimativa uniforme.**

Este resultado não preenche o certificado HP, não constrói outro operador
e não prova positividade em todas as ordens ou RH. Ele decide um novo setor
real que estava expressamente excluído do resultado anterior.
