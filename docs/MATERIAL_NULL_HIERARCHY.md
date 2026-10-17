# Transporte material em ordem arbitrária e positividade de ordem oito

## Resultado

Foi formalizada uma única lei de transporte para qualquer ordem finita
`k>=1` da **mesma energia residual** material dos PRs #8–#11. Para uma família
finita fixa de coeficientes reais `c_i` e direções reais `a_i`, escreva

\[
 M_j=\sum_i c_i a_i^j.
\]

Sob os cancelamentos `M1=...=M(k-1)=0`, temos, em escalas próximas de zero,

\[
 \boxed{E_R(\varepsilon)=\varepsilon^{2k}Q_k(\varepsilon)},\qquad
 Q_k(\varepsilon)\longrightarrow C_k M_k^2,
\]

com calibração literal pela fonte canônica:

\[
 \boxed{C_k=\begin{cases}
 h_k,& k\text{ ímpar},\\
 h_k-h_{k/2}^2/h_0,& k\text{ par},
 \end{cases}}
 \qquad h_j=\texttt{canonicalCompletedNativeLogDerivativeMoment}\ j.
\]

A identidade e o limite gerais **não recebem hipótese de sinal de `Ck`**.
A fatoração inclui zero; o limite do quociente `E_R(epsilon)/epsilon^(2k)`
é enunciado somente no filtro perfurado `nhdsWithin 0 {0}ᶜ`.

A aplicação desta rodada prova, a partir de um certificado já existente
para a própria fonte,

\[
 C_4=h_4-\frac{h_2^2}{h_0}>0.
\]

Portanto toda família fixa com `M1=M2=M3=0` e `M4!=0` tem energia residual
positiva em escalas não nulas suficientemente pequenas, com margem

\[
 E_R(\varepsilon)\ge\frac{C_4M_4^2}{2}\varepsilon^8.
\]

O teorema de ordem oito não pede ao usuário uma hipótese adicional de
positividade. A vizinhança depende da família e da ordem.

## Proveniência e objeto preservado

- Destino: `geometry-of-numbers`.
- Base: `e9acca7896674234db229ba498c6cf484a0d3d20`, merge do PR #11.
- Consulta externa somente de leitura: `carry-self-adjoint-operator`,
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

Os estados de semente, gradiente, retorno global, domínio do relógio,
dressing e reconstrução TFVD/Green anteriores permanecem sem alterações.
O ponto de partida é a resposta `r = carryMaterialNormalizedResponse`,
obtida **depois da síntese completada**, e o residual original

\[
 R(t,u)=\operatorname{Re}
  \left(\overline{r(t)}r(u)\operatorname{dslope}r_1(t,u)\right).
\]

A identificação anterior permite sua apresentação centralizada exata

\[
 R(t,u)=\operatorname{Re}\left(
 \operatorname{dslope}r(t,u)-\frac{A(t)A(u)}{h_0}\right),
 \quad A(t)=\operatorname{dslope}r(0,t).
\]

Essa igualdade, inclusive as diagonais, é reutilizada por
`material_residual_centered_kernel` do PR #11. A realidade dos escalares
no eixo real foi demonstrada; a notação complexa mantém o empacotamento das
duas quadraturas e a norma existente. Não foi criado outro kernel para
realizar uma matriz escolhida antecipadamente.

## 1. Uma identidade finita para todos os cancelamentos

Reutilizamos os shifts de Taylor centrais

\[
 T_0=r,\qquad T_{j+1}(t)=\operatorname{dslope}T_j(0,t).
\]

O índice `j` conta diferenças divididas; não é profundidade vertical,
raio, câmera ou índice material. Esses shifts tampouco são as respostas
obtidas pela cadeia de reduções recíprocas.

O PR #11 já fornecia `carryScalar_finite_energy_shift`: quando a soma dos
coeficientes de uma síntese é zero, ambos os argumentos de seu pareamento
são deslocados. A nova declaração `carryMaterial_kernel_power_transport`
itera essa identidade por indução em `k`:

\[
 \sum_{i,l}c_it_i c_lt_l\operatorname{dslope}T_2(t_i,t_l)
 =\sum_{i,l}c_it_i^k c_lt_l^k
          \operatorname{dslope}T_{2k}(t_i,t_l).
\]

As hipóteses são exatamente os momentos de ordens `1,...,k-1` nulos e a
regularidade escalar nas posições utilizadas. **Não foi exigido `M0=0`.**
Todas as somas são duplas e ordenadas, incluindo diagonais e direções
coincidentes.

A reconstrução `T_j(t)=T_j(0)+t*T_(j+1)(t)` transporta também o canal central:

\[
 \sum_i c_it_iT_2(t_i)=\sum_i c_it_i^kT_{k+1}(t_i).
\]

Esse é `carryMaterial_channel_power_transport`. Nenhum termo foi eliminado
antes da síntese. Os momentos anulam as somas de bordo correspondentes.

## 2. Correção central preservada na mesma ordem

Definimos somente a síntese calculada dos shifts da mesma resposta:

\[
 S_k(\varepsilon)=\sum_i c_ia_i^kT_{k+1}(\varepsilon a_i).
\]

A identidade completa é

\[
 \boxed{
 E_R(\varepsilon)=\varepsilon^{2k}\left[
 \sum_{i,l}c_ic_la_i^ka_l^k
  \operatorname{Re}\operatorname{dslope}T_{2k}
      (\varepsilon a_i,\varepsilon a_l)
 -\frac{|S_k(\varepsilon)|^2}{h_0}\right].}
\]

A expressão entre colchetes é `carryMaterialNullEnergy k c a epsilon`.
O canal central tem sinal negativo e conserva sua normalização original.
Não se atribui positividade ao primeiro termo ou ao resto por definição.

O canário de compatibilidade demonstra a igualdade **literal**, para todo
`epsilon`, entre `carryMaterialNullEnergy 3` e
`carryMaterialThirdNullEnergy` do PR #11. Com `T4(0)=0`, temos
`S3(epsilon)=epsilon*S4(epsilon)` na notação daquele PR; a correção aparece
como `-epsilon⁸*|S4|²/h0` na energia completa, exatamente como antes.

## 3. Coeficientes e regularidade de qualquer ordem

O PR #11 já provou para todo shift sua proveniência como germe da mesma
resposta analítica da fonte, sua regularidade local e a continuidade da
derivada no centro. A aplicação atual reutiliza esses teoremas e verifica
simultaneamente as condições para os finitíssimos shifts necessários a
cada `k`. Não se exige regularidade forte adicional do estado de Hilbert.

As identidades canônicas dos jets dão

\[
 T_{2k}(0)=0,\qquad T'_{2k}(0)=h_k.
\]

A síntese central tende a

\[
 S_k(0)=M_k T_{k+1}(0).
\]

A fonte tem somente coeficientes ímpares na resposta `r`. Assim,
`T_(k+1)(0)=0` para `k` ímpar e `T_(k+1)(0)=h_(k/2)` para `k` par.
Isso produz os dois valores de `Ck` sem alterar constantes.

A continuidade escalar de diferenças divididas rescaladas, incluindo
argumentos coincidentes, permite passar ao limite na soma **completa**.
A norma do canal central também permanece até a avaliação desse limite.

Os teoremas `material_null_energy_factor`, `material_null_energy_limit`
e `material_null_scaled_energy_limit` valem em qualquer ordem finita, sem
sinal presumido. `material_null_coefficient_even` e
`material_null_coefficient_odd` dão as duas calibrações acima.

Os corolários gerais de positividade e margem recebem explicitamente
`Ck>0` e `Mk!=0`. São consequências **condicionais** do transporte, não
provas de sinal em todas as ordens. A aplicação `k=4` demonstra o sinal
necessário pela fonte.

## 4. Ordem oito: sinal recuperado da própria fonte

O módulo existente `CompletedNativeChiralReturnTenthSourceIntegral.lean`
prova `nativeSourceFiveEvenBoundaryEnergy_pos`. Seu certificado provém das
integrais theta originais, antes de qualquer identificação com momentos
canônicos.

As relações existentes de proveniência dão literalmente

\[
 \texttt{nativeSourceOddBoundaryCoefficient}\ j=2h_j.
\]

A nova declaração `material_source_five_even_specialization` avalia a forma
nativa completa no vetor `(-h2/h0,0,1)`:

\[
 E_{\mathrm{five,even}}(-h_2/h_0,0,1)
 =2\left(h_4-h_2^2/h_0\right)=2C_4.
\]

O cruzamento entre a primeira e a terceira coordenada permanece na conta.
A terceira coordenada é um, garantindo não degenerescência. A positividade
do certificado nativo fornece `C4>0`; não foi postulada essa desigualdade.

Essa avaliação é usada para extrair um **sinal de coeficientes** da fonte.
Ela não é uma aplicação de estados entre os carriers da face e do material,
nem uma identificação isométrica ou uma realização positiva global do
residual. A passagem para a energia material usa a lei de transporte já
provada, com as normalizações literais.

## 5. Regressões, auditoria e limites

- Família `c=(-4,6,-4,1)`, `a=(1,2,3,4)`: `M1=M2=M3=0`, `M4=24` e `M0=-1`.
  Positividade local e limite de `Q4` igual a `576*C4` verificados em Lean.
- Igualdade exata da fórmula geral em `k=3` com o PR #11.
- Calibração ímpar em `k=5`, sem atribuir sinal a `h5` nesta rodada.
- Caso `Mk=0` produz coeficiente central zero; não se declara energia
  identicamente nula nem sinal do próximo resto.
- Regressões anteriores de 72, quadraturas, relógio, dressing, retorno global,
  TFVD e seus cruzamentos Green/retorno preservadas.

São **26 teoremas novos e 3 definições**, com **29 roots públicos** auditados
transitivamente por tipos e corpos. A análise usa somente os axiomas usuais
`propext`, `Classical.choice`, `Quot.sound`. Foundation e Geometry mantêm
seus próprios contratos e auditorias separados. Sem novos axiomas, `sorry`,
`admit` ou escapes de confiança.

O build focado tem 8.795 jobs e o completo 8.834, ambos com `--wfail`.
Regressões e comparação externa usam warnings como erros. Proveniência,
comandos, logs e footprints estão em `research/material-null-hierarchy/`.

| Status | Resultado |
| --- | --- |
| **Provado em Lean** | Transporte exato e limite de qualquer ordem finita, conservando a correção e os cruzamentos. |
| **Provado em Lean** | Fórmulas dos coeficientes pares e ímpares a partir dos jets originais. |
| **Condicional explícito** | Positividade por família numa ordem genérica quando seu coeficiente da fonte é positivo e seu momento não é nulo. |
| **Provado em Lean** | Sinal `C4>0`, limite, positividade e margem do setor de ordem oito, sem hipótese adicional de sinal. |
| **Aberto** | Sinal de toda a hierarquia, controle uniforme em ordem e famílias e realização positiva global do residual. |

O teorema vale para todo `k` finito, mas não fornece uma única vizinhança
que sirva para todos os `k,c,a`. O setor `M1=M2=M3=M4=0` não foi
decidido pelos teoremas de positividade desta rodada.
A identificação global com o Gram físico e o operador das alturas mantém
suas obrigações anteriores. Nenhum novo operador, métrica, amplitude,
fonte ou normalização foi introduzido.
