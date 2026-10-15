# Proveniência da fonte material Carry e transporte entre câmeras

Data: 2026-10-15. Repositório: `thiagomassensini/geometry-of-numbers`.

Base: PR #1, `1c530e7114fbaa2960e2c95209de307e6d939b83`.
Comparação: PR #106 de `carry-self-adjoint-operator`,
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
O inventário de arquivos, hashes e commits de última alteração está em
[`provenance.json`](../research/carry-material-camera-source/provenance.json).

## Resultado

Há uma fonte comum **já existente**: o estado
`GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCompletedBoundaryHilbertState`.
Foram construídas leituras lineares contínuas finitas desse mesmo estado nas
incidências inteiras do PR #1. Não foram escolhidos dois campos independentes.

Para 72, as leituras de passos 8 e 9 satisfazem, no Lean,

\[
B_3(t)=B_2(t)+\delta(t),\qquad
\delta(t)=g_t(79)-g_t(62),\quad
g_t(j)=f_t(j+2)-f_t(j+1).
\]

O Lean também prova `Re δ(0) > 0`, usando desigualdades racionais exatas para
raízes quadradas. Essa diferença pertence à fonte prescrita; não é um novo
contramodelo com campos livres. Conservar a mesma fonte não obriga segundas
diferenças de passos distintos a coincidirem.

A passagem da torre residual ao estado real central foi formalizada para
quantidades positivas em qualquer base positiva, com profundidade relacional
testemunhada. O pareamento cruzado das duas leituras preserva as nove
incidências ordenadas, suas multiplicidades e duas fases independentes.

Isso não identifica o pareamento global com o kernel Green canônico. A primeira
ponte adicional necessária é descrita ao final.

## 1. O que vem dos inteiros e o que exige uma entrada

Os nomes abaixo são declarações existentes, não resultados novos desta rodada.
O JSON de proveniência registra o commit de cada módulo, além dos dois merges
que fixam esta auditoria.

| Camada | Declarações e proveniência matemática | Dado adicional efetivo |
|---|---|---|
| Capacidade | `GeometryOfNumbers.Foundation.EmergentLocalCapacity`, `exists_emergentLocalCapacity`, em `FirstLocalReturnCapacity` | Trajetória, modelo local autônomo, apresentação finita e suas hipóteses. A emergência de uma capacidade não parte apenas de um inteiro isolado. |
| Torre | `GeometryOfNumbers.Foundation.emergentResidualTower`, `emergentResidualTower_expansion`, `residualTower_unique` | Base positiva, quantidade e corte. Reconstrução preserva prefixo e cauda. |
| Profundidade | `GeometryOfNumbers.Geometry.HasCarryDepthAtLeast`, `hasCarryDepthAtLeast_eq_scaled_tail`, `hasCarryDepthAtLeast_iff_dvd_pow` | Prefixo zero da torre original. Valuation é representação posterior; maximalidade prima exige as hipóteses do PR #1. |
| Incidências | `GeometryOfNumbers.Geometry.integerCameraTowerCell_reconstruction`, `integerCamera_common_integer`, `integerCamera_same_center_overlap` | A regra de célula do PR #1 escolhe raio `b^k`. Centro comum não identifica as pernas. |
| Reflexão | `GeometryOfNumbers.Geometry.reflect_leftLeg`, `reflect_involutive`, `centerDefect_constructed` | Centro e raio. O balanceamento ímpar tem suas condições próprias; não é automaticamente aplicável à câmera 2. |
| Segunda diferença | `GeometryOfNumbers.Geometry.centeredSecondDifference`, `balancedCarry_secondDifference_identity_shift` | As posições são aritméticas. Avaliar a diferença de um observável requer esse observável; o defeito aditivo dos próprios inteiros não determina sua imagem por uma função não linear. |
| Massa e amplitude | `GeometryOfNumbers.Foundation.canonicalResidualDepthMass_quadraticCompatibility_iff_half`, `foundational_half_scaling_capstone`; `GeometryOfNumbers.Analysis.realDepthMass_eq_inv_pow`, `realCriticalAmplitude_sq_eq_realDepthMass` | Compatibilidade quadrática é requisito explícito. A meia escala já estava provada; não determina fases, cruzamentos ou uma fonte global única. |
| Estado de profundidade | `GeometryOfNumbers.Analysis.realCriticalDepthState_energy` | Base, profundidade e ângulo. O ângulo é entrada. A energia é `x²+y²`; não foi escolhida outra métrica. |
| TFVD | `GeometryOfNumbers.Analysis.realCarryWeightedSecondDifference_gauge`, `realCarryTfvdSynthesis_comp_analysis` | Sequência de entrada e razão `0<eta<1`. A análise conserva interior e dois traços; síntese inclui Green e retorno. Índice vertical não é índice material nem ordem de jet. |
| Fonte material | `GeometryOfNumbers.Analysis.BaseTwoCompletion.criticalMaterialSample_eq_finiteMaterialOrbit` | A órbita usa `GeometryOfNumbers.Analysis.FiniteClockJets.historicalInitialState`, amplitude prescrita `n^(-1/2)`, e o relógio material existente. Tempo/fase é parâmetro externo. |
| Completação da fonte | `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCompletedBoundaryHilbertPrefixState_tendsto`, `baseTwoCompletedBoundaryHilbertReadout_eq_signal` | Gradiente da mesma fonte e retorno derivado da soma geométrica de células completas. Condições de convergência já provadas nessa construção. |
| Dressing | `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalResponse_eq_dressing_mul_signal`, `baseTwoVectorDressing_hasDerivAt` | Fatores canônicos existentes. Derivar um produto vetorial exige a regularidade vetorial indicada; não se deduz de derivadas coordenadas. |

Portanto, a cadeia efetivamente recuperada é: relações inteiras e incidências;
realização da massa/amplitude sob os requisitos anteriores; **lei de entrada e
fase já prescritas**; gradiente, retorno e completação dessa fonte; leituras
reais de suas incidências. A etapa em negrito não foi provada inevitável a
partir apenas da divisibilidade.

Há outra construção relevante:
`GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry`, em
`C2GlobalPhysicalBranchCanary`. Ela preserva norma e endereçamento material
ímpar, mas recebe `v : CoreState`. Não seleciona automaticamente esse estado
de entrada nem identifica toda a fonte material utilizada aqui.

## 2. Uma fonte existente, dois readouts contínuos

Escreva a fonte prescrita do repositório como

\[
f_t(n)=\frac{1}{\sqrt n}e^{-it\log n}\quad(n>0).
\]

Seu estado completado existente é

\[
Y_t=(f_t(1),\,(g_t,\beta_t))
\in\mathbb C\oplus_2(\ell^2(\mathbb N,\mathbb C)\oplus_2\mathbb C).
\]

`β_t` é o retorno de células completas construído em
`BaseTwoCompletedBoundaryLimit`, por limite de prefixos. Não o redefinimos
como uma diferença escolhida para acertar o sinal. A sequência bruta
`f_t(n)` não é colocada em `ℓ²`; usa-se o gradiente, cuja pertinência já estava
provada. O carrier, norma e readout completo são os anteriores.

O novo funcional `carryMaterialPointReadout n` lê

\[
P_n(Y)=Y_{seed}+\sum_{j<n-1}Y_{gradient}(j),\qquad P_n(Y_t)=f_t(n).
\]

A igualdade exige `n>0`. A definição total em zero não lhe atribui significado
de ponto físico logarítmico. Para uma célula com três posições positivas,
`carryMaterialCameraReadout` é o funcional `P_left-2P_center+P_right`.

São readouts **finitos** do estado completado; não são isometrias, nem o
readout de todo o retorno. A coordenada de retorno continua no carrier e no
pareamento completo, embora esses readouts finitos não a consultem.

## 3. Profundidade, núcleo horizontal e o mesmo centro

Se a torre dá `n=b^k m>0`, a nova identidade é

\[
\frac1{\sqrt{b^k m}}=b^{-k/2}m^{-1/2},\qquad
\mathbf f_t(n)=m^{-1/2}\,\mathrm{depthState}(b,k,-t\log n).
\]

`carryMaterialTower_center_realization` extrai `m` da **cauda da torre original**
e demonstra sua positividade pela reconstrução, sem substituir a profundidade
por valuation. `carryMaterial72_common_center` especializa as duas apresentações:

\[
9^{-1/2}\,\mathrm{depthState}(2,3,-t\log72)
=\mathbf f_t(72)
=8^{-1/2}\,\mathrm{depthState}(3,2,-t\log72).
\]

O fator horizontal vem da fonte anterior. Não foi ajustado para conservar
energias. As massas locais permanecem `1/8` e `1/9`, como no PR #1.

## 4. Transporte exato e os cruzamentos

As células são `(64,72,80)` e `(63,72,81)`. Assim,

\[
\begin{aligned}
B_2(t)&=f_t(64)-2f_t(72)+f_t(80),\\
B_3(t)&=f_t(63)-2f_t(72)+f_t(81),\\
\delta(t)&=f_t(81)-f_t(80)-f_t(64)+f_t(63).
\end{aligned}
\]

`carryMaterialCamera72_transport` demonstra a relação no carrier existente;
`carryMaterialCamera72_source_transport` a especializa à mesma família `Y_t`.
`carryMaterialCamera72_defect_zero_positive` prova, exatamente,

\[
\delta(0)=\frac1{\sqrt{63}}+\frac19-\frac18-\frac1{\sqrt{80}}>0.
\]

Esse é um defeito de mudança dos extremos da célula. Não o identificamos com
o retorno global `β`, com a conexão derivativa do dressing, ou com `D₄`.

Para **dois parâmetros independentes**, defina
`K(t,u;n,m)=conj(f_t(n))*f_u(m)`. O novo teorema
`carryMaterialCamera72_pairing` conserva os nove termos:

\[
\overline{B_2(t)}B_3(u)=
\sum_{i,j=0}^{2} a_i a_j K(t,u;n_i,m_j),
\quad a=(1,-2,1),\ n=(64,72,80),\ m=(63,72,81).
\]

As multiplicidades ordenadas são
`((1,-2,1),(-2,4,-2),(1,-2,1))`; o centro comum contribui com 4.
`carryMaterialSamplePair_phase` dá as duas partes, sem eliminar a fase:

\[
\operatorname{Re}K=\frac{\cos(t\log n-u\log m)}{\sqrt n\sqrt m},\qquad
\operatorname{Im}K=\frac{\sin(t\log n-u\log m)}{\sqrt n\sqrt m}.
\]

O ledger polarizado de transporte também foi formalizado:

\[
\overline{B_3(t)}B_3(u)=
\overline{B_2(t)}B_2(u)+\overline{B_2(t)}\delta(u)
+\overline{\delta(t)}B_2(u)+\overline{\delta(t)}\delta(u).
\]

Na diagonal, sua parte real fornece a diferença de energias. A condição
necessária e suficiente para conservá-las é
`2 Re(conj(B₂(t)) δ(t)) + |δ(t)|² = 0`. Esta consequência algébrica em texto
não é uma hipótese imposta, nem uma conclusão de conservação. Os termos
mistos precisam ser computados na fonte efetiva.

## 5. Dinâmica, quadraturas e comparação literal com o PR #106

Com `J(x,y)=(-y,x)` e o pareamento anterior `P(x,y)=x₁y₁+x₂y₂`, foram provadas

\[
\operatorname{Re}(\bar a b)=P(a^{real},b^{real}),\qquad
\operatorname{Im}(\bar a b)=P(Ja^{real},b^{real}).
\]

`carryMaterialCamera72_real_pairing` aplica as duas identidades aos nove
cruzamentos. O sinal e a ordem coincidem literalmente com
`CarrySelfAdjointOperator.RealQuadrature.pack_inner` do PR #106:
`inner(pack x,pack y) = inner_R(x,y) + i inner_R(Jx,y)`.
Isto é comparação de convenções e fórmulas; não foi construída uma aplicação
entre os dois carriers apenas por suas fórmulas se parecerem.

`carryMaterialCamera_clock_connection` prova, para qualquer célula positiva,

\[
B'(t)=-i\log(c) B(t)
-i\left[(\log l-\log c)f_t(l)+(\log r-\log c)f_t(r)\right].
\]

São derivadas finitas de coordenadas da fonte existente. A correção conserva
as frequências de cada perna. Nos gradientes consecutivos, a fonte anterior
tem exatamente `log(j+2)-log(j+1)`, em
`criticalMaterialGradient_deriv_eq_diagonalClock_add_residual`; o PR #106
conserva a mesma diferença em
`CarrySelfAdjointOperator.RealQuadrature.materialLogClock_edge_connection`.
Não foi afirmada diferenciabilidade forte de `Y_t`, nem jet holomorfo.

A forma complementar do PR #106 permanece

\[
C(x,y)=\langle x,y\rangle_{\mathbb R}
-\langle Tx,Ty\rangle_{\mathbb R},\qquad
C_{\mathbb C}(x,y)=C(x,y)+iC(Jx,y).
\]

Ela está em `CarrySelfAdjointOperator.RealFirstNative.towerComplement_pack_pairing`,
para a contração **prime-carry existente**. Nossos readouts não são essa
contração e não produzem automaticamente esse complemento.

## 6. Retorno, dressing e limites do resultado

`carryMaterial_completed_source_pairing` registra o produto interno completo
de `Y_t,Y_u`: semente, gradiente e retorno. A ortogonalidade desses três
summands vem do Hilbert produto previamente definido, e não autoriza declarar
independentes as câmeras que consultam o mesmo estado.

Reutilizando o dressing existente `D(t)`, foram provadas as especializações

\[
\ell(D(t)Y_t)=\mathrm{baseTwoCanonicalResponse}(t),\qquad
\langle D(t)Y_t,D(u)Y_u\rangle
=\overline{D(t)}D(u)\langle Y_t,Y_u\rangle.
\]

O retorno permanece dentro deste último produto. A regra derivativa do
dressing, quando suas hipóteses valem, inclui `D'Y`; não substituímos esse
termo pelos dois extremos `δ`.

As células nativas C2 usadas na soma histórica têm centro `4(k+1)` e raio 1.
As novas células escaladas do PR #1 não foram identificadas com essas células
nem com o perfil completo C3/Naimark. São novas consultas às posições inteiras
da **mesma fonte anterior**. A rota desta rodada lê suas duas quadraturas reais
a partir de um carrier complexo já existente; não demonstra por isso uma
construção global que anteceda historicamente a complexificação.

No carry, PR #105/#106 preservam `R=Gamma+Q`, `ER=0`, `EQ=-E Gamma` e os quatro
cruzamentos do escape. Sua identidade continua sendo
`D₄(z,w)=(w-conj z) K_R(z,w)-W_F(w,z)`, com `W_F(w,z)` nessa ordem.
Nenhum termo dessa identidade foi anulado ou substituído por `δ`.
Nenhuma divisão por `w-conj z` foi introduzida.

## 7. A primeira ponte que falta

**PROVADO:** a torre determina apresentações do mesmo inteiro; a fonte
material prescrita admite leituras contínuas nessas incidências; essas
leituras têm transporte com correção explícita e pareamento real completo.

**CONDICIONAL, já no repositório carry:** um estado com
`CarrySelfAdjointOperator.HasCompletedNativeRealAxisNormalizedGreenKernel`
e transporte tipado das incidências pode alimentar a rota
`CompletedNativeRealHPCarrierCertificate`. Essa interface exige, para dois
argumentos reais independentes onde a característica não zera,

\[
\langle\mathrm{normalizedCompletedGreenState}(F,Z,x),
\mathrm{normalizedCompletedGreenState}(F,Z,u)\rangle
=\mathrm{dslope}(\mathrm{completedGreenNormalizedResponse}(F,F_{comp}),x,u).
\]

**ABERTO:** construir `Z` a partir da síntese material completa efetiva,
preservando incidências, retorno, fase e o pareamento acima. Não há nesta
rodada uma identificação demonstrada entre `baseTwoCanonicalResponse` da
geometria e a característica completada utilizada no carry. É necessário
construir/verificar essa identificação normalizada, em vez de escolher um
Gram positivo ou ajustar sua constante central.

Para a rota de quadraturas, falta ainda o mapa concreto da semente,
gradientes e retorno material às coordenadas TFVD/Green/prime-carry corretas,
com ação sobre `J`, conexão material e domínios demonstrada. A propriedade de
preservar o pareamento deve ser provada para esse mapa; recebê-la como campo
de uma estrutura não prova sua existência. A calibração de ordem zero e o
primeiro cruzamento precisam ser verificados nessa identificação, que ainda
não foi construída.

Alternativamente, a interface existente
`CarrySelfAdjointOperator.HasCanonicalCompletedNativeTfvdGreenCenterLegReadout`
pede exatamente o coeficiente Green polarizado igual ao produto interno dos
**mesmos** jets TFVD, com testemunho centro–pernas fora da diagonal. A nova
identidade finita fornece proveniência de readouts, mas não esse teorema de
jets em todas as ordens.

Não se tentou preencher o antigo certificado complexo refutado pelo primeiro
jet ímpar nulo. Não se identificaram profundidade e jet, raio e profundidade,
câmera e índice material, norma vertical e Hankel canônico. O no-go existente
`completeCriticalVerticalObservabilityGram_not_canonicalHankel` permanece.

## 8. Código e validação reproduzível

Os módulos novos são `CarryMaterialSourceRealization.lean` e
`CarryMaterialCameraTransport.lean`, na camada Analysis. Há 34 raízes públicas:
27 teoremas e 7 definições. Todas são listadas em
[`public-roots.json`](../research/carry-material-camera-source/public-roots.json)
e registradas em `Analysis/Audit.lean`, com `#assert_analysis_axioms` e
`#print axioms`. O coletor transitivo verifica tipos e corpos.

Validação desta mudança:

- Build focado `lake build --wfail GeometryOfNumbers.Analysis.CarryMaterialCameraTransport`.
- Build completo `lake build --wfail`.
- `scripts/audit-foundation.sh`, `scripts/audit-geometry.sh`, `scripts/audit-analysis.sh`.
- Regressão das interfaces anteriores em
  [`Regression.lean`](../research/carry-material-camera-source/Regression.lean).
- Nenhum `sorry`, `admit`, axioma novo ou modificação de pins, fonte, métrica,
  pesos e normalizações. Foundation e Geometry não foram modificadas.

Os resultados e hashes dos registros de validação estão no arquivo
`validation.json` do mesmo diretório de evidências. As provas desta rodada
são teoremas finitos e de readout; nenhuma positividade geral dos momentos,
identificação espectral ou conclusão sobre RH foi obtida.
