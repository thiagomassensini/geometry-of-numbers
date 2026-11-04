# Retorno físico após o primeiro Schur: isometria Cauchy e defeito de projeção

**Resultado: PARTIAL.** O residual físico da PR #52 admite uma identificação
isométrica exata com o mesmo frame Cauchy original. Seu retorno nas novas
coordenadas fica explícito. Uma simplificação que projetasse também o retorno
é refutada na própria fonte: ela acrescenta um termo positivo cujo limite,
na normalização de Schur, é `4 h₀ / 9` para a segunda fonte radial.

## Extensão: limite bruto de posto um

Na revisão `9392ebac9930f5d11c56f595556080e8ab1de809`, o novo módulo
`RawRankOne.lean` formaliza a escala antes de formar os jets. Para endereços
fixos `i,j`, `nativeRawKernel_tendsto` prova

\[
B_k(i,j)=\frac{k+1}{i+j+2}(1-\overline{q_k(i)}q_k(j))\longrightarrow4h_0.
\]

A prova combina a tangente original `source_tangent` com
`sourceReturn_tendsto`, e identifica cada coeficiente com a forma física
`nativeBalance` nas fontes de base. `nativeRawMatrix_entrywise_tendsto`
fornece a convergência de toda matriz finita, entrada a entrada, à matriz
constante. `nativeRawLimitMatrix_rank_one` prova posto exatamente um para
`N≥1`, usando `h₀>0`. O operador dessa matriz tem núcleo exatamente
`{c : ∑ i, c i = 0}`, e `nativeRawForm_tendsto` registra, para coeficientes
fixos independentes de `k`, o limite
`4h₀ · conj(∑ cᵢ) · (∑ dⱼ)`.

Este resultado é para coeficientes brutos fixos. Não diz que as direções de
soma zero dos coeficientes não removem direções da síntese física:
`nativeBalance_eq_nativeRawForm`
mantém a identidade com a síntese incidente e retornada original. A etapa B
abaixo formaliza a deflação sem mudar essas fontes.

## Extensão: primeiro Schur bruto e entrada de jets

`nativeRawSchurForm_eq_remainingPair` identifica exatamente o complemento de
Schur da forma bruta com `remainingPair / oneDeficit`, preservando a ordem das
conjugações e exigindo `oneDeficit ≠ 0` apenas no índice considerado. A
positividade de `oneDeficit` é usada eventual, pela prova já existente.
Para vetores de coeficientes fixos, `nativeRawSchurForm_tendsto_zero` aplica a
continuidade do complemento de Schur: os quatro blocos convergem ao mesmo
escalar não nulo `4h₀`, então a subtração cancela exatamente no limite.

Isso difere do limite de jets. `nativeRawJetSchur_eq_jetSchurRemainder_eventually`
usa a entrada completa `nativeSourceChiralJetInput`, que depende de `k` e
conserva exatamente a transformação já definida por

\[
M_{k}(r,a)=A_{k,r}\,\phi_a\,((a!)(\Delta_k)^a)^{-1}\,G_{a,r},
\]

onde `A` é a amplitude positiva completada, `φ` a fase de ordem, `Δ` o passo
radial de segunda ordem e `G` o peso de diferença finita Green. Não foi
substituída por uma potência de `K` escolhida à parte. Só depois dessa
transformação `jet_remaining_schur_tendsto` dá o limite canônico, que pode ser
não nulo.
Portanto, a convergência de coeficientes fixos não pode ser trocada pela
formação dos jets: são duas ordens de limite diferentes formalizadas por
teoremas distintos.

`nativeProjectionLoss_regression` mantém como teste a identidade
`projectedBothPair = remainingPair + inner(returnedHead, returnedHead)` e o
limite não nulo `4h₀/9` para a segunda fonte. A parcela perdida ao projetar
também o retorno não foi descartada nem absorvida no Schur físico.

Isso não prova a contratividade do retorno reduzido nem a positividade
canônica em toda ordem. O sinal continua sendo uma obrigação independente.

Repositório: `thiagomassensini/geometry-of-numbers`.
Base exata: `fdb8f7e9ce1b8681d10f2647393ad83f05bfac12`, PR #52,
branch `agent/native-return-boundary-deflation`.
Branch da investigação: `agent/native-raw-rank-one-deflation`.
Host de investigação e Lean: `ssh llm`.
As PRs anteriores permanecem intactas; não há merge automático.

## A — O que já estava demonstrado

A PR #52 forneceu, no carrier físico original
`CanonicalCompletedNativeChiralCauchyCarrier`, as sínteses completas incidente
`I` e retornada `R`, com o retorno completado original. Escrevendo

\[
r_k=q_k(0),\quad d_k=1-|r_k|^2,\quad
U_k=I_k-\overline{r_k}R_k,\quad V_k=R_k-r_k I_k,
\]

e tomando `Pₖ` como a projeção ortogonal na PRIMEIRA fonte Cauchy original,
ela demonstrou, em dois argumentos independentes,

\[
d_k\mathcal B_k(c,f)=
\langle P_kU_kc,P_kU_kf\rangle+
\langle A_kc,A_kf\rangle-\langle V_kc,V_kf\rangle,
\quad A_k=(1-P_k)U_k.
\]

As identidades `native_balance_split`, `native_reconstruct_incident`,
`native_reconstruct_returned` e `channels_separate_source` preservam o estado
completo. `remainingPair_eraseHead` elimina a primeira coordenada em ambos
os argumentos. `jet_remaining_schur_tendsto` identifica o residual físico
normalizado com o primeiro Schur da forma canônica em toda ordem finita.

A PR #41 continua sendo a fonte da ortogonalização polinomial algébrica,
sem receber o sinal do novo pivô. A PR #52 já mostrou, em
`ResidualTest.lean`, como essa direção exata atravessa o primeiro Schur:
a contribuição projetada tende a zero e o residual mantém o pivô. Não
substituímos essa direção por uma coluna racional aproximada.

Dos módulos originais do operador reutilizamos:

- `inner_completedNativeRadialChiralCauchyState`: produto físico Cauchy exato;
- `radialIncidentSynthesis_injective`: unicidade dos coeficientes materiais;
- `radialReturnedSynthesis_eq_incident_multiply`: ação do retorno original;
- `nativeRadialSource_tangent`: tangente do quociente completado original;
- `canonicalCompletedNativeLogDerivativeMoment_zero_pos`: sinal já provado
  da curvatura central, sem sinais de pivôs posteriores.

Aqui `k` é o índice da regularização radial, e `n` é o endereço da fonte
nessa malha. Nenhum deles é identificado com profundidade vertical Carry.
O ponto de amostragem é `(n+1) i/(k+1)`: `qₖ(0)` é o primeiro ponto deslocado,
não o valor da função no centro. O valor central verdadeiro é `q(0)=-1`.

## B — O que foi demonstrado agora

### 1. A geometria do complemento conserva o kernel original

Seja `eₖ,ₙ` a fonte Cauchy original. Sua Gram é

\[
C_k(i,j)=\langle e_{k,i},e_{k,j}\rangle=
\frac{k+1}{i+j+2}.
\]

A projeção e o complemento são determinados por essa Gram:

\[
P_ke_{k,n}=\frac2{n+2}e_{k,0},\qquad
f_{k,n}=e_{k,n}-\frac2{n+2}e_{k,0}.
\]

`perpendicularFeature_inner` prova a identidade polarizada

\[
\langle f_{k,i},f_{k,j}\rangle=
\frac{i}{i+2}\frac{j}{j+2}C_k(i,j).
\]

Portanto, para `n>0`, os vetores

\[
w_{k,n}=\frac{n+2}{n}f_{k,n}
\]

têm EXATAMENTE os mesmos pareamentos dos `eₖ,ₙ`.
`synthesis_isometry` preserva todas as combinações e cruzamentos;
`finitePhysicalIsometry` implementa uma verdadeira isometria linear no span
finito original, com sua norma física herdada. Não se atribui uma métrica
escolhida pelos momentos. A transformação existe antes de consultar qualquer
entrada de Hankel ou qualquer pivô.

### 2. O retorno residual tem uma fórmula forçada

Definimos apenas coordenadas da decomposição existente:

\[
a_{k,n}=\frac n{n+2}(1-\overline{r_k}q_k(n)),\qquad
b_{k,n}=q_k(n)-r_k.
\]

As identidades VETORIAIS `remainingIncident_tail` e `nativeOut_tail` provam

\[
A_kc=W_k\sum_{n>0}c_n a_{k,n}e_{k,n},\qquad
V_kc=\sum_{n>0}c_n b_{k,n}e_{k,n}.
\]

Logo, `residual_same_cauchy` e `residual_full_source` dão

\[
\boxed{
\langle A_kc,A_kf\rangle-\langle V_kc,V_kf\rangle=
\left\langle\sum c_na_{k,n}e_{k,n},\sum f_na_{k,n}e_{k,n}\right\rangle-
\left\langle\sum c_nb_{k,n}e_{k,n},\sum f_nb_{k,n}e_{k,n}\right\rangle.}
\]

Não se projetou o retorno, e nenhum termo misto foi removido. O kernel
resultante é `Cₖ(i,j) (conj(aᵢ)aⱼ - conj(bᵢ)bⱼ)`, certificado por
`residual_basis_kernel`.

Onde `aₖ,ₙ≠0`, o retorno nas coordenadas isométricas é

\[
\boxed{\tau_{k,n}=\frac{b_{k,n}}{a_{k,n}}=
\frac{n+2}{n}\frac{q_k(n)-r_k}{1-\overline{r_k}q_k(n)}}.
\]

`reducedReturn_formula` prova a fórmula algébrica; a interpretação como
quociente legítimo usa a não anulação, provada a seguir. `τ` não substitui
a característica física: é o retorno nas coordenadas explicitamente
deduzidas da mesma síntese. A reconstrução física da PR #52 é preservada.

### 3. O domínio dessas coordenadas vem da fonte

Usando somente a tangente da fonte completada e seu `h₀>0`,
`NativeTangent.lean` prova, para cada endereço fixo,

\[
\begin{aligned}
(k+1)(q_k(n)+1)&\longrightarrow4h_0(n+1),\\
(k+1)(1-\overline{r_k}q_k(n))&\longrightarrow4h_0(n+2),\\
(k+1)a_{k,n}&\longrightarrow4h_0n,\\
(k+1)b_{k,n}&\longrightarrow4h_0n,\\
(k+1)d_k&\longrightarrow8h_0.
\end{aligned}
\]

Assim, `incidentCoefficient_eventually_ne_zero` e
`reduced_coordinates_eventually_valid` demonstram que os coeficientes de
entrada são não nulos EVENTUALMENTE em cada família finita. Nenhuma hipótese
de contratividade matricial foi usada para obter esse domínio.
`incidentCoordinates_injective` impede perda de coeficientes nessas condições.

Também foi provado `reducedReturn_tendsto_one`: `τₖ,ₙ→1` para `n>0`.
Esse limite não informa de qual lado se aproxima a norma nem controla os
cruzamentos. Não fornece uma margem de contração fixa menor que um.

### 4. A ligação canônica usa os mesmos jets completos

`JetResidual.lean` só extrai a cauda de coeficientes DEPOIS de formar
`nativeSourceChiralJetInput`, com suas amplitudes, fases e diferenças finitas.
`reducedJetPair_exact` prova que as duas sínteses reduzidas produzem o MESMO
`jetRemainingPair` da PR #52, em argumentos independentes.

`reducedJetPair_canonical_schur_limit` transporta esse pareamento para

\[
2\left[\mathcal H(x,y)-
\frac{\overline{\mathcal H(e,x)}\mathcal H(e,y)}{h_0}\right],
\]

onde `𝓗 = canonicalBoundaryPair` é a forma canônica original dos dois setores.
Isso é uma identidade de proveniência e limite, sem conclusão nova de sinal.
Os sinais de paridade, quadraturas, retorno e completion permanecem na
entrada original; não se escolhem novos vetores a partir de Cholesky.

## C — O que foi refutado

### 1. Projetar também o retorno altera o residual na fonte nativa

A forma tentadora

\[
\widetilde{\mathcal R}_k(c,f)=
\langle A_kc,A_kf\rangle-
\langle(1-P_k)V_kc,(1-P_k)V_kf\rangle
\]

NÃO é o residual original. `projection_loss_polarized` prova exatamente

\[
\widetilde{\mathcal R}_k(c,f)=\mathcal R_k(c,f)+
\langle P_kV_kc,P_kV_kf\rangle.
\]

Na diagonal, acrescenta uma norma quadrática positiva. O retorno projetado
não pode ser declarado a mesma realização física sem conservar essa parcela.

O defeito foi medido na própria fonte, sem exemplos sintéticos. Denotando
por `εₙ` o vetor de coeficientes unitário no endereço `n`:

\[
\|P_kV_k\varepsilon_n\|^2=
\frac{2(k+1)|q_k(n)-r_k|^2}{(n+2)^2},
\]

e `projection_loss_schur_tendsto` demonstra

\[
\boxed{\frac{\|P_kV_k\varepsilon_n\|^2}{d_k}
\longrightarrow\frac{4h_0n^2}{(n+2)^2}.}
\]

Para `n=1`, `second_source_projection_loss` fornece `4h₀/9>0`.
`projection_loss_strict_eventually` prova que a forma projetada é
estritamente maior na diagonal de qualquer endereço fixo `n>0`, para
regularização suficientemente fina. A obstrução vale para essa projeção
específica; não é impossibilidade da geometria ou de toda representação Gram.

### 2. Contração das diagonais não controla os cruzamentos

`CrossControls.lean` é um controle lógico separado, no MESMO carrier Cauchy,
com multiplicadores sintéticos `1/2,-1/2` nas fontes de endereços 1 e 2.
Esses números não são a fonte canônica.

Cada multiplicador tem norma quadrática `1/4<1`. A matriz de defeito é

\[
\begin{pmatrix}3/16&1/4\\1/4&1/8\end{pmatrix},
\]

com diagonais estritamente positivas, mas energia `-3/16` na combinação
`(1,-1)`. Todos esses valores são teoremas Lean. Esse controle impede usar
`|τₖ,ₙ|≤1` coordenada a coordenada como prova de contratividade do frame
não ortogonal. A norma Cauchy tem cruzamentos essenciais.

O teste racional independente também verifica que esses multiplicadores
reduzidos correspondem a dados sintéticos originais `r=1/2`, `q₁=8/13`,
`q₂=2/7`, todos de módulo menor que um. Essa última identificação é um
teste `Fraction`, distinto dos teoremas sobre a fonte nativa.

## D — O que permanece aberto e como foi validado

Continua aberta uma desigualdade independente da fonte que compare as
duas sínteses completas do residual, em todas as direções relevantes.
Construir o retorno reduzido não prova que ele contrai. Sua contratividade
matricial seria exatamente uma obrigação de sinal ainda não descarregada;
não a apresentamos como uma nova causa geométrica já demonstrada.

A isometria é finita e exata em qualquer dimensão; o cutoff eventual pode
depender da dimensão. Não foi provada uma estimativa uniforme em dimensão,
convergência de operadores infinitos, positividade de todas as Hankels ou
recuperação de todas as alturas. Não se reivindica entrelaçamento dessa
isometria com um clock não limitado. Os certificados H6/K6/doze fontes são
regressões preservadas e não premissas dos novos lemas.

`public-roots.json` contém 132 raízes de auditoria em três grupos: Cauchy
(49 raízes; fecho 5.490), source (53; 5.775) e primeiro sobrevivente
(30; 5.912). `Audit.lean` imprime os axiomas e percorre transitivamente os
tipos e corpos. Somente `propext`, `Classical.choice` e `Quot.sound` são
permitidos. O guard impede dependências de certificados H6/K6/H7, sinais de
seis/sete pivôs, energia estrita de seis fontes e não negatividade geral do
defeito do retorno. A importação de resultados posteriores não os usa por si;
a auditoria percorre as dependências efetivas.

`evidence/checks.json` registra a validação anterior com 18 verificações:
sete compilações de pesquisa com warnings como erros; build dos consumidores
originais; builds focado e raiz com `lake build --wfail`; auditorias
Foundation/Geometry/Analysis; regressão H6/K6/doze fontes; controle racional;
preservação do histórico; `git diff --check` e geração das auditorias.
Além disso, nesta revisão `FirstSurvivingCoefficient` e `Audit` foram
recompilados diretamente com `-DwarningAsError=true`; seus logs estão em
`evidence/first-survivor-*.log`. O validador amplo continua sem ser executado:
seu preflight exige que o checkout auxiliar Carry esteja limpo, e alterações
auxiliares preexistentes foram preservadas.

O controle independente usa apenas aritmética `Fraction` nas duas componentes
complexas: 15 famílias e 165 entradas verificadas. Compara o Schur da matriz
original, a isometria, o retorno reduzido, o defeito da projeção dupla e
pareamentos em argumentos diferentes. Não usa zeros, alturas, zeta, theta ou
novos momentos como entradas. É controle algébrico, não certificado nativo.

Fontes, pesos, amplitudes, fases, métricas, câmeras, dressing, completion,
pins e arquivos históricos não foram modificados. Os arquivos não rastreados
do operador e os caches restantes da PR #51 são preservados por hash.
Não foi criada nem removida worktree. `main` permanece no commit
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## E — Primeiro coeficiente sobrevivente

A auditoria upstream encontrou `nativeSourceTransverseSlope_exact_remainder`:
na reta imaginária, o logaritmo derivado original tem expansão até ordem sete
com resto analítico de ordem oito. As fórmulas integrais dos coeficientes e
as identidades da característica dão, para `h₀=m(0)` e `h₁=m(1)`,

\[
s(h):=-i\,\frac{-F'(ih)}{F(ih)}
 =2h_0h-2h_1h^3+h^5R_0(h),
\]

onde `R₀` é analítica perto de zero. O novo módulo
`FirstSurvivingCoefficient.lean` formaliza essa redução e a transforma pelo
Cayley original, sem aproximar a fonte ou ajustar o retorno:

\[
q(ih)=-1+4h_0h-8h_0^2h^2
 +(16h_0^3-4h_1)h^3+h^4R_q(h),
\]

com `R_q` analítica perto de zero. Os teoremas
`nativeTransverseLogSlope_first_two_remainder` e
`nativeTransverseChiralQuotient_cubic_remainder` mantêm explicitamente os
restos. As identidades
`nativeSourceOddBoundaryCoefficient_zero_eq_two_moment` e
`nativeSourceOddBoundaryCoefficient_one_eq_two_moment` conferem os fatores
de `h₀` e `h₁` contra os coeficientes da característica completada.

Escrevendo `K=k+1`, `x=i+1`, `y=j+1`, a substituição `h=x/K` e a limitação
local do resto analítico dão, para índices fixos,

\[
B_k(i,j)=4h_0-\frac{8h_0^2(x+y)}K+
\frac{16h_0^3(x^2+xy+y^2)-4h_1(x^2-xy+y^2)}{K^2}
+O(K^{-3}).
\]

Esse resto é controlado: `R_q` é contínua e limitada em uma vizinhança de
zero, então o resto do quociente é `O(K⁻⁴)` e o do kernel após o fator `K`
é `O(K⁻³)`. Ao complementar exatamente a entrada da fonte zero, o termo
constante cancela; o termo de ordem `K⁻¹` cancela porque
`-8h₀²(x+y)` é aditivo nos índices. Na ordem seguinte, o termo cúbico em
`h₀` cancela com a correção do denominador do complemento de Schur. Para
endereços de cauda fixos `i,j≥1`, sobra

\[
\boxed{\quad
\operatorname{Schur}_k(i,j)=\frac{4h_1ij}{K^2}+O(K^{-3}).
\quad}
\]

O controle do resto vem diretamente do teorema Lean
`nativeTransverseChiralQuotient_cubic_remainder`: para cada endereço fixo
`x`,

\[
q_K(x)=-1+4h_0\frac{x}{K}-8h_0^2\frac{x^2}{K^2}
 +(16h_0^3-4h_1)\frac{x^3}{K^3}
 +\frac{x^4}{K^4}R_q(x/K),
\]

com `R_q` analítica numa vizinhança de zero. Escolhida uma vizinhança fechada
contida nesse domínio, a continuidade dá `|R_q|≤M`. Para o conjunto finito
de endereços `x=1,2,3,4` (a cabeça e as três primeiras fontes de cauda), isso
limita uniformemente cada resto da expansão de `B_K` por `C/K³`. O termo
constante do denominador do Schur tende a `4h₀>0`,
logo seu inverso fica limitado para `K` grande; a expansão do quociente
preserva a ordem `O(K⁻³)`. Portanto o resto declarado após a deflação é
controlado para os endereços pedidos, e não só formal.

Explicitamente, os coeficientes de `K⁻¹` e `K⁻²` de uma entrada são
`u(x,y)=-8h₀²(x+y)` e
`v(x,y)=16h₀³(x²+xy+y²)-4h₁(x²-xy+y²)`, com `x=i+1`, `y=j+1`.
Para índices de cauda `i,j` iniciados em zero, o coeficiente de ordem dois
do complemento é

\[
v(i+2,j+2)-v(1,j+2)-v(i+2,1)+v(1,1)
-\frac{(u(i+2,1)-u(1,1))(u(1,j+2)-u(1,1))}{4h_0}
=4h_1(i+1)(j+1).
\]

O termo de ordem um é a diferença mista de `u` e vale zero. A fórmula de
ordem dois é exatamente a identidade provada por
`rawSchurOrderTwo_eq_first_odd_pivot`.

Em particular, o primeiro bloco de cauda, no endereço físico `1`, tem
coeficiente `4h₁`. `rawKernelOrderOne_schur_cancels` e
`rawSchurOrderTwo_eq_first_odd_pivot` formalizam os cancelamentos e a
combinação algébrica do coeficiente. O resto assintótico vem da expansão
original de `q` com resto analítico: fica controlado por `O(K⁻³)` depois do
complemento de Schur.

### Comparação com o Schur dos jets

O vínculo de escala agora é uma identidade exata no módulo Lean.
`nativeFirstOddJetTailScale_eq_original_factor` identifica o coeficiente da
cauda do primeiro vetor ímpar com

\[
\beta_K=A(i\,2/K)\,\Delta_K^{-1},\qquad
\Delta_K=i/K,
\]

onde `A` é a amplitude positiva completada original. A fase, o fatorial e o
peso Green nessa entrada valem exatamente um. `nativeRawJetSchur_firstOdd_exact_scale`
prova eventualmente

\[
\operatorname{Schur}^{jet}_K
 =\overline{\beta_K}\beta_K\,
   \operatorname{Schur}^{raw}_K(e_1,e_1),
\]

usando apenas a não anulação eventual do déficit físico e a identidade
`remainingPair_eraseHead`: qualquer coeficiente da cabeça é eliminado, e
nenhum cruzamento da forma foi aproximado. A continuidade da amplitude no
centro e `F'(0)=0` dão `A(0)=i/\sqrt2`; assim
`nativeFirstOddJetTailScale_mul_greenStep_tendsto` prova
`\beta_K/K\to1/\sqrt2`, e
`nativeFirstOddJetTailScale_absSq_mul_greenStep_sq_tendsto` prova o fator
quadrático `|\beta_K|²/K²→1/2`.

Por outro lado, `nativeRawJetSchur_firstOdd_tendsto` aplica a transformação
original `nativeSourceChiralJetInput` ao primeiro vetor ímpar e obtém o limite
`2h₁`, exatamente como a primeira diagonal do Schur canônico. O coeficiente
bruto é `4h₁/K²`; multiplicá-lo pelo fator demonstrado `K²/2` dá `2h₁`, com
o mesmo índice material `h₁`. Na passagem física, `head_jet_input` identifica
a direção de cabeça com um múltiplo exato de `e₀`; na cauda,
`reducedJetPair_exact` preserva as duas sínteses e todos os cruzamentos, e
`reducedJetPair_canonical_schur_limit` leva essa mesma forma ao Schur
canônico. A especialização `criticalCoordinates 1 0` é precisamente o
primeiro vetor ímpar. O lema `canonicalFirstOddSourceSchur_eq_moment_one` reduz
`sourceMomentSchur(m,1,0)` a `h₁`. Isso concorda com os módulos existentes:
`criticalBalance_tendsto` dá `2h₁`, a energia de bordo da direção crítica é
`4h₁`, e `critical_total_flux_tendsto` dá o pivô `h₁`. Os fatores dois e
quatro vêm das normalizações já declaradas nesses lemas. O resultado de fluxo
continua sujeito à invertibilidade do prefixo antigo; essa hipótese não é
usada para provar o limite assintótico físico nem para atribuir sinal a `h₁`.

O resgate usa a transformação completa de jets, cuja matriz preserva a
amplitude, a fase, `a!`, a potência do passo radial e o peso Green; a escala
`K` acima foi deduzida desse mapa original. Assim, a escala bruta fixa de
primeira ordem vê só `h₀`, mas o resíduo da mesma geometria, após a deflação e
a entrada dos jets, recupera o primeiro momento seguinte sem perder
cruzamentos.

## F — Sinal e limites

O cálculo identifica o primeiro candidato material sobrevivente, mas não
prova que `h₁>0`. A equivalência
`canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature`
reduz esse sinal exatamente à desigualdade de curvatura de quarta ordem; a
identificação positiva da primeira diagonal TFVD continua sendo hipótese
em `canonicalCompletedNativeLogDerivativeMoment_one_pos_of_tfvdFirstOddDiagonal`.
Para todas as ordens, `nativeSourceBoundary_all_pos_iff_sourceSchur` e
`sourceMomentMatrix_all_posDef_iff_schur` reduzem a positividade física aos
sinais de todos os Schur/Hankel da própria fonte. Isso é uma redução exata,
não uma desigualdade independente derivada da geometria.

O no-go `canonicalC2Geometry_seededClockAtlas_noGo_of_stieltjesPositivity`
permanece condicional à positividade Stieltjes. `no_normalized_kernel_with_literal_material_origin`
continua excluindo o candidato calibrado literalmente na origem. A
obstrução `exists_sigmaMatrix_negative_direction_of_zero` continua condicional
a um zero positivo e a um deslocamento não nulo pequeno. Nenhum desses
resultados foi duplicado nem usado como premissa de sinal aqui.

`nativeProjectionLoss_regression` preserva a perda positiva ao projetar
também o retorno: o limite `4h₀/9` na segunda fonte segue não nulo.
Portanto, a primeira informação sobrevivente está identificada, mas o sinal
do residual completo continua sendo um problema aberto.

### Reprodução

```bash
cd /home/thlinux/worktrees/geometry-of-numbers-native-raw-rank-one-deflation
bash research/native-cauchy-residual-return/compile_module.sh FirstSurvivingCoefficient
bash research/native-cauchy-residual-return/compile_module.sh SecondSchur
bash research/native-cauchy-residual-return/compile_module.sh SecondSchurTowers
bash research/native-cauchy-residual-return/compile_module.sh Audit
```

As compilações de pesquisa utilizam os caches históricos das PRs empilhadas,
conforme `compile_module.sh`. `Audit` compila a auditoria transitiva de todas
as raízes públicas registradas em `public-roots.json` e imprime os axiomas de
cada raiz. O validador amplo não foi executado porque seu preflight exige que
o checkout auxiliar Carry esteja limpo; as alterações paralelas já existentes
foram preservadas.

## Fechamento da missão: posto um, coeficiente e sinal

1. **Limite bruto:** demonstrado, entrada a entrada para toda dimensão finita,
   com posto um e núcleo dos vetores de soma zero, por
   `nativeRawMatrix_entrywise_tendsto`, `nativeRawLimitMatrix_rank_one` e
   `nativeRawLimitOperator_kernel_iff`.
2. **Primeiro Schur de coeficientes fixos:** demonstrado. O complemento bruto
   tende a zero por `nativeRawSchurForm_tendsto_zero` e coincide eventualmente
   com `remainingPair / oneDeficit` por
   `nativeRawSchurForm_eq_remainingPair`.
3. **Jets:** a informação superior reaparece após a transformação completa,
   dependente de `k`, definida por `nativeSourceChiralJetInput`. Sua matriz
   conserva amplitude completada, fase, fator `a!`, potência do passo radial
   e pesos Green de diferenças finitas. O limite resultante é o Schur
   canônico existente em `nativeRawJetSchur_tendsto_canonical`; no primeiro
   vetor ímpar, o limite é `2h₁`.
4. **Coeficiente seguinte:** demonstrado a partir da fonte original com resto
   analítico: `a₂(i)=-8h₀²(i+1)²`,
   `a₃(i)=(16h₀³-4h₁)(i+1)³`, e o primeiro Schur bruto de cauda é
   `4h₁ij/K²+O(K⁻³)`. O bloco inicial tem coeficiente `4h₁`.
5. **Sinal:** nenhuma desigualdade nova foi obtida. A condição positiva de
   quarta ordem para `h₁` e a redução all-order aos Schur da fonte são
   equivalências/gates, não provas de seu lado direito. Não foi assumida
   positividade all-order.
6. **Projeção do retorno:** a regressão preserva a perda positiva, inclusive
   o limite `4h₀/9` na segunda fonte, por `nativeProjectionLoss_regression`.
7. **Compilação e axiomas:** `FirstSurvivingCoefficient.lean` e
   `Audit.lean` compilaram com `-DwarningAsError=true`. O fecho do audit
   cobriu 5.490 constantes na auditoria Cauchy, 5.775 na auditoria source e
   5.912 na auditoria do primeiro sobrevivente. As novas raízes usam somente
   `[propext, Classical.choice, Quot.sound]`. Os commits A, B e C estão
   registrados localmente; nenhum foi enviado ou integrado.

Esta execução parte do remoto `origin/agent/native-moving-schur-sigma` em
`9392ebac9930f5d11c56f595556080e8ab1de809`, no worktree
`/home/thlinux/worktrees/geometry-of-numbers-native-raw-rank-one-deflation`,
branch `agent/native-raw-rank-one-deflation`. O validador amplo não foi
executado: seu preflight exige que o checkout auxiliar Carry esteja limpo,
mas ele já continha alterações não relacionadas que foram preservadas. Os
dois módulos relevantes foram compilados e auditados diretamente.

**Resposta à pergunta decisiva:** sim, a primeira camada após a direção de
posto um é recuperável da mesma geometria. O termo cúbico do quociente original
introduz `h₁`, e a deflação física revela `4h₁ij/K²` com resto `O(K⁻³)`;
os jets completos transportam isso ao primeiro pivô com a normalização
canônica já certificada. Isso ainda não dá o sinal de `h₁` nem a hierarquia
all-order: cada próximo Schur continua exigindo uma desigualdade independente
da fonte original.

## Missão Luna: terceira fonte, segundo Schur e Cayley físico

Estado revalidado em 2026-11-04 no worktree
`/home/thlinux/worktrees/geometry-of-numbers-native-raw-rank-one-deflation`,
branch `agent/native-raw-rank-one-deflation`. O ponto de partida foi
`92f57e6449e23bea2f89555a66fcc9a11ae066ca`; `git fetch` confirmou o mesmo SHA
na branch remota. Os commits A, B e C (`0905551`, `6a5670d`, `92f57e6`) já
estavam publicados nessa branch e pertencem à linha que parte de
`9392ebac9930f5d11c56f595556080e8ab1de809`. Links permanentes:
[A](https://github.com/thiagomassensini/geometry-of-numbers/commit/0905551),
[B](https://github.com/thiagomassensini/geometry-of-numbers/commit/6a5670d) e
[C](https://github.com/thiagomassensini/geometry-of-numbers/commit/92f57e6).

### PROVADO

`SecondSchur.lean` conserva `completedNativeOperatorCharacteristic`,
`completedNativeLogDerivative` e o quociente quiral original. A coordenada
real local `nativePhysicalCayleyRho` é identificada com
`nativeTransverseLogSlope`; `nativePhysicalCayleyRho_cayley_eventually`
prova `q(is)=(rho(s)-1)/(rho(s)+1)`, certifica que `rho` é real e que o
denominador não se anula no domínio local. Os fatores diagonais são
eventualmente reais e não nulos nas três fontes. A identidade algébrica do
kernel bruto é `nativePhysicalCayleyCongruenceEntry_eq_eventually`, usando a
conjugação física e os endereços originais `i+1`, `j+1`.

`nativePhysicalCayleyCongruenceEntry_hasSum_eventually` e
`nativePhysicalCayleyMatrix_hasSum_eventually` provam a expansão convergente
no domínio local de amostragem. O termo de ordem `n` contém precisamente
`canonicalCompletedNativeLogDerivativeMoment n`, a potência de malha
`(k+1)⁻²ⁿ` e o quociente
`((i+1)^(2n+1)+(j+1)^(2n+1))/(i+j+2)`. A afirmação é local/eventual; não foi
estendida para fora do domínio analítico estabelecido.

Para a matriz física bruta das três primeiras fontes, os limites Lean são

\[
D_1\to4h_0,\qquad (k+1)^2D_2\to16h_0h_1,
\]

\[
(k+1)^6D_3\to256h_1\det H_2
 =256h_1(h_0h_2-h_1^2).
\]

O segundo pivô é formado pelos determinantes dessa mesma matriz, não por uma
Gram auxiliar. `nativePhysicalSecondSchurPivotScaled_tendsto` prova

\[
(k+1)^4p_2(k)\longrightarrow16\left(h_2-\frac{h_1^2}{h_0}\right).
\]

O sinal do residual não entra nessa prova assintótica: a positividade é usada
depois, em `nativePhysicalP2_eventually_re_pos`, via o certificado canônico
independente `canonicalCompletedNativeSecondSchurComplement_pos`.

`nativePhysicalP0_eventually_re_pos`, `nativePhysicalP1_eventually_re_pos`,
`nativePhysicalP2_eventually_re_pos'` e os lemas de determinantes dão os
sinais eventuais dos três pivôs e de `D₁,D₂,D₃`. O teorema
`nativePhysicalCauchyMatrix_three_eventually_posDef` fecha a positividade
definida da matriz física complexa 3×3: usa o certificado de duas fontes já
existente para o bloco inicial e identifica o complemento escalar com `p₂`.
A conclusão está restrita às três primeiras fontes.

### FASE G — coeficientes homogêneos e torres Hankel

`SecondSchurTowers.lean` formaliza a soma geométrica finita como um polinômio
homogêneo em duas variáveis para cada momento canônico. O lema
`nativePhysicalCayleyGeometricPolynomial_mul` prova, inclusive no ponto
`s+t=0`, a identidade polinomial

\[
(s+t)Q_n(s,t)=s^{2n+1}+t^{2n+1},\qquad
Q_n(s,t)=\sum_{r=0}^{2n}(-1)^r s^{2n-r}t^r.
\]

Para `s+t ≠ 0`, `nativePhysicalCayleyAnalyticMomentTerm_eq_homogeneous_eval`
identifica cada termo racional da série local original com a avaliação desse
polinômio, e `nativePhysicalCayleyHomogeneousPolynomialSeries_hasSum`
identifica a soma convergente com o kernel analítico local. A hipótese fora da
diagonal é explícita: o teorema ainda não estende a identidade da soma do
kernel ao ponto removível `s+t=0`.

`nativePhysicalCayleyHomogeneousPolynomial_coeff` dá todos os coeficientes
exatos de cada parcela. Em particular, as duas torres são teoremas Lean:

- grau `(2i,2j)`: `4(-1)^(i+j) h_(i+j)`;
- grau `(2i+1,2j+1)`: `4(-1)^(i+j) h_(i+j+1)`;
- os dois setores de paridade mista têm coeficiente zero.

Assim, a estrutura de coeficientes das duas Hankels está provada para a série
homogênea convergente no domínio local declarado; não é apenas uma leitura
formal do quociente. Seguem abertos a extensão analítica do kernel da soma à
diagonal removível, a fórmula all-order dos pivôs por Vandermonde confluente,
sinais independentes para Hankels de ordem arbitrária e a identificação
dessa série com os estados materiais do ledger Green/TFVD.

### ABERTO

1. Formalizar a extensão analítica da soma do kernel no ponto removível
   `s+t=0`; a identidade polinomial de cada parcela já vale nesse ponto, mas
   a identificação da soma foi provada somente para `s+t ≠ 0`.
2. Determinar, em ordem geral, os limites de Schur via Vandermonde confluente.
3. Obter sinais independentes para Hankel de ordem arbitrária; a positividade
   das três primeiras fontes não implica positividade central all-order.
4. Identificar a série homogênea com os estados materiais do ledger
   Green/TFVD.

### REFUTADO

Nenhuma parte desta etapa substitui o kernel físico por outro ou remove os
retornos originais. As regressões de projeção dupla, Gram Cauchy, atlas finito
e obstrução off-critical continuam nos módulos anteriores e não foram
alteradas.

### AUDITORIA E PUBLICAÇÃO

`compile_module.sh SecondSchurTowers` e `compile_module.sh Audit` compilaram com
`-DwarningAsError=true`. A auditoria inclui agora 71 raízes públicas de
`SecondSchur` e `SecondSchurTowers`; o fecho de tipos e corpos contém 5.672
constantes e aceita somente `[propext, Classical.choice, Quot.sound]`. A
compilação percorre os corpos e tipos transitivos, além de imprimir axiomas
para cada raiz; não foram introduzidos `sorry`, `admit` nem axiomas novos.

Os resultados D/E/F foram publicados no commit
[`5e5454a7afa339c63e7d400f0819e6e301d9574c`](https://github.com/thiagomassensini/geometry-of-numbers/commit/5e5454a7afa339c63e7d400f0819e6e301d9574c),
cujo SHA remoto foi confirmado após o push. A/B/C também permanecem publicados
nos links acima. A fase G foi publicada no commit
[`2c853d8bb6b46ecb80a132e0eef39abdaadce5c7`](https://github.com/thiagomassensini/geometry-of-numbers/commit/2c853d8bb6b46ecb80a132e0eef39abdaadce5c7);
o SHA foi conferido com `git ls-remote`. O cache `.lake` foi preservado. O
checkout auxiliar Carry contém alterações alheias e
não foi limpo nem modificado. O validador espera o checkout em
`/home/thlinux/worktrees/carry-self-adjoint-operator`, mas o checkout existente
está em `/home/thlinux/carry-self-adjoint-operator`; com uma referência
temporária removível para o caminho correto, o preflight parou no `assert not
git diff HEAD` da linha 45 de `validate.py`, devido às alterações locais
pré-existentes do Carry. A referência temporária foi removida e o checkout
não foi alterado. O bloqueio observado está registrado em
`evidence/second-schur-preflight-block.md`; as compilações focadas e a auditoria
transitiva passaram.
