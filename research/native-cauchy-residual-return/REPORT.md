# Retorno físico após o primeiro Schur: isometria Cauchy e defeito de projeção

**Resultado: PARTIAL.** O residual físico da PR #52 admite uma identificação
isométrica exata com o mesmo frame Cauchy original. Seu retorno nas novas
coordenadas fica explícito. Uma simplificação que projetasse também o retorno
é refutada na própria fonte: ela acrescenta um termo positivo cujo limite,
na normalização de Schur, é `4 h₀ / 9` para a segunda fonte radial.

Isso não prova a contratividade do retorno reduzido nem a positividade
canônica em toda ordem. O sinal continua sendo uma obrigação independente.

Repositório: `thiagomassensini/geometry-of-numbers`.
Base exata: `fdb8f7e9ce1b8681d10f2647393ad83f05bfac12`, PR #52,
branch `agent/native-return-boundary-deflation`.
Nova branch: `agent/native-cauchy-residual-return`.
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

Há **51 teoremas públicos, 26 definições/aliases e um lema privado** em seis
módulos. As 77 raízes públicas estão em `public-roots.json`.
`Audit.lean` imprime os axiomas e percorre transitivamente os tipos e corpos.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos.
Os dois grupos têm 49/28 raízes e 5.490/5.696 dependências transitivas.

Ambos os grupos rejeitam dependências dos certificados H6/K6/H7, sinais de
seis/sete pivôs, energia estrita de seis fontes e não negatividade geral do
defeito do retorno. A importação de um módulo com resultados posteriores
não autoriza usá-los: a auditoria percorre as dependências efetivas.

`validate.py` executa 18 verificações, registradas em `evidence/checks.json`:
sete compilações de pesquisa com warnings como erros; build dos consumidores
originais; builds focado e raiz com `lake build --wfail`; auditorias
Foundation/Geometry/Analysis; regressão H6/K6/doze fontes; controle racional;
preservação do histórico; `git diff --check` e geração das auditorias.

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

## E — Próximo passo mínimo

Agora as duas sínteses restantes são comparáveis sobre o mesmo frame físico,
e o quociente completado que precisa ser estudado está explícito. O próximo
teste concreto é obter o PRIMEIRO coeficiente polarizado não cancelado de

\[
C_k(i,j)(1-\overline{\tau_{k,i}}\tau_{k,j}),\qquad i,j>0,
\]

diretamente da resposta logarítmica completada e da identidade Green, com
resto controlado em ambos os argumentos. Não basta sua diagonal.

Uma calibração específica para essa tentativa é o alvo

\[
(k+1)C_k(i,j)(1-\overline{\tau_{k,i}}\tau_{k,j})
\stackrel{?}{\longrightarrow}2h_1/h_0.
\]

Esse alvo é sugerido pela expansão formal
`-F'(iy)/F(iy)=2iy(h₀-h₁y²+…)` e pela transformação Cayley existente.
**Não foi formalizado nem auditado nesta entrega.** Uma tentativa deve
primeiro verificar essa expansão e seu resto na fonte original. Mesmo um
limite positivo constante nos dois índices teria posto um: direções que o
anulam exigiriam a ordem seguinte. Não seria uma prova all-order.

Esse é um próximo passo menor e verificável do que simplesmente solicitar
contratividade em toda dimensão: testar a primeira correção completa do
retorno reduzido e identificar seu núcleo antes de qualquer nova projeção.
Se houver cancelamentos adicionais, conservar o retorno de bordo já medido.

**Conclusão:** a redução isométrica é verdadeira e não circular; a projeção
dupla sem correção é refutada na própria fonte; o sinal do residual completo
continua aberto. Resultado `PARTIAL`, com um NO-GO específico e quantitativo.

### Reprodução

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/native-cauchy-residual-return
python3 research/native-cauchy-residual-return/validate.py
```

As compilações de pesquisa utilizam os caches históricos das PRs empilhadas,
conforme `compile_module.sh`. Esta é reprodução no host canônico preparado,
não uma alegação de bootstrap de um clone sem os módulos históricos.
