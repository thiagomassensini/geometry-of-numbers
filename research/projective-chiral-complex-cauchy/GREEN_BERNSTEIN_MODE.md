# O modo de Bernstein no fluxo Green nativo

No zero Genuine, o bordo bracketado tende a zero. O fluxo Green
sem compressão conserva um resíduo radial, com sinal e módulo
explícitos. Esse resíduo é um detector do mesmo deslocamento
transversal que faz a taxa de Bernstein passar de \(1\).
A etapa de exclusão continua sendo fazer uma coordenada do fluxo
tender a zero em cada zero Genuine.

## 1. O que já fecha na fonte

Fixe \(s\) na faixa Genuine e escreva \(d=\Re s-1/2\).
O bracket, os cortes e o pareamento refletido abaixo são os de
\(\texttt{finiteBracketCoupledCpGreenFlux}\). Para a câmera prima
\(p\), num corte \(M\), ponha
\[
G_{p,M}(s)=(p^d-p^{-d})E_M(s)+B_M(s).
\]
Aqui \(E_M=\Re\,\texttt{finiteReflectedGradientPairing}\) e
\(B_M=\texttt{finiteBracketCoupledSignedBoundary}\). É a identidade
\(\texttt{finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing}\).
Ao longo dos cortes alinhados, \(E_M\ge E_1>0\) e
\(E_M\to E_\infty>0\). Num zero Genuine, \(B_M\to0\), portanto
\[
G_p(s):=\lim_M G_{p,M}(s)=2\sinh(d\log p)\,E_\infty(s).
\]
Esse limite já está no Lean como
\(\texttt{finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero}\).
[Identidade finita](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpBracketGreenFlux.lean)
· [Limite e energia positiva](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpGenuineFirstOrthogonalGreenLimit.lean#L253)

Em [AlignedGreenFluxSeparation.lean](AlignedGreenFluxSeparation.lean),
a cota no próprio corte é
\[
|G_{p,M}(s)|\ \ge\ |p^d-p^{-d}|E_1(s)-|B_M(s)|
\ \ge\ 2 |d|\log(p)\,E_1(s)-|B_M(s)|.
\]
Assim, fora da linha, todo corte alinhado suficientemente grande
retém uma separação explícita de zero. O Lean registra que, para
concluir \(d=0\), basta fazer o fluxo de uma única câmera convergir
a zero ao longo de qualquer subsequência cofinal. O lema é sobre
os fluxos Genuine-first, com os cutoffs do \(\texttt{primos}\).

A síntese horizontal normalizada, por sua vez, é a diferença entre
as duas leituras de câmera. Ela tende a zero em todo zero Genuine.
O par \((1,1)\) mostra que essa compressão escalar pode zerar com
energia de carry estritamente positiva, inclusive com as amplitudes
originais. O Lean também mostra que elevar toda essa convergência
horizontal a fechamento Green coordenada a coordenada equivale
à forte não anulação fora da linha.
[Compressão e ativação](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpC2GpreGreenActivationGuard.lean#L65)

Há uma segunda leitura da mesma fronteira. A parte real da
diferença entre as proveniências TFVD de duas câmeras distintas
converge para \(((r^d-r^{-d})-(p^d-p^{-d}))E_\infty(s)\).
Esse resultado já usa o mesmo bordo TFVD para ambas as câmeras.
A igualdade do bordo comum preserva essa diferença de proveniência.
[Observabilidade cruzada](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpGenuineCrossPrimeObservability.lean)

## 2. Relação com a taxa de Bernstein

Use a identificação entre o nativo e Genuine, seguida do
completamento. O fator arquimediano é não nulo no interior da faixa.
Um zero \(s\) nessa faixa corresponde a \(z=-i(s-1/2)\) na variável
da característica completada e a \(\lambda=1/z^2\) na variável
inversa da resposta. Em particular \(\Im z=-d\).
[Identificação no CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/NativeScalarGenuineIdentification.lean#L108)
· [Separação do completamento](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/NativeBoundaryArchimedeanDressingSeparation.lean#L41)

Com \(q=22/175\), \(a=\lambda/q\) e \(v=|a|<1\), o
[certificado anterior](BERNSTEIN_GROWTH_RATE.md) dá
\[
\rho_\lambda-1=|1-a|+|a|-1
  =\frac{4qv^2}{|1-a|+1-v}d^2 .
\]
Como \(d=\operatorname{arsinh}(G_p(s)/(2E_\infty(s)))/\log p\),
obtemos a relação exata
\[
\rho_\lambda-1=
\frac{4qv^2}{|1-a|+1-v}
\left(\frac{\operatorname{arsinh}(G_p(s)/(2E_\infty(s)))}{\log p}\right)^2 .
\]
O resíduo Green normalizado lê o deslocamento com sinal. O
excesso do fator de Bernstein lê seu quadrado. A fórmula usa o
polo simbolicamente, sem uma tabela de alturas. Em particular,
excluir todos os fatores \(\rho_\lambda>1\) equivale a anular
esse fluxo, em uma câmera, em cada zero Genuine. A fórmula do
limite mostra que um hipotético zero fora da linha conservaria
o resíduo mesmo com fechamento horizontal exato.

## 3. Como o mesmo modo apareceria numa direção finita do GoN

Esta é uma consequência analítica no germe completado. Suponha
\(\lambda\notin\mathbb R\) e escolha \(0<r<|\lambda|\).
Sejam \(\mu\) os polos inversos distintos, de multiplicidade
\(m_\mu\). Pelo produto centrado, para qualquer polinômio real \(f\),
\[
L_1(f^2)=\sum_\mu m_\mu\mu^2 f(\mu)^2 .
\]
Seja \(A(x)\) o produto de \(x-\mu\) sobre os polos com
\(|\mu|>r\) que restam após retirar \(\lambda,\bar\lambda\).
O conjunto é finito e fechado por conjugação, logo \(A\) é real.
Escolha \(a_N,b_N\in\mathbb R\) para que
\[
f_N(x)=A(x)x^N(a_N+b_Nx),\qquad
\lambda f_N(\lambda)=i .
\]
A escolha existe pois \(A(\lambda)\ne0\) e
\(1,\lambda\) formam uma base real de \(\mathbb C\).
Com \(w_N=i/(A(\lambda)\lambda^{N+1})\), basta tomar
\(b_N=\Im(w_N)/\Im(\lambda)\) e
\(a_N=\Re(w_N)-b_N\Re(\lambda)\).
Na parte \(|x|\le r\), há uma constante \(C\), independente de \(N\),
com \(|f_N(x)|\le C(r/|\lambda|)^N\). Por exemplo, tome
\[
C=\frac{\sup_{|x|\le r}|A(x)|}{|A(\lambda)\lambda|}
  \left(1+\frac{|\Re\lambda|+r}{|\Im\lambda|}\right).
\]
O par destacado contribui exatamente \(-2m_\lambda\).
Cada outro polo acima de \(r\) é zerado por \(A\). Assim
\[
\big|L_1(f_N^2)+2m_\lambda\big|
 \le C^2(r/|\lambda|)^{2N}
     \sum_{|\mu|\le r} m_\mu|\mu|^2 .
\]
A soma é finita. Escolher e fixar \(N\) grande produz uma
direção negativa num bloco ímpar finito \(K_{\deg(f_N)+1}\).

A passagem à forma física usa a confluência já disponível.
Com \(R(z)=zH(z^2)\), os coeficientes do divided slope são
\(h_{(i+j)/2}\) se \(i+j\) for par, e zero caso contrário.
Coloque os coeficientes de \(f_N\) no setor ímpar e leve essa
entrada à malha física pela transformação triangular de
diferenças. O pareamento assinado converge para \(L_1(f_N^2)<0\)
nessa direção, após a normalização confluente. Pela identidade
\(\mathcal P/2=\Pi+D\), com \(\Pi\) a Gram amortecida, o defeito
\(D\) teria de consumir toda a Gram e excedê-la na direção
transportada. Esse é um teste de sinal no germe original. A
fibra negativa de \(D\) já cancela \(\Pi\) entrada a entrada, e
a obrigação de sinal fica na diferença dos dois traços.
[Confluência e paridade](RADIAL_SCHUR_PIVOT_LAW.md)
· [Decomposição do defeito no GoN](../native-jet-overlap-budget/CONNECTED_DEFECT_RADIAL_LIMIT.md)

## Verificação

O novo módulo verifica a separação no corte, a cota linear no
deslocamento e o critério da subsequência. Os termos da relação com
Bernstein e da direção polinomial são demonstrados acima.
O módulo é um anexo de pesquisa do GoN. Ele usa a dependência
\(\texttt{CPFormal}\) do CSA fixada em \(\texttt{65d50f6}\).
