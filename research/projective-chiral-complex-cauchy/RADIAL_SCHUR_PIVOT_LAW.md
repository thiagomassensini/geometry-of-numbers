# Sinal dos pivôs radiais da fonte física C2

O retorno físico original e o Pick material da C2 expõem os mesmos dois
setores de momentos no limite confluente. A lei abaixo vale para cada ordem
finita antes de certificar sinais. O resultado novo identifica o coeficiente
que sobrevive à eliminação de todos os cruzamentos.

## Fonte e normalização

O bracket centrado C2, sua síntese Genuine e o completamento continuam sendo
os da construção original. Usamos o germ material–nativo de GoN #335
(`physicalC2RadialPickMatrix_eventually_eq_native_dslope`) e os momentos
`canonicalCompletedNativeLogDerivativeMoment` do CSA. O refinamento físico
é \(t=(k+1)^{-1}\), com pontos \(z_j=i(j+1)t\). A letra \(i\) nos pontos
denota a unidade imaginária.

Escreva \(H_m=(h_{a+b})_{a,b<m}\), \(K_m=(h_{a+b+1})_{a,b<m}\) e
\[
\Delta_N=\det H_{\lceil N/2\rceil}\det K_{\lfloor N/2\rfloor},\qquad
\Delta_0=1.
\]
Se \(C_N(k)\) é a matriz `physicalC2RadialPickMatrix k N` do GoN,
\[
\frac{\det C_N(k)}{t^{N(N-1)}\prod_{j=0}^{N-1}(j!)^2}\longrightarrow\Delta_N.
\]
A matriz triangular de diferenças do CSA tem diagonal
\(1/(j!(it)^j)\). A congruência exata por essa matriz escala o determinante
pelo quadrado do módulo do determinante triangular. O limite misto do CSA
leva as entradas à matriz de coeficientes `polarizedGreenMomentCoefficient`.
Uma permutação simultânea por paridade dá \(H_{\lceil N/2\rceil}\oplus
K_{\lfloor N/2\rfloor}\). Em particular, para \(\Delta_N\ne0\),
\[
\frac{\det C_{N+1}(k)/\det C_N(k)}{(N!)^2t^{2N}}
\longrightarrow \frac{\Delta_{N+1}}{\Delta_N}.
\]
O denominador físico anterior é eventualmente não nulo nessa hipótese.

Os dois limites acima, a paridade e a normalização do determinante triangular
estão em `PhysicalRadialAllOrderDeterminant.lean`. A escala Lean é o inverso
do quadrado do módulo do determinante da transformação. Os lemas de sinal
transferem tanto o sinal positivo quanto o negativo de \(\Delta_N\).
Quando os determinantes dos prefixos até uma ordem são estritamente
positivos, a hermiticidade física e o critério de Sylvester dão positividade
estrita eventual nessa ordem. Cada ordem pode exigir seu próprio limiar.

## Energia incidente–retorno após a âncora

Na notação do carrier de `ResidualReturn.lean`, seja
\(q_j=q(i(j+1)t)\) o quociente quiral completado e
\[
P_{ij}=\frac{1-\overline{q_i}q_j}{(i+j+2)t},\qquad
d=1-|q_0|^2,\qquad M_0=\frac{1}{2t}.
\]
Agora \(i,j\) nos subscritos e no denominador são índices inteiros. \(P\) é
o Pick quiral do CSA, com a métrica Cauchy original. \(C\) acima é o Pick
material GoN, com sua própria normalização. Para a energia residual \(R\)
da projeção da âncora, usando os mesmos coeficientes incidentes e retornados,
\[
R_{ij}=d P_{ij}-\frac{P_{i0}P_{0j}}{M_0}.
\]
Essa identidade preserva cada cruzamento e vale inclusive em \(d=0\).
Como \(P_{00}=M_0d\), para \(d\ne0\) ela é \(R=d\,\operatorname{Schur}_0(P)\).
As duas igualdades estão formalizadas em `RadialPickSchur.lean`.

Abaixo, \(R_n\) restringe \(R\) aos índices \(1,\ldots,n\).
Usando \(q(ix)=(u(x)-1)/(u(x)+1)\) com \(u(x)=2xH(-x^2)\), a reflexão
torna o quociente real nesses pontos. Essas são as identidades
`native_chiral_radial_real` e `native_chiral_eq_reduced_cayley_eventually`
recuperadas na VM em `HigherOrderCayleyDefect.lean`
(CSA, frente `research/source-schur-curvature-20261117`).
Então
\[
P_{ij}
=\frac{2}{(1+u(x_i))(1+u(x_j))}
 \frac{u(x_i)+u(x_j)}{x_i+x_j},\qquad x_j=(j+1)t.
\]
O coeficiente de \(x^a y^b\) em \((u(x)+u(y))/(x+y)\) é zero se \(a+b\)
é ímpar. Se \(a+b\) é par, ele é \(2i^a\overline{i^b}h_{(a+b)/2}\).
As fases conjugadas se cancelam no determinante. O mesmo stencil real
normalizado dá \(\det P_N/(t^{N(N-1)}\prod_{j<N}(j!)^2)\to4^N\Delta_N\),
onde \(P_N\) usa os índices \(0,\ldots,N-1\).
Também \(d/t\to8h_0\). Pela fórmula de determinante do primeiro Schur,
\(\det R_n=d^n\det P_{n+1}/P_{00}\). Isso dá a lei do pivô bruto
\[
\boxed{\quad
\frac{\det R_n/\det R_{n-1}}{t^{2n+1}}
 \longrightarrow 32h_0(n!)^2\,\frac{\Delta_{n+1}}{\Delta_n}
\quad}\qquad(n\ge1,\ \Delta_n\ne0).
\]
Esta última fórmula de limite no carrier bruto é uma demonstração analítica
neste relatório. O Lean desta rodada cobre a identidade física finita \(R\)
e os limites confluentes no Pick material \(C\).

O quociente cancela um bloco inteiro a cada passo. Para \(n=2m\), sobra
\(\det H_{m+1}/\det H_m\). Para \(n=2m+1\), sobra
\(\det K_{m+1}/\det K_m\). Em particular os três primeiros coeficientes são
\[
32h_0h_1,\quad 128(h_0h_2-h_1^2),\quad
1152h_0\frac{h_1h_3-h_2^2}{h_1}.
\]

## Por que a direção fixa superestima a margem de quinta ordem

No par de direções \(e_1=(1,0)\) e \(w=(2,-1)\), seja \(R(a,b)=a^\top R_2b\).
A expansão do quociente nativo ou da identidade do Schur produz
\[
\begin{aligned}
R(e_1,e_1)&=32h_0h_1t^3+O(t^4),\\
R(e_1,w)&=128h_0^2h_1t^4+O(t^5),\\
R(w,w)&=128(h_0h_2-h_1^2+4h_0^3h_1)t^5+O(t^6).
\end{aligned}
\]
O Schur usa \(w_t=w-[R(e_1,w)/R(e_1,e_1)]e_1\). A correção de \(w\) é de
ordem \(t\) e subtrai \(512h_0^3h_1t^5\) da margem. O coeficiente efetivo
fica \(128(h_0h_2-h_1^2)\), cujo sinal positivo já existe em GoN
(`canonical_two_even_determinant_pos_from_c3` em
`research/c3-fourteenth-tail/FourNativeBoxes.lean`).
A subtração algébrica dos coeficientes está em
`fifthCoefficient_sub_crossing`. Os três coeficientes da expansão foram
conferidos em série simbólica com \(h_0,h_1,h_2\) livres.

Há um contraexemplo local à inferência pela direção fixa. Com
\((h_0,h_1,h_2)=(1,1,1/2)\), o coeficiente cúbico vale \(32\), o coeficiente
quinto na direção fixa vale \(448\), mas o quinto do Schur vale \(-64\).
Esses três dados vêm do germ
\(F_\star(z)=\exp(-z^2-z^4/2-z^6/6)\), pela mesma leitura
\(-F_\star'/2F_\star=zH_\star(z^2)\). Isso testa a alegação de suficiência
dos sinais locais em germes com a mesma paridade. A característica e as
identidades da fonte C2 permanecem as do projeto.

## Redução escalar que pode ser iterada na fonte

No centro confluente, o mesmo passo de Schur admite uma recorrência sem
matriz. Comece com \(f_0(s)=2H(s)\). Enquanto \(a_r=f_r(0)\ne0\), defina
\[
f_{r+1}(s)=\frac{1/a_r-1/f_r(s)}{s},\qquad
a_{r+1}=\frac{f_r'(0)}{a_r^2}.
\]
Para \(u_r(x)=x f_r(-x^2)\), essa operação dá
\(u_{r+1}(x)=1/u_r(x)-1/(a_rx)\).
Com \(L_r(x,y)=(u_r(x)+u_r(y))/(x+y)\), a identidade algébrica de centro é
\[
L_r(x,y)-\frac{[u_r(x)/x][u_r(y)/y]}{a_r}
  =u_r(x)u_r(y)L_{r+1}(x,y).
\]
O Lean prova essa identidade fora dos denominadores nulos
(`radialResponseKernel_centered_schur`). Analiticamente a expressão estende
ao centro porque \(u_r\) é ímpar analítica e tem inclinação \(a_r\ne0\).
Em coeficientes, cada multiplicação por \(u_r\) desloca uma ordem e tem
diagonal \(a_r\). Portanto o determinante do bloco de coeficientes de
tamanho \(N\) de \(L_r\) é \(a_r^{2N-1}\) vezes o de tamanho \(N-1\) de
\(L_{r+1}\). O pivô de índice \(N\) de \(L_0\) é assim
\[
2\frac{\Delta_{N+1}}{\Delta_N}
=a_N\prod_{r<N} a_r^2.
\]
Os primeiros \(a_r\) são \(2h_0\), \(h_1/(2h_0^2)\) e
\(2h_0(h_0h_2-h_1^2)/h_1^2\). A obrigação de fonte passa a ser
\(f_r'(0)>0\) em cada redução sucessiva, começando em \(a_0>0\).
A recorrência explicita onde um argumento vindo de TFVD/Green precisaria
preservar o sinal. A identidade de redução sozinha não fornece essa
desigualdade. O CSA já tem `NativeSourceAllOrderSchur.lean` com o critério
condicional na forma de restos da recorrência da característica.

## Checagens e reprodução

Na VM, o `canonical_h` de `momentos`, commit `05c9314`, veio de
`native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json`.
Na verificação multiprecisão, o coeficiente da direção fixa deu
\(4.84267556654\,10^{-7}\) e o do Schur deu \(2.49514951017\,10^{-7}\).
A diferença foi \(2.34752605637\,10^{-7}\). Reconstruindo \(q\) pelos
primeiros 32 coeficientes e avaliando o Gram Cauchy com 170 dígitos, os
primeiros seis pivôs normalizados, a \(t=10^{-4}\), ficaram entre
\(0.999926\) e \(0.999972\) vezes as previsões da fórmula. Essa verificação
numérica usa somente momentos canônicos.

```bash
bash research/projective-chiral-complex-cauchy/validate-radial-schur.sh \
  /home/thlinux/geometry-of-numbers /home/thlinux/carry-self-adjoint-operator
```

O script usa os módulos históricos já compilados na VM. A base GoN deste
trabalho é a PR #343, commit `228986e`, onde o resultado físico 9×9 já
estava fechado. Os limites de ordem variável se referem ao refinamento
radial para cada ordem fixa.
