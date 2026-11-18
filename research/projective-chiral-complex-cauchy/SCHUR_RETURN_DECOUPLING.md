# Desacoplamento do retorno na malha Cauchy original

A direção mais amplificada pela [métrica do Schur](SCHUR_NEGATIVE_CHANNEL_METRIC.md)
é a última diferença do prefixo antigo. Nesta rodada escolhemos como entrada
nova a próxima amostra bruta da mesma malha. O transporte normalizado do
retorno nessa direção tem a potência que compensa o ganho singular.
A primeira potência e seu coeficiente podem ser calculados sem supor
positividade do novo pivô.

## Identidade na fonte original

Fixe \(m\ge1\) e \(z_j=\mathrm i(j+1)t\), \(0\le j\le m\).
Seja \(Q(t)=A(t)^*A(t)-B(t)^*B(t)\) o traço quiral completado, com a
normalização de \(\mathcal P/2\) e a amplitude positiva HB absorvida na
entrada. A [identidade TFVD](../native-jet-overlap-budget/CONNECTED_DEFECT_RADIAL_LIMIT.md)
identifica essa matriz com o divided slope no domínio regular.
Escreva \(A_0,B_0\) para os primeiros \(m\) vetores de cada canal e
\(a_m,b_m\) para o vetor novo. Use a projeção pelo canal positivo
\[
\lambda(t)=(A_0^*A_0)^{-1}A_0^*a_m,\qquad
x_t=(-\lambda(t),1),\qquad b_\perp=B(t)x_t .
\]
Como \(A_0^*A(t)x_t=0\), temos para todo \(t\) admissível
\[
B_0^*b_\perp=-[Q(t)x_t]_{\rm antigo}.
\]
Assim o cruzamento que a métrica de Schur cobra é a diferença dividida
no primeiro argumento do próprio traço TFVD completado. O retorno novo
e o cruzamento com cada vetor antigo entram antes de tomar o limite.
A identidade é exata, sem sinal no fechamento Green.

Se \(T_t\) é a transformação das diferenças divididas e \(T_te_r=t^{-r}\beta_r\),
para \(0\le r<m\), então
\[
g_r(t):=\langle\sqrt t B_0\beta_r,b_\perp\rangle
  =-t^{r+1/2}[T_t^*Q(t)x_t]_r .
\]
Na última expressão usamos o stencil do bloco de \(m+1\) pontos.
A coluna de ordem \(r<m\) se restringe ao prefixo antigo. O índice \(r\)
funciona também para todos os demais modos antigos, com a mesma
normalização própria.

## O cancelamento que impõe a velocidade

Na forma analítica da resposta, o coeficiente de \(b^a w^d\) no kernel
com \(b=\bar z\) é \(c_{ad}=h_{(a+d)/2}\) se \(a+d\) é par e zero de outro modo.
A diferença de ordem \(r\) cancela exatamente todos os monômios em \(b\)
com grau menor que \(r\), ainda com o \(w\) bruto. Equivalentemente, a
inversão binomial da transformação \(T_t\) é a carta de Newton \(R_t\),
\[
(R_t)_{\ell j}=\binom{j}{\ell}\ell!(\mathrm i t)^\ell,
\qquad T_t^*Q(t)=(T_t^*Q(t)T_t)R_t .
\]
Cada coluna de \(R_t\) tende a \(e_0\). Logo, em toda combinação \(x_t\to x_0\),
\[
[T_t^*Q(t)x_t]_r\ \longrightarrow\ c_{r0}\sum_j(x_0)_j .
\]
`SchurReturnDecoupling.lean` prova a identidade de Newton, o limite
unilateral para combinações convergentes e a transferência algébrica do
cruzamento negativo. A passagem via Newton usa somente o limite bilateral
dos jets que já existia, sem hipótese sobre o inverso de \(Q\).

## Os coeficientes da próxima amostra nativa

A Gram positiva vem dos vetores \(t^{-1/2}\alpha_j(t)v_j/\sqrt2\),
\(v_j(s)=s^{j+1/2}\). A amplitude nativa \(\alpha_j(t)\) é analítica e
tem o mesmo valor não nulo no centro. Logo
\(\lambda_j(t)=\ell_j\alpha_m(t)/\alpha_j(t)=\ell_j+O(t)\), onde
\(p_m(s)=s^m-\sum_{j<m}\ell_j s^j\) é o residual mônico ortogonal
a \(1,\ldots,s^{m-1}\) em \(L^2([0,1],s\,ds)\). Aqui os coeficientes
\(\ell_j\) vêm do Cauchy positivo, sem dados da Hankel de momentos.

Os valores na ponta desse polinômio são
\[
\delta_m=p_m(1)=\binom{2m+1}m^{-1},
\qquad
p_m'(1)=m(m+2)\delta_m.
\]
Para ver isso, escreva \(p_m(s)=\sum_{j=0}^m u_j s^j\), com \(u_m=1\).
A função racional \(\sum_{j=0}^m u_j/(z+j)\) se anula em
\(z=2,\ldots,m+1\) pela ortogonalidade. Seu numerador sobre
\(\prod_{j=0}^m(z+j)\) é \(\delta_m\prod_{\ell=2}^{m+1}(z-\ell)\).
Igualar a avaliação do numerador em \(-m\) dá \(\delta_m\).
A expansão em \(z^{-2}\) dá \(-p_m'(1)\).

Para \(r=m-1\) par, a diferença normalizada tende a \(\delta_m h_{r/2}\).
Para \(r=m-1\) ímpar, seu termo constante zera por paridade e na ordem
seguinte só sobrevivem \(b^{r+1}\) e \(b^r w\). O momento assinado do
stencil em grau \(r+1\), dividido por \(r!\), é \((r+1)(r+2)/2\).
Com \(x_t=(-\lambda(t),1)\), o coeficiente de \(\mathrm i t h_{(r+1)/2}\)
fica
\[
p_m(1)+p_m'(1)-\frac{(r+1)(r+2)}2p_m(1)
=\frac{(m+1)(m+2)}2\delta_m .
\]
A expansão converge num bidisco do centro. Em cada família finita,
o resto depois dos termos de grau total \(r+1\) é \(O(t^{r+2})\) antes
da divisão por \(t^r\). Assim a lei analítica para a última diferença é
\[
g_{m-1}(t)=
\begin{cases}
-\delta_m h_{(m-1)/2}\,t^{m-1/2}+O(t^{m+1/2}), & m\text{ ímpar},\\[2pt]
-\mathrm i\,\delta_m\frac{(m+1)(m+2)}2 h_{m/2}\,t^{m+1/2}
   +O(t^{m+3/2}), & m\text{ par}.
\end{cases}
\]
Em particular \(t^{-(2m-1)}|g_{m-1}(t)|^2\) fica limitado.
Para \(m\) par essa contribuição é \(O(t^2)\). Para \(m\) ímpar,
o limite do produto é \(\delta_m^2 h_{(m-1)/2}^2\). Se \(C_m\succ0\),
os momentos que aparecem como coeficientes líderes nas duas paridades
são positivos, pois são entradas diagonais de \(C_m\). Nesse caso os
expoentes acima são exatos. O teste multiprecisão com os vetores originais e a
característica completada, em \(m=1,\ldots,8\), reproduziu os coeficientes
com erro relativo menor que \(3\cdot10^{-5}\) em \(t=10^{-5}\).
Nenhum zero é usado no teste.

## O que resta depois dessa compensação

Se o limite confluente \(C_m\) do prefixo já é positivo, o vetor inteiro
\(T_{t,\rm antigo}^*B_0^*b_\perp\) tende a \(-\delta_m C_m e_0\).
Portanto a cobrança ponderada dos cruzamentos antigos tende
exatamente a \(\delta_m^2 h_0\). Essa é também a ordem constante da
energia assinada \(\|A(t)x_t\|^2-\|B(t)x_t\|^2\). Os termos constantes
cancelam ao formar o Schur.

O resultado identifica a origem da potência e da constante na
normalização atual. O controle simultâneo acima é de escala dominante
para um prefixo fixo. O sinal do termo que sobrevive em toda ordem
continua a ser o alvo. A identidade usada é do traço TFVD já completado.
Uma prova separada, célula por célula do ledger, da próxima margem
positiva permanece uma questão de fonte.
