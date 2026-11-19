# Fechamento refletido do Green e teste de ordem no bordo

A obrigação é transportar o fechamento bracketado de uma onda nativa
para o fechamento do fluxo Green numa câmera. Abaixo testamos duas
maneiras de fazer esse transporte. O teste diagonal perde o
deslocamento. A dominação pela energia escalar do bordo falha
localmente para o bulk e para uma família que contenha duas câmeras.
O fechamento em todo zero Genuine continua em aberto.

## O teste misto com a semente

Na realização logarítmica de \(\texttt{primos}\), o tempo é \(z\) e
\(s=\tfrac12+iz\). O par refletido de valores no endpoint vale
\(e=(1,1)\) e o par de fluxos característicos é
\(\tau(z)=(z,\bar z)\). Ambos são os valores das ondas do módulo
\(\texttt{CpNativeCarryReflectedLogBoundarySymmetry}\).

Na forma orientada \(\omega(y,x)=\bar y_1x_1-\bar y_2x_2\), temos
\[
\omega(\tau(z),\tau(z))=|z|^2-|\bar z|^2=0,\qquad
\omega(e,\tau(z))=z-\bar z=-2i(\Re s-\tfrac12).
\]
Assim a energia assinada de uma única onda perde o deslocamento,
inclusive fora da linha. A comparação mista com a semente detecta a igualdade
dos dois fluxos na diagonal fixa. Os dois cálculos estão no Lean.
[Relação refletida no \(\texttt{primos}\)](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpNativeCarryReflectedLogBoundarySymmetry.lean)

O endpoint da própria onda refletida dá uma segunda entrada
que já satisfaz o fechamento bracketado. De fato,
\(s^\#=1-\bar s\) corresponde ao tempo \(\bar z\), e a
reflexão preserva os zeros Genuine. Agora
\[
\omega(\tau(\bar z),\tau(z))=z^2-\bar z^2
 = -4i\,(\Im s)(\Re s-\tfrac12).
\]
O \(\texttt{primos}\) certifica \(\Im s\ne0\) em todo zero Genuine
da faixa. Assim uma única igualdade, a anulação dessa entrada
mista para as duas ondas que já fecham, basta para o casamento
refletido. O lema Lean
\(\texttt{nativeReflectedWave_mixed_green_test_of_bracket_closure}\)
verifica a disponibilidade da segunda onda e a equivalência.
A igualdade mista ainda requer transportar as duas entradas do
bracket à mesma forma orientada.
[Reflexão que preserva os zeros](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpGenuineRiemannZetaIdentification.lean#L197)
· [Zeros fora do eixo real de \(\texttt{Genuine}\)](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpGenuineReflectionRigidity.lean#L72)

O análogo vale para a parte de bulk no corte aritmético. Para
\(s^\#=1-\bar s\), os dois argumentos do pareamento de gradientes
trocam de posição. Assim \(P_M(s^\#)=\overline{P_M(s)}\) e
\(E_M(s^\#)=E_M(s)\), com \(E_M=\Re P_M\). O fator radial
\(c_p(d)=p^d-p^{-d}\) é ímpar em \(d=\Re s-\tfrac12\).
Portanto \(G_{p,M}-B_M=c_p(d)E_M(s)\) troca de sinal
na reflexão, em qualquer corte. Somar os dois bulks refletidos
dá zero identicamente. Esse cancelamento preserva a possibilidade
de cada coordenada carregar fluxo.

## O limite da correção angular

No corte canônico \(3M\), o módulo
\(\texttt{CpNativeCarryAngularCorrectionExactLimit}\) identifica a
correção por \(\text{pareamento escalar}-P_{3M}\).
Em um zero Genuine, o primeiro termo tende a zero e a
correção tende a \(-P_\infty(s)\), cuja parte real é
\(-E_\infty(s)<0\). Consequentemente a correção sem fator
radial permanece não nula até nos zeros que estão na linha.
Com o fator \(c_p(d)\), o limite passa a \(-c_p(d)P_\infty(s)\).
A obrigação está precisamente no pareamento misto ou na
anulação desse produto, e a cauda da correção já tem limite explícito.
[Limite da correção angular](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpNativeCarryAngularCorrectionExactLimit.lean)

## Teste de uma cota pela energia do bordo

Seja \(A(s)=\texttt{bracketedDirichletChart}\ 3\ s\), a carta
Genuine com sua semente. A identidade finita de bordo dá
\(B_M(s)\to-\Re A(s)\) em toda a faixa aberta.
Logo \(G_p^\infty=c_p(d)E_\infty-\Re A\), e para duas
câmeras distintas \(p,r\), o bordo comum cancela exatamente
na diferença
\[
G_r^\infty(s)-G_p^\infty(s)
  =(c_r(d)-c_p(d))E_\infty(s).
\]
A diferença e o limite foram verificados no Lean.
[Bordo finito e limite](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpBracketGreenBoundary.lean)

Para verificar a ordem do primeiro termo, use
\(\Delta n^{-s}=-s\int_n^{n+1}x^{-s-1}\,dx\) para o gradiente
progressivo. O produto refletido é limitado em módulo por
\(|s|\,|s^\#|n^{-3}\), já que as partes reais de \(s\) e
\(s^\#\) somam \(1\). A convergência uniforme em compactos
implica a continuidade de \(E_\infty\) na faixa. O sinal estrito
de \(E_\infty(s)>0\) já está certificado na fonte.
[Positividade do pareamento infinito](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpGenuineFirstOrthogonalGreenLimit.lean#L217)

Fixe um zero crítico \(s_0=\tfrac12+it_0\) e analise
\(s=s_0+d\) com \(d\) real. Para cada câmera prima,
\[
\lim_{d\to0}\frac{G_p^\infty(s_0+d)+\Re A(s_0+d)}{d}
=2\log(p)\,E_\infty(s_0)>0 .
\]
E para duas câmeras distintas,
\[
\lim_{d\to0}\frac{G_r^\infty(s_0+d)-G_p^\infty(s_0+d)}{d}
=2\log(r/p)\,E_\infty(s_0)\ne0 .
\]
A carta \(A\) é holomorfa na faixa. No compacto, uma segunda
diferença de \(x^{-s}\) é uma integral de
\(s(s+1)x^{-s-2}\) com peso triangular de suporte \([-1,1]\).
Isso dá convergência normal da carta C3. Como \(A(s_0)=0\),
segue que \(|A(s_0+d)|^2=O(d^2)\), inclusive em zero simples.

Logo inexiste constante local \(C\) com
\(\big|G_p^\infty+\Re A\big|\le C|A|^2\). Também inexiste
uma cota \(\max(|G_p^\infty|,|G_r^\infty|)\le C|A|^2\)
para duas câmeras em uma vizinhança de \(s_0\), pois ela daria o
mesmo controle quadrático para a diferença. Esse teste usa
o germe da própria carta e um zero crítico simbólico.
O fechamento exatamente no conjunto dos zeros requer informação
adicional sobre a interação do fluxo com a semente.

## Verificação

O anexo [GreenReflectedClosureTest.lean](GreenReflectedClosureTest.lean)
usa o \(\texttt{CPFormal}\) do CSA fixado em
\(\texttt{65d50f6db1208708e109982ba97e1d51d3039956}\).
O limite transversal e a impossibilidade da cota quadrática são
demonstrações analíticas neste texto.
