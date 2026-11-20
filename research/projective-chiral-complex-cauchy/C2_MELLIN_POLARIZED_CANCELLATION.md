# C2 Mellin e o núcleo polarizado com a Gamma já cancelada

A densidade bracketada C2 fornece uma representação positiva em que
a Gamma e um dos fatores da câmera já foram cancelados. O núcleo
completado se torna a diferença de dois termos construídos de medidas
positivas. O segundo termo é explícito e tem um bloco Hankel indefinido
já em dimensão \(3\). A positividade da diferença nativa continua em aberto.

O ponto de partida é a identidade da fonte C2
\(I_\rho(s)=\Gamma(s)\kappa_2(s)N(s)\) na faixa, seguida da identificação
\(F(s)=A(s)N(s)\), na variável \(s\).
\(\rho\) é a densidade da carta C2 com semente da PR #127 do CSA.
A origem da identidade é a passagem ao limite dos brackets da fonte.
[PR #127](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/127)
· [Fator de completamento no CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/CompletedOperatorCharacteristic.lean#L26)

## 1. Cancelamento na integral antes do logaritmo

Escreva \(f(x)=1/(1+e^x)\), \(L=\log 2\) e
\(I_f(s)=\int_0^\infty x^{s-1}f(x)\,dx\).
Com \(u=e^{-x}\), a redução racional da densidade da PR #127 dá
\[
\rho(x)=
u+\frac{u^3(1-u)}{(1+u)(1+u^2)}
=\frac{u}{1+u}+\frac{u^2}{1+u^2}=f(x)+f(2x).
\]
A mudança de escala lê \(I_\rho=(1+2^{-s})I_f\). Como
\(\kappa_2=(1+2^{-s})(1-2^{1-s})\), obtemos
\[
 I_f(s)=\Gamma(s)(1-2^{1-s})N(s).
\]
A redução preserva a carta original e usa seu fator de câmera inteiro.

Duas integrações por partes, válidas para \(\Re s>0\), dão
\[
 J(s):=\int_0^\infty x^{s+1}f''(x)\,dx=s(s+1)I_f(s).
\]
Os termos de bordo em zero e infinito tendem a zero nessas
integrações. A identidade
\(f''(x)=\frac14\operatorname{sech}^2(x/2)\tanh(x/2)\)
também dá \(f''(x)>0\) para \(x>0\).

Aplique duplicação e recorrência da Gamma no completamento.
O fator restante de câmera é a integral positiva
\[
 Q(s)=\frac{1-2^{1-s}}{s-1}=\int_0^L e^{(1-s)v}\,dv .
\]
Sua expressão integral dá a continuação também em \(s=1\).
A característica, com a constante do CSA, fica
\[
 F(s)=\frac{\sqrt\pi}{2}(2\sqrt\pi)^{-s}
             \frac{J(s)}{\Gamma((s+3)/2)\,Q(s)} .
\]
[Duplicação e recorrência da Gamma](https://dlmf.nist.gov/5.5)

## 2. O quociente pela Gamma continua vindo de uma medida positiva

Para \(y\ge0\), o produto de cosh dá
\[
 \operatorname{sech}^2(\sqrt y/2)=
 \prod_{n\ge0}\left(1+\frac{y}{\pi^2(2n+1)^2}\right)^{-2}.
\]
Escolha variáveis independentes \(G_n\) de distribuição Gamma
com forma \(2\) e taxa \(\pi^2(2n+1)^2\). A soma
\(S=\sum_{n\ge0}G_n\) é finita quase certamente pela soma de
suas esperanças. O produto acima é \(\mathbb E e^{-yS}\).
Se \(S'\) é uma cópia independente e \(U\) é uniforme em
\([0,1]\), independente de ambas, então
\(T=S+U^2S'\) satisfaz
\[
 \frac{f''(x)}{x}=\frac18\,\mathbb E e^{-x^2 T}.
\]
Com efeito, use
\(\tanh a/a=\int_0^1\operatorname{sech}^2(va)\,dv\)
com \(a=x/2\). A troca de integrais pela estimativa em \(\Re s\)
ou por Tonelli no eixo real, seguida de analiticidade, dá, para
\(r=(s+3)/2\),
\[
 \frac{J(s)}{\Gamma(r)}=\frac1{16}\mathbb E T^{-r}.
\]
A expectativa existe para todos os expoentes reais. Para potências
positivas, \(T\le S+S'\) admite um momento exponencial para
\(0<c<\pi^2\), pelo produto das funções geradoras Gamma. Para
potências negativas de ordem \(a>0\), escolha \(k\) com \(2k>a\).
A soma das primeiras \(k\) variáveis tem densidade
\(O(x^{2k-1})\) perto de zero, por convolução das densidades
\(O(x)\). Como \(T\) domina essa soma, \(\mathbb E T^{-a}<\infty\).
Isso também fornece dominação em compactos para
\(\mathbb E T^{-r}\). [Produto de cosh](https://dlmf.nist.gov/4.36.E2)

Com \(s_0=1/2\), tome a lei de \(T\) inclinada por
\(T^{-7/4}/\mathbb E T^{-7/4}\), e nessa lei faça \(Y=-\frac12\log T\).
Tome \(B\) em \([0,L]\) com densidade proporcional a \(e^{v/2}\).
Então
\[
 \frac{F(s_0+u)}{F(s_0)}
    =(2\sqrt\pi)^{-u}\frac{\mathbb E e^{uY}}{\mathbb E e^{-uB}} .
\]
Assim a única correção remanescente após o cancelamento analítico
é a lei compacta determinada pela câmera. Ela depende do mesmo
vértice físico \(V(s)=2^{-s}\), pois \(Q=(2V-1)/(1-s)\).

## 3. Identificação de todos os cruzamentos

Escreva \(M_Y(u)=\mathbb E e^{u(Y-Y')}\) e
\(M_B(u)=\mathbb E e^{u(B-B')}\) usando cópias independentes.
O produto das igualdades em \(u\) e \(-u\), com a simetria par de
\(F(s_0+u)\), dá
\[
 \left(\frac{F(s_0+u)}{F(s_0)}\right)^2
    =\frac{M_Y(u)}{M_B(u)} .
\]
As igualdades valem perto do centro para logaritmos locais.
A diferenciação logarítmica vale também em todo ponto regular
da faixa. Os fatores exponenciais lineares se cancelam na reflexão.

Para um desses dois \(M\), ponha \(\ell_M'=M'/M\) e
\[
 K_M(z,w)=\frac14\,
 \frac{\ell_M'(iw)-\ell_M'(i\bar z)}{iw-i\bar z}.
\]
Use o prolongamento removível quando os dois argumentos coincidem.
Para \(F_{\mathrm{alt}}(z)=F(s_0+iz)\) e
\(R(z)=-F_{\mathrm{alt}}'(z)/(2F_{\mathrm{alt}}(z))\),
obtemos exatamente
\[
 \frac{R(w)-\overline{R(z)}}{w-\bar z}
 =K_{M_Y}(z,w)-K_{M_B}(z,w).
\]
Ambos os termos são hermitianos por paridade e reflexão. A
identidade vale para \(z,w\) independentes e portanto transporta
cada entrada de uma seção finita. O lado esquerdo é, por
definição, o kernel \(\texttt{canonicalCompletedNativePolarizedDslopeKernel}\)
nas cartas regulares. O CSA já o identifica com a matriz quiral
regularizada do Wronskiano no grid radial. Com a normalização de
entradas da GoN, o mesmo kernel lê o balanço de fonte dividido por
dois, que o CSA escreve como energia Gamma menos o termo assinado na
diagonal. A comparação acima localiza a correção no kernel
normalizado e conserva os cruzamentos. Os termos \(K_{M_Y}\) e
\(K_{M_B}\) foram deduzidos da representação escalar integral.
[Definição do núcleo](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/CanonicalCompletedC3GammaDslopeGram.lean#L108)
· [Identidade de matriz do Wronskiano](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/CompletedNativeChiralReturnStorage.lean#L309)
· [Balanço Gamma–Wronskiano](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/8f15ec7/CarrySelfAdjointOperator/CompletedNativeChiralReturnGammaCorrectionCancellation.lean#L119)

## 4. Onde aparece o sinal indefinido

Se \(c_n=[u^n]\log Q(s_0+u)\), os coeficientes do kernel da câmera
são \(b_j=(-1)^j(j+1)c_{2j+2}\), com a mesma convenção de momentos
do núcleo completado. Isso segue expandindo \(\ell'_{M_B}\)
na identidade de dois argumentos. Para certificar esses coeficientes,
use somente
\[
 Q(s_0+u)=\frac{\sqrt2\,e^{-uL}-1}{1/2-u}.
\]
O script usa \(\texttt{arb_series}\) com precisão de 192 bits.
Os menores principais de dimensão \(1\) e \(2\) são positivos.
Em dimensão \(3\), os determinantes de
\((b_{i+j})_{i,j<3}\) e \((b_{i+j+1})_{i,j<3}\) são
aproximadamente \(-1{,}693756447969871\cdot10^{-20}\) e
\(-4{,}067607771997152\cdot10^{-27}\).
Os dois intervalos certificados ficam estritamente abaixo de zero,
logo cada bloco tem exatamente uma direção negativa. Assim uma
lei positiva e compacta já produz indefinição depois de derivar
o logaritmo. O próximo teste de sinal é a diferença dos dois
blocos na mesma direção, com sua eliminação de Schur.

A aritmética de alta precisão, usada como diagnóstico separado
da certificação intervalar dos determinantes, reproduziu os
derivados pares de ordem \(2\) a \(12\). Para ordem \(12\),
a fração do derivado completado em relação à parcela de fonte
passou de \(7{,}75\cdot10^{-18}\), na escrita anterior, para
\(6{,}26\cdot10^{-3}\), com o cancelamento da Gamma já feito.
Em ordem \(2\), as frações são \(0{,}00955\) e \(0{,}53727\).
Os nove cruzamentos de uma seção de três pontos complexos também
coincidiram em quadratura de alta precisão com o núcleo calculado
diretamente da característica. A demonstração principal é
analítica e o teste de sinal da câmera é intervalar.
[Reprodução numérica e intervalar](check-c2-mellin-centered.py)
