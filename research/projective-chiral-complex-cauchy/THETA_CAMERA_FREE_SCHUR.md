# Do cancelamento completo da câmera aos pivôs de Bézout

O quociente da [decomposição Mellin C2](C2_MELLIN_POLARIZED_CANCELLATION.md)
admite uma densidade real par e estritamente positiva. Essa densidade
permite calcular o sinal dos pivôs pela matriz de Bézout construída
dos coeficientes brutos da característica completada. O cálculo
evita separar a fonte da câmera no nível dos cumulantes.

## 1. A retirada da escala acontece antes da derivada logarítmica

Escreva \(s_0=1/2\), \(f(x)=(1+e^x)^{-1}\),
\(Q(s)=(1-2^{1-s})/(s-1)\), e use a lei \(T\) construída
na nota Mellin. Com \(r=(s+3)/2\) vale
\[
 F(s)=\frac{\sqrt\pi}{32}(2\sqrt\pi)^{-s}
             \frac{\mathbb E T^{-r}}{Q(s)}.
\]
O ponto de partida é a densidade bracketada com semente, a divisão
exata pelo fator da câmera e o completamento original. Como \(F\),
\(Q\) e a expectativa de potência de \(T\) são inteiras, a identidade
multiplicada por \(Q\) se prolonga ao semiplano \(\Re s>1\).
Nesse semiplano a retirada da escala da câmera pode ser feita dentro
de integrais absolutamente convergentes.

Da série de \(f''\) e da identidade gaussiana
\[
 \int_0^\infty t^{-1/2}e^{-yt-n^2/(4t)}\,dt
 =\sqrt{\pi/y}\,e^{-n\sqrt y}
 \qquad (y>0,\ n>0)
\]
segue a densidade da lei \(T\)
\[
 p_T(t)=\frac{8}{\sqrt{\pi t}}\bigl(S(t)-8S(t/4)\bigr),
 \qquad S(t)=\sum_{n\ge1} n^2e^{-n^2/(4t)} .
\]
Para obter a identidade gaussiana, ponha
\(G(c)=\int_0^\infty e^{-x^2-c^2/x^2}dx\). Diferenciar em
\(c>0\) e substituir \(x=c/v\) dá \(G'=-2G\);
\(G(0)=\sqrt\pi/2\). A aplicação termo a termo à série de
\(f''(\sqrt y)/\sqrt y\) é absoluta depois de multiplicar a densidade
por \(e^{-yt}\). Assim a identidade das transformadas de Laplace
identifica a expressão com \(p_T\). O \(8S(t/4)\) vem de duas vezes
os inteiros pares com o seu quadrado.

Para \(\Re s>1\), a integral de cada parcela de \(p_T\) contra
\(t^{-r}\) converge. A substituição \(t=4v\) na segunda
parcela dá o fator \(8\cdot4^{1/2-r}=2^{1-s}\). A divisão por
\(Q\) cancela o fator \(1-2^{1-s}\) e deixa \(s-1\).
Com \(v=(4\pi t)^{-1}\), ficam
\[
 F(s)=\pi(s-1)\int_0^\infty v^{s/2}
             \sum_{n\ge1} n^2 e^{-\pi n^2v}\,dv .
\]
A convergência perto de \(v=0\) usa a cota
\(\sum n^2 e^{-\pi n^2v}=O(v^{-3/2})\). Ela segue por comparação
da soma com a integral e o máximo da função unimodal
\(x^2e^{-\pi v x^2}\).

Agora use \(v=e^{2y}\) e integre por partes. O fator \(s-1\)
vira o derivado de \(e^{3y}\sum n^2e^{-\pi n^2 e^{2y}}\)
com sinal invertido. O termo de bordo em \(-\infty\) desaparece
pois o produto a derivar é limitado e \(\Re(s-1)>0\).
Em \(+\infty\) o decaimento é duplamente exponencial.
O resultado é
\[
 \begin{split}
 F(s_0+u)&=\int_{\mathbb R} e^{uy}\Phi(y)\,dy,\\
 \Phi(y)&=\sum_{n\ge1}
   2\pi n^2 e^{5y/2}\bigl(2\pi n^2e^{2y}-3\bigr)
                         e^{-\pi n^2e^{2y}} .
 \end{split}
\]
Para ver a paridade, ponha \(D=v\partial_v\) e
\(\vartheta(v)=\sum_{n\in\mathbb Z}e^{-\pi n^2v}\).
A densidade é \(2v^{1/4}D(D+1/2)\vartheta(v)\).
Na transformação
\(\vartheta(v)=v^{-1/2}\vartheta(1/v)\),
o \(D\) do lado direito atua no argumento inverso como
\(-D-1/2\). O polinômio \(D(D+1/2)\) permanece igual, e o
fator \(v^{1/4}\) dá a paridade em \(y\). Para \(y\ge0\),
cada termo da série é estritamente positivo por \(2\pi>3\).
A paridade leva o sinal e o decaimento para o outro
semieixo. A integral agora é inteira em \(u\), e a
identidade vale por continuação analítica.
[Transformação teta de Jacobi](https://dlmf.nist.gov/20.7.E32)

## 2. As duas matrizes nascem dos coeficientes brutos

Na variável quadrática escreva
\[
 W(z^2)=F(s_0+iz),\quad
 W(X)=\sum_{j\ge0}w_jX^j,\quad
 w_j=(-1)^j\,\frac{2}{(2j)!}
                \int_0^\infty y^{2j}\Phi(y)\,dy .
\]
A resposta nativa satisfaz
\(H(X)=\sum_{j\ge0}h_j X^j=-W'(X)/W(X)\).
As duas funções de dois argumentos
\((U H(U)-V H(V))/(U-V)\) e
\((H(U)-H(V))/(U-V)\) têm coeficientes \(h_{i+j}\) e
\(h_{i+j+1}\), respectivamente. Multiplique ambas por
\(W(U)W(V)\). Os numeradores de Bézout ficam
\[
 \begin{split}
 C_0(U,V)&=\frac{V W(U)W'(V)-U W'(U)W(V)}{U-V},\\
 C_1(U,V)&=\frac{W(U)W'(V)-W'(U)W(V)}{U-V}.
 \end{split}
\]
Se \(T_N\) é a matriz triangular de convolução pelos \(w_j\),
cada bloco \(C_e^{(N)}\) é
\[
 C_e^{(N)}=T_N(h_{i+j+e})_{i,j<N}T_N^{\mathsf T}.
\]
A diagonal de \(T_N\) vale \(W(0)>0\). Em particular os
pivôs de Bézout são \(W(0)^2\) vezes os pivôs Hankel, onde
a eliminação existe. Em geral vale a igualdade de inércia
por congruência. Portanto os cruzamentos e o sinal dos
pivôs podem ser calculados diretamente dos coeficientes
brutos da integral. Nenhum momento da câmera é avaliado.

A direção crítica inteira também se transporta. Para
\(N=n+1\), denote por \(c_C\) e \(c_H\) as direções de
Schur de \(C_e^{(N)}\) e do seu Hankel, com última
coordenada \(1\) e cruzamentos com as \(n\) direções da
cabeça iguais a zero. Quando a cabeça é invertível, vale
\[
 T_N^{\mathsf T}c_C=W(0)c_H.
\]
De fato, as primeiras \(n\) coordenadas de \(C_ec_C\)
são nulas. Pela triangularidade, as primeiras \(n\)
coordenadas de \(H_eT_N^{\mathsf T}c_C\) também são nulas, e a última
coordenada de \(T_N^{\mathsf T}c_C\) é \(W(0)\).
A direção normalizada de Schur é única por
invertibilidade da cabeça.

Para calcular uma entrada \([U^iV^j]C_e\), some os
coeficientes \(U^{i+1+k}V^{j-k}\) do seu numerador para
\(0\le k\le j\). Isso vem do telescópio de multiplicar
a série por \(U-V\). No script a escala escolhida é
\(\widehat W(X)=W(196X)/W(0)\), com diagonal unitária
na convolução. Retirada essa escala, obtém-se o pivô
canônico original.

## 3. Certificação da integral e fronteira de sinal

O [certificado](certify-camera-free-theta-schur.py) integra
a série finita de \(\Phi\) em \([0,Y]\) com aritmética de
bolas. Os dois restos usam as seguintes cotas para o
momento bruto de ordem \(d=2j\):

- Para \(n>K\) e \(0\le y\le Y\), majoramos
  \(4\pi^2 Y^{d+1}e^{9Y/2}\sum_{n>K} n^4e^{-\pi n^2}\).
  A razão entre parcelas é no máximo
  \(16 e^{-\pi(2K+3)}\).
- Para \(y\ge Y\ge1\), use
  \(n^2 e^{2y}\ge(n^2+e^{2y})/2\),
  \(y^d\le e^{dy}\) e
  \(\sum n^4e^{-\pi n^2/2}<1\), por cota geométrica.
  A estimativa \(e^{2y}\ge e^{2Y}(1+2(y-Y))\)
  dá para o resto
  \[
   \frac{4\pi^2 e^{(9/2+d)Y-(\pi/2)e^{2Y}}}
        {\pi e^{2Y}-(9/2+d)} .
  \]

A prova da representação e da congruência é analítica.
O cálculo com bolas usa apenas a densidade teta, sem
alturas de zeros como entrada. Com \(Y=4\), \(K=14\) e
768 bits, os 20 pivôs centrais de cada setor ficaram
estritamente positivos. Os últimos intervalos na escala
canônica foram
\[
 \begin{aligned}
 \sigma_{0,19}(0)&\in 1.151911949329445\cdot10^{-138}
                         \ \pm\ 4.86\cdot10^{-154},\\
 \sigma_{1,19}(0)&\in 1.084596493636020\cdot10^{-142}
                         \ \pm\ 3.63\cdot10^{-159}.
 \end{aligned}
\]

```sh
python3 certify-camera-free-theta-schur.py --size 20 --bits 768 --terms 14
```

Com \(Y=4\), \(K=21\) e 1500 bits, a certificação chegou
aos 40 primeiros pivôs de cada setor. Os últimos intervalos foram
\[
 \begin{aligned}
 \sigma_{0,39}(0)&\in 1.279775460951138\cdot10^{-308}
                         \ \pm\ 2.64\cdot10^{-324},\\
 \sigma_{1,39}(0)&\in 4.520595704459119\cdot10^{-313}
                         \ \pm\ 1.77\cdot10^{-329}.
 \end{aligned}
\]

```sh
python3 certify-camera-free-theta-schur.py --size 40 --bits 1500 --terms 21
```

[Quadratura de bolas em FLINT](https://flintlib.org/doc/acb_calc/integrate.html)

O primeiro pivô par é \(h_0=\mathbb E(Y^2)/2>0\), para
\(Y\) com densidade \(\Phi/W(0)\). Já no primeiro pivô
ímpar a condição é \(\mathbb E(Y^4)<3\mathbb E(Y^2)^2\).
De fato, \(h_1=\mathbb E(Y^2)^2/4-\mathbb E(Y^4)/12\).
No bloco de Bézout, a mesma condição tem a forma
\[
 [U^0V^0]C_1=\frac{1}{24}\int_{\mathbb R^2}
 (6x^2y^2-x^4-y^4)\Phi(x)\Phi(y)\,dx\,dy.
\]
O peso é positivo. Para \(y\ne0\), o polinômio é positivo
exatamente quando \(\sqrt{2}-1<|x/y|<\sqrt{2}+1\), e é
negativo fora da faixa fechada correspondente.

A condição do quarto momento pode falhar mesmo para
uma densidade simétrica estritamente log-côncava. Tome
uma gaussiana de variância
\(4\) e some uma variável independente que vale \(0\)
com probabilidade \(3/4\) e \(\pm1\) com probabilidade
\(1/8\) cada. Sua densidade é par, positiva e estritamente
log-côncava: a segunda derivada do logaritmo é
\(-1/4+\operatorname{Var}_x(A)/16\le-3/16\),
onde \(A\in\{-1,0,1\}\) recebe os pesos inclinados
pela observação \(x\). O quarto cumulante vale \(1/16\),
logo o seu \(h_1\) é \(-1/192\). Uma prova em toda
dimensão para a fonte nativa precisa usar a estrutura
específica de \(\Phi\) para controlar os cofatores de
\(C_0,C_1\). Essa positividade geral permanece em aberto.
