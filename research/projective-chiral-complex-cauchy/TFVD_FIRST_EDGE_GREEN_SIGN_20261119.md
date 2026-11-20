# Sinal do Green na primeira aresta da onda TFVD

Partimos do bracket C3 com semente, da onda Dirichlet nativa e do
traço físico do [transporte TFVD](GREEN_TFVD_MIXED_TRANSPORT_20261119.md)
no commit \(\texttt{b7526a6}\). O módulo
[TfvdFirstEdgeGreenSign.lean](TfvdFirstEdgeGreenSign.lean) usa o
\(\texttt{CPFormal}\) do CSA no pin \(\texttt{65d50f6}\).

## O sinal vem do déficit de massa no vértice 2

Escreva \(s=\sigma+it\), \(s^\#=1-\bar s\) e \(d=\sigma-\tfrac12\).
O dado realmente analisado pelo TFVD são as arestas
\(g_s(n)=(n+2)^{-s}-(n+1)^{-s}\). Seu traço no prefixo de duas
arestas é \((g_s(0),q^{-1}g_s(1)-g_s(0))\). A semente
Genuine \(C3\) vale \(1\). Portanto o readout
\(V(s)=1+g_s(0)=2^{-s}\) vem do próprio traço, para qualquer razão
\(q\) e atlas de análise TFVD. O corte e a câmera de análise
continuam sendo os do transporte original.

O produto e a diferença das amplitudes dão as duas identidades
\[
 |V(s)|\,|V(s^\#)|=\tfrac12,\qquad
 |V(s^\#)|-|V(s)|=2^{-1/2}(2^d-2^{-d}).
\]
Em particular,
\(|V(s)|(|V(s^\#)|-|V(s)|)=\tfrac12-|V(s)|^2\).
Essa é a parte do desequilíbrio que o produto conservado deixa livre.

Se \(G_{2,M}\) é o fluxo acoplado \(\texttt{finiteBracketCoupledCpGreenFlux}\)
com coeficiente radial de base \(2\), e \(B_M\) é seu bordo, o
Lean prova no mesmo corte
\[
\boxed{\quad
2^{-1/2}|V(s)|\bigl(G_{2,M}(s)-B_M(s)\bigr)
  =\bigl(\tfrac12-|V(s)|^2\bigr) E_M(s).
\quad}
\]
Aqui \(E_M=\Re\langle g_s,g_{s^\#}\rangle_{n<M}\) é o
pareamento original reconstruído. O fator \(|V|>0\), e \(E_M>0\)
para \(M>0\) na faixa Genuine. O teorema
\(\texttt{tfvdBaseTwoGreenBulk_pos_iff_firstVertex_mass_lt_half}\)
identifica o sinal positivo corte a corte.

Num zero Genuine o bordo tende a zero, e o mesmo resultado
vale para o fluxo limite, com \(E_\infty>0\).
A correção angular não escalada continua com limite de parte
real \(-E_\infty\). O fechamento do total, já provado, ocorre
pelo cancelamento. A anulação do fluxo isolado pediria a
igualdade \(|V(s)|^2=\tfrac12\).

A primeira aresta dá inclusive uma cota inferior que dispensa
o restante do pareamento. Como
\(\overline{V(s)}V(s^\#)=\tfrac12\), a contribuição dessa
aresta é
\[
\Re\bigl[(\overline{V(s)}-1)(V(s^\#)-1)\bigr]
 \ge(1-|V(s)|)(1-|V(s^\#)|)>0 .
\]
Todas as demais arestas têm parte real positiva na faixa.
Assim a margem do módulo do fluxo isolado num zero Genuine é
\[
|G_{2,\infty}(s)|\ \ge\
 \frac{\sqrt2}{|V(s)|}\left|\tfrac12-|V(s)|^2\right|
 (1-|V(s)|)(1-|V(s^\#)|).
\]
[Positividade por aresta no primos](https://github.com/thiagomassensini/primos/blob/65d50f6/CPFormal/Analytic/CpFiniteGreenPositivity.lean#L176)

## Ligação com o skew espectral

O lema
\(\texttt{im_spectralQuadratic_eq_log_tfvdFirstVertex_mass}\)
liga \(\Lambda=s(1-s)\) ao mesmo readout:
\[
\Im\Lambda=\frac{t}{\log 2}\log(2|V(s)|^2).
\]
O arquivo \(\texttt{green_spectral_skew_20261119.lean}\) identifica
o pareamento misto dos fluxos refletidos com
\(\Lambda-\bar\Lambda=2i\Im\Lambda\). A parte transversal
recuperada pelo traço é a massa. O fator \(t\) vem da variável
dinâmica. Para \(t>0\), o fluxo Green e \(\Im\Lambda\)
têm sinais opostos quando a massa difere de \(1/2\).
[Arquivo original](https://chatgpt.com/library?file_id=libfile_5ef0235806488191b61ce5b821419a28&account_id=personal)

Há uma obstrução a recuperar o fluxo característico completo
por uma aplicação contínua apenas desse traço finito em toda a
faixa. O traço de duas arestas depende só de \(2^{-s},3^{-s}\).
Para \(\sigma\) fixo, há \(T_k\to\infty\) tais que
\(e^{-iT_k\log2}=1\) e \(e^{-iT_k\log3}\to1\).
De fato, tome diferenças de dois termos cada vez mais separados
de uma subsequência convergente de
\(e^{-2\pi i m\log3/\log2}\), e multiplique os índices
resultantes por \(2\pi/\log2\). Assim volta-se ao mesmo traço
como limite, tanto na onda direta quanto na refletida. Ao
mesmo tempo \(t+T_k\) cresce sem limite. Para \(d\ne0\),
isso impede até recuperar \(\Lambda-\bar\Lambda\) do par
de traços por uma aplicação contínua em sua imagem. A fórmula
com a massa identifica exatamente a parcela do skew acessível
pelo traço sem o dado dinâmico \(t\).

## Teste da passagem do fechamento para a massa equilibrada

A conservação refletida, mesmo em **todos os vértices**,
e o fechamento das **duas** cartas C3 em todos os cortes
\(M\ge1\) permitem desequilíbrio para amostras gerais.
O primeiro bloco com semente é
\[
(f_1,f_2,f_3,f_4)=(1,\tfrac23,\tfrac23,-\tfrac13),\qquad
(g_1,g_2,g_3,g_4)=(1,\tfrac34,\tfrac12,-\tfrac34).
\]
Em cada onda, \(u_1+u_2-2u_3+u_4=0\).
Nos quatro vértices \(\bar f_ng_n=1/n\), mas
\(|f_2|^2=4/9\ne1/2\).
O pareamento misto das primeiras três arestas é \(4/3>0\).
O primeiro bloco consta no Lean em
\(\texttt{seededFirstCell_conserved_product_counterexample}\).

Os demais blocos C3 são disjuntos. Para cada centro \(c=6,9,\ldots\)
tome \(a=(c-1)^{-1/2}\), \(b=(c+1)^{-1/2}\) e
\(m=2c^{-1/2}\). Temos \(|a-b|<m<a+b\) pela convexidade
estrita de \(x^{-1/2}\) e por \(a<2c^{-1/2}\).
Escolha \(\theta\) com \(|a+be^{i\theta}|=m\), e ponha
\[
 f=g=(a,(a+be^{i\theta})/2,be^{i\theta})
 \quad\text{nos vértices }(c-1,c,c+1).
\]
Assim cada bracket posterior zera, a semente é preservada,
e \(\bar f_ng_n=1/n\) em todo vértice. As duas sequências de
arestas estão em \(\ell^2\). Com efeito,
\(a+b-m=O(c^{-5/2})\) pelo resto de segunda ordem,
\(1-\cos\theta=((a+b)^2-m^2)/(2ab)=O(c^{-2})\),
e os valores ficam a \(O(n^{-3/2})\) de \(n^{-1/2}\).
As arestas entre blocos também ficam nessa ordem. Seu
pareamento real mantém a contribuição positiva \(4/3\):
a quarta aresta tem incremento real positivo nas duas ondas,
e as posteriores vêm de \(f=g\).

O modelo testa a passagem a partir da reconstrução, do
fechamento e da conservação ponto a ponto. A realização
exponencial \(n^{-s}\) traz uma identidade dinâmica adicional.
Já no primeiro bloco do modelo \(f_4\ne f_2^2\).
Portanto a obrigação nos zeros da **onda original** é fazer
a dinâmica nativa, junto com o fechamento, forçar a igualdade
de massas no vértice \(2\). É essa passagem que continua em
aberto, e da qual depende a anulação do modo pela rota Green.

## O que a multiplicatividade já força no primeiro bloco

Para a onda nativa, escreva \(a=2^{-s}\), \(b=3^{-s}\).
Como \(4^{-s}=a^2\), o primeiro corte com semente é
\(A_1(s)=1+a+a^2-2b\). Para a refletida, as fases são
compatíveis com o produto de vértice e
\(\overline{a^\#}=1/(2a)\), \(\overline{b^\#}=1/(3b)\).
O lema Lean
\(\texttt{reflectedMultiplicativeFirstCell_polynomial}\)
verifica a eliminação algébrica de \(b\) abaixo.

Ponha \(w=\sqrt2\,a\), \(r=|w|\in(1/\sqrt2,\sqrt2)\),
\(x=w+w^{-1}\) e \(P(w)=1+w/\sqrt2+w^2/2\). Então
\[
 P(w)P(w^{-1})-\tfrac43
  =\tfrac12 x^2+\tfrac{3}{2\sqrt2}x-\tfrac7{12}
  =P(w^{-1})A_1(s)+2b\,\overline{A_1(s^\#)}.
\]
A quadrática tem uma raiz \(x_+\in(0,1)\) e outra \(x_-<-5/2\),
por seu sinal em \(0,1,-5/2\). Como
\(|x|\le r+r^{-1}\le 3/\sqrt2<9/4\),
temos \(|x-x_-|>1/4\). Escreva \(x_+=\omega+\bar\omega\)
com \(|\omega|=1\) e \(|\Im\omega|>\sqrt3/2\).
Em \(|x-x_+|=|w-\omega|\,|w-\bar\omega|/r\), cada fator
do numerador é pelo menos \(|r-1|\), e o maior é pelo menos
\(|\omega-\bar\omega|/2>3/4\). Como \(1/r>2/3\), resulta
\[
\bigl|P(w)P(w^{-1})-\tfrac43\bigr|\ \ge\ |r-1|/16.
\]
Por outro lado \(|P(w^{-1})|\le3\) e \(2|b|\le2\).
Portanto
\[
 \boxed{\displaystyle
 |A_1(s)|+|A_1(s^\#)|\ \ge\
   \frac{|\sqrt2\,|2^{-s}|-1|}{48}.}
\]
Esse é um limite inferior para a compensação de cauda em
qualquer zero Genuine. Como as duas cartas completas zeram,
suas duas caudas após o primeiro bloco precisam reter juntas
ao menos essa margem. Se ambos os primeiros cortes fechassem, essa cota forçaria
massa crítica na classe multiplicativa. A exclusão fora da linha
exigiria ainda mostrar que a cauda nativa não pode suprir
essa compensação. A cota e a extensão infinita do contramodelo
acima são provas analíticas.
