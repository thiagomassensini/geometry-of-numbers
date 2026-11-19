# A taxa exata do orçamento de Bernstein no centro

A [redução anterior](ONE_SHIFT_BERNSTEIN_CRITERION.md) pede uma cota
para a variação \(V_N\) de uma única linha de Bernstein ao longo de
uma subsequência de ordens ilimitadas. Fixamos o deslocamento \(s=1\).
O resultado abaixo determina a taxa exponencial exata de \(V_N\) e
fornece uma cota incondicional em cada ordem. A cota uniforme
necessária para concluir a positividade central permanece em aberto.

Usamos o germe da resposta logarítmica da característica já sintetizada,
\(H(u)=-W'(u)/W(u)=\sum_{j\ge0}h_j u^j\), com
\(W(z^2)=\xi(\tfrac12+iz)\). O majorante nativo fornece \(q=22/175\).
A identificação é a da [resposta central](POSITIVE_CENTER_DERIVATIVE.md)
na base GoN de commit 008d31f92504a7cf252520e60c9b18edabf3959f.
[Majorante no CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeLogCoefficientMajorant.lean)

## 1. Polinômio que lê a linha inteira

Para \(L_1(x^j)=h_{j+1}\) e os pesos \(w_{N,k}\) da redução anterior,
o binômio dá
\[
P_N(\zeta)=\sum_{k=0}^N w_{N,k}\zeta^k
  =L_1\big((1+(\zeta-1)x/q)^N\big).
\]
Assim, com \(H_1(u)=\sum_{j\ge0}h_{j+1}u^j\),
\[
\sum_{N\ge0}P_N(\zeta)t^N
  =\frac{1}{1-t}H_1\!\left(\frac{(\zeta-1)t}{q(1-t)}\right).
\]
A igualdade segue de \(\sum_{N\ge j}\binom Nj t^N
=t^j/(1-t)^{j+1}\) e vale como identidade de germes. Na continuação
meromorfa, um polo de \(H\) em \(1/\lambda\) continua presente em
\(H_1=(H-h_0)/u\). Para \(\zeta\ne1\) e \(1+(\zeta-1)\lambda/q\ne0\),
ele dá um polo em \(t=(1+(\zeta-1)\lambda/q)^{-1}\).
A desigualdade \(|P_N(\zeta)|\le V_N\) vale para todo \(|\zeta|=1\).

## 2. Limite exato para a fonte completada

O produto centrado de Hadamard para a característica identificada
emparelha os zeros \(z,-z\). Na variável \(u=z^2\), ele dá
\[
W(u)=W(0)\prod_{\lambda}(1-\lambda u)^{m_\lambda},
\qquad \sum_{\lambda}m_\lambda|\lambda|<\infty,
\qquad \lambda=1/z^2 .
\]
A soma e o produto percorrem valores distintos de \(\lambda\), com
\(m_\lambda\) a multiplicidade do zero de \(W\). O produto agrupado
em \(z^2\) tem gênero zero. A derivada logarítmica perto do centro dá
\(h_j=\sum_\lambda m_\lambda\lambda^{j+1}\). Usamos o produto após a
identificação da fonte. [Produto centrado de Hadamard em Voros, §§2 e 5](https://www.numdam.org/item/10.5802/aif.1955.pdf)

Escreva \(a_\lambda=\lambda/q\), \(A_\lambda(\zeta)=1-a_\lambda+a_\lambda\zeta\)
e \(\rho=\sup_\lambda(|1-a_\lambda|+|a_\lambda|)\ge1\).
Temos as identidades de linha e a estimativa
\[
P_N(\zeta)=\sum_\lambda m_\lambda\lambda^2 A_\lambda(\zeta)^N,
\qquad
V_N\le\left(\sum_\lambda m_\lambda|\lambda|^2\right)\rho^N.
\]
A cota toma a norma \(\ell^1\) do binômio após a expansão de cada
termo. Para provar a estimativa inversa na escala \(N\)-ésima, usamos
\(|a_\lambda|\le(196q)^{-1}<1/2\), certificado na seção 3.

Se \(\rho>1\), fixe \(1<R<\rho\). Existe uma fase \(|\zeta|=1\) com
\(|A_\lambda(\zeta)|>R\) para algum \(\lambda\), pois
\(\max_{|\zeta|=1}|A_\lambda(\zeta)|=|1-a_\lambda|+|a_\lambda|\).
Só um conjunto finito de polos pode superar \(R\) em alguma fase,
já que \(|A_\lambda|\le 1+2|a_\lambda|\) e os \(\lambda\) acumulam
apenas em zero. Para polos distintos nesse conjunto, o coeficiente
de \(\zeta\) em \(|A_\lambda(\zeta)|^2\) é \(a_\lambda-|a_\lambda|^2\)
e distingue os polos. De fato, sua parte imaginária fixa
\(\operatorname{Im}a_\lambda\) e \(x-x^2\) é estritamente crescente
para \(x<1/2\). Logo o empate de módulos de cada par ocorre em no
máximo duas fases. Escolha uma fase próxima da original evitando
esses empates. O maior módulo \(M>R\) passa a ter um único termo.
O restante tem módulo total no máximo \(C M_2^N\), para \(M_2<M\),
pela somabilidade de \(\sum_\lambda m_\lambda|\lambda|^2\). O termo
de módulo \(M\) tem coeficiente não nulo. Isso dá
\(\liminf_{N\to\infty}V_N^{1/N}\ge M>R\). Tome \(R\uparrow\rho\).

Se \(\rho=1\), a igualdade triangular força todos os
\(a_\lambda\in[0,1]\). Todos os pesos \(w_{N,k}\) são então
não negativos por sua expansão binomial. Nesse caso \(V_N=h_1>0\).
Concluímos em todos os casos que
\[
\boxed{\displaystyle
  \lim_{N\to\infty}V_N^{1/N}
   =\sup_\lambda\big(|1-\lambda/q|+|\lambda/q|\big).}
\]

No strip dos zeros, \(\Re z\ne0\) pela seção 3. Assim \(\lambda=1/z^2\)
é real positiva exatamente quando \(\Im z=0\). A cota \(V_N=O(1)\)
em qualquer subsequência ilimitada é equivalente a \(\rho=1\), que
para esta característica equivale à hipótese de Riemann. Para
\(\rho=1\), a representação positiva e a não recorrência da fonte
dão os prefixos centrais estritamente positivos conforme a
[redução anterior](ONE_SHIFT_BERNSTEIN_CRITERION.md).
[Faixa crítica e hipótese de Riemann no DLMF](https://dlmf.nist.gov/25.10)

## 3. Cota incondicional

Os zeros de \(\xi(s)\) estão na faixa \(0<\Re s<1\). O script
[certify-bernstein-growth-bound.py](certify-bernstein-growth-bound.py)
certifica \((s-1)\zeta(s)\ne0\) em
\(\frac12\le\Re s\le 1,\ 0\le\Im s\le14\). A função é regularizada
também em \(s=1\). Cada folha da subdivisão diádica tem uma inclusão
por aritmética de bolas que exclui zero. Por simetria funcional e
conjugação, a mesma ausência de zeros de \(\xi\) vale em toda a
largura da faixa quando \(|\Im s|\le14\). O cálculo usa avaliações
da função no retângulo, sem uma tabela de alturas.
[Deflação em FLINT](https://flintlib.org/doc/acb_dirichlet/acb_dirichlet_zeta_jet.html)

Consequentemente \(r=|\lambda|\le r_0=1/196\) para cada zero transformado.
Para \(b=\Im z\), temos \(|b|<\tfrac12\) e
\(\Re\lambda=r-2b^2r^2\).
Com \(v=r/q\), isso dá o excesso exato
\[
|1-\lambda/q|+v-1
 =\frac{4b^2qv^2}{|1-\lambda/q|+1-v}.
\]
Em particular, \(|1-\lambda/q|+v\le v+\sqrt{(1-v)^2+qv^2}\).
Esta última função é convexa, por ser a soma de uma função afim com
a norma euclidiana de uma função afim vetorial. Seu máximo em
\(0\le v\le r_0/q\) ocorre num extremo. O valor em \(0\) é \(1\) e o
valor no outro extremo é \(\rho_0\).

Além disso,
\[
\Re(\lambda^2)
 \ge c|\lambda|^2,\qquad
c=2(1-r_0/2)^2-1>0 .
\]
Com efeito, \(\Re\lambda/r\ge1-r_0/2>0\) e
\(\Re(\lambda^2)/r^2=2(\Re\lambda/r)^2-1\).
Tomando parte real em \(h_1=\sum_\lambda m_\lambda\lambda^2\),
obtemos \(\sum_\lambda m_\lambda|\lambda|^2\le h_1/c\).
Portanto, para todo \(N\ge0\),
\[
h_1\le V_N
 \le \frac{h_1}{c}\rho_0^N
 \le 1.011\,h_1(1.000108)^N .
\]
A cota inferior é a identidade de massa. O script verifica ambas
as constantes decimais por comparações racionais exatas. O certificado
em FLINT e a demonstração acima constituem uma prova analítica com
verificação intervalar da faixa finita.

## 4. O que uma cabeça finita e um majorante absoluto determinam

Considere um modelo auxiliar com polos inversos
\(p_k=q/(64k^2)>0\), todos simples. Ele tem a mesma forma de produto,
momentos limitados em módulo por \(q^{j+1}\) e infinitos polos
positivos. Podemos preservar qualquer cabeça de \(J\) coeficientes
exatos desse modelo e introduzir um par de polos complexos
conjugados dentro da faixa correspondente a \(|\Im z|<1/2\).

Para isso tome \(\lambda=(X+i/4)^{-2}\) com \(X\) arbitrariamente
grande. Ajuste só \(p_1,\ldots,p_J\) para valores reais próximos
\(p_1',\ldots,p_J'\), resolvendo
\[
\sum_{k=1}^J(p_k')^\ell
 =\sum_{k=1}^Jp_k^\ell-2\Re(\lambda^\ell),\qquad 1\le\ell\le J.
\]
O jacobiano em \(p\) tem entradas \(\ell p_k^{\ell-1}\) e é inversível
por Vandermonde. Para \(X\) grande, o teorema da função inversa
fornece a solução, mantendo os \(p_k'\) positivos. Os primeiros \(J\)
coeficientes de \(-W'/W\) ficam idênticos. Todos os módulos dos polos
podem ser mantidos abaixo de \(q/16\) e a soma de seus módulos abaixo
de \(q/4\), por convergência de \(\sum p_k\) e continuidade do ajuste
finito. Assim o majorante estrito
\(4(q/16)^{j+1}\le q^{j+1}-(1/25)^{j+1}\) vale em todo \(j\).
O novo par tem \(|1-\lambda/q|+|\lambda/q|>1\), de modo que a taxa
na seção 2 é maior que 1 para esse modelo. A construção testa o poder
lógico da cabeça e do majorante isolados. O erro conectado do Green
nativo requer uma identidade adicional para restringir a cauda.
