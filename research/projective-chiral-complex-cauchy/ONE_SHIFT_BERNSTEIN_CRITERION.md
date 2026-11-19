# Um deslocamento fixo e um orçamento escalar para os momentos centrais

Sejam \(H(u)=\sum_{j\ge0}h_j u^j=-W'(u)/W(u)\) e
\(W(z^2)=\xi(\frac12+iz)\), na normalização dos momentos da fonte
completada. Use \(q=22/175\), com \(|h_j|\le q^{j+1}\) pelo
majorante nativo. Para um deslocamento inteiro fixo \(s\ge0\),
escrevemos \(H_s(u)=\sum_{j\ge0}h_{s+j}u^j\), o germe obtido
subtraindo os primeiros \(s\) termos de \(H\) e dividindo por \(u^s\).
[Identificação e eixo negativo](POSITIVE_CENTER_DERIVATIVE.md)
· [Majorante nativo](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeLogCoefficientMajorant.lean)

Mostramos duas reduções analíticas. Qualquer deslocamento fixo
que seja semidefinido em todos os tamanhos implica positividade
central em toda ordem nos dois setores. Para o mesmo deslocamento,
basta limitar uma soma escalar de módulos em uma subsequência de
ordens ilimitadas. A cota necessária nessa subsequência segue em aberto.

## 1. Queda no eixo negativo e recuperação do prefixo

A característica \(W\) é inteira e não se anula em \(u<0\), pois
\(W(-r^2)=\xi(\frac12+r)>0\). Para \(x_\ell=2(\ell+1)\) e
\(R_\ell=(x_\ell-\frac12)^2\), temos
\[
H(-R_\ell)=\frac{\xi'(x_\ell)/\xi(x_\ell)}{2(x_\ell-\frac12)}
  \longrightarrow 0.
\]
Basta aqui a subsequência par. O CSA formalizou que a derivada
logarítmica da característica inteira nos pares, dividida por
\(\ell+1\), tende a zero em
`completedNativeHarmonicLogDerivativeReal_div_succ_tendsto_zero`.
Retirar o prefixo de Taylor e dividir por \((-R_\ell)^s\) dá
também \(H_s(-R_\ell)\to0\) para cada \(s\) fixo.
[Cauda real no CSA #120](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/1e64d2b/CarrySelfAdjointOperator/CompletedNativeEntireComparison.lean)

Se \((h_{s+i+j})_{i,j<N}\succeq0\) para todo \(N\), a
representação de Hamburger dá uma medida positiva \(\mu_s\).
A cota dos momentos pares força suporte em \([-q,q]\), pois
\(\mu_s(|x|\ge b)\le h_{s+2j}/b^{2j}\to0\) para \(b>q\).
O transformado de Cauchy coincide com \(H_s(1/w)/w\) perto
do infinito pela expansão em \(1/w\), e depois nos semiplanos
pela identidade meromorfa. No eixo negativo ele se prolonga
holomorficamente com valores reais. A inversão de Cauchy
elimina o suporte negativo. É o mesmo argumento já usado
para \(s=0\) em [Positive Center Derivative](POSITIVE_CENTER_DERIVATIVE.md).
Assim
\[
H_s(u)=\int_{[0,q]}\frac{d\mu_s(x)}{1-ux}.
\]

Se \(s\ge1\), a relação \(H_{s-1}(u)=h_{s-1}+uH_s(u)\) dá
\[
h_{s-1}-H_{s-1}(-R_\ell)
  =\int_{[0,q]}\frac{R_\ell}{1+R_\ell x}\,d\mu_s(x).
\]
Por convergência monótona e queda no eixo negativo,
\(\int x^{-1}\,d\mu_s=h_{s-1}<\infty\), com \(+\infty\) como
valor do integrando em \(0\). Logo \(\mu_s(\{0\})=0\) e
\(d\mu_{s-1}=x^{-1}d\mu_s\) reproduz todos os momentos a partir
de \(h_{s-1}\). Iterando, obtemos \(\mu_0\ge0\) em \([0,q]\).
Em particular, para o deslocamento 1,
\(h_0=\int x^{-1}d\mu_1(x)\). A não recorrência já demonstrada
no CSA promove a semidefinitude de ambos os setores a
positividade estrita em cada dimensão.

## 2. Um orçamento de Bernstein sem inversão de matriz

Para \(L_s(x^j)=h_{s+j}\), tome os pesos escalares
\[
w_{N,k}
 =L_s\left(\binom Nk(x/q)^k(1-x/q)^{N-k}\right),\qquad
V_N=\sum_{k=0}^{N}|w_{N,k}|.
\]
Os pesos são diferenças finitas dos momentos escalados.
O binômio dá \(\sum_k w_{N,k}=h_s\). Para \(j\le N\), a
identidade binomial fatorial dá
\[
\sum_{k=0}^N w_{N,k}\frac{(k)_j}{(N)_j}
   =q^{-j}h_{s+j},
\]
onde \((k)_j=k(k-1)\cdots(k-j+1)\).
A diferença entre \((k/N)^j\) e \((k)_j/(N)_j\) tem módulo
no máximo \(j(j-1)/(2N)\). De fato, essas são as probabilidades
de \(j\) sucessos com e sem reposição em \(N\) endereços,
dos quais \(k\) são favoráveis. A primeira distribuição
condicionada a endereços distintos dá a segunda e a
probabilidade de colisão é limitada pela soma sobre os pares.

Seja \(\nu_N=\sum_k w_{N,k}\delta_{qk/N}\), uma medida finita
possivelmente assinada. Portanto, sem supor sinal dos pesos,
\[
\left|\int x^j\,d\nu_N-h_{s+j}\right|
 \le \frac{V_N q^j j(j-1)}{2N}.
\]
Se \(V_N\) é limitado ao longo de uma subsequência não limitada,
os momentos de \(\nu_N\) convergem nessa subsequência. Para
cada polinômio \(p\), isso dá
\(|L_s(p)|\le(\sup V_N)\|p\|_{\infty,[0,q]}\).
A extensão por densidade de polinômios e o teorema de
representação de Riesz dão uma medida assinada finita
\(\mu_s\) em \([0,q]\), reproduzindo os momentos.

## 3. Por que a medida assinada da fonte acaba positiva

Para uma medida assinada, a mesma expansão perto do infinito
identifica seu transformado de Cauchy
\(G_s(w)=\int(w-x)^{-1}d\mu_s(x)\) com \(H_s(1/w)/w\).
A identidade meromorfa continua em cada semiplano.
Em um intervalo compacto que evita os polos, o lado direito
é holomorfo e real no eixo. A parte imaginária tende a zero
uniformemente em subintervalos compactos.
A fórmula de Poisson
\[
-\operatorname{Im}G_s(t+i\varepsilon)=
  \int \frac{\varepsilon}{(t-x)^2+\varepsilon^2}\,d\mu_s(x)
\]
elimina a restrição da medida nesses intervalos. Para ver isso,
integre contra funções contínuas compactamente suportadas no
intervalo e use a aproximação da identidade, com convergência
dominada pela variação total. Assim, fora de zero, apenas os
polos reais positivos podem carregar massa.

Em um polo \(x>0\), \(W\) tem um zero em \(1/x\) de multiplicidade
\(m_x\). O resíduo de \(H\) nesse zero é \(-m_x\). Divisão
por \(u^s\) e a mudança \(u=1/w\) dão
\[
\mu_s(\{x\})=\operatorname{Res}_{w=x}G_s(w)=m_x x^{s+1}>0.
\]
A leitura da massa pelo resíduo segue de
\(i\varepsilon G_s(x+i\varepsilon)\to\mu_s(\{x\})\):
o integrando tem módulo no máximo 1 e tende ao indicador de
\(\{x\}\). Por fim, convergência dominada em
\(H_s(-R_\ell)=\int(1+R_\ell x)^{-1}d\mu_s\) dá
\(\mu_s(\{0\})=0\), pela queda no eixo negativo.
Os polos são discretos longe de zero e todas as suas massas
são positivas. A seção 1 recupera então \(\mu_0\).

Reciprocamente, a medida positiva em \([0,q]\) dá
\(w_{N,k}\ge0\) para qualquer \(s\) fixo e \(V_N=h_s\).
Assim, para o germe nativo, basta limitar \(V_N\) em uma
subsequência não limitada, em um único \(s\).
Pela identidade de massa, isso equivale a limitar a massa
negativa agregada \((V_N-h_s)/2\) nessa subsequência.
A positividade individual dos pesos pode ser dispensada na
hipótese, pois os resíduos da fonte impõem o sinal depois.

O orçamento \(V_N\) é crescente. A elevação de grau da base dá
\[
w_{N,k}=\frac{N+1-k}{N+1}w_{N+1,k}
       +\frac{k+1}{N+1}w_{N+1,k+1}.
\]
Tomar módulos e somar usa coeficientes com soma 1 para
cada peso da linha \(N+1\), portanto \(V_N\le V_{N+1}\).
Para a fonte completada, a equivalência acima dá a alternativa
\(V_N=h_s\) em toda linha, ou \(V_N\to+\infty\).
O majorante bruto \(|h_j|\le q^{j+1}\) sozinho dá
\(V_N\le q^{s+1}3^N\), que ainda cresce com \(N\).

## 4. Verificações finitas na fonte C3

O verificador recompõe a característica C3 antes de dividir
pelo fator de câmera e usa a recorrência logarítmica do
[certificado do limiar](C3_LAST_COEFFICIENT_THRESHOLD.md).
Confere massa, alguns momentos fatoriais e sinal por
intervalos Arb com 6144 bits.

| Deslocamento \(s\) | Ordem \(N\) | Todos os pesos certificados positivos |
|---:|---:|:---:|
| 1 | 32 | ✓ |
| 1 | 64 | ✓ |
| 1 | 115 | ✓ |
| 6 | 110 | ✓ |
| 20 | 96 | ✓ |

A equivalência do orçamento é analítica. Os testes são
certificados finitos por intervalos, e a formalização Lean
desta redução ainda está em aberto.

```bash
/home/thlinux/miniforge3/bin/python3 \
  research/projective-chiral-complex-cauchy/certify-bernstein-weights.py
```
