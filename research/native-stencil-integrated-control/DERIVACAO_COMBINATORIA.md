# Identidade dos stencils por diferença finita centrada

A derivação abaixo explica a prova para ordens arbitrárias. O Lean formaliza a redução da soma dupla do stencil à diferença centrada em `odd_stencil_pair_eq_centered` e a identidade completa em `odd_stencil_correction_all_order`. A etapa beta usa o complemento e as features de Cauchy da fonte original. `original_odd_pair_expansion_lambda` transporta o mesmo coeficiente à expansão nativa com a cauda preservada.

Sejam `m,n` ímpares não negativos, `N=m+n+2`, `c=n+1`, e defina, para `d` ímpar,

$$T_{m,n}(d)=\frac1{m!n!}\sum_{i=0}^m\sum_{j=0}^n(-1)^{m+n-i-j}\binom mi\binom nj\frac{(i+1)^d+(j+1)^d}{i+j+2}.$$

Esta é a soma combinatória com os dois índices e o denominador de Cauchy originais, antes de afirmar uma identidade com o pareamento físico completo.

## 1. Somar uma perna sem eliminar a outra

Para inteiros `i,n≥0`, a expansão do binômio e a integral beta elementar dão

$$\sum_{j=0}^n\frac{(-1)^{n-j}\binom nj}{i+j+2}
=\int_0^1 t^{i+1}(t-1)^n\,dt
=(-1)^n\frac{(i+1)!\,n!}{(i+n+2)!}.$$

A integral aqui é apenas uma identidade para uma soma racional finita: não introduz fonte theta ou positividade de momentos. Aplicando-a primeiro ao termo `(i+1)^d` e depois, simetricamente, ao termo `(j+1)^d`, obtêm-se duas somas finitas. Na primeira, coloque `k=i+1` e use

$$\frac1{(m-i)!(i+n+2)!}=\frac{\binom{N}{n+1+k}}{N!}.$$

Na segunda, com `k=j+1`, use simetria binomial para escrever seu coeficiente como `binom(N,n+1-k)`. Como `m,n` são ímpares, `m+n` e `c=n+1` são pares. Como `d` é ímpar, `d+1` é par. Os dois lados se juntam numa diferença finita centrada; o termo `k=0` é zero. Assim,

$$\boxed{T_{m,n}(d)=-\frac1{N!}\sum_{j=0}^N(-1)^j\binom Nj(j-c)^{d+1}.} \tag{1}$$

Nenhuma passagem eliminou cruzamentos: a redução é uma igualdade algébrica da soma dupla inteira.

## 2. As duas camadas

Pela expansão binomial e pela identidade de diferenças finitas de Stirling,

$$\sum_{j=0}^N(-1)^{N-j}\binom Nj j^r=N!\,S(r,N),$$

onde `S(r,N)=0` para `r<N`. Como N é par, o sinal é o de (1). Para `d=N-1`, apenas `r=N` contribui e `S(N,N)=1`; portanto

$$T_{m,n}(N-1)=-1.$$

Para `d=N+1`, aparecem apenas `r=N,N+1,N+2`, dando

$$T_{m,n}(N+1)=-\left[\binom{N+2}{2}c^2-(N+2)c\binom{N+1}{2}+S(N+2,N)\right]. \tag{2}$$

A recorrência de Stirling fornece

$$S(N+1,N)=\binom{N+1}{2},\qquad S(N+2,N)=\frac{N(N+1)(N+2)(3N+1)}{24}.$$

Substituindo `N=m+n+2`, `c=n+1` e simplificando o polinômio do colchete, obtemos exatamente

$$\boxed{T_{m,n}(m+n+3)=-\Lambda_{m,n}},$$

$$\Lambda_{m,n}=\frac{(m+1)(m+2)(2m+3)}{12}+\frac{(n+1)(n+2)(2n+3)}{12}+\frac12\left(\frac{(m+1)(m+2)-(n+1)(n+2)}2\right)^2.$$

Essa igualdade foi demonstrada em Lean para quaisquer `m,n` ímpares. O coeficiente foi identificado com `spatialCorrection`, já transportado à expansão do par nativo completo; o novo teorema `original_odd_pair_expansion_lambda` explicita essa identidade mantendo fases e cauda. Ela não é uma lei de sinal da combinação crítica: seus cruzamentos têm coeficientes próprios.
