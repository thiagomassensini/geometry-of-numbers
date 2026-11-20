# A câmera e a fonte nas mesmas direções de Schur

A identidade do [núcleo Mellin polarizado](C2_MELLIN_POLARIZED_CANCELLATION.md)
dá uma relação exata \(H_e=A_e-B_e\) em cada setor \(e=0,1\).
Aqui \(H_e\) é o Hankel completado, \(A_e\) a fonte Mellin
com a Gamma já cancelada e \(B_e=(b_{i+j+e})\) a câmera.
Este checkpoint calcula as três formas na **mesma direção**
e estabelece uma obstrução para cotas relativas termo a termo.

## 1. Comparação certificada em ordem finita

Escreva \(L_e(x^j)=h_{j+e}\), \(B_e(x^j)=b_{j+e}\) e
\(A_e=L_e+B_e\) para os funcionais associados.
O polinômio mônico \(P_{e,n}\) de grau \(n\) que resolve a
eliminação de Schur é \(L_e\)-ortogonal aos graus menores.
Logo
\[
 \sigma_{e,n}=L_e(P_{e,n}^{\,2}),\qquad
 A_e(P_{e,n}^{\,2})=\sigma_{e,n}+B_e(P_{e,n}^{\,2}).
\]
Aplicar os mesmos multiplicadores da eliminação de \(H_e\) à
câmera por congruência conserva todos os cruzamentos. A razão
\(B_e(P_{e,n}^{\,2})/\sigma_{e,n}\) independe da escala do
monômio usada no cálculo. A direção da câmera eliminada
isoladamente seria diferente.

O script
[certify-mellin-matched-schur.py](certify-mellin-matched-schur.py)
reutiliza os coeficientes intervalares da característica completada
do GoN, na base \(\texttt{b7526a6}\). Para a câmera, usa a série
exata de \(Q\) do checkpoint anterior. Toda a eliminação e a
congruência usam bolas reais em 3072 bits, sem alturas de zeros
como dados. Os 20 pivôs de cada setor foram certificados
estritamente positivos. Alguns dos intervalos, arredondados
para exibição, são:

| Setor \(e\) | Grau da direção \(n\) | Pivô completado \(\sigma_{e,n}\) | Câmera dividida pelo pivô |
|---:|---:|---:|---:|
| 0 | 2 | \(1,1146\cdot10^{-13}\) | \(+6,4369\cdot10^2\) |
| 0 | 5 | \(4,1272\cdot10^{-33}\) | \(+3,9383\cdot10^9\) |
| 0 | 6 | \(5,1369\cdot10^{-40}\) | \(-4,2004\cdot10^{12}\) |
| 0 | 19 | \(1,1519\cdot10^{-138}\) | \(-6,8541\cdot10^{60}\) |
| 1 | 5 | \(1,5729\cdot10^{-36}\) | \(-3,9492\cdot10^9\) |
| 1 | 19 | \(1,0846\cdot10^{-142}\) | \(+6,4318\cdot10^{62}\) |

A razão da fonte é exatamente um mais a razão da câmera.
Em particular a fonte isolada já dá energia negativa na direção
de grau \(6\) no setor par e na de grau \(5\) no setor ímpar.
A diferença completada é estritamente positiva nessas direções.
A fonte no experimento foi lida via identidade exata
\(A_e=H_e+B_e\), usando a expressão completada identificada
com a fonte nativa e a série da câmera. O cálculo não pressupõe
que \(A_e\) seja um Gram.

## 2. Fórmula exata dos modos da câmera

Com \(L=\log 2\), \(\omega_k=2\pi k/L\) e
\(\lambda_k=(\omega_k-i/2)^{-2}\), o produto de \(\sinh\)
dá a expansão
\[
 b_j=\frac12\sum_{k\ge1}
    \left(\lambda_k^{j+1}+\overline{\lambda_k}^{\,j+1}\right).
\]
De fato,
\(Q(s)=L e^{(1-s)L/2}
 \prod_{k\ge1}(1+(1-s)^2/\omega_k^2)\).
No produto \(M_B(u)=Q(1/2+u)Q(1/2-u)/Q(1/2)^2\),
os fatores exponenciais desaparecem. Cada par em
\(M_B(iz)\) é \((1-\lambda_k z^2)(1-\overline{\lambda_k}z^2)\).
Derivar o logaritmo e aplicar a normalização de \(1/4\)
do núcleo dá a expansão acima. A série converge absolutamente
perto do centro, pois \(|\lambda_k|=O(k^{-2})\).
[Produto de \(\sinh\)](https://dlmf.nist.gov/4.36.E1)

Ao retirar os primeiros \(m\) pares comuns da fonte e da câmera,
a diferença completada permanece \(H_e\). A câmera que sobra
em qualquer direção polinomial real \(P\) tem a leitura exata
\[
 B_e^{>m}(P^2)=
 \Re\sum_{k>m}\lambda_k^{e+1}P(\lambda_k)^2 .
\]
Assim o sinal vem da fase de \(P(\lambda_k)^2\). Uma
soma dos módulos dessas parcelas perde essa informação.

No teste que retira o primeiro par, os pivôs completados
permanecem iguais. Na direção de grau \(19\), as razões
da câmera restante são \(-4{,}1288\cdot10^{35}\) no setor
par e \(-1{,}2933\cdot10^{37}\) no ímpar, também certificadas
por intervalos. Isso confirma a fórmula de retirada do par
na escala das direções efetivamente usadas.

## 3. Obstrução assintótica nas direções de Schur

**Hipótese desta seção.** Suponha a positividade central em todas
as ordens. A redução anterior identifica \(L_e\) com a medida positiva
discreta dos polos inversos nativos. Seus pontos distintos
\(x_j>0\) têm única acumulação em zero e \(\sum_j x_j<\infty\)
pelo produto de Hadamard da característica completada. Aqui
usamos a medida para testar a estratégia sob a hipótese mais
favorável. A seção 1 é incondicional.
[Redução de medida](ONE_SHIFT_BERNSTEIN_CRITERION.md)
· [Produto centrado e identificação dos polos](BERNSTEIN_GROWTH_RATE.md)

Fixe um setor \(e\) e escreva \(P_n=P_{e,n}\), \(\sigma_n=\sigma_{e,n}\).
A caracterização variacional dá
\[
 \lim_{n\to\infty}\sigma_n^{1/(2n)}=0 .
\]
Para cada \(\varepsilon>0\), teste com o polinômio mônico que zera
nos finitíssimos pontos \(x_j>\varepsilon\), multiplicado por
\(x^{n-d}\), sendo \(d\) o número de pontos eliminados. No suporte
restante seu módulo é no máximo \(C_\varepsilon\varepsilon^{n-d}\).
Tomar a raiz e depois \(\varepsilon\downarrow0\) prova o limite.

Na base ortonormal \(P_n/\sqrt{\sigma_n}\), a multiplicação por
\(x\) é um operador compacto, pois na base atômica sua cauda
diagonal tem norma que tende a zero. Seus coeficientes de Jacobi
\(\alpha_n\) e \(\sqrt{\beta_n}\) tendem a zero. Para
\(z\notin\mathbb R\), a recorrência mônica e a compressão de Jacobi
\(J_n\) dão
\[
 \frac{P_{n+1}(z)}{P_n(z)}
  =z-\alpha_n-\beta_n\frac{P_{n-1}(z)}{P_n(z)}
   \longrightarrow z.
\]
O quociente \(P_{n-1}/P_n\) é o último elemento diagonal
de \((z-J_n)^{-1}\), pelo cofator e pela recorrência dos
determinantes. Seu módulo é limitado por \(1/|\Im z|\).
Em particular \(|P_n(z)|^{1/n}\to |z|\).

Fixe qualquer número \(m\) de pares removidos e
\(\lambda=\lambda_{m+1}\). Os zeros de \(P_n\) são os
autovalores de \(J_n\), que está no intervalo do suporte
\([0,R]\). Como \(\mathrm{tr}\,J_n\le\sum_j x_j\), o número
de zeros acima de \(\varepsilon\) está limitado
independentemente de \(n\). O produto sobre os zeros dá, para
todos \(k>m+1\),
\[
 |P_n(\lambda_k)|\le C_\varepsilon
                (|\lambda_{m+2}|+\varepsilon)^n.
\]
Com efeito, todos os fatores exceto um número limitado são
no máximo \(|\lambda_{m+2}|+\varepsilon\); os outros são
no máximo \(|\lambda_{m+2}|+R\). Escolha \(\varepsilon\)
para deixar \(|\lambda_{m+2}|+\varepsilon<|\lambda|\).
A contribuição inteira dos pares restantes então é
exponencialmente menor que
\(|\lambda|^{e+1}|P_n(\lambda)|^2\).

A fase levantada de \(\lambda^{e+1}P_n(\lambda)^2\) cresce
por incrementos que tendem a \(2\arg\lambda\in(0,\pi/2)\).
Ela alcança infinitos intervalos com cosseno ao menos
\(1/2\), e infinitos com cosseno no máximo \(-1/2\).
Cada um desses intervalos tem comprimento \(2\pi/3\),
maior que o passo em fase a partir de alguma ordem.
Nessas duas subsequências a cauda exponencialmente menor
preserva o sinal do primeiro par e a raiz de ordem \(2n\)
do módulo tende a \(|\lambda|\).

Em consequência, em cada setor e para todo \(m\) fixo,
\[
 \limsup_{n\to\infty}
       \frac{B_e^{>m}(P_n^2)}{\sigma_n}=+\infty,\qquad
 \liminf_{n\to\infty}
       \frac{B_e^{>m}(P_n^2)}{\sigma_n}=-\infty .
\]
Isso exclui uma cota relativa uniforme nas próprias
direções de Schur, mesmo depois de retirar qualquer número
fixo de pares. A demonstração usa a positividade em todas
as ordens como hipótese e o teste finito confirma a oscilação
de sinal em dimensões determinadas sem essa hipótese.

A identidade exata \(M_Y=M_B(F/F(1/2))^2\) permite cancelar
a câmera inteira antes da eliminação. Uma prova do sinal
completado precisaria controlar o quociente que resta.
A positividade em todas as ordens continua em aberto.

## Reprodução

Execute o script da seção 1 dentro de
\(\texttt{research/projective-chiral-complex-cauchy}\), ao lado
de \(\texttt{certify-radial-reduction-pivots.py}\).
A opção \(\texttt{--drop-pairs}\) retira os mesmos pares das
duas formas antes da comparação. O resultado assintótico
é uma demonstração analítica.
