# Preservação da derivada central sob redução recíproca

A redução escalar da [lei dos pivôs radiais](RADIAL_SCHUR_PIVOT_LAW.md)
preserva a realização por um resolvente positivo. Para a fonte completada,
basta provar a semidefinitude positiva de cada bloco Hankel não deslocado.
O setor deslocado e a estriteza seguem de propriedades analíticas da mesma
característica. O sinal do bloco não deslocado em ordem arbitrária continua
sendo a obrigação de fonte.

## 1. O passo que se repete

Sejam \(B:\mathcal H\to\mathcal K\) limitado, \(T=B^*B\) e \(v\ne0\). Escreva
\[
f(u)=\langle v,(I-uT)^{-1}v\rangle,\qquad
a=f(0)=\|v\|^2,\qquad P_v=I-\frac{vv^*}{a}.
\]
Use o produto interno com a variável linear no segundo argumento.
Defina \(B_+=P_vB^*\), \(T_+=B_+^*B_+=BP_vB^*\) e \(v_+=Bv/a\).
Então, como identidade de germes,
\[
f_+(u)=\frac{1/a-1/f(u)}{u}
      =\langle v_+,(I-uT_+)^{-1}v_+\rangle.
\]
Em particular,
\[
f_+'(0)=\|B_+v_+\|^2
       =\frac{\|P_vTv\|^2}{a^2}.
\]

Para verificar a identidade, use \(x=(I-uT)^{-1}v\), \(w=Bv\) e
\(y=(I-uT_+)^{-1}w\). A equação de \(x\), contraída com \(v\), dá
\(f-a=u\langle w,Bx\rangle\). Aplicar \(B\) à mesma equação e acrescentar
o termo de posto um dá
\[
(I-uT_+)Bx=w+\frac{u}{a}w\langle w,Bx\rangle=(f/a)w.
\]
Assim \(Bx=(f/a)y\) e \((1/a-1/f)/u=\langle w,y\rangle/a^2\).
A derivada vem do termo linear da série do resolvente. Todas as inversas
existem numa vizinhança de zero pela série de Neumann e \(a>0\).

Se \(f'(0)=0\), então \(Bv=0\), \(Tv=0\) e \(f\) é constante.
Se \(f_+\) é racional, \(f=a/(1-ua f_+)\) é racional. A redução preserva
a não racionalidade de \(f\), a positividade do resolvente e a existência
de uma nova massa positiva \(a_+=f'(0)>0\). Por indução, uma realização
positiva inicial com \(f_0\) não racional dá \(f_r'(0)>0\) para todo \(r\).

O módulo `PositiveResolventReduction.lean` verifica a projeção, a identidade
dos sistemas lineares finitos, a nova fatoração Gram e o critério de
estriteza. O argumento de germes em Hilbert e a indução acima são analíticos.

## 2. A hipótese de fonte que resta

Os \(h_j\) continuam vindo do bracket, da síntese Genuine e do completamento
nativo. O passo a seguir usa a igualdade analítica já disponível para o
completamento em um entorno do centro. O CSA prova essa identificação em
`completedNativeOperatorCharacteristic_eq_completedRiemannZeta` e
`nativeXiCompletionFactor_mul_riemannZeta_eq_regularizedCompleted`.
[Identificação nativa](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/NativeScalarZetaIdentification.lean)
· [Regularização](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedGreenJetCoefficientRecurrence.lean)

Seja \(F_{\rm ext}(z)=\xi(1/2+iz)\) a continuação inteira regularizada do
germ completado. Ela é par, então \(F_{\rm ext}(z)=W(z^2)\) com \(W\) inteira.
Pela normalização \(-F'/2F=zH(z^2)\),
\[
H(u)=-W'(u)/W(u),\qquad f_0=2H.
\]
Para \(r\ge0\), \(W(-r^2)=\xi(1/2+r)>0\). Para \(1/2\le x<1\), a série
alternada pareada prova que \(\eta(x)>0\) e \(\zeta(x)<0\). O fator
\(x(x-1)\) restaura o sinal positivo. Para \(x>1\), os fatores do
completamento são positivos. Em \(x=1\), o valor regularizado é \(1/2\).
Isso deixa \(H\) holomorfa em uma vizinhança de cada ponto real
negativo. [DLMF, série alternada e valor polar](https://dlmf.nist.gov/25.2)
· [Reflexão do completamento](https://dlmf.nist.gov/25.4)

Suponha agora \(H_N=(h_{i+j})_{i,j<N}\succeq 0\) para cada \(N\).
Hamburger fornece \(\mu\ge0\) em \(\mathbb R\) com
\(h_j=\int x^j\,d\mu(x)\). Como \(H\) é analítica no centro, para algum
\(\rho>0\) e \(C\) vale \(|h_{2j}|\le C\rho^{-2j}\). Para todo
\(b>1/\rho\),
\[
\mu(|x|\ge b)\le \frac{h_{2j}}{b^{2j}}\le C(\rho b)^{-2j}\to0.
\]
Portanto \(\mu\) tem suporte compacto. [Teorema de Hamburger](https://www.imath.kiev.ua/~golub/ref2/The-Moment-Problem.pdf)

Por expansão perto do infinito,
\[
\int\frac{d\mu(x)}{w-x}=\frac{H(1/w)}{w}.
\]
A identidade continua meromorficamente em ambos os semiplanos. O lado
esquerdo é holomorfo neles, e o lado direito também é holomorfo em uma
vizinhança de cada \(w<0\). Pela inversão de Cauchy–Stieltjes, o suporte de
\(\mu\) fica em \([0,\rho^{-1}]\). Em particular
\(K_N=(h_{i+j+1})_{i,j<N}\succeq0\) e \(f_0\) tem a realização positiva
com \(T\) dado pela multiplicação por \(x\) em \(L^2(\mu)\) e \(v=\sqrt2\).
[Inversão e suporte](https://www.mathsoc.jp/publication/JMSJ/pdf/JMSJ9325.pdf#page=17)

A não racionalidade nessa realização pode ser fechada pela cauda real.
A função digama satisfaz \(\psi(x/2)=\log(x/2)+o(1)\) para \(x\to+\infty\).
Pela série de Dirichlet absolutamente convergente, \(\zeta'/\zeta=o(1)\).
A derivada logarítmica da expressão completada dá, para \(r\to+\infty\),
\[
f_0(-r^2)=\frac{\xi'(1/2+r)}{r\,\xi(1/2+r)}
          \sim\frac{\log r}{2r}.
\]
Um germ racional, se coincidisse com \(f_0\), teria uma potência inteira
de \(u\) como ordem dominante no infinito. A assintótica acima é
incompatível com isso. [DLMF, assintótica da digama](https://dlmf.nist.gov/5.11.E2)

Reciprocamente, \(f_0(0)>0\) e \(f_r'(0)>0\) para todo \(r\) dão
\(a_{r+1}=f_r'(0)/a_r^2>0\). A identidade da rodada anterior
\(2\Delta_{r+1}/\Delta_r=a_r\prod_{j<r}a_j^2\) força cada determinante de
prefixo nos dois setores a ser positivo. Em particular,
\[
\big[\forall N,\ H_N\succeq0\big]\quad\Longleftrightarrow\quad
\big[\forall r,\ f_r'(0)>0\big].
\]
Aqui a caracterização usa o completamento regularizado e a cauda real.
A demonstração analítica acima usa a caracterização de Hamburger e a
inversão de Cauchy–Stieltjes. Ela ainda não está em Lean.

## 3. Controle contra uma inferência só por sinais escalares

Com \(\lambda=1/2+(3/5)i\), tome a característica reduzida
\[
W_*(u)=(1-u)(1-\lambda u)(1-\bar\lambda u)
                   \prod_{m=1}^\infty(1-u/(100\,2^m)).
\]
O produto converge localmente uniformemente, \(W_*\) é positiva no eixo
real negativo e \(F_*(z)=W_*(z^2)\) tem infinitos zeros reais.
Os coeficientes de \(-W_*'/W_*\) são
\[
h_j^*=1+2\Re(\lambda^{j+1})+
       \frac{100^{-(j+1)}}{2^{j+1}-1}.
\]
São todos positivos. Para \(j\ge3\), basta
\(2|\lambda|^4=2(61/100)^2<1\) e os três primeiros são
\(201/100\), \(23401/30000\) e \(1190001/7000000\).
Contudo,
\[
h_0^*h_2^*-(h_1^*)^2=-840267899/3150000000<0.
\]
Portanto \(f_{0,*}'(0)>0\) e \(f_{1,*}'(0)=-840267899/51159786300<0\)
para \(f_{0,*}=-2W_*'/W_*\). Os sinais escalares e a infinitude de zeros
reais, juntos, ainda deixam livre o cruzamento que a forma
\(L(p^2)=\sum_{i,j}p_i p_j h_{i+j}\) precisa controlar na fonte C2.

## 4. Certificados finitos pelo completamento identificado

Na base GoN consultada, `even_source_seven_posDef` e
`odd_source_six_posDef` certificam \(H_7\) e \(K_6\). A identidade de
pivôs dá \(f_r'(0)>0\) para \(0\le r\le11\) a partir desses resultados.
A frente seguinte tem a equivalência formal para \(K_7\), isolada em
[`K7PivotBridge.lean`](https://github.com/thiagomassensini/geometry-of-numbers/blob/b6e5d07/research/seventh-odd-canonical-source/K7PivotBridge.lean).

O programa `certify-radial-reduction-pivots.py` usa python-flint 0.8.0.
A série de \(-F'/2F\) é avaliada pela expressão completada que coincide
com a fonte nativa no centro. Só se aceitam pivôs cujo intervalo inteiro
esteja acima de zero. Os primeiros coeficientes coincidem com os canônicos
da rodada anterior. Nenhum zero entra na avaliação. O certificado é
intervalar, com a aritmética de inclusão da FLINT, e é independente de
uma formalização Lean dos limites numéricos. [FLINT](https://flintlib.org/doc/guide/types/ball-arithmetic.html)

Em particular, o pivô \(K_7/K_6\) ficou em
\([1.397873288605521\times10^{-43}\ \pm 4.31\times10^{-59}]\) e a derivada
\(f_{12}'(0)\) em \([1.197656854246802\times10^{-5}\ \pm 6.99\times10^{-23}]\).
A execução de tamanho 128 e 16.384 bits certificou \(H_N\succ0\) e
\(K_N\succ0\) para \(1\le N\le128\), logo \(f_r'(0)>0\) para
\(0\le r\le254\). Os últimos pivôs dos setores \(H\) e \(K\) ficaram,
respectivamente, em \([2.568520175523391\times10^{-1162}\ \pm 2.60\times10^{-1178}]\)
e \([1.907725832180484\times10^{-1167}\ \pm 1.76\times10^{-1183}]\).
A última derivada ficou em \([9.902682989575850\times10^{-8}\ \pm 3.80\times10^{-24}]\).

Execute a partir de um checkout da branch desta rodada.

```bash
python3 research/projective-chiral-complex-cauchy/certify-radial-reduction-pivots.py --size 128 --bits 16384
gon=$(pwd)
(cd /home/thlinux/carry-self-adjoint-operator && \
  lake env lean -DwarningAsError=true "$gon/research/projective-chiral-complex-cauchy/PositiveResolventReduction.lean")
```

Para o comando Lean, use o mesmo ambiente Lean 4.32 da VM. A auditoria do
módulo tem apenas `propext`, `Classical.choice` e `Quot.sound`.
