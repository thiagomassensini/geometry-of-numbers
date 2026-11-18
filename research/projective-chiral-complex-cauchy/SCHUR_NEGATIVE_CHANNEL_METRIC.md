# A métrica do canal negativo após o Schur

A análise parte do pareamento quiral completado que permanece quando a
fibra cancela a Gram no orçamento TFVD/Green. Em uma família finita
regular, o pareamento \(\mathcal P/2\) é a diferença \(A^*A-B^*B\) das
duas sínteses Cauchy quirais com sua normalização nativa. A passagem a
esse carrier usa as identidades já provadas. [Defeito TFVD](../native-jet-overlap-budget/CONNECTED_DEFECT_RADIAL_LIMIT.md)
· [Formas quirais do CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeProjectiveChiralCarrier.lean)

## A eliminação muda o custo do retorno

Sejam \(A_0,B_0\) os canais das direções antigas e \(A_1,B_1\) os canais
das novas. O único sinal usado é o do prefixo já eliminado,
\(P=A_0^*A_0-B_0^*B_0\succ0\).
Ponha \(G=A_0^*A_0\) e
\[
L=G^{-1}A_0^*A_1,\qquad
A_\perp=A_1-A_0L,\qquad B_\perp=B_1-B_0L .
\]
Como \(G=P+B_0^*B_0\succ0\), essa projeção é legítima. A mesma
subtração é feita nos dois canais, e o bloco de cruzamento assinado
vira \(-B_0^*B_\perp\), pois \(A_0^*A_\perp=0\). O Schur verdadeiro
é invariante por essa mudança triangular e fica
\[
S=A_\perp^*A_\perp-B_\perp^*M B_\perp,\qquad
M=I+B_0P^{-1}B_0^*
 =(I-B_0G^{-1}B_0^*)^{-1}.
\]
A segunda expressão vem de Woodbury. Em uma direção \(x\),
\[
\langle x,Sx\rangle=\|A_\perp x\|^2
 -\|B_\perp x\|^2
 -\|P^{-1/2}B_0^*B_\perp x\|^2.
\]
O último quadrado mede o cruzamento do retorno novo com o retorno
antigo. O operador \(M\) age como a identidade no ortogonal à imagem
de \(B_0\). Esse cruzamento dá a localização exata do custo extra.

Uma conservação que provaria o sinal teria a forma polarizada
\[
A_\perp^*A_\perp
 = B_\perp^*B_\perp+
   (P^{-1/2} B_0^* B_\perp)^*(P^{-1/2} B_0^* B_\perp)
   +\mathcal L^*\mathcal L .
\]
O mapa \(\mathcal L\) precisaria ser identificado no transporte da
fonte e servir às sucessivas eliminações. A fatoração formal de um
\(S\) já não negativo recuperaria a mesma equação com \(\mathcal L=S^{1/2}\).
Assim o conteúdo a demonstrar é um canal obtido independentemente do
sinal do novo bloco.

### Controle finito no Cauchy original

Os vetores dos dois primeiros pontos têm Gram
\(\begin{psmallmatrix}1/2&1/3\\1/3&1/4\end{psmallmatrix}\) para \(t=1\).
Use os multiplicadores sintéticos \(3/4,1/2\), aplicados a esses mesmos
vetores. A projeção pelo positivo dá
\[
\|a_\perp\|^2=1/36,\qquad \|b_\perp\|^2=1/48,\qquad
\frac{|\langle b_0,b_\perp\rangle|^2}{P}=1/56 .
\]
A margem sem o cruzamento é \(1/144>0\) e a margem do Schur é
\(-11/1008<0\). A mesma comparação vale com os dois multiplicadores
trocados de sinal simultaneamente. Isso testa a suficiência da
dominação ordinária dos canais, usando a geometria Cauchy original.

## O custo cresce na malha física

Na âncora, o retorno é \(q(z_0)\) vezes o incidente. Na direção da
âncora o autovalor de \(M\) é exatamente \(1/d\), com
\(d=1-|q(z_0)|^2\). O limite já conhecido \(d/t\to8h_0\), para
\(t=(k+1)^{-1}\), dá \(t\|M\|\to1/(8h_0)\).
O módulo `NativeAnchorNegativeGain.lean` verifica a expressão
escalar e seu limite no carrier nativo.

Para um prefixo fixo de \(m\ge1\) pontos radiais, seja \(Q_m(t)\) a
matriz \(\mathcal P/2\) depois de absorver a amplitude positiva
Hermite–Biehler nas entradas. Use os canais \(A_m,B_m\) nessa
normalização, de modo que \(Q_m=A_m^*A_m-B_m^*B_m\).
Seja \(T_t\) a matriz de diferenças divididas original. O limite
confluente já provado fornece
\[
C_m(t)=T_t^*Q_m(t)T_t\longrightarrow C_m ,
\]
onde \(C_m\) é a matriz confluente de coeficientes de momentos que
separa os dois setores. A afirmação abaixo usa \(C_m\succ0\) apenas
para esse prefixo. [Lei radial anterior](RADIAL_SCHUR_PIVOT_LAW.md)

Escreva \(r=m-1\). A última coluna tem a forma
\(T_te_r=t^{-r}\beta_r\), com
\((\beta_r)_j=(-1)^{r-j}\binom rj/(r!\,i^r)\), \(0\le j\le r\).
A Cauchy original tem vetores
\(t^{-1/2}v_j\), \(v_j(x)=x^{j+1/2}\) em \(L^2([0,1])\).
Com \(V_m e_j=v_j\), o limite de \(\sqrt t B_m(t)\) é
\(b_*V_m\), onde \(|b_*|^2=1/4\). Esse fator vem da
amplitude Hermite–Biehler normalizada no centro, do fator
\(1/\sqrt2\) do pareamento e de \(|q(0)|=1\).
[Normalização e vetores Cauchy](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean)

A identidade \(Q_m(t)^{-1}=T_t C_m(t)^{-1}T_t^*\) mostra em norma
de operadores que
\[
 t^{2m-1} M_m(t)\ \longrightarrow\
 \frac{(C_m^{-1})_{rr}}4(V_m\beta_r)(V_m\beta_r)^*.
\]
De fato, \(t^rT_t\to\beta_re_r^*\) e
\(C_m(t)^{-1}\to C_m^{-1}\).
A norma de \(V_m\beta_r\) ao quadrado é
\(1/((r!)^2(2r+1)(2r+2))\), pela integral
\(\int_0^1x(1-x)^{2r}\,dx\).
Assim, com \(p_r>0\) o último pivô de \(C_m\),
\[
\boxed{\displaystyle
 \lim_{t\to0}t^{2m-1}\|M_m(t)\|
 =\frac{1}{4(r!)^2(2r+1)(2r+2)p_r}.}
\]
O crescimento é direcional. A direção limite é a última diferença
da família antiga, em vez de um custo uniforme em todo o retorno.
O argumento de ordem arbitrária acima é analítico. Um teste
multiprecisão com a expressão completada, para \(m=1,2,3,4\)
e \(t=10^{-5}\), reproduziu cada constante com erro relativo
inferior a \(10^{-6}\). O teste não entra na demonstração.

## O que uma conservação da fonte precisaria controlar

Há também uma forma exata que evita a métrica de ganho grande.
O custo suplementar na direção \(b=B_\perp x\) é
\[
 \langle T_t^*B_m^* b,\ C_m(t)^{-1} T_t^*B_m^* b\rangle .
\]
Em particular, a não negatividade do Schur força
\[
 |\langle \sqrt t B_m\beta_r,b\rangle|
 \le \sqrt{(C_m(t))_{rr}}\,t^{m-1/2}\|A_\perp x\|.
\]
A escala vem da última coluna \(T_te_r\) e da desigualdade de
Cauchy–Schwarz na métrica \(C_m(t)\). É uma condição necessária,
enquanto a equação polarizada com \(\mathcal L\) controlaria todos
os cruzamentos de uma só vez. A fonte TFVD/Green ainda precisa
fornecer essa identidade ou uma estimativa suficiente na mesma
normalização. A auditoria anterior já exclui a componente ambiente
literal e o candidato coisométrico causal a parâmetro fixo como canais
de perda para esse fim. [Auditoria de dilatação no CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeProjectiveChiralLosslessDilationAudit.lean) O módulo `SchurNegativeChannelMetric.lean` prova a
álgebra finita do Schur, a invariância, Woodbury e o sinal da
correção sob o prefixo positivo.
