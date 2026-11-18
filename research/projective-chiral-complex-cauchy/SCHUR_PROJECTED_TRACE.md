# O traço TFVD na direção que lê o próximo pivô

O primeiro objetivo desta rodada é testar a Gram de câmera na direção
que elimina **todos** os cruzamentos assinados. O segundo é localizar
na fonte uma desigualdade que baste para o sinal, inclusive na
possibilidade de um prefixo semidefinido ter núcleo.

## A mesma direção no traço e na malha bruta

Seja \(Q(t)=\mathcal P/2=A(t)^*A(t)-B(t)^*B(t)\) na normalização
nativa da [rodada anterior](SCHUR_RETURN_DECOUPLING.md). Fixe \(m\ge1\)
e use \(m+1\) amostras. Escreva \(C_{m+1}(t)=T_t^*Q(t)T_t\),
\(C_m(t)\) para seu bloco antigo e \(v_m(t)\) para a coluna de cruzamentos
com as antigas. Quando \(C_m=\lim C_m(t)\) é positivo definido, todos
os inversos usados abaixo existem eventualmente e convergem. Ponha
\[
\eta(t)=\binom{-C_m(t)^{-1}v_m(t)}{1},\qquad
x_m(t)=m!(\mathrm i t)^m T_t\eta(t).
\]
A transformação \(T_t\) é triangular e suas primeiras \(m\) colunas
geram exatamente o prefixo antigo. Logo \(Q(t)x_m(t)\) tem zero nas
primeiras \(m\) coordenadas, e \(x_m(t)\) tem última coordenada igual
a \(1\). Sua energia assinada é o Schur com a amostra nova fixa.
Em particular
\[
Q(t)[x_m(t)]=(m!)^2 t^{2m}
\bigl(C_{m+1}(t)_{mm}-v_m(t)^*C_m(t)^{-1}v_m(t)\bigr).
\]
Como \(\eta(t)\) converge, a coluna de ordem \(r<m\) em \(x_m(t)\) tem
fator \(t^{m-r}\). A última coluna dá
\[
x_m(t)\longrightarrow\beta,\qquad
\beta_j=(-1)^{m-j}\binom mj .
\]
\(\beta_m=1\) e \(\sum_j\beta_j=0\). O arquivo
`SchurProjectedTrace.lean` verifica a fatoração sem potências negativas
e esse limite da direção, para qualquer vetor confluente convergente
com última coordenada igual a um.

## Teste da Gram que vem da câmera

Use a decomposição original [\(\Pi+D=Q\)](../native-jet-overlap-budget/CONNECTED_DEFECT_RADIAL_LIMIT.md).
Nela \(\Pi=O\odot G\) é a Gram amortecida e \(D\) é o defeito conectado
do transporte bilinear Green. Na subsequência cofinal usada nessa
identidade, \(\Pi(t)\to A_0O\), onde \(A_0>0\) é a energia ambiente
no centro. O overlap \(O_{ij}=2\sqrt{(i+1)(j+1)}/(i+j+2)\) é a Gram
dos vetores \(\sqrt{2(j+1)}s^{j+1/2}\) em \(L^2[0,1]\). Esses
vetores são linearmente independentes, por independência dos monômios
após tirar o peso comum \(s^{1/2}\).
Assim, na própria direção Schur,
\[
\Pi(t)[x_m(t)]\to L_m=A_0\beta^*O\beta>0,\qquad
D(t)[x_m(t)]\to-L_m.
\]
Mais ainda, a diferença de proporções tem limite
\[
\lim\frac{1+D(t)[x_m(t)]/\Pi(t)[x_m(t)]}{t^{2m}}
 =\frac{(m!)^2\sigma_m}{L_m},
\qquad
\sigma_m=h_m-v_m^*C_m^{-1}v_m .
\]
A margem da Gram amortecida, se ela própria for ortogonalizada, também
tende a um número estritamente positivo. Com efeito, seu Schur converge
ao de \(A_0O\), que é positivo definido. Portanto tanto a avaliação na
direção Schur assinada quanto a projeção usando apenas \(\Pi\) retêm
uma margem de ordem constante. A margem que precisa ser certificada
está na diferença entre \(\Pi\) e a parcela que \(D\) cancela, na escala
\(t^{2m}\). Isso testa a Gram existente após a eliminação, além do teste
anterior com uma combinação balanceada fixa.

A assinatura física permite uma segunda leitura. Seus dois canais
satisfazem \(\sqrt t A(t)\to a_*V\) e \(\sqrt t B(t)\to b_*V\), com
\(|a_*|^2=|b_*|^2=1/4\), \(V e_j=s^{j+1/2}\). Esses são os fatores
do carrier Cauchy normalizado na [análise da métrica](SCHUR_NEGATIVE_CHANNEL_METRIC.md).
Como \(V\beta=s^{1/2}(s-1)^m\), as duas normas separadas obedecem a
\[
t\|A(t)x_m(t)\|^2,\quad t\|B(t)x_m(t)\|^2
 \longrightarrow \frac{1}{4(2m+1)(2m+2)}.
\]
Logo, em unidades da energia incidente, a primeira margem da assinatura é
\[
\lim\frac{\|A(t)x_m(t)\|^2-\|B(t)x_m(t)\|^2}
 {t^{2m+1}\|A(t)x_m(t)\|^2}
 =4(2m+1)(2m+2)(m!)^2\sigma_m .
\]
As duas leituras são para cada prefixo fixo. A primeira usa a
subsequência em que o overlap foi identificado. A segunda usa a malha
radial original. Nenhuma usa positividade do bloco novo.
A conferência numérica usou a característica completada na mesma malha
com 140 dígitos e nenhuma tabela de zeros. Para \(m=1,\ldots,8\),
\(t=10^{-6}\), os limites das normas reescaladas e da margem relativa
tiveram erro relativo inferior a \(1.5\cdot10^{-12}\).

## Qual teste de fonte bastaria no Gamma original

Em cada paridade \(s\in\{0,1\}\), escreva
\(M=(h_{i+j+s})_{i,j<n}\),
\(b=(h_{i+n+s})_{i<n}\) e \(d=h_{2n+s}\).
Use \(M\succeq0\) como hipótese indutiva e \(\lambda>0\).
Defina \(r_\lambda=-(M+\lambda I)^{-1}b\), \(y_\lambda=(r_\lambda,1)\).
Em dimensão \(2(n+1)\), injete \(y_\lambda\) no setor \(s\), com o outro
setor zerado, por `nativeSourceBoundaryFromParity`. Seja \(c_\lambda(k)\)
a aplicação de `nativeSourceChiralJetInput` a essa entrada
fixa. São as coordenadas do CSA, incluindo as fases originais.

O limite de `rawGamma_chiralJetInput_eventually_energy_control` e a
separação por paridade dão exatamente
\[
\lim_k\bigl(\|\texttt{gammaSourceSynthesis}(c_\lambda(k))\|^2
 -\Im\texttt{rawGammaWronskianBalance}(c_\lambda(k),c_\lambda(k))\bigr)
 +\lambda\|r_\lambda\|^2
 = d-b^\top(M+\lambda I)^{-1}b .
\]
O controle de erro mede quatro vezes a diferença entre norma e balanço.
O desdobramento do bordo também mede quatro vezes a forma de momentos
nesse setor. Os fatores se cancelam. A igualdade restante vem de
\((M+\lambda I)r_\lambda=-b\). O limite do Gamma vale para cada \(\lambda\)
fixo antes de \(\lambda\downarrow0\).

Se o lado esquerdo for não negativo ao longo de uma sequência positiva
\(\lambda\downarrow0\), o Schur com bloco antigo \(M+\lambda I\) prova
\[
\begin{pmatrix}M+\lambda I&b\\ b^\top&d\end{pmatrix}\succeq0
\]
completando o quadrado. O limite dá o bloco ampliado semidefinido.
A recíproca decorre somando a regularização positiva ao bloco
semidefinido e lendo o seu Schur. Assim é possível tentar uma
desigualdade de fonte numa entrada específica por paridade e parâmetro
de regularização, e fazer a indução mesmo se um pivô provisório zerar.
Com bloco antigo estrito, pode-se usar \(\lambda=0\) para testar o
pivô local. A desigualdade no Gamma continua uma hipótese.

Para passar da não negatividade em ambas as torres para positividade
estrita, a não recorrência nativa já foi provada no CSA. Um vetor nulo
num prefixo semidefinido tem cruzamento zero com todos os monômios de
prefixos maiores, por Cauchy–Schwarz. Isso daria uma recorrência linear
finita dos momentos, contradizendo a não recorrência. A versão formal
`canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg_of_harmonicNonrecurrence`
depende apenas da hipótese de sinal do bordo e dispensa entrada de dados
sobre zeros. [CSA #120](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/120)
· [Transporte do Gamma](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeChiralJetStorageTransport.lean)

O teste radial e a redução variacional no Gamma são analíticos. O lema
Lean deste checkpoint verifica o limite da direção em coordenadas
originais. Como controle finito já existente, os certificados de
fonte `even_source_six_posDef` e `odd_source_six_posDef` dão a
positividade de 12 fontes em `twelve_boundary_positive`, por caixas
e congruência da fonte original.
