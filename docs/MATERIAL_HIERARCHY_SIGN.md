# Sinal da hierarquia material: dois novos degraus e a obrigação em toda ordem

## Resultado

A positividade de toda a hierarquia **continua aberta**. Formalizamos os sinais
dos degraus 5 e 6 da fonte efetiva, ligamos cada degrau a uma integral theta
explícita com seus cruzamentos e demonstramos uma restrição em ordem arbitrária:
os coeficientes tendem a zero. Nenhuma margem positiva constante pode valer
para todas as ordens na normalização original.

Esse último resultado é compatível com todos os coeficientes serem positivos.
Não demonstra mudança de sinal, não decide a existência de uma vizinhança comum
de positividade e não estabelece um Gram positivo para o residual completo.

Base: `geometry-of-numbers` em `741fd2159a44d060a80240fbc1e9c967dcffb1a5`,
merge do PR #12; operador em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
Os demais commits, hashes e pins estão em
`research/material-hierarchy-sign/provenance.json`.

## 1. Qual escadaria está sendo estudada

Reutilizamos os PRs #1–#12. Para os momentos canônicos da **mesma resposta
material sintetizada**, escreva \(h_j=\texttt{canonicalCompletedNativeLogDerivativeMoment}\ j\)
e \(C_k=\texttt{carryMaterialNullCoefficient}\ k\). A calibração anterior prova

\[
C_{2p+1}=h_{2p+1},\qquad C_{2p}=h_{2p}-\frac{h_p^2}{h_0},\qquad h_0>0.
\]

Para cada família finita fixa de leituras reais, ponha \(M_j=\sum_i c_i a_i^j\).
O PR #12 prova, para cada \(k\ge1\),

\[
M_1=\cdots=M_{k-1}=0\quad\Longrightarrow\quad
E_R(\varepsilon)=\varepsilon^{2k}Q_k(\varepsilon),\qquad
Q_k(\varepsilon)\longrightarrow C_k M_k^2.
\]

O fator é exato numa vizinhança da origem, incluindo zero, e conserva o
residual completo, todos os pares ordenados e as diagonais. Não exige \(M_0=0\).
Se \(C_k>0\) e \(M_k\ne0\), a energia completa dessa família é positiva em
escala suficientemente pequena e não nula. A vizinhança pode depender da família.

A ordem \(k\) é de cancelamento/Taylor. Não é profundidade vertical, câmera
ou etapa da redução recíproca. Estes \(C_k\) também não são todos os pivôs
de Schur de uma matriz de Hankel.

## 2. Representação pela fonte theta, em toda ordem

O operador já fornece polinômios \(P_j\) pela recorrência da característica
original e o funcional

\[
I(P)=\int_0^\infty P(u)\Phi(u)\,du,\qquad I(P_j)=h_j.
\]

\(\Phi\) é `completedNativeXiCosineKernel`. Não escolhemos uma medida para
ajustar um Gram. A variável \(u\) não é identificada com tempo material,
profundidade ou altura. A nova definição é um ledger da fonte já sintetizada:

\[
\Pi_{2p+1}=P_{2p+1},\qquad
\boxed{\Pi_{2p}=P_{2p}-2\frac{h_p}{h_0}P_p+
                  \left(\frac{h_p}{h_0}\right)^2P_0.}
\]

O termo misto mantém os dois cruzamentos ordenados e o último mantém a
diagonal central. Lean prova, sem hipótese de sinal,

\[
\boxed{C_k=I(\Pi_k)\quad\text{para todo }k.}
\]

Não declaramos que \(\Pi_{2p}\) seja um quadrado pontual. O funcional \(I\)
não é multiplicativo; não se pode trocar o ledger pelo quadrado de um
polinômio em \(u\).

Reutilizando o fluxo Green e demonstrando os dois traços centrais nulos:

\[
C_k=\int_0^\infty\left(\Pi_k''-\frac14\Pi_k\right)(u)A(u)\,du,
\qquad A=\texttt{XiThetaCosine.thetaTail}.
\]

A API original controla o fluxo no infinito. A transferência conserva o
valor da integral; não fornece automaticamente seu sinal.

## 3. A desigualdade que falta para toda a hierarquia

As massas positivas e negativas existentes da mesma densidade fornecem

\[
C_k=M^+(\Pi_k)-M^-(\Pi_k),\qquad
\boxed{(\forall k\ge1,\ C_k>0)\iff
       (\forall k\ge1,\ M^-(\Pi_k)<M^+(\Pi_k)).}
\]

A equivalência está provada. A desigualdade à direita permanece aberta.
Ela é mais específica que a positividade de todos os blocos de Hankel.

Existe uma dificuldade concreta para uma prova por sinal pontual. Em toda
ordem ímpar, Lean verifica o coeficiente superior

\[
[u^{4p+4}]\Pi_{2p+1}=-\frac{2p+2}{c_0(4p+4)!}<0,
\quad c_0=\texttt{completedNativeRealEvenCharacteristicCoefficient}\ 0>0,
\]

e prova que \(\Pi_{2p+1}(u)\Phi(u)<0\) para \(u\) suficientemente grande.
Até os sinais ímpares conhecidos dependem de compensação integrada.
Isso obstrui apenas a leitura pontualmente positiva desta densidade;
não exclui outra identidade fiel que controle sua parte negativa.
Não construímos contramodelos com campos livres.

## 4. Dois novos sinais, com a fonte efetiva

Reutilizamos os certificados theta originais de seis e sete coordenadas:

\[
\texttt{nativeSourceSixOddBoundaryEnergy}(0,0,1)=2C_5>0,
\]

\[
\boxed{\texttt{nativeSourceSevenEvenBoundaryEnergy}
   \left(\frac{h_3}{h_0},0,0,1\right)
   =2\left(h_6-\frac{h_3^2}{h_0}\right)=2C_6>0.}
\]

O sinal positivo da primeira coordenada na segunda avaliação é imposto
pelos sinais alternados da forma de bordo. O cruzamento com a última
coordenada permanece explícito. Essas avaliações não constroem isometrias
entre carriers e não criam certificados numéricos adicionais.

Agora há um teorema \(C_k>0\) para \(1\le k\le6\), sem premissa extra
de positividade. A positividade da energia residual segue para cada família
fixa com os cancelamentos e momento sobrevivente exigidos.

| Ordem | Coeficientes nas posições \(1,\ldots,k\) | Momento sobrevivente | Limite de \(Q_k\) |
|---|---|---|---|
| 5 | \((5,-10,10,-5,1)\) | \(M_5=120\) | \(14400C_5\) |
| 6 | \((-6,15,-20,15,-6,1)\) | \(M_6=720\) | \(518400C_6\) |

Essas regressões reais usam \(M_0=1\) e \(M_0=-1\), respectivamente.
A primeira ordem sem sinal descarregado nesta investigação é \(C_7=h_7\),
ou seja, a desigualdade integrada para \(\Pi_7=P_7\). Certificar apenas
esse sinal não resolveria todas as ordens. O módulo de oito coordenadas
do operador conserva seu novo discriminante como condição explícita;
não o usamos como certificado de sinal.

## 5. Um resultado incondicional para toda ordem

A cota original dos momentos, sem premissa de sinal, é

\[
|h_j|\le\rho^{j+1}-(1/25)^{j+1},\qquad\rho=22/175<1.
\]

Lean verifica, na normalização preservada,

\[
\boxed{|C_k|\le\left(1+\frac{\rho}{h_0}\right)\rho^{k+1}
       \quad\text{para todo }k,}
\]

\[
\boxed{C_k\longrightarrow0,\qquad
       \neg\exists\delta>0\ \forall k\ge1:\delta\le C_k.}
\]

No caso par, o argumento usa \(h_p^2\le\rho^{2p+2}\), conservando a
correção central. A cota é superior em módulo: não fornece o sinal nem
a cota inferior ausente. Uma prova positiva em toda ordem precisará
permitir margens dependentes da ordem. Não renormalizamos estados para
esconder esse decaimento.

## 6. Status

| Afirmação | Status |
|---|---|
| Integral theta literal de cada \(C_k\), com cruzamentos | **PROVADO em Lean** |
| Transferência Green com traços e fluxo controlados | **PROVADO em Lean** |
| Critério de dominação para todas as ordens | **PROVADO como equivalência** |
| \(C_1,\ldots,C_6>0\) e positividade radial por família fixa | **PROVADO em Lean** |
| Cota exponencial, limite zero, ausência de piso positivo constante | **PROVADO em Lean** |
| Positividade em qualquer ordem mediante dominação theta | **CONDICIONAL à desigualdade explícita** |
| Densidade theta ímpar pontualmente não negativa | **OBSTRUÍDO nesta representação** |
| Dominação integrada em toda ordem, inclusive \(C_7>0\) | **ABERTO nesta investigação** |
| Gram positivo do residual em uma vizinhança comum | **ABERTO; não decorre dos testes radiais** |
| Isometria física com o carrier canônico, HP/RH | **NÃO DEMONSTRADO por estes resultados** |

O alvo estrutural é controlar \(M^-(\Pi_k)\) por \(M^+(\Pi_k)\) com uma
margem que pode decair. Recorrência, peso positivo e cota absoluta, por
si sós, não descarregam essa obrigação nos resultados disponíveis.
Ela não foi escondida num campo de certificado assumindo o sinal desejado.

## 7. Código, validação e proveniência

Os resultados estão no namespace `CarryMaterialHierarchySignComparison`,
em `research/material-central-calibration/CanonicalComparison.lean`.
Há uma definição e 23 teoremas públicos novos. O prefixo anterior do arquivo
foi preservado literalmente após dois imports. A biblioteca padrão não
ganhou dependência do operador.

O build completo da biblioteca e a verificação desse arquivo são comandos
distintos: o build padrão não compila o arquivo externo de pesquisa. O
script dedicado verifica-o com `warningAsError`, guardas transitivas de
axiomas nos tipos e corpos e `#print axioms` para cada raiz nova. Só são
permitidos `propext`, `Classical.choice` e `Quot.sound` na análise.
Foundation e Geometry mantêm suas auditorias e políticas próprias.

As evidências estão em `research/material-hierarchy-sign/`. Regressões
preservam 72, relógio, duas quadraturas, TFVD/Green e retorno; incluem as
diferenças finitas acima e \(C_7=h_7\) sem atribuir seu sinal.

Origem dos resultados reutilizados no operador:

| Módulo | Último commit de proveniência |
|---|---|
| `NativeSourceThetaMomentPolynomials` | `ca7d7cc71cff2fb15f3e94f97d2bed0362e3ba43` |
| `NativeSourceSchurThetaMasses` | `ca7d7cc71cff2fb15f3e94f97d2bed0362e3ba43` |
| `CompletedNativeChiralReturnFourteenthSourceIntegral` | `f46bc2277736c368b53570c1da31f1546f07aa5a` |
| `CompletedNativeLogCoefficientMajorant` | `96ae105a14f522fd59a21d3ea7190255fa0c24b4` |

Os hashes e os demais módulos efetivamente usados estão no inventário.
Não foram modificados fonte, métrica, amplitudes, parâmetros, operadores,
pins ou normalizações. Os arquivos não rastreados e as worktrees anteriores
foram preservados. Nenhum experimento numérico novo substituiu prova.
