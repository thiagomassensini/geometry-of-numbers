# Da quantidade à normalização do prefixo residual

## Escopo e modo de leitura

A pergunta fundacional é o que uma representação pode esquecer localmente
sem que uma representação fiel perca a distinção global entre quantidades.
Não começamos com uma base, uma expansão em dígitos ou uma medida. Começamos
com uma trajetória de passos unitários e um observador local.

Este texto acompanha os resultados já compilados nesta árvore. Distingue
entradas, construções e consequências. Todos os resultados fundacionais
citados são verificados pelo kernel com lista de axiomas vazia. Isso não
significa ausência de hipóteses: finitude apresentada, autonomia e injetividade
são entradas explícitas. Na última etapa entra também um princípio explícito
de neutralidade da normalização por contagem.

## 1. Quantidade, passos e representação fiel

Seja `Q` um tipo de quantidades. Não supomos adição, multiplicação ou ordem
em `Q`. Uma trajetória é uma família `xₙ` acompanhada de uma transição `T`:

\[
x_{n+1}=T(x_n).
\]

O natural `n` conta passos externos. A trajetória é injetiva: passos distintos
correspondem a quantidades distintas. Esses dados são a entrada
`UnitTrajectory`; não são deduzidos da finitude local.

Uma representação fiel `e` satisfaz

\[
e(a)=e(c)\Longrightarrow a=c.
\]

Se a representação se separa em dois canais, `e(a)=(local(a), extension(a))`,
duas quantidades distintas com o mesmo canal local devem ter extensões
distintas. Caso contrário, os pares seriam iguais, contrariando a fidelidade.
Esse é o conteúdo de `sameLocal_forces_extension_difference`.

Isso prova preservação de distinção, não uma identificação da extensão com
um contador particular. A composição de codificações fiéis continua fiel
(`faithfulRepresentation_comp`). O próximo problema é descobrir quando
ocorre uma coincidência local.

## 2. Finitude local apresentada e recorrência

Um observador envia cada quantidade a um estado local. Sua finitude é dada
por uma codificação injetiva explícita dos estados locais em `Fin N`.
`FiniteLocalPresentation` guarda essa apresentação; não escolhemos uma
enumeração a partir de uma mera afirmação abstrata de finitude.

Observamos `x₀,…,x_N`: são `N+1` observações com apenas `N` códigos
disponíveis. Uma prova combinatória por indução produz

\[
0\le m<n\le N,\qquad observe(x_m)=observe(x_n).
\]

`finiteCodeCollision` e `unitTrajectory_forces_localRecurrence` certificam
essa colisão. Ela não identifica as quantidades: a trajetória permanece
injetiva. Com uma representação global fiel alinhada ao observador, a
distinção fica necessariamente na extensão.

Ainda não temos retorno à observação inicial. Uma colisão entre dois tempos
não implica isso sem uma hipótese sobre a evolução local.

## 3. Autonomia, retorno positivo e capacidade emergente

Recebemos uma evolução local `S` que é autônoma e injetiva:

\[
observe(T(x))=S(observe(x)).
\]

Autonomia propaga coincidências. Injetividade permite cancelar os primeiros
`m` passos de uma colisão e obter um retorno positivo à observação inicial.
`autonomousLocalDynamics_has_positiveReturn` produz um tempo de retorno
positivo limitado por `N`.

Uma busca limitada encontra o menor retorno positivo, chamado `b`:

\[
observe(x_b)=observe(x_0),\qquad b>0,
\]

e nenhum retorno positivo ocorre antes dele. A especificação
`EmergentLocalCapacity` registra essa minimalidade, enquanto
`existsUnique_emergentLocalCapacity` prova sua existência e unicidade.
Não introduzimos uma base previamente escolhida para produzir esse retorno.

Se o primeiro passo altera a observação, `b` não pode ser `1`; então

\[
1<b\le N.
\]

Esse reforço usa explicitamente a não trivialidade do primeiro passo.
Uma observação constante admite capacidade `1`. O orçamento `N` dos códigos
e a capacidade emergente `b` não são identificados.

## 4. Ciclos e resíduos por evolução unitária

Dado `b>0`, construímos coordenadas `(c,r)` a partir de `(0,0)` pela regra

\[
(c,r)\longmapsto
\begin{cases}
(c,r+1),&r+1<b,\\
(c+1,0),&r+1=b.
\end{cases}
\]

É uma definição recursiva por passos. Não calculamos divisão ou resto para
depois atribuir-lhes uma interpretação dinâmica.

Por indução, a construção satisfaz

\[
n=c_b(n)b+r_b(n),\qquad r_b(n)<b.
\]

`cycleCoordinatesRec_spec` prova conservação e limite. A prova de
`cycleDecomposition_unique` mostra que dois pares limitados reconstruindo
o mesmo `n` coincidem. Portanto não há uma segunda escolha de coordenadas
que satisfaça a mesma especificação.

No regime interior apenas o resíduo cresce. Na fronteira, o resíduo zera e
o contador aumenta uma unidade. Esses regimes são exaustivos e exclusivos
nos estados construídos (`cycle_step_dichotomy`). O primeiro ciclo completo
tem coordenadas `(1,0)` (`firstSaturation_coordinates`).

## 5. Reset local sem perda global

O retorno inicial se propaga para todo tempo:

\[
observe(x_{n+b})=observe(x_n).
\]

Usando essa periodicidade e a conservação das coordenadas, provamos

\[
observe(x_n)=observe(x_{r_b(n)}).
\]

Pela minimalidade de `b`, um resíduo estritamente entre `0` e `b` não retorna
à observação inicial. Assim,

\[
observe(x_n)=observe(x_0)\quad\Longleftrightarrow\quad r_b(n)=0.
\]

São os teoremas `cycleResidual_controls_localReadout` e
`localReturn_iff_cycleResidual_zero`. O resíduo construído mede a posição
no ciclo do mesmo observador que produziu `b`.

Entretanto, `x_n` e `x_{n+b}` são quantidades distintas. A extensão de uma
representação global fiel deve distingui-las
(`cycle_reset_forces_extension_difference`). O reset não destrói informação
global. Isso não demonstra que uma extensão arbitrária seja literalmente
`c_b(n)`: o contador é uma coordenada canônica construída, não a definição
retroativa daquele canal.

## 6. Torre residual e profundidade

O contador de ciclos é um natural. Podemos aplicar a ele a mesma regra,
sem postular uma nova dinâmica para a extensão abstrata. Repetindo a operação
`k` vezes, obtemos

\[
(r_0,r_1,\ldots,r_{k-1},q_k).
\]

Em profundidade zero permanece apenas `n`. No próximo nível extraímos
`r_b(n)` e construímos a torre do contador `c_b(n)`. Essa é a definição de
`emergentResidualTower`. A profundidade é o número de canais residuais
resolvidos; a cauda `q_k` permanece explícita e ilimitada.

Todos os resíduos ficam abaixo de `b`. Reinserindo-os na ordem inversa,
reconstruímos exatamente `n`. Duas torres limitadas que reconstruam o mesmo
valor são iguais. Construir mais níveis e recompô-los na cauda inferior
devolve a torre menos profunda. Essas propriedades são, respectivamente,
limite, reconstrução, unicidade e coerência por truncamento.

Ainda não afirmamos que a cauda termina para todo `n` quando `b>1`.
Para `b=1`, uma cauda não nula pode permanecer para sempre.

## 7. A escala acumulada nasce da reconstrução

A definição da torre não usa potências. Depois dela, a reconstrução prova

\[
n=P_k(r_0,\ldots,r_{k-1})+q_k b^k,
\]

onde

\[
P_k=r_0+b r_1+\cdots+b^{k-1}r_{k-1}.
\]

`emergentResidualTower_expansion` é consequência da aplicação repetida da
mesma reconstrução de uma célula. `b^k` aparece como escala da cauda, não
como uma hipótese que define a torre. Essa escala permitirá delimitar
o prefixo independentemente da informação ainda não resolvida.

## 8. Prefixo resolvido e capacidade exata

O carrier da torre completa não é finito: guarda uma cauda natural. Para
contar somente os estados resolvidos, definimos outro tipo:

\[
ResidualPrefix(b,0)=\{\ast\},\qquad
ResidualPrefix(b,k+1)=Fin(b)\times ResidualPrefix(b,k).
\]

Cada coordenada é limitada, e a primeira é `r₀`. O tipo não menciona `b^k`.
Sua avaliação é a reconstrução da torre existente com cauda zero.

Por indução, todo prefixo tem valor menor que `b^k`. Reciprocamente, se
`n<b^k`, a reconstrução da torre força `q_k=0`: uma cauda positiva já
contribuiria pelo menos `b^k`. Extraímos então o prefixo da torre canônica.

A avaliação e essa extração são inversas. Uma direção usa reconstrução;
a outra, unicidade da torre. Temos assim uma bijeção explícita

\[
ResidualPrefix(b,k)\longleftrightarrow Fin(b^k),\qquad b>0.
\]

`residualPrefixEquivFin` guarda os mapas e ambas as inversas;
`residualPrefix_cardinality` prova uma codificação fiel e sobrejetiva.
Logo há exatamente `b^k` estados prefixais. Isso não conta a torre inteira.
Em profundidade zero há um prefixo vazio; em capacidade `1` há um único
prefixo em qualquer profundidade.

## 9. O limite lógico da cardinalidade

Cardinalidade não escolhe uma medida. Mesmo em dois estados, os pesos
`(1,0)` têm total positivo e são desiguais. O theorem
`finiteCapacity_does_not_force_uniformity` fornece esse contraexemplo formal.

Além disso, a dinâmica distingue um estado inicial, e a reconstrução atribui
valores diferentes a diferentes prefixos. Não seria correto dizer que toda
permutação preserva esses objetos.

Por isso a próxima camada não deriva uma medida privilegiada de toda a
estrutura dinâmica. Ela constrói a **normalização por contagem dos estados
resolvidos**, que deliberadamente não usa sua identidade ou seu valor para
escolher privilégios. Essa passagem contém um princípio novo e explícito.

## 10. Neutralidade dos rótulos e igualdade de cotas

Uma relabeling é uma mudança reversível dos nomes dos estados. A exigência
da normalização por contagem é que seu peso permaneça igual após qualquer
dessas mudanças:

\[
w(\pi(x))=w(x)\qquad\text{para toda permutação }\pi.
\]

`RelabelingInvariant` expressa esse princípio. É mais forte do que mudar
simultaneamente os rótulos de estados e de pesos: uma distribuição não
uniforme também pode ser transportada covariantemente. Aqui exigimos que
a atribuição de contagem em si não distinga os estados do conjunto nu.
Isso não é uma afirmação sobre automorfismos da dinâmica.

Não colocamos a igualdade dos pesos como campo. Construímos a troca de
quaisquer dois códigos finitos, provamos suas inversas e a transportamos
ao prefixo pela bijeção existente. Aplicar invariância a essa troca prova

\[
w(x)=w(y)\qquad\text{para quaisquer prefixos }x,y.
\]

O caminho inverso também vale: uma atribuição constante é invariante.
`residualPrefix_relabelingInvariant_iff_constant` certifica as duas direções.
Portanto a uniformidade é consequência do princípio explícito de
neutralidade, não da cardinalidade isolada.

## 11. Uma unidade distribuída sem formar quocientes

Ainda trabalhamos com naturais. Uma apresentação de cotas consiste em
contagens `w(x)` e um denominador comum positivo `D`. A normalização exige
que a soma finita das contagens seja `D`. Essa soma é construída
recursivamente por adição (`finiteLabelTotal`).

Se há `C` estados e cada contagem é `c`, a soma prova `D=Cc`. Logo, para
cada estado,

\[
w(x)C=D.
\]

Essa igualdade diz, sem divisão, que a apresentação `(w(x),D)` é a mesma
cota que `(1,C)`. `FormalCountingShare` guarda numerador e denominador
positivo; `SameCountingShare` compara duas apresentações por multiplicação
cruzada. Não construímos o quociente dessas apresentações. Por exemplo,
`(2,18)` e `(1,9)` representam a mesma cota, mas não são pares iguais.

`residualPrefix_normalizedShare_unique` prova que toda apresentação por
contagens naturais, com denominador comum, neutralidade e total normalizado,
tem a mesma cota formal. O resultado não pretende abranger ainda medidas
numéricas arbitrárias.

A apresentação canônica conta cada estado uma vez e obtém o denominador
pela soma dessas unidades sobre os códigos da bijeção já provada. A soma
total vale `C=b^k`; só então identificamos a cota como

\[
\boxed{(1,b^k).}
\]

`canonicalResidualPrefixCountingShare` constrói essa apresentação;
`canonicalResidualPrefixCountingShare_invariant` prova neutralidade;
`canonicalResidualPrefixCountingShare_eq_unit_over_capacity` prova seu
numerador e denominador. O teorema de unicidade mostra que contar cada estado
duas ou mais vezes não altera a cota normalizada. Nenhuma massa antecipada
foi usada para justificar a torre ou sua capacidade.

## 12. Fronteira atual

A cadeia verificada é

\[
\begin{gathered}
\text{trajetória e observação finita autônoma injetiva}\\
\Downarrow\\
\text{retorno mínimo }b\to\text{ciclos/resíduos}\to\text{torre com cauda}\\
\Downarrow\\
\text{prefixos}\leftrightarrow Fin(b^k)\\
\Downarrow\quad\text{com neutralidade explícita da contagem}\\
\text{cotas iguais}\to\text{normalização formal }(1,b^k).
\end{gathered}
\]

A invariância é satisfeita pela contagem canônica construída. Não foi provado
que toda atribuição admissível pela dinâmica tenha essa invariância.

Permanecem posteriores: compatibilidade da normalização entre profundidades,
cotas de agrupamentos de estados, interpretação numérica das cotas formais,
eliminação eventual da cauda e construções métricas. Nenhum desses objetos é
premissa dos resultados acima. A rigidez aritmética de expoentes, já existente
em módulo separado, não foi usada nesta passagem: relacioná-la à normalização
exige uma etapa adicional, ainda não realizada aqui.
