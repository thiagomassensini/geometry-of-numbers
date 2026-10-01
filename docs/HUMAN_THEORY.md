# Da quantidade à seleção da escala e sua realização real

## Escopo e modo de leitura

A pergunta fundacional é o que uma representação pode esquecer localmente
sem que uma representação fiel perca a distinção global entre quantidades.
Não começamos com uma base, uma expansão em dígitos ou uma medida. Começamos
com uma trajetória de passos unitários e um observador local.

Este texto acompanha os resultados já compilados nesta árvore. Distingue
entradas, construções e consequências. Todos os resultados fundacionais
citados são verificados pelo kernel com lista de axiomas vazia. Isso não
significa ausência de hipóteses: finitude apresentada, autonomia e injetividade
são entradas explícitas. A contagem usa neutralidade e a seleção exige composição
quadrática. A realização real, na seção 17, tem outra auditoria e axiomas padrão.

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

## 12. Refinamento geométrico: esquecer apenas o novo resíduo

**INPUT.** Já temos os prefixos limitados, a torre que os produz e sua
codificação finita. Nenhuma nova hipótese de simetria é necessária aqui.

**CONSTRUÇÃO.** O primeiro elemento da tupla é o resíduo mais baixo `r₀`.
Por isso, a projeção para a segunda componente não é o truncamento desejado:
ela removeria `r₀`. Definimos recursivamente uma operação que percorre a tupla,
preserva os resíduos baixos e remove apenas o último:

\[
(r_0,\ldots,r_{k-1},r_k)\longmapsto(r_0,\ldots,r_{k-1}).
\]

A operação inversa de extensão recebe um pai e um elemento `a` de `Fin b`,
acrescentando `a` na posição mais profunda. `topResidual` lê essa nova
coordenada. As três operações são construídas sobre as tuplas existentes;
nenhuma delas usa potências ou divisão.

**TEOREMA.** As operações satisfazem

\[
truncate(extend(x,a))=x,\qquad top(extend(x,a))=a,
\]

e

\[
extend(truncate(y),top(y))=y.
\]

Além disso, extrair o prefixo da torre canônica em profundidade `k+1` e
truncá-lo dá exatamente o prefixo extraído em profundidade `k`, para qualquer
quantidade inicial, inclusive quando permanece uma cauda não nula
(`truncateResidualPrefix_of_canonicalTower`). Portanto não estamos
acrescentando uma segunda noção desconectada de profundidade.

Para um pai `x`, definimos sua fibra como o conjunto efetivo

\[
\{y:ResidualPrefix(b,k+1)\mid truncate(y)=x\}.
\]

O mapa `a ↦ extend(x,a)` tem inverso `y ↦ top(y)`. As leis acima provam
que todos os membros da fibra aparecem exatamente uma vez. Assim,

\[
\boxed{Fin(b)\longleftrightarrow\text{fibra de refinamento de }x.}
\]

`residualPrefixRefinementEquivFin` empacota essa bijeção e
`residualPrefixRefinement_fiber_cardinality` prova injetividade e
sobrejetividade. O fator `b` vem da coordenada residual nova, não de uma
reinterpretação da identidade entre potências.

Depois dessa construção, a avaliação ainda prova

\[
P_{k+1}(extend(x,a))=P_k(x)+a\,b^k.
\]

**INTERPRETAÇÃO.** A nova coordenada resolve informação adicional na
profundidade seguinte sem modificar a informação já resolvida. Ela não
é a ordem de uma derivada nem uma alteração dos resíduos anteriores.

**LIMITES.** Para `b=0`, o prefixo vazio existe, mas não tem refinamentos;
os tipos e as leis da fibra continuam fazendo sentido. Para `b=1`, cada pai
tem um único filho. Nada disso implica eliminação da cauda da torre completa.

## 13. Conservação das cotas e massa formal de profundidade

**INPUT.** Usamos a fibra já parametrizada e as cotas canônicas construídas
pela normalização neutra da seção 11. Não recebemos conservação de massa
como premissa.

**CONSTRUÇÃO.** Para cada filho efetivo `extend(x,a)`, tomamos sua cota
canônica em profundidade `k+1`. Todas possuem o mesmo denominador nessa
profundidade. Somamos seus numeradores sobre os parâmetros `a : Fin b`,
preservando esse denominador comum. Essa é a definição de
`residualPrefixRefinementAggregateShare`; ela não inclui uma igualdade com
a cota do pai.

**TEOREMA.** A soma das contagens unitárias dos filhos vale `b` porque
esses parâmetros enumeram exatamente a fibra. Logo a apresentação da
agregação é `(b,b^(k+1))`. Só agora a identidade aritmética de potências
verifica a igualdade cruzada

\[
b\,b^k=1\,b^{k+1}.
\]

Obtemos

\[
\boxed{\text{soma das cotas dos filhos}\sim\text{cota do pai}.}
\]

`residualPrefix_refinement_conserves_share` prova isso na relação
`SameCountingShare`. Não é igualdade de apresentações: em base `3` e
profundidade `2`, a agregação é `(3,27)` e a cota do pai é `(1,9)`.
O código testa tanto a equivalência quanto a desigualdade desses pares.

**INTERPRETAÇÃO.** Já podemos chamar a família construída de **massa formal
de profundidade dos prefixos resolvidos**: ela atribui a unidade ao prefixo
vazio e conserva a cota de cada pai sob o refinamento finito.

`canonicalResidualDepthMass` não define uma nova lei numérica. Ele toma
a cota canônica existente num prefixo representante, e o theorem
`canonicalResidualPrefixCountingShare_eq_depthMass` prova que qualquer
prefixo da mesma profundidade produz literalmente a mesma apresentação.
O representante não recebe massa privilegiada.

Se `μₖ` denota essa massa formal, os teoremas provam

\[
\mu_0=(1,1),\qquad b\,\mu_{k+1}\sim\mu_k.
\]

A multiplicação por `b` aqui significa agregar `b` cotas iguais pela adição
finita de seus numeradores (`repeatCountingShare`), não multiplicar números
racionais já construídos. O theorem da lei de escala é obtido da conservação
da fibra. A identificação posterior continua sendo `μₖ=(1,b^k)`.

**LIMITES.** Trata-se de massa formal em níveis finitos, não de uma medida
numérica sobre uma torre infinita ou de um teorema de aditividade enumerável.
Não provamos aqui a unicidade de qualquer família arbitrária a partir somente
da equação recursiva. A unicidade já disponível é a das cotas sob neutralidade
e normalização em cada nível. São afirmações diferentes.

Uma família coerente com unidade inicial requer `b>0`. Quando `b=0`, a soma
dos filhos é vazia e nenhuma cota com denominador positivo pode fazê-la
equivaler à unidade (`zeroRefinement_cannot_conserve_unit`). Não forçamos
uma massa de profundidade zero a estender-se coerentemente a uma fibra vazia.

## 14. Fronteira atual

A cadeia verificada é

\[
\begin{gathered}
\text{trajetória e observação finita autônoma injetiva}\\
\Downarrow\\
\text{retorno mínimo }b\to\text{ciclos/resíduos}\to\text{torre com cauda}\\
\Downarrow\\
\text{prefixos}\leftrightarrow Fin(b^k)\\
\Downarrow\quad\text{com neutralidade explícita da contagem}\\
\text{cotas iguais}\to\text{normalização formal }(1,b^k)\\
\Downarrow\quad\text{pela fibra de refinamento parametrizada por }Fin(b)\\
\text{agregação conservativa}\to\text{massa formal coerente por profundidade}.
\end{gathered}
\]

A invariância é satisfeita pela contagem canônica construída. Não foi provado
que toda atribuição admissível pela dinâmica tenha essa invariância.

Permanecem posteriores: agrupamentos finitos arbitrários além da fibra de um
pai, interpretação numérica das cotas formais, eventual medida sobre estados
infinitos, eliminação eventual da cauda e construções métricas. Nenhum desses objetos é
premissa dos resultados acima. A rigidez aritmética de expoentes, já existente
em módulo separado, não foi usada na construção da massa. A próxima seção
formaliza sua ligação com essa massa mediante compatibilidade quadrática.

## 15. Da massa derivada à seleção de um expoente formal

### INPUT: o que existe antes da ponte

Já temos a massa formal `μₖ = canonicalResidualDepthMass b k hb`, com `b>0`.
Ela é a cota da contagem neutra dos prefixos, nomeada somente depois de sua
conservação nas fibras de refinamento. Seu numerador é `1` e seu denominador
é a capacidade `b^k`, pelo theorem anterior. Não voltamos a definir a massa
por uma fórmula de potência nem usamos uma amplitude para justificá-la.

A profundidade `k` continua sendo o número de coordenadas residuais resolvidas
na mesma torre. A cauda não faz parte da contagem desses estados.

### CONSTRUÇÃO: uma apresentação de escala posterior à massa

Definimos a cota de escala `S_b(e) = radixShare b e hb` pela apresentação

$$
S_b(e)=(1,b^e).
$$

O expoente `e` é um natural. Esse objeto não é uma fração numérica nem uma
potência real com expoente negativo. A identificação
`canonicalResidualDepthMass_eq_radixShare` prova, como igualdade literal de
apresentações e não apenas equivalência de cotas,

$$
\boxed{\mu_k=S_b(k).}
$$

A direção da prova usa os campos já calculados da massa. A notação de escala
é uma interpretação posterior, não uma nova origem da normalização.

Introduzimos também a composição multiplicativa de apresentações:

$$
(a,d)\otimes(c,e)=(ac,de),\qquad (a,d)^{\otimes q}=(a^q,d^q).
$$

Os denominadores permanecem positivos. As leis de potência zero e sucessor
provam que a segunda operação é a composição repetida da primeira. Isso é
distinto de agregar filhos: naquele caso somávamos numeradores mantendo um
denominador comum. Aqui compomos escalas, não somamos massas de estados.
Não afirmamos uma nova lei de independência probabilística.

### TEOREMA: a escala permite ler seu expoente quando `b>1`

Comparar duas cotas de escala por multiplicação cruzada dá

$$
S_b(a)\sim S_b(c)\quad\Longleftrightarrow\quad b^a=b^c.
$$

Para `b>1`, cada passo aumenta estritamente a potência: `b^n<b^(n+1)`.
Indução e comparação de naturais dão injetividade, portanto

$$
\boxed{S_b(a)\sim S_b(c)\quad\Longleftrightarrow\quad a=c.}
$$

Esse é `radixShare_same_iff_exponent_eq`. Nenhum teorema sobre potências reais
entra na prova. A hipótese `b>1` é indispensável: para `b=1`, todas as cotas
são `(1,1)` independentemente do expoente. A capacidade positiva, sozinha,
não permite ler escala.

### CONSTRUÇÃO: o requisito quadrático, antes da equação

Uma razão candidata é apresentada por naturais `p,q`, com `q>0`. Não formamos
o número `p/q`. Para interpretar uma lei de amplitude formal, usamos unidades
de expoente com esse denominador já eliminado: sua escala candidata na
profundidade `k` tem expoente `kp`. Compor essa escala consigo mesma é a
operação quadrática. Para comparar com a massa, compomos a massa `q` vezes.

Definimos `QuadraticAmplitudeScaleCompatibleAt` pelo requisito

$$
q>0\quad\text{e}\quad
S_b(kp)\otimes S_b(kp)\sim\mu_k^{\otimes q}.
$$

A massa geométrica aparece no lado direito da própria definição. Nem
`2kp=kq` nem `2p=q` são campos da compatibilidade. Não definimos uma amplitude
numérica: especificamos apenas quais escalas formais seriam compatíveis.

**Princípio semântico explícito:** exigir composição quadrática é o critério
para essa amplitude candidata. A contagem neutra e o refinamento não provam
que todo observável deva obedecer a ele. O teorema abaixo classifica as leis
que satisfazem esse requisito, não cria uma métrica a partir da contagem.

### TEOREMA: a comparação com a massa produz a equação

As leis de composição provam

$$
S_b(kp)\otimes S_b(kp)=S_b(2(kp)),\qquad
\mu_k^{\otimes q}=S_b(kq).
$$

A segunda igualdade é `canonicalResidualDepthMass_power_eq_radixShare`:
parte da massa de profundidade `k`, não de uma cota desconectada. Logo, para
`b>1`, a comparação semântica equivale à equação

$$
q>0,\qquad 2(kp)=kq.
$$

`quadraticAmplitudeScaleCompatibleAt_iff_carryCompatibleAt` liga esse resultado
à interface aritmética já existente. Em profundidade positiva, o theorem
anterior `quadraticCarryCompatibleAt_iff_half` cancela `k` e obtém

$$
\boxed{2p=q.}
$$

Essa relação representa metade sem divisão. `(1,2)`, `(2,4)` e `(17,34)`
são apresentações distintas da mesma razão formal; não se afirma unicidade
do par. O capstone `canonicalResidualDepthMass_quadraticCompatibility_iff_half`
prova ambas as direções: uma escala é compatível exatamente quando sua razão
representa metade. A aritmética antiga não foi reprovada.

Uma versão `emergentResidualDepthMass_quadraticCompatibility_iff_half` usa
literalmente a capacidade do primeiro retorno da trajetória. Seu `b>1` vem
do primeiro passo local não trivial, pelo theorem pré-carry já existente.
Assim a condição de leitura da escala também se conecta à origem dinâmica.

### INTERPRETAÇÃO E LIMITES

A nova cadeia é

$$
\text{massa derivada}\to\text{apresentação de escala}
\xrightarrow{\text{requisito quadrático explícito}}
\text{comparação de cotas}\to 2kp=kq\to 2p=q.
$$

Não começamos com metade para construir a massa ou a compatibilidade. Ela
aparece somente na classificação final, sob `b>1` e `k>0`.

- `b=0`: não fornece a família anterior de massa com denominador positivo;
  não inventamos uma escala para contornar a fibra vazia.
- `b=1`: qualquer razão válida passa o teste, mesmo em profundidade positiva.
- `k=0`: qualquer razão válida passa o teste, mesmo com capacidade não trivial.
- `q=0`: é excluído pela validade da razão, em todas as profundidades.

A realização numérica dessa razão formal aparece na seção 17. Na etapa
discreta acima não entram números racionais ou reais, raízes ou normas.
A seleção formal já está ligada à massa geométrica; sua interpretação numérica
é posterior, e a construção/justificativa de uma métrica continua aberta.

## 16. Fechamento da Zona A: da massa formal à rigidez de metade

### INPUT E COSTURA

A trajetória global é injetiva; a observação local possui apresentação finita,
e sua evolução é autônoma e injetiva. O primeiro passo altera a observação.
Essas hipóteses não são deduzidas de uma conservação abstrata isolada, nem
guardadas num certificado contendo as conclusões desejadas.

`FoundationalHalfScalingCapstone` compõe os resultados anteriores, sem novas
definições matemáticas. A existência já provada produz o menor retorno
positivo `b`, com `1<b` e `b` limitado pelo orçamento da apresentação local.
A massa utilizada é a mesma massa dos prefixos da torre com essa capacidade.

### TEOREMA

`foundational_half_scaling_capstone` vale para a capacidade emergente da
própria trajetória. `exists_foundational_half_scaling_capstone` produz uma
capacidade com esse resultado, a partir da apresentação finita. Para todo
`k>0`, a comparação quadrática com a massa é equivalente a metade:

$$
\mu_{b,k}\ \xrightarrow{\text{compatibilidade quadrática}}
2(kp)=kq\ \Longleftrightarrow\ 2p=q,\qquad q>0.
$$

Os dois teoremas são costuras: não repetem as provas da torre, de contagem,
de injetividade da escala ou de cancelamento de expoentes.

### INTERPRETAÇÃO E LIMITES

**Aqui termina a fundação discreta de seleção da escala.** Seu footprint é
vazio: nem axiomas clássicos nem axiomas de quocientes participam da prova.
Isso não elimina as hipóteses operacionais ou o requisito semântico quadrático.

O corte não declara pronta uma norma, nem todas as metas históricas de
geometria. A cauda continua explícita. A massa é uma cota formal finita e
coerente por refinamento, não uma medida em uma torre infinita. Metade é uma
relação entre naturais, não ainda uma amplitude numérica.

## 17. Realização real da massa e da amplitude

### INPUT: o que a análise recebe

A nova camada recebe o objeto formal de massa e a classificação do expoente,
já provados antes de qualquer número real. Sua dependência é unilateral:

```text
Foundation — seleção formal da escala, axiomas vazios
    ↓
Analysis — realização real, axiomas padrão de Mathlib
```

Não existe uma seta de volta justificando a fundação. O import público
`GeometryOfNumbers` permanece discreto; `GeometryOfNumbers.Analysis` abre
a nova camada. O parser Lean verifica que os arquivos fundacionais não
importam análise ou Mathlib.

### CONSTRUÇÃO: interpretar, não redefinir a massa

Uma apresentação formal tem numerador natural `a` e denominador natural
positivo `d`. `realizeCountingShare` interpreta esse dado como divisão real:

$$
\operatorname{realize}(a,d)=\frac{(a:\mathbb R)}{(d:\mathbb R)}.
$$

O theorem `realizeCountingShare_eq_iff_sameCountingShare` garante que duas
interpretações são iguais exatamente quando as apresentações já eram a
mesma cota por multiplicação cruzada. Assim `(2,18)` e `(1,9)` dão o mesmo
valor sem exigir igualdade dos pares.

Definimos a massa real como a realização do objeto já existente:

$$
M_b(k):=\operatorname{realize}(\mu_{b,k}).
$$

Esta é `realDepthMass`. Não começamos com `b^{-k}` como definição de massa.
Usando a identificação fundacional `μₖ=(1,b^k)`, provamos depois:

$$
\boxed{M_b(k)=\frac1{(b:\mathbb R)^k}=(b:\mathbb R)^{-k}.}
$$

`realDepthMass_eq_one_div_pow`, `realDepthMass_eq_inv_pow` e
`realize_canonicalResidualDepthMass` expõem essas apresentações numéricas.
A potência negativa é consequência da realização, não uma nova hipótese
sobre a torre ou sua contagem.

### CONSTRUÇÃO: realizar o expoente já selecionado

Agora podemos interpretar a razão formal válida `p,q` em `ℝ`. O fato
fundacional `2p=q`, com `q>0`, implica

$$
\frac{(p:\mathbb R)}{(q:\mathbb R)}=\frac12.
$$

Esse é `formalHalf_realizes_half`, uma conversão após a seleção, não um
argumento analítico para selecioná-la. A realização de uma escala candidata é

$$
A_{b;p,q}(k)=(b:\mathbb R)^{-k\,(p/q)}.
$$

Usamos `(1,2)` para nomear a amplitude crítica real `A_b(k)`.
`formalHalf_realizes_realCriticalAmplitude` prova que toda apresentação de
metade — inclusive `(17,34)` — realiza esse mesmo valor. Portanto:

$$
\boxed{A_b(k)=(b:\mathbb R)^{-k/2}.}
$$

Não colocamos essa função na fundação para justificar o expoente anterior.
Sua definição e as potências reais pertencem somente à camada analítica.

### TEOREMA: o quadrado realiza a massa

A lei de composição das potências reais verifica

$$
A_b(k)^2=(b:\mathbb R)^{(-k/2)\,2}
        =(b:\mathbb R)^{-k}=M_b(k).
$$

Esse é `realCriticalAmplitude_sq_eq_realDepthMass`. A prova usa o expoente
selecionado; não usa o quadrado como premissa para selecionar metade.
`quadraticScaleCompatible_realizes_realCriticalAmplitude` torna explícita
a composição: compatibilidade formal → classificação fundacional → mesma
amplitude real.

### INTERPRETAÇÃO, HIPÓTESES E LIMITES

A realização e sua identidade do quadrado exigem `b>0`. Em profundidade
zero, a massa formal `(1,1)` e ambas as realizações dão `1`. Em base `1`,
os valores também são `1`; a realização trivial existe, mas a fundação não
seleciona expoentes nessa base. Para `b=0`, não realizamos uma família
canônica de massa com denominador positivo. Uma amplitude de razão geral
exige também `q>0`. A seleção discreta permanece no regime `b>1`, `k>0`.

Os exemplos formais verificam massas em base `2`, profundidades `0` e `1`,
e base `3`, profundidade `2`, bem como `A_3(2)=1/3` e apresentações equivalentes.
São testes de realização, não dados usados para definir os objetos.

A auditoria analítica registra `propext`, `Classical.choice` e `Quot.sound`.
Ela permite somente esses axiomas padrão; não é uma auditoria de footprint
vazio. A auditoria da fundação permanece separada e vazia.

Até esta etapa escalar não havíamos construído estado rotacional, espaço
vetorial, produto interno, norma, câmeras, brackets, TFVD, Green, isometria
ou operador. O estado coordenado é introduzido nas seções 23–24. `A²=M` é uma
identidade de escalares reais; não deriva, sozinha, uma norma quadrática.
A massa real continua sendo a realização de cotas finitas, não uma medida
analítica mais forte. A próxima estrutura geométrica deve ser introduzida
explicitamente quando chegar sua rodada, sem retornar como premissa da fundação.

## 18. Geometria centro–pernas e reflexão

### INPUT: uma camada adicional, não uma premissa retroativa

A fundação de seleção da escala já foi encerrada: primeiro retorno, torre,
contagem, massa formal coerente e compatibilidade quadrática selecionam a
razão formal de metade. Nada dessa prova pressupôs a geometria que agora
construímos. A realização escalar real também permanece aquela da seção
anterior; não a usamos para construir a nova configuração discreta.

Recebemos um centro `c` e um raio **inteiro com sinal** `r`. Esse carrier
permite deslocamentos para os dois lados sem a subtração truncada dos
naturais. Nenhuma divisão, média, estrutura normada ou novo dado analítico
é necessária.

### CONSTRUÇÃO: o centro vem antes das pernas

Definimos apenas as duas avaliações determinadas pelos dados:

$$
\ell(c,r)=c-r,\qquad \rho(c,r)=c+r.
$$

Não colocamos sua simetria como hipótese nem armazenamos relações
redundantes num certificado. `leftLeg` e `rightLeg` são essas construções;
`leftLeg_add_rightLeg` prova depois:

$$
\ell(c,r)+\rho(c,r)=2c.
$$

Raio zero faz ambas as pernas coincidir com o centro. Inverter o sinal do
raio troca os nomes das pernas, sem mudar a configuração não orientada.
Esse resultado vale também para centros e raios negativos.

### TEOREMA: reflexão involutiva e centro recuperável

A reflexão em torno do centro é

$$
R_c(x)=2c-x.
$$

Ela fixa `c`, leva `c-r` a `c+r`, leva `c+r` a `c-r` e satisfaz

$$
R_c(R_c(x))=x.
$$

`reflect_center`, `reflect_leftLeg`, `reflect_rightLeg` e
`reflect_involutive` provam essas leis. Elas não escolhem um novo centro;
testam a operação determinada pelo centro já recebido.

Para duas pernas **fixas**, podemos perguntar se um candidato `a` é centro:
`IsCenterOf left right a` significa que sua reflexão troca esses endpoints.
`isCenterOf_iff_sum` caracteriza essa condição, sem dividir por dois:

$$
R_a(\ell)=\rho\iff \ell+\rho=2a.
$$

As pernas construídas possuem o centro `c`, e `constructed_center_unique`
prova que qualquer candidato que satisfaça a condição coincide com ele.
Não concluímos que quaisquer endpoints inteiros tenham centro inteiro:
`0` e `1`, por exemplo, não admitem um inteiro `a` com `2a=1`.

### INTERPRETAÇÃO E LIMITES

O centro construído e sua caracterização são afirmações diferentes: a
primeira fornece uma configuração a partir de dados; a segunda testa um
candidato contra endpoints mantidos fixos. Nenhum teorema novo identifica
esse centro ou raio com resíduos, contadores ou profundidades da torre.
Nesta etapa abstrata o crosswalk ainda não estava construído. A seção 20
fecha uma célula carry → centro/pernas para capacidade ímpar; as seções 21–22
acrescentam depois a identificação relacional de profundidades, sem valuation.

Essa geometria adicional é Init-only, mas não pertence ao capstone vazio
da Zona A. As provas inteiras usuais desta versão usam `propext` e
`Quot.sound`; o audit próprio rejeita escolha e qualquer outro axioma.
As definições geométricas têm footprint vazio. A fundação continua com
footprint vazio e sem importar Geometry. A organização das entradas
`Foundation → Geometry → Analysis` não é, por si só, uma prova desse crosswalk.

## 19. Segunda diferença e defeito de centro

### CONSTRUÇÃO: um candidato contra pernas fixas

Só depois da configuração definimos o teste geométrico

$$
D(\ell,a,\rho)=\ell-2a+\rho.
$$

Ele zera precisamente quando `a` é centro dessas pernas, conforme
`centerDefect_eq_zero_iff_isCenterOf`. Para pernas produzidas por `c_0`,
`centerDefect_constructed` dá zero no centro original. Se mantemos **as mesmas
pernas** e deslocamos somente o candidato, o capstone da camada é:

$$
\boxed{D(c_0-r,c_0+\delta,c_0+r)=-2\delta.}
$$

`centerDefect_fixed_legs_shift` prova esse resultado para todo deslocamento
inteiro; `centerDefect_fixed_legs_shift_neg` dá `2δ` ao testar `c_0-δ`.
O sinal vem da orientação definida, não de um ajuste posterior.

### TEOREMA: recentrar as pernas elimina o mismatch

Se mudamos também as pernas para a geometria do novo centro, temos

$$
\ell'=(c_0+\delta)-r,\qquad \rho'=(c_0+\delta)+r,
$$

e `centerDefect_recentered` prova

$$
D(\ell',c_0+\delta,\rho')=0.
$$

Portanto o defeito **não é uma propriedade absoluta do número chamado
centro**. É a incompatibilidade entre um candidato e as pernas fixas da
geometria anterior. Os exemplos dão `(7,10,13)` no centro verdadeiro,
`D(7,11,13)=-2` no candidato deslocado e `D(8,11,14)=0` após recentramento.

### CONSTRUÇÃO: observar a configuração

Para um observável inteiro `f : Int → Int`, a operação sobre três nós é

$$
\operatorname{SD}_f(\ell,a,\rho)=f(\ell)-2f(a)+f(\rho).
$$

Essa é `secondDifferenceAt`. Depois a especializamos às pernas construídas:

$$
\Delta^2_{c,r}f=\operatorname{SD}_f(c-r,c,c+r).
$$

Essa é `centeredSecondDifference`. Separar as duas APIs é importante: testar
`a=c_0+δ` com as pernas originais **não** equivale a construir
`centeredSecondDifference f (c_0+δ) r`, pois esta última também muda as pernas.

### TEOREMA: identidade detecta miscentering; não linearidade responde à geometria

`secondDifferenceAt_identity` recupera literalmente `D`. Assim a identidade
tem segunda diferença zero na configuração centrada, e o mesmo teste com
pernas fixas e candidato deslocado dá `-2δ`. Não foi preciso scalarizar
outro carrier: trabalhamos diretamente com a geometria inteira definida.

Não generalizamos essa anulação a qualquer observável. O exemplo formal
`centeredSecondDifference_square` prova

$$
(c-r)^2-2c^2+(c+r)^2=2r^2.
$$

Para `c=10,r=3`, a resposta é `49-200+169=18`, embora a configuração esteja
perfeitamente centrada. A identidade lê diretamente o defeito de centro;
um observável geral lê sua resposta — ou curvatura discreta — sobre essa
geometria. Raio negativo preserva a segunda diferença, e raio zero a anula
para qualquer observável, pois os três nós então coincidem.

### LIMITES E PRÓXIMAS PONTES

A camada tem 21 teoremas públicos e sete definições auditados separadamente.
Seus testes não são pressupostos das provas gerais. Na etapa abstrata não
construímos o mapa da célula carry para centro–pernas, acrescentado abaixo;
não identificamos o bracket histórico, Green
ou tilt com a segunda diferença ou com o defeito. Não há nova norma, estado
rotacional, câmera ou operador. Essas pontes serão enunciadas e provadas
em suas próprias etapas, sem reescrever a origem da massa e de metade.

## 20. Do resíduo ordinário ao offset balanceado

### INPUT: a mesma célula de carry, com seu regime explicitado

A decomposição ordinária já foi construída por passos unitários e reset:

$$
n=qb+r,\qquad 0\le r<b,
$$

onde `q=completedCycleCount b n` e `r=cycleResidual b n`. Esses objetos
continuam exatamente os da fundação: não são redefinidos por divisão ou
módulo. O natural `n` é a contagem do relógio usada nessa construção; não
se presume aritmética adicional no tipo abstrato de quantidade da trajetória.

Para este crosswalk recebemos a hipótese explícita de que a capacidade é
ímpar. Sua apresentação mínima é um testemunho natural `h` com

$$
b=2h+1.
$$

`IsOddCapacity` expressa esse regime. Ele implica positividade e exclui
`2r=b` para qualquer resíduo natural. Não exigimos primalidade. Também
**não deduzimos oddness da fundação**: o primeiro retorno pode ser par;
a geometria desse regime não se fecha mudando silenciosamente a capacidade.

`emergentCapacity_balancedCarry_spec` recebe o primeiro retorno da mesma
trajetória e, separadamente, sua oddness; expõe a decomposição original
junto da geometria obtida dela. Não introduz uma base posicional externa.

### PROBLEMA: resíduo ordinário não é ainda offset simétrico

O resíduo ordinário lê a posição no ciclo a partir do múltiplo anterior.
Isso não determina que esse múltiplo seja o centro mais próximo. Em
capacidade `5`:

$$
9=1\cdot5+4=10-1.
$$

O resíduo é `4`, mas a coordenada simétrica é o offset `-1` do centro `10`.
Conservar sempre o centro `qb` perderia esse balanceamento.

### CONSTRUÇÃO: comparar distâncias sem dividir por dois

Comparamos apenas `2r` e `b`, e definimos:

$$
(c,a)=
\begin{cases}
(qb,r),&2r<b,\\
((q+1)b,r-b),&b<2r.
\end{cases}
$$

A subtração `r-b` ocorre em `Int`, não é truncada. As funções
`balancedCarryCenter` e `balancedCarryOffset` exigem a hipótese ímpar;
seu segundo ramo nunca representa uma escolha de lado no empate par.
Nenhuma fórmula nova escolhe ciclos ou resíduos: somente reexpressa os
mesmos dados já construídos.

### TEOREMA: reconstrução, alinhamento e janela estrita

`balancedCarry_spec` reúne as conclusões:

$$
\boxed{n=c+a,\qquad b\mid c,\qquad 2|a|<b.}
$$

O primeiro resultado transporta a reconstrução natural existente para
inteiros. O segundo vem do fato de que o centro é `qb` ou `(q+1)b`. O
terceiro usa `r<b` e a comparação estrita dos dois lados.

Na implementação, `IsBalancedOffset b a` significa `-b<2a<b`;
`balancedOffset_iff_natAbs` prova a equivalência com `2*natAbs(a)<b`.
Portanto não se supõe unicidade como campo de um predicado. A janela
estrita expressa que o offset permanece dentro da meia-célula, sem formar
uma fração.

### TEOREMA: por que a representação é canônica

Considere duas decomposições da mesma quantidade, com centros alinhados
e offsets estritamente balanceados. Sua diferença de centros é um múltiplo
de `b`; pela igualdade das quantidades, é também a diferença dos offsets.
Os limites estritos colocam essa diferença entre `-b` e `b`. Um múltiplo
não nulo de `b` não cabe nessa janela. Logo os centros coincidem, e então
os offsets também.

Esse é `balancedCenterOffset_unique`; ele não precisa de paridade, uma vez
que os representantes estritos existam. A oddness é necessária nesta API
para garantir a construção para **todo** resíduo da capacidade, não como
ingrediente da prova de unicidade. `balancedCarry_unique` identifica
qualquer decomposição válida com a que veio do carry.

### TEOREMA: quantidade e reflexão são as pernas da API existente

Não criamos outra geometria. A reconstrução identifica

$$
\operatorname{rightLeg}(c,a)=c+a=n,
$$

e a reflexão existente dá

$$
\operatorname{reflect}(c,n)=c-a=\operatorname{leftLeg}(c,a).
$$

Com raio/offset negativo, os nomes `leftLeg` e `rightLeg` são os nomes
algébricos da API, não uma afirmação de ordem numérica. As pernas vivem
em `Int`; uma reflexão próxima da origem pode ser negativa.

Em capacidade `5`, os testes certificam:

| Quantidade | Ciclos, resíduo | Centro, offset | Reflexão |
| --- | --- | --- | --- |
| `6` | `(1,1)` | `(5,+1)` | `4` |
| `7` | `(1,2)` | `(5,+2)` | `3` |
| `8` | `(1,3)` | `(10,-2)` | `12` |
| `9` | `(1,4)` | `(10,-1)` | `11` |
| `10` | `(2,0)` | `(10,0)` | `10` |

Resíduo zero implica offset zero e centro igual à quantidade. Sua reflexão
é fixa; um múltiplo não é declarado perna não central. Resíduo não zero
implica offset não zero e quantidade distinta do centro.

Por composição com os teoremas da seção anterior, o centro correto tem
defeito zero para `reflect(c,n),n`. Mantendo essas pernas e testando `c+δ`,
`balancedCarry_centerDefect_shift` dá `-2δ`; a segunda diferença da
identidade herda exatamente esse resultado. Não foi redefinido o defeito.

### LIMITES: a obstrução antipodal e o próximo gate

Em capacidade par pode ocorrer `2r=b`. O caso mínimo é:

$$
b=2,\quad n=1,\qquad 1=0+1=2-1.
$$

`antipodal_two_no_strict_decomposition` prova que nenhum centro alinhado
representa essa quantidade com offset estrito. Se permitimos o bordo
`2|a|=b`, `antipodal_two_boundary_nonunique` exibe os dois centros distintos
`0` e `2`, ambos válidos. Portanto não se pode estender a construção ímpar
ao antipodal apenas relaxando uma desigualdade e alegando canonicidade.
**C2 permanece uma ponte dedicada futura; nenhum lado foi escolhido.**

Capacidade `1` é ímpar e tem apenas o caso central; capacidade `0` não entra
no domínio. O teste com capacidade composta `9` dá `17=18-1`, confirmando
que primalidade não é input. A fundação de massa e metade não foi alterada.

Esta rodada acrescenta 23 teoremas e quatro definições ao audit geométrico.
As definições são vazias; os teoremas usam somente os axiomas já permitidos
`propext` e `Quot.sound`, sem escolha. O witness antipodal de bordo também
tem footprint vazio. A fundação continua intocada, com seu audit vazio.

Essa etapa fechou uma célula: carry existente → centro/offset canônicos no
regime ímpar → pernas refletidas. Ainda não definimos uma profundidade
efetiva máxima da quantidade. A etapa seguinte identifica os níveis de
profundidade relacional do centro e do único offset profundo. Brackets
históricos, Green e tilt permanecem posteriores. O primeiro estado angular
de profundidade é construído somente nas seções 23–24.

## 21. Profundidade como zeros sucessivos da torre

### INPUT: a torre já construída, com sua cauda

Para capacidade positiva `b`, a torre em nível `k` já resolve:

$$
x\longmapsto(r_0,\ldots,r_{k-1},q_k),\qquad 0\le r_i<b.
$$

Seu carrier e suas coordenadas vêm da repetição de `cycleResidual` e
`completedCycleCount`, não de uma função de valuation. Já sabemos reconstruir
o mesmo `x` e identificar unicamente qualquer tupla limitada que o reconstrua.
Não sabemos ainda que a cauda eventualmente termine para todo `x` em `b>1`.

### CONSTRUÇÃO: uma relação, não uma profundidade máxima

`ResidualTowerZeroPrefix` testa recursivamente se todos os resíduos de uma
tupla são zero. Não consulta nem restringe a cauda. Definimos:

$$
\operatorname{Depth}_{\ge k}(b,x)
\quad\Longleftrightarrow\quad
r_0=\cdots=r_{k-1}=0
\quad\text{na torre canônica de }x.
$$

Essa é `HasCarryDepthAtLeast`. Potências e divisibilidade não aparecem em
sua definição. O teste vazio sempre é verdadeiro:

$$
\operatorname{Depth}_{\ge0}(b,x).
$$

O próximo nível vem literalmente da recursão da mesma torre:

$$
\operatorname{Depth}_{\ge k+1}(b,x)
\iff
\operatorname{cycleResidual}(b,x)=0
\ \land\
\operatorname{Depth}_{\ge k}
  (b,\operatorname{completedCycleCount}(b,x)).
$$

`hasCarryDepthAtLeast_succ` certifica essa lei por expansão da definição,
sem recorrer à divisibilidade. Cada zero deixa a informação inteira no
contador de ciclos seguinte, e a mesma operação pode ser aplicada novamente.

### TEOREMA: a divisibilidade emerge da reconstrução

O valor prefixal é uma soma de naturais com pesos positivos. Para `b>0`,
seu valor é zero exatamente quando cada resíduo é zero. A expansão já
provada da torre então reduz a:

$$
\operatorname{Depth}_{\ge k}(b,x)
\ \Longrightarrow\
x=q_k b^k.
$$

Esta é `hasCarryDepthAtLeast_eq_scaled_tail`, com a **cauda da própria
torre** no lado direito. A direção inversa não calcula quociente ou módulo.
Dado um witness `x=b^k t`, formamos apenas uma tupla comparativa com `k`
resíduos zero e cauda `t`. Ela é limitada e reconstrói `x`; a unicidade
`residualTower_eq_canonical` obriga essa tupla a ser a torre canônica.
Concluímos:

$$
\boxed{\operatorname{Depth}_{\ge k}(b,x)\iff b^k\mid x}
\qquad(b>0).
$$

O teorema é `hasCarryDepthAtLeast_iff_dvd_pow`. Também provamos a equivalência
com `residualTowerPrefixValue = 0`. Não se trata de `tail = 0`: no exemplo
`b=5,x=25,k=2`, os resíduos são `(0,0)` e a cauda é `1`. Profundidade positiva
concentra a informação na cauda; não a elimina.

### INTERPRETAÇÃO, DEGENERADOS E LIMITES

Zero suporta qualquer nível, pois sua torre mantém resíduos zero. A capacidade
`1` também suporta qualquer nível de qualquer quantidade: seu único resíduo
é zero e os contadores não precisam decrescer. Não lhes atribuímos um máximo.
O nível zero vale para todos por ser um prefixo vazio, mas não seleciona
nenhum canal entre offsets candidatos.

As funções totais antigas ainda têm valores em capacidade `0`, mas ali não
representam uma célula carry positiva. O contraexemplo formal
`zeroCapacity_depth_does_not_characterize_divisibility` dá teste de prefixo
zero em `(b,x,k)=(0,1,1)`, embora `0^1` não divida `1`. A hipótese `b>0` na
ponte é portanto substantiva, não cosmética.

Para preservar a fundação congelada, esta extensão está em
`Geometry/ResidualTowerDepth.lean`, importando apenas a API fundacional da
torre. Seus nove teoremas públicos têm footprint vazio e guard adicional
de auditoria. Não alteramos a seleção de metade nem suas premissas.
Terminação eventual, profundidade exata finita e uma função máxima continuam
abertas; nada disso é necessário para os enunciados relacionais desta etapa.

## 22. Profundidade do centro balanceado

### INPUT E EXTENSÃO TIPADA

Agora recebemos a decomposição já canônica, no regime de capacidade ímpar:

$$
n=c+a,\qquad b\mid c,\qquad 2|a|<b.
$$

Offsets candidatos são inteiros, logo `n-a'` também é inteiro. Depois de
provar a caracterização natural, estendemos a relação por:

$$
\operatorname{Depth}^{\mathbb Z}_{\ge k}(b,x)
\iff (b:\mathbb Z)^k\mid x.
$$

`hasIntegerCarryDepthAtLeast_natCast_iff` mostra que essa extensão restringe-se
exatamente à relação da torre nos naturais para `b>0`. Não construímos uma
torre inteira paralela e não introduzimos nenhuma valuation pronta.

### TEOREMA: o offset canônico deixa o centro exposto

A reconstrução dá literalmente:

$$
n-a=c.
$$

`balancedCarry_sub_offset_eq_center` nomeia esse elo. Assim, para qualquer
nível, a sobrevivência de `n-a` coincide com a do centro. Isso ainda não
afirma que um centro não nulo tenha sobrevivência ilimitada ou máximo definido.

Para um candidato estritamente balanceado `a'`, se `b\mid(n-a')`, então
`n=(n-a')+a'` é outra decomposição alinhada e balanceada. A unicidade já
provada na etapa anterior força `a'=a`. Não é preciso reprovar o argumento
de diferença pequena de múltiplos; `balancedCarry_offset_unique_of_dvd`
reutiliza exatamente `balancedCarry_unique`.

Em nível `k>0`, a divisibilidade por `b^k` implica divisibilidade por `b`.
Portanto o primeiro nível já seleciona o canal, e os níveis seguintes
interrogam somente o centro desse canal:

$$
\boxed{
b^k\mid(n-a')
\iff
a'=a\ \land\ b^k\mid c
}
\qquad(k>0,\quad 2|a'|<b).
$$

Este é `balancedCarry_positive_depth_iff`. Eliminando o candidato obtemos:

$$
\boxed{
\exists a'\text{ balanceado},\
\operatorname{Depth}^{\mathbb Z}_{\ge k}(b,n-a')
\iff
\operatorname{Depth}^{\mathbb Z}_{\ge k}(b,c)
}.
$$

`balancedCarry_exists_depth_iff_center_depth` prova essa equivalência, e
`balancedCarry_unique_depth_witness` fornece o witness com sua lei de
unicidade. Essa é a forma relacional, pré-valuation, da identidade histórica
entre profundidade efetiva e profundidade do centro. Não é uma igualdade
de duas funções máximas que tenhamos definido aqui.

### EXEMPLOS E O MESMO ÍNDICE VERTICAL

Em base `5`, `9=10-1`. Dos offsets `-2,-1,0,1,2`, somente `-1` deixa um
múltiplo de `5`: os outros candidatos dão `11,9,8,7`. Para `26=25+1`, o
offset `1` deixa o centro `25`, divisível por `5` e `25`, mas não por `125`.
Os testes verificam esses níveis sem dar ao objeto um nome de máximo.

O índice `k` usado na torre, na divisibilidade do centro e em
`canonicalResidualDepthMass b k hb` é o mesmo. O corolário
`balancedCarry_depth_and_mass_at_same_index` expõe conjuntamente a relação
do canal canônico nesse nível e os campos da massa existente:

$$
\operatorname{numerador}(\mu_{b,k})=1,\qquad
\operatorname{denominador}(\mu_{b,k})=b^k.
$$

Ele não redefine a massa, não cria massa de `n` e não transforma a amplitude
por profundidade em amplitude global por quantidade. A fórmula de massa já
existia; a novidade é identificar onde um candidato deixa exposto esse nível.

### LIMITES E AUDITORIA

Centro zero sobrevive em todos os níveis. Capacidade um permanece degenerada.
A relação natural vale também para capacidades pares positivas; a seleção
balanceada continua no regime ímpar já provado. Não resolvemos C2 nem usamos
primalidade. Nessa etapa relacional não criamos profundidades máximas,
valuation, bracket, Green, tilt ou estado rotacional. O estado real angular
é uma construção analítica posterior, descrita a seguir.

A ponte inteira tem onze teoremas públicos, com no máximo `propext` e
`Quot.sound`, sem escolha ou axioma novo. Ao fechar essa etapa Geometry contava 64 teoremas
e 14 definições auditados; o submódulo natural continua vazio. Foundation e
seu capstone permanecem byte a byte inalterados. A cadeia adicional fechada é:

```text
torre → zeros sucessivos → divisibilidade por b^k
→ offset balanceado único em níveis positivos → profundidade do centro
→ identificação do mesmo índice k da massa já existente
```

## 23. Do raio crítico ao estado real bidimensional

### INPUT: a escala já selecionada e realizada

A fundação já selecionou a razão formal compatível com composição quadrática.
A camada real já realizou a massa formal e a amplitude correspondente, para
`b>0`:

$$
M_b(k)=\operatorname{realize}(\mu_{b,k})=b^{-k},
\qquad A_b(k)=b^{-k/2},\qquad A_b(k)^2=M_b(k).
$$

A igualdade do quadrado é um theorem anterior,
`realCriticalAmplitude_sq_eq_realDepthMass`. Não a usamos como uma nova
premissa para selecionar metade. A massa continua sendo a realização das
cotas finitas já construídas, não uma nova medida sobre uma torre infinita.

### CONSTRUÇÃO: duas coordenadas e uma energia explícita

Usamos o carrier `RealPlaneState := ℝ × ℝ`. Introduzimos explicitamente:

$$
E(x,y)=x^2+y^2.
$$

Esta é `realPlaneEnergy`. A forma quadrática é uma construção desta camada,
não uma conclusão de que contagem finita, sozinha, produziria uma norma.
Não usamos a norma pronta do produto como definição dessa energia e não
introduzimos uma API de produto interno ou de espaço de Hilbert.

Só então empacotamos a amplitude existente na semente:

$$
\boxed{v_{b,k}=(A_b(k),0).}
$$

`realCriticalDepthSeed` recebe apenas capacidade positiva e profundidade.
Não recebe quantidade, centro, offset, ângulo ou qualquer parâmetro temporal.
É um estado desse nível radial, não um estado global de um inteiro.

### TEOREMA: a energia realiza a massa do mesmo nível

Primeiro, pela própria energia coordenada:

$$
E(v_{b,k})=A_b(k)^2+0^2=A_b(k)^2.
$$

`realCriticalDepthSeed_energy_eq_amplitude_sq` prova essa igualdade. Depois,
reutilizando o theorem escalar anterior, `realCriticalDepthSeed_energy` dá:

$$
\boxed{E(v_{b,k})=M_b(k).}
$$

Não há nova prova de seleção do expoente nem repetição da identidade de
potências. `realCriticalAmplitude_pos` também registra `A_b(k)>0` por
potência real de base positiva; `M_b(k)>0` já estava provado na ponte escalar.

### INTERPRETAÇÃO E LIMITES

A semente escolhe a primeira coordenada como direção de referência para
representar um raio já conhecido. Essa escolha não é uma direção física
selecionada pela teoria. A rotação introduzida em seguida mostrará que a
energia não privilegia essa direção. Não foi construída uma evolução,
um estado por quantidade ou uma aplicação da segunda diferença a esses estados.

No nível basal `k=0`, a semente é `(1,0)` e sua energia é `1`. Em capacidade
`b=1`, isso vale para todo `k`; a realização trivial não recupera a seleção
de expoente que a fundação não fornece nesse regime. Não há semente canônica
de massa positiva para `b=0`, pois o argumento `hb : 0<b` é exigido.

## 24. Rotação sem escolha de fase

### CONSTRUÇÃO: ângulo real arbitrário

Para qualquer `θ : ℝ`, definimos:

$$
R_\theta(x,y)=
(x\cos\theta-y\sin\theta,\;x\sin\theta+y\cos\theta).
$$

Essa é `rotateRealPlane`. A orientação manda `(1,0)` para
`(cosθ,sinθ)`; um quarto de volta positivo manda a semente para o eixo da
segunda coordenada positiva. Não se introduz sentido espectral, tempo ou
lei que determine `θ`. A API usa somente coordenadas reais e trigonometria real.

### TEOREMA: invariância, identidade e composição angular

Expandindo os quadrados, os termos cruzados cancelam e obtemos:

$$
E(R_\theta(x,y))=(x^2+y^2)(\sin^2\theta+\cos^2\theta)=x^2+y^2.
$$

`rotateRealPlane_energy` prova essa identidade usando apenas álgebra e a
identidade trigonométrica. A invariância não é campo de uma estrutura nem
uma hipótese. As fórmulas de adição também dão:

$$
R_0(v)=v,\qquad R_{\theta+\phi}(v)=R_\theta(R_\phi(v)).
$$

São `rotateRealPlane_zero` e `rotateRealPlane_add`. A composição é uma lei
geométrica de ângulos; não implica que tenha sido selecionada uma lei física
para organizar esses ângulos.

### CONSTRUÇÃO E TEOREMA: estado de profundidade com direção livre

Agora, e somente depois da semente e da rotação, definimos:

$$
\psi_{b,k,\theta}=R_\theta(v_{b,k}).
$$

`realCriticalDepthState_eq_coordinates` prova a forma explícita:

$$
\boxed{\psi_{b,k,\theta}=
(A_b(k)\cos\theta,\;A_b(k)\sin\theta).}
$$

A invariância e a energia da semente, por composição, produzem o capstone
`realCriticalDepthState_energy`:

$$
\boxed{E(\psi_{b,k,\theta})=M_b(k)\quad\text{para todo }\theta.}
$$

**A escala radial já possui proveniência na torre e na massa. O ângulo ainda
é um parâmetro livre. Esta rodada não seleciona uma lei de fase.**

### PROVENIÊNCIA: um nível realmente suportado pelo centro

Se o centro balanceado associado a uma quantidade suporta o nível `k`,
podemos registrar a mesma identidade de energia nesse nível por
`balancedCarryDepth_realState_energy`. Sua hipótese de suporte é
intencionalmente desnecessária na prova algébrica: a identidade vale para
qualquer nível. O papel da hipótese é certificar por que estamos usando
esse `k` na leitura carry-derived, não tornar verdadeiro um cálculo falso
fora dos níveis suportados.

O capstone `balancedCarryDepth_realState_realizes_formalMass` expõe juntos:

```text
o canal do offset canônico suporta k
a massa formal nesse k tem campos (1,b^k)
a energia do estado nesse k é a realização real dessa mesma cota
```

O estado ainda recebe somente `(b,k,θ)`. A quantidade aparece na hipótese
de proveniência do centro, não na definição do estado. Não se definiu uma
massa por quantidade, uma amplitude global por quantidade ou um máximo de
profundidade. A ponte de centro permanece ímpar; o plano real só exige `b>0`.

### TESTES, AUDITORIA E PRÓXIMO LIMITE

Base `3`, nível `2`, dá semente `(1/3,0)`, energia `1/9`, a mesma semente
em ângulo zero e `(0,1/3)` em `π/2`. Para qualquer ângulo, a energia continua
`1/9`. Um teste genérico rotaciona `(3,4)` e preserva energia `25`. Outro
usa o nível `2` suportado pelo centro `25` da quantidade `26` em base `5`.
Nível zero e capacidade um têm energia unitária em todo ângulo.

Quinze teoremas novos e cinco nomes de carrier/mapas são auditados na Zona B,
com os axiomas padrão `propext`, `Classical.choice` e `Quot.sound`, sem
axioma adicional. Ao fechar esta etapa, a Analysis contava 29 teoremas públicos auditados.
Foundation e Geometry matemáticas e seus audits permanecem inalterados.

R0 está parcialmente fechado: construímos a geometria quadrática estática
do plano e sua família angular de profundidade. Nessa etapa não construímos
lei de fase, tempo, espectro, operador, norma, bracket real, Green ou câmera.
Nenhum logaritmo aparece nos novos objetos ou argumentos de prova; isso
não afirma que a infraestrutura transitiva de Mathlib dispense logaritmos
ou complexos internamente. O próximo gate deverá introduzir explicitamente
qualquer estrutura adicional, sem reinterpretar o ângulo livre como fase física.

## 25. Reflexão quadrática das pernas

### INPUT: o centro já vem da massa

Fixemos capacidade positiva e profundidade `k`. A massa real e a amplitude
crítica já foram construídas, antes desta geometria. Escrevemos:

$$
C=A_b(k)>0,\qquad M=M_b(k),\qquad C^2=M.
$$

Não definimos um novo centro como raiz da massa, não selecionamos novamente
um expoente e não usamos o bracket como premissa dessas identidades.
A fundação discreta e a geometria inteira permanecem inalteradas.

### CONSTRUÇÃO: uma reflexão multiplicativa

Para um parâmetro real positivo `q`, definimos a reflexão recíproca:

$$
\iota(q)=q^{-1}.
$$

Ela conserva positividade e é involutiva. As duas pernas vêm depois:

$$
L_C(q)=Cq,\qquad R_C(q)=Cq^{-1}.
$$

São `reciprocalReflection`, `quadraticLeftLeg` e `quadraticRightLeg`.
Não se parametriza `q` por uma exponencial nem se identifica essa involução
com a reflexão aditiva de um parâmetro anterior.

### TEOREMA: troca das pernas e conservação do produto

A reflexão troca literalmente as funções das pernas:

$$
L_C(q^{-1})=R_C(q),\qquad R_C(q^{-1})=L_C(q).
$$

Para `q≠0`, a álgebra da inversão dá:

$$
\boxed{L_C(q)R_C(q)=C^2.}
$$

`quadraticReflectedLegs_product` prova a lei genérica. Só então a
especialização `criticalQuadraticLegs_product` usa o theorem anterior da
amplitude e obtém:

$$
\boxed{L_{b,k}(q)R_{b,k}(q)=M_b(k).}
$$

A deformação modifica cada perna, mas sua reflexão recíproca preserva a
quantidade quadrática determinada pelo centro. Não é uma lei assumida como
campo: resulta das pernas construídas e da identidade anterior `C²=M`.

### INTERPRETAÇÃO E LIMITES: duas conservações, não uma identificação

Na geometria aditiva anterior, as pernas `c-a,c+a`, trocadas por `a↦-a`,
conservam a soma `2c`. Agora, `Cq,Cq⁻¹`, trocadas por `q↦q⁻¹`, conservam
o produto `C²`. Temos a mesma arquitetura centro–reflexão–pernas, mas duas
leis de conservação diferentes. Não transportamos ainda entre os dois
parâmetros por uma função exponencial.

`q` atua radialmente nas pernas escalares; `theta` continua um ângulo livre
do estado bidimensional. São parâmetros independentes, sem lei que os ligue.
Não se define um novo estado global por quantidade.

## 26. O bracket como defeito entre centro multiplicativo e centro aditivo

### CONSTRUÇÃO: o readout vem depois das pernas

Introduzimos a versão real da forma centrada de três termos:

$$
D(L,C,R)=L-2C+R.
$$

`realCenteredReadout` não consulta produto, massa ou expoente. Aplicado às
pernas aditivas `C-a,C+a`, ele é zero, como prova
`realCenteredReadout_additiveLegs`. Aplicado às pernas recíprocas já
construídas, ele **define** o bracket local:

$$
\boxed{B_C(q)=D(L_C(q),C,R_C(q)).}
$$

`quadraticCenteredBracket` usa essa aplicação como definição, não uma
fatoração contendo de antemão um quadrado positivo.

### TEOREMA: forma fechada, fatoração e zero central

A expansão e, para `q≠0`, a álgebra da inversão provam sucessivamente:

$$
\boxed{B_C(q)=C(q+q^{-1}-2)=C(q-1)^2q^{-1}.}
$$

A última expressão pode ser escrita `C(q-1)²/q`. Não usamos cálculo ou
convexidade para obtê-la. Sob `C>0,q>0`, quadrado não negativo e inverso
positivo dão:

$$
\boxed{B_C(q)\ge0,\qquad B_C(q)=0\iff q=1.}
$$

Também se prova `B_C(q)>0` se `q≠1`. Em `q=1`, as pernas coincidem com
o centro: `L=R=C`. Fora desse ponto, a simetria multiplicativa permanece
perfeita, `LR=C²`, mas sua leitura aditiva tem defeito estritamente positivo.
Esses resultados têm versões `criticalQuadraticBracket_*` no mesmo `(b,k)`.

### INTERPRETAÇÃO: por que o bracket aparece

A lei `LR=C²` caracteriza o centro positivo como centro geométrico das
pernas. O readout pergunta outra coisa: sua soma é `2C`? As duas condições
coincidem apenas quando as pernas colapsam no centro. A fatoração é a
forma algébrica local dessa diferença entre médias geométrica e aritmética;
nenhuma raiz precisa ser introduzida no código.

**A simetria multiplicativa conserva a massa; o bracket mede quanto ela
se afasta da simetria aditiva do centro.** O bracket lê a segunda configuração
usando a forma aditiva da primeira. Isso não é uma afirmação de que toda
segunda diferença seja assimetria geométrica: a distinção anterior entre
defeito de centro e resposta de observável continua válida.

### TESTES E DOMÍNIOS

Base `3`, nível `2`, tem `C=1/3` e `M=1/9`. Em `q=2`, as pernas são
`2/3,1/6`, seu produto é `1/9` e o bracket é `1/6`. Em `q=1/2` as pernas
trocam e o bracket mantém `1/6`. Em `q=1`, ambas valem `1/3` e o bracket zera.
Esses exemplos são provas Lean, não identificação por cálculo numérico.

Nível zero e capacidade um dão `C=M=1`, produto unitário e bracket
`q+q⁻¹-2`, sem produzir seleção de expoente nesses casos degenerados.
Capacidade zero continua excluída da amplitude canônica. Em Lean, `0⁻¹=0`
é uma convenção de inversão total: a involutividade ainda é verdadeira,
mas a lei de produto não vale em `q=0`. Nesse parâmetro, as pernas são zero
e o bracket vale `-2C`. Por isso o domínio positivo não pode ser omitido.
Se `C=0`, o bracket também zera para qualquer `q`: a hipótese `C>0` no
teorema de zero único é essencial.

## 27. Identidade funcional de reflexão e proveniência da massa

### TEOREMA: a função local preserva a massa refletida

Considere a própria função da perna esquerda `F_C(q)=L_C(q)=Cq`.
A troca das pernas e a lei do produto dão:

$$
\boxed{F_C(q)F_C(q^{-1})=C^2,\qquad
F_{b,k}(q)F_{b,k}(q^{-1})=M_b(k).}
$$

São `quadraticReflection_product` e `criticalQuadraticReflection_product`.
É uma identidade funcional de reflexão **da construção atual**, não uma
equação funcional de função clássica nem uma ponte já provada para ela.

O readout é simétrico nas duas pernas. Portanto, usando sua troca, e não
tomando a forma fechada como origem da simetria, prova-se:

$$
\boxed{B_C(q^{-1})=B_C(q).}
$$

### PROVENIÊNCIA: o produto realiza a cota que veio da torre

`criticalQuadraticLegs_product_realizes_formalMass` expõe literalmente:

$$
L_{b,k}(q)R_{b,k}(q)
=\operatorname{realize}(\operatorname{canonicalResidualDepthMass}(b,k)).
$$

A massa preservada não foi inventada neste módulo. A origem continua sendo
o prefixo e sua normalização coerente. Quando o centro balanceado associado
a uma quantidade suporta `k`, `balancedCarryDepth_quadraticLegs_product`
registra essa proveniência. A hipótese de suporte é desnecessária para a
álgebra do produto; ela justifica qual nível estamos lendo.

`balancedCarryDepth_quadraticReflection_provenance` também compõe o suporte
do canal canônico, os campos formais `(1,b^k)`, o produto como realização
dessa cota e o bracket como readout das mesmas pernas. Não constrói outro
carrier nem assume que um bracket histórico seja igual ao novo objeto.

### AUDITORIA E FRONTEIRA

31 teoremas públicos e oito definições novos têm guard no audit analítico;
ao fechar essa etapa a Analysis contava 60 teoremas públicos. Seu footprint consiste nos
axiomas padrão `propext`, `Classical.choice`, `Quot.sound`, sem adicionais.
Foundation e Geometry e seus audits permanecem sem alterações.

Nessa etapa R1 tinha somente a forma local do bracket, sem câmera,
agregação saturada ou crosswalk histórico. R0 conserva ângulo livre e lei
angular aberta. Não se introduziram parametrização física de `q`, logaritmo,
tempo, estrutura complexa, Green, TFVD ou operador nos novos objetos/provas.
Nenhum resultado daqui retorna como justificativa da massa, de metade ou de
uma norma. O próximo gate pode comparar uma realização histórica local com
este readout, mas terá de provar essa ponte em vez de presumir identidade.

## 28. A câmera ímpar como coleção de pares refletidos

### INPUT: metade da capacidade como dado, não como escolha

A geometria das pernas já existe antes da câmera. Recebemos um natural `h`
e um centro inteiro `c`. A capacidade da câmera é:

$$
b=2h+1.
$$

Essa definição não altera a capacidade emergente da dinâmica. Ela fornece
uma apresentação explícita da câmera no regime ímpar. Quando se parte de
uma capacidade emergente ímpar, seu witness `b=2h+1` pode ser aberto numa
prova e usado como dado. Não deduzimos oddness da dinâmica, nem selecionamos
um witness computacional por escolha clássica.

`oddCapacity_exists_cameraHalf` prova existência e unicidade desse witness;
`oddCameraHalf_unique` compara duas apresentações. Isso não é uma função
que extraia a metade escondida de uma proposição existencial.

### CONSTRUÇÃO: raios positivos e pernas existentes

Os raios são exatamente `1,...,h`. `Fin h` os indexa explicitamente:
o índice `i` representa o raio `i.val+1`. Prova-se o limite, que todo raio
do intervalo tem um índice e que não existem índices repetidos para um raio.
Cada índice produz, pela geometria já construída, o par:

$$
(c-r,c+r).
$$

`oddCameraPair_reflection` reutiliza a troca das pernas pela reflexão em `c`.
`oddCameraPair_straddles_center` prova que as pernas ficam em lados estritos
do centro; `oddCameraPair_injective` impede repetição de pares.
Não usamos primalidade, divisão por dois ou offsets históricos como premissa.

### CONSTRUÇÃO E TEOREMA: enumerar antes de contar

Uma soma recursiva pequena enumera os raios na ordem:

$$
S_0(t)=0,\qquad S_{h+1}(t)=S_h(t)+t(h+1).
$$

É `sumPositiveRadii`, construída apenas com zero e adição. Seu código é
comum às camadas inteira e real, mas as leis algébricas são provadas em
seus respectivos carriers. Geometry não importa Mathlib ou Finset.

A contagem das pernas soma duas unidades em cada raio. Só depois a indução
identifica essa contagem com `2h`, e a apresentação da capacidade dá:

$$
\boxed{\text{número de pernas}=2h=b-1.}
$$

São `oddCameraLegCount_eq_twice_half` e
`oddCameraLegCount_eq_capacity_sub_one`. A potência ou a cardinalidade de
outro carrier não é usada para criar os pares.

### LIMITES

Capacidade composta `9` fornece `h=4`, quatro pares e oito pernas; não
precisa ser prima. Em `h=0`, a capacidade é `1` e não há pares. Isso não
produz seleção fundacional de expoente. Capacidade `2` não é desta forma:
não introduzimos meia coordenada nem resolvemos seu crosswalk antipodal.

## 29. Bracket da câmera como soma saturada

### INPUT E CONSTRUÇÃO: observável sobre a geometria discreta

A API inicial permanece inteira: `F : Int → Int`. Primeiro somamos as
leituras das pernas já construídas:

$$
\operatorname{LegSum}_h(F,c)=
\sum_{r=1}^{h}\bigl(F(c-r)+F(c+r)\bigr).
$$

Só depois definimos o bracket da câmera pela contagem de pernas:

$$
\boxed{\operatorname{CameraBracket}_h(F,c)
=\operatorname{LegSum}_h(F,c)-2hF(c).}
$$

`oddCameraLegSum` precede `oddCameraBracket`. A subtração não é definida
como uma soma de segundas diferenças; queremos provar essa identidade.
Separadamente, `oddCameraSaturatedSecondDifference` soma a segunda diferença
existente, com a mesma convenção de orientação:

$$
\sum_{r=1}^{h}\left[F(c-r)-2F(c)+F(c+r)\right].
$$

### TEOREMA: distribuir as cópias do centro

A distribuição da soma finita e a soma de uma constante dão:

$$
\boxed{\operatorname{CameraBracket}_h(F,c)
=\sum_{r=1}^{h}\Delta^2_{c,r}F.}
$$

Esse é `oddCameraBracket_eq_saturatedSecondDifference`. A prova não importa
um theorem histórico de pareamento: agrupa as duas pernas por raio e
distribui as `h` cópias de `2F(c)` na mesma enumeração.

Em C3, `h=1`, o corolário `oddCameraBracket_C3` reduz a uma única segunda
diferença de raio `1`. Em capacidade `5`, `h=2`, o teste também verifica:

$$
B=F(c-2)+F(c-1)+F(c+1)+F(c+2)-4F(c).
$$

Em capacidade `9`, a identidade soma quatro diferenças. Para `F(x)=x²`
e `c=10`, o resultado testado é `60=2(1²+2²+3²+4²)`.

### INTERPRETAÇÃO E LIMITES

Uma câmera agrupa um conjunto finito de pares refletidos em torno do mesmo
centro. Seu bracket soma a resposta centrada de cada par. A identidade usa
somente esse pareamento e a contagem; primalidade não participa.

Não se conclui positividade para qualquer observável. A identidade tem
bracket zero para a função identidade, mas o teste `F(x)=-x²` em C3 dá
`-2`. A positividade da próxima realização será um theorem com suas próprias
hipóteses, não uma consequência da saturação para `F` arbitrário.

## 30. Câmera quadrática e total não negativo de defeito

### INPUT: a mesma câmera, uma família livre por par

Agora recebemos `C>0` e uma função `q : Nat → ℝ`, exigindo positividade
somente quando `1≤r≤h`. Os valores fora da câmera não são consultados.
Cada raio rotula um par, mas não determina seu valor `q_r`.
Não se escolhe lei de deformação nesta construção.

As pernas locais já provadas são reutilizadas:

$$
L_r=Cq_r,\qquad R_r=Cq_r^{-1},\qquad L_rR_r=C².
$$

### CONSTRUÇÃO: somar brackets locais, não fatorações

Definimos `quadraticCameraBracket` pela mesma enumeração dos raios:

$$
\boxed{B_h^{\rm quad}(C,q)=\sum_{r=1}^{h}B_C(q_r).}
$$

Uma soma das pernas quadráticas é definida separadamente. A álgebra finita
também prova que o total é essa soma menos `2hC`, mantendo a mesma forma
centrada da câmera discreta.

### TEOREMAS: fatoração, positividade e equilíbrio de todos os pares

Somando os teoremas locais e extraindo o centro comum, provamos:

$$
\boxed{B_h^{\rm quad}(C,q)
=C\sum_{r=1}^{h}(q_r+q_r^{-1}-2)
=C\sum_{r=1}^{h}(q_r-1)^2q_r^{-1}.}
$$

O domínio positivo torna cada bracket local não negativo, portanto:

$$
\boxed{B_h^{\rm quad}(C,q)\ge0.}
$$

`sumPositiveRadii_real_zero_iff` prova por indução que uma soma de parcelas
não negativas só pode zerar quando cada parcela zera. Aplicando depois o
zero único do bracket local, obtemos `quadraticCameraBracket_zero_iff`:

$$
\boxed{B_h^{\rm quad}(C,q)=0
\iff \forall r\in\{1,\ldots,h\},\ q_r=1.}
$$

Não há cancelamento de defeitos positivos entre pares. Em `h=0`, a soma
é zero e a condição à direita é vacuamente verdadeira, mesmo que a função
fornecida tenha valores arbitrários fora do domínio vazio.

### TEOREMA: reflexão independente em qualquer subconjunto

Uma máscara booleana fornecida decide quais pares serão refletidos. A
invariância local de cada bracket implica invariância da soma inteira.
`quadraticCameraBracket_independent_reflections` permite qualquer máscara;
inverter todos os pares ou apenas um são corolários. Não se escolhe a
máscara por uma regra física nem se precisa formalizar um grupo abstrato.

O teste `C=1/3`, `h=2`, com entradas `q₁=2,q₂=3`, dá:

$$
B_1=\frac16,\qquad B_2=\frac49,\qquad
B_{\rm cam}=\frac{11}{18}.
$$

Inverter ambos ou somente o primeiro preserva `11/18`; fornecer ambos
iguais a `1` dá zero. São escolhas explícitas de teste, não uma lei canônica
que selecione as deformações. O centro genérico `1/3` desse teste não é
apresentado como amplitude crítica da câmera de capacidade `5`.

### PROVENIÊNCIA: a especialização crítica usa a capacidade da câmera

`criticalQuadraticCameraBracket half k q` usa a amplitude anterior com
base `oddCameraCapacity half=2h+1`. Assim sua base não fica desligada da
coleção de pares. `criticalQuadraticCameraPair_product` prova que cada par
conserva a mesma massa `M_b(k)`. Não se somam essas massas para obter o
bracket; ele soma defeitos, não o produto conservado.

`balancedCarryDepth_quadraticCamera_provenance` registra o suporte carry-derived
do mesmo `k`, os campos `(1,b^k)` da massa formal, a realização dessa massa
no produto de cada par e o total como soma dos brackets locais. O suporte
não é usado para tornar verdadeiras as identidades algébricas.

### LIMITES DA ETAPA DE FAMÍLIA LIVRE: a ponte de valores ainda não existia

Na câmera discreta, `r` desloca o argumento do observável: `F(c±r)`.
Na câmera quadrática, `q_r` deforma o valor radial: `Cq_r,Cq_r⁻¹`.
As duas usam a forma `left-2*center+right`, mas isso **não prova**:

$$
F(c-r)=Cq_r,\qquad F(c+r)=Cq_r^{-1}.
$$

Nessa etapa não se definiu um observável para forçar essa igualdade nem se assumiu
uma lei `r↦q_r`. Era o próximo gap explícito de R1, tratado na seção seguinte
sob uma compatibilidade semântica nova e explícita. O ângulo do plano permanece
independente; não se introduziram fase, logaritmo, tempo ou leituras posteriores.

O total pode ser interpretado como custo não negativo de incompatibilidade
aditiva dos pares multiplicativos. Isso não introduz uma nova norma, nem
identifica esse readout com `realPlaneEnergy` ou com a massa central.

### AUDITORIA

Geometry recebeu 23 teoremas e oito definições, totalizando 87 teoremas e
22 definições guardadas. As definições têm footprint vazio; as provas usam
no máximo `propext` e `Quot.sound`, sem escolha. Analysis recebeu 24 teoremas
e quatro definições, totalizando 84 teoremas públicos, com somente os três
axiomas padrão. Foundation e sua auditoria vazia não foram alteradas.
Ao fim dessa etapa R1 ficava parcial: câmera ímpar e agregação fechadas,
seleção e crosswalk dos valores ainda abertos. C2 continua separado.

## 31. Do offset aditivo ao transporte multiplicativo

### INPUT: uma compatibilidade nova, não uma conclusão da reflexão

Já existiam a geometria dos offsets inteiros, as pernas `c-r,c+r`, a câmera
finita e os brackets quadráticos para uma família livre de deformações.
Nada disso, sozinho, obrigava as deformações de raios diferentes a comporem.
Refletir um par não determina como outro par deve ser realizado.

Introduzimos agora uma especificação semântica explícita para uma função
`Q : Int → ℝ`:

$$
Q(0)=1,\qquad Q(a+b)=Q(a)Q(b),\qquad Q(1)>0.
$$

Ela pede que realizar dois deslocamentos somados seja o mesmo que compor
suas deformações multiplicativamente. Essa é a entrada adicional de
`IsPositiveMultiplicativeOffsetTransport`. Não é apresentada como um fato
extraído da torre residual, da massa ou da reflexão isolada.

### TEOREMA: a reflexão aditiva vira inversão

Como `a+(-a)=0`, a composição e a unidade dão:

$$
Q(a)Q(-a)=Q(0)=1.
$$

Portanto nenhum valor de `Q` é zero, e o fator correspondente à reflexão
é necessariamente o inverso:

$$
\boxed{Q(-a)=Q(a)^{-1}.}
$$

Essa lei não foi adicionada como um campo independente. Os teoremas
`multiplicativeOffsetTransport_product_neg` e
`multiplicativeOffsetTransport_neg` a deduzem da compatibilidade.

### TEOREMA: toda a família é classificada por um passo

Escreva `rho=Q(1)`. Em raio zero, `Q(0)=rho^0=1`. Se a igualdade vale
em `r`, então:

$$
Q(r+1)=Q(r)Q(1)=\rho^r\rho=\rho^{r+1}.
$$

Logo, por indução discreta:

$$
\boxed{Q(r)=\rho^r\quad(r\in\mathbb N).}
$$

A reciprocidade determina os negativos. O passo positivo e seus produtos
têm valores positivos, assim como seus inversos; obtemos `Q(a)>0` para
todo inteiro. A classificação completa é `Q(z)=rho^z`, usando potência
inteira, sem precisar de logaritmo ou exponencial analítica.

### CONSTRUÇÃO E CANONICIDADE RELATIVA AO PASSO

Dado um passo positivo `rho`, definimos `Q_rho(z)=rho^z`. As leis de
potências inteiras provam a unidade, a composição e `Q_rho(1)=rho`.
Qualquer transporte compatível com esse mesmo passo coincide com ele em
todos os inteiros, não apenas nos raios da câmera.

`existsUnique_multiplicativeOffsetTransport` fornece existência e unicidade
para cada passo positivo. **Não seleciona o passo.** Há uma família de
transportes possíveis, parametrizada por `rho>0`. A unicidade é condicional
ao dado unitário, não uma afirmação de que a geometria já escolheu um valor.

### LIMITES

O raio `r` é um deslocamento horizontal; a profundidade `k` é um índice
vertical da torre. Não foi provada uma relação entre o passo horizontal
`rho` e a amplitude ou a massa vertical. A compatibilidade transforma uma
família arbitrária em uma progressão geométrica; a origem do passo continua
como próximo problema independente.

## 32. O perfil multiplicativo centrado

### CONSTRUÇÃO: orientação dos offsets e observável real

Recebemos um centro espacial inteiro `c`, um valor central real `C` e um
transporte compatível `Q`. A orientação é `offset_c(x)=c-x`. Portanto a
perna espacial esquerda tem offset positivo e a direita, negativo.
Construímos o observável:

$$
F_{C,Q,c}(x)=C\,Q(c-x).
$$

Esse é `centeredMultiplicativeProfile`. A definição realiza o transporte
fornecido; não pretende caracterizar todo observável possível na câmera.

### TEOREMA: avaliações e conservação do produto

Os argumentos do transporte nos três pontos são `r,0,-r`. Assim:

$$
\boxed{F(c-r)=C\rho^r,\qquad F(c)=C,\qquad
F(c+r)=C(\rho^r)^{-1}.}
$$

Os teoremas `profile_leftLeg_eq_quadraticLeftLeg` e
`profile_rightLeg_eq_quadraticRightLeg` identificam esses valores com as
pernas quadráticas anteriores. Não são apenas fórmulas parecidas:
as avaliações são literalmente os objetos `quadraticLeftLeg` e
`quadraticRightLeg` nos parâmetros `Q(r)`.

Reutilizando a lei do produto desses objetos:

$$
\boxed{F(c-r)F(c+r)=C^2.}
$$

Se `C=A_b(k)`, o theorem anterior do quadrado da amplitude transforma esse
produto na massa real `M_b(k)`. Não se reconstrói o centro por uma raiz nem
se seleciona novamente o expoente. O suporte carry-derived de `k` pode
registrar a proveniência da camada cuja massa cada par conserva.

### INTERPRETAÇÃO E LIMITES

Trata-se de um caráter multiplicativo do **offset aditivo**: a variável
realizada é `c-x`, não o argumento absoluto `x`. Não identificamos esse
perfil com uma potência de `x` ou com uma razão de ramificação histórica.
O parâmetro angular anterior permanece independente e não entra aqui.

## 33. Crosswalk discreto–quadrático do bracket

### CONSTRUÇÃO: lift real sem modificar a geometria discreta

Na Analysis, `realCenteredSecondDifference` aplica o readout real existente
às duas pernas inteiras e ao centro:

$$
\Delta^2_{\mathbb R}F(c,r)=F(c-r)-2F(c)+F(c+r).
$$

`realOddCameraLegSum`, `realOddCameraBracket` e
`realOddCameraSaturatedSecondDifference` usam exatamente `sumPositiveRadii`,
`leftLeg` e `rightLeg` da Geometry. Como antes, o bracket por soma das
pernas menos cópias do centro é definido independentemente da saturação.
Para qualquer observável `Int → ℝ`, demonstra-se primeiro:

$$
\operatorname{RealCameraBracket}_h(F,c)
=\sum_{r=1}^{h}\Delta^2_{\mathbb R}F(c,r).
$$

Essa igualdade genérica não depende do perfil ou da compatibilidade nova.

### TEOREMA LOCAL E GLOBAL: a mesma leitura nas duas realizações

Somente então aplicamos as avaliações do perfil. Elas dão:

$$
\boxed{\Delta^2_{\mathbb R}F_{C,Q,c}(c,r)=B_C(Q(r))=B_C(\rho^r).}
$$

Somar o crosswalk local sobre os mesmos raios fecha o capstone
`profile_realOddCameraBracket_eq_quadratic`:

$$
\boxed{\operatorname{RealCameraBracket}_h(F_{C,Q,c},c)
=\operatorname{QuadraticCameraBracket}_h(C,r\mapsto Q(r))
=\operatorname{QuadraticCameraBracket}_h(C,r\mapsto\rho^r).}
$$

A prova preserva a cadeia câmera → saturação → brackets locais. Depois
reutilizamos a fatoração e a não negatividade já provadas para a câmera
quadrática:

$$
\boxed{\operatorname{RealCameraBracket}_h(F,c)
=C\sum_{r=1}^{h}\frac{(\rho^r-1)^2}{\rho^r}.}
$$

### TEOREMA: positividade, zero e reflexão do passo

Para `C>0,rho>0`, o bracket do observável concreto é não negativo. Para
`h>0`, o zero total exige que todos os valores `rho^r` sejam `1`; o raio
`1`, presente na câmera, recupera diretamente `rho`. Portanto:

$$
\boxed{\operatorname{RealCameraBracket}_h(F,c)=0\iff\rho=1
\quad(h>0).}
$$

Em câmera vazia (`h=0`), o bracket zera para qualquer passo: não há seleção.
Inverter o passo troca as avaliações das duas pernas, porque
`(rho^{-1})^r=(rho^r)^{-1}`. A invariância estrutural anterior dos pares
prova a invariância global, sem usar a fatoração como origem da simetria.
C3 reduz ao bracket local `B_C(rho)`; capacidade composta `9` usa quatro
pares e funciona sem primalidade. O problema antipodal C2 continua separado.

### TESTE DE ORIENTAÇÃO E TOTAL

Para `C=1/3,rho=2,h=2`, as deformações são `2,4`, não uma escolha independente
por raio. As avaliações das pernas são `2/3,1/6` e `4/3,1/12`; cada produto
é `1/9`. Os brackets são `1/6` e `3/4`, totalizando `11/12`. O passo `1/2`
troca as pernas e preserva esse total; o passo `1` produz total zero.

### ESTADO E AUDITORIA

R1 tem agora o crosswalk do perfil **fechado sob compatibilidade multiplicativa
explícita**. O passo positivo continua livre. Não se afirma que essa condição
foi deduzida da fundação ou que o perfil seja toda a radialidade da teoria.
A seleção do passo, sua ligação com outras estruturas e comparações históricas
são gates posteriores. Nenhuma camada de leituras posteriores é aberta aqui.

Os três módulos acrescentam 44 teoremas e nove definições guardados no audit
analítico, com somente os três axiomas padrão permitidos. Foundation e Geometry,
inclusive seus audits e seleção de escala, não são modificadas. Não se usa
esta nova realização para justificar retroativamente qualquer resultado delas.
