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

Ainda não construímos estado rotacional, espaço vetorial, produto interno,
norma, câmeras, brackets, TFVD, Green, isometria ou operador. `A²=M` é uma
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
fecha uma célula carry → centro/pernas para capacidade ímpar; a identificação
de profundidades da torre continua pendente.

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

Fechou uma célula: carry existente → centro/offset canônicos no regime
ímpar → pernas refletidas. Não identificamos profundidade do centro com
profundidade efetiva da quantidade, nem construímos brackets históricos,
Green, tilt ou estado rotacional. Essas são pontes posteriores.
