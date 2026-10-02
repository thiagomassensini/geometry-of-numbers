# Plano de execução: proveniência real do carry

Fonte do plano: `PLANO_FORMALIZACAO_TEORIA_REAL_DO_CARRY.md`, fornecido pelo
autor em 2026-09-29. Este resumo orienta a implementação em
`geometry-of-numbers`, o repositório escolhido para esta rodada.
Não substitui os enunciados Lean nem declara fechadas as metas do plano.

## Zonas de confiança

**Zona A — fundação discreta:** quantidade, carry, profundidade,
massa/expoentes e rigidez quadrática. O núcleo de seleção da escala está
encerrado em `FoundationalHalfScalingCapstone`. Isso não fecha outras metas
históricas do plano. A identificação relacional de profundidades foi acrescentada
posteriormente em Geometry, sem alterar esse capstone. Axiomas transitivamente usados:
**nenhum**. Nem `Classical.choice`, nem `propext`, nem `Quot.sound`.
As provas atuais importam apenas `Init`.

**Geometria discreta adicional — `Geometry/`:** centro–pernas, reflexão e
segunda diferença sobre `Int`, somente com Init nos arquivos matemáticos.
Sua auditoria permite `propext` e `Quot.sound`, rejeitando escolha e qualquer
outro axioma. Não pertence ao capstone axiom-free de seleção da escala.
`ResidualTowerDepth` é uma extensão conservativa da API da torre nesta camada,
com footprint vazio verificado separadamente; não modifica Foundation.

**Zona B — análise real:** realiza massa e amplitude e agora constrói o
estado de profundidade em `ℝ × ℝ`, com energia coordenada e rotação de ângulo
livre. Mathlib entra por `Analysis/`; lei de fase, Hilbert, adjuntos, limites
e cálculo funcional continuam posteriores.
Os axiomas usuais são exibidos, não ocultados. Nenhuma representação
complexa justificará um resultado fundacional.

## Ordem e estado

| Fase | Conteúdo | Estado nesta árvore |
| --- | --- | --- |
| F0 | Fidelidade → recorrência → primeiro retorno → carry → torre | Primeiro retorno, reset, torre finita, capacidade prefixal e fibras de refinamento fechados; crosswalk clássico ainda aberto |
| F1 | Centro–pernas, profundidade e resíduo | Geometria e célula ímpar fechadas; profundidade relacional da torre e único offset profundo identificados; máximo/terminação e ramo antipodal par/C2 ainda abertos |
| F2 | Massa/amplitude e rigidez algébrica do expoente `1/2` | Núcleo discreto encerrado em capstone; massa e amplitude reais realizadas em camada separada, com amplitude² = massa |
| R0 | Rotação e estado espectral reais | Estado de profundidade, energia quadrática e rotação abstrata fechados; lei de fase/espectro e estado global de quantidade ainda abertos |
| R1 | Câmeras e brackets reais | Câmera ímpar, saturação e realização quadrática fechadas; ponte offset→deformação e crosswalk do perfil fechados sob compatibilidade multiplicativa explícita, q_r=rho^r; seleção do passo rho ainda aberta |
| R2 | Reconstrução TFVD real, Green e retorno | Não iniciada |
| R3 | Frame global, whitening e isometria | Não iniciada |
| R4 | Fatorização de câmeras pelo mesmo estado global | Não iniciada |
| R5 | Gerador logarítmico e transporte autoadjunto | Não iniciada |
| R6 | Momentos provenientes de operador positivo real; Jacobi | Não iniciada |
| R7 | Operador de alturas e ponte com dinâmica real | Não iniciada |
| R8 | Compatibilidade/convergência e operador limite | Não iniciada |
| R9 | Capstones da álgebra real da teoria | Não iniciada |

## Portas construtivas e capacidade prefixal fechadas

Foi portado o conteúdo de `unitTrajectory_forces_localRecurrence` e
`autonomousLocalDynamics_has_positiveReturn` da fonte, com:

1. capacidade finita apresentada construtivamente, sem escolher uma enumeração
   por axioma de escolha (`FiniteLocalPresentation`);
2. recorrência derivada, não recebida como premissa;
3. retorno inicial derivado de recorrência e injetividade do passo local;
4. primeiro retorno calculado/buscado sem `classical`;
5. auditoria vazia dos teoremas resultantes.

`finiteCodeCollision` prova a colisão entre `N+1` códigos com orçamento `N`.
`autonomousLocalDynamics_has_positiveReturn` cancela o prefixo comum usando
a injetividade do passo. `boundedLeastOrAbsent` busca por indução no orçamento,
e `existsUnique_emergentLocalCapacity` produz o menor retorno `b ≤ N`.
Todos esses teoremas têm footprint vazio.

`EmergentCycleTransport` agora porta a recursão de ciclos/resíduo, sem divisão
ou módulo. A especificação `n = cycles*b + residual`, com `residual < b`, é
provada por indução; qualquer outro par válido coincide com o construído.
O primeiro ciclo dá `(1,0)`. O resíduo preserva o readout original e seu zero
equivale exatamente ao retorno local. A extensão fiel distingue os endpoints.
Os dez teoremas públicos dessa porta também têm footprint vazio.

`EmergentResidualTower` itera a mesma operação sobre os contadores de ciclos.
Seu carrier dependente da profundidade guarda os resíduos e a cauda. Estão
provados os limites, reconstrução, unicidade, truncamento coerente e a
reconstrução `n = prefixValue + tail*b^k`. A potência é consequência dessa
reconstrução; não entra na definição dos dados nem da operação de torre.
Os oito teoremas públicos dessa camada também têm footprint vazio.

`ResidualTowerCapacity` define o prefixo por `PUnit` em profundidade zero e
`Fin b × ResidualPrefix b k` no próximo nível, sem colocar `b^k` na definição.
A avaliação fica abaixo de `b^k`, e a reconstrução força cauda zero quando
`n < b^k`. A torre canônica fornece o decoder; reconstrução e unicidade provam
as duas inversas. A bijeção explícita com `Fin (b^k)` certifica a capacidade
prefixal, separadamente da cauda ilimitada. Os dez teoremas novos e o
empacotamento dos mapas têm footprint vazio.
A eliminação eventual da cauda ainda não está provada aqui.
O crosswalk clássico de normalização continua posterior à construção.
O núcleo **não** esconde recorrência em uma hipótese de carry.
A apresentação finita, autonomia e injetividade são entradas explícitas;
não foram deduzidas de conservação de quantidade isoladamente.
Os ciclos contam passos do relógio externo; não se supõe aritmética no tipo
abstrato de quantidade nem que sua extensão arbitrária seja esse contador.

O capstone de origem documenta hipóteses operacionais adicionais a
fidelidade/capacidade finita. Elas devem permanecer explícitas. Não afirmar
que finitude e fidelidade, sozinhas, forçam toda a notação posicional.

## Quatro fronteiras para a seleção do expoente

1. **Quantity puro:** construir o primeiro retorno único; transportar somente
   `EmergentLocalCapacity` e a prova de `b > 1`. Essa porta está fechada sob
   finitude apresentada, autonomia, injetividade e primeiro passo não trivial.
2. **Geometria residual:** a torre finita, sua reconstrução e a bijeção dos
   prefixos com `Fin (b^k)` estão fechadas. A cota formal `(1,b^k)` foi construída
   por contagem unitária, com invariância por relabeling provada. A unicidade
   usa neutralidade e total normalizado explicitamente. Não inferir uniformidade
   de medidas arbitrárias só de finitude; não contar a cauda ilimitada.
3. **Rigidez discreta:** usar `p, q : Nat`, `q > 0`, sem quociente racional.
   A compatibilidade é agora uma comparação entre o quadrado da escala
   candidata e a composição de `q` cópias da massa derivada. Para `1 < b`,
   ela implica a equação `2 * (k * p) = k * q`, que em profundidade positiva
   equivale a `2 * p = q`. Essa ponte está fechada, com axiomas vazios.
4. **Realização real:** cota formal → divisão real → potência negativa;
   razão formal selecionada → amplitude → quadrado = massa. Essa ponte
   escalar está fechada na Zona B, sem novo argumento de seleção.

Não usar `FoundationalCapstoneAt` como premissa do encadeamento inicial:
esse certificado histórico já contém normalização carry e representação
posicional. O lema `emergentLocalCapacity_gt_one_of_first_step_changes` foi
portado para a interface anterior, sem importar aquele certificado.

O núcleo discreto recebe explicitamente o requisito semântico de composição
quadrática para uma escala candidata; a equação de expoentes é deduzida, não
recebida. Ele não demonstra, por si só, que a contagem produz uma métrica
quadrática. A injetividade das potências naturais para `1 < b` está provada;
a classificação de expoentes reais arbitrários não é refeita aqui.
Sua família formal cobre razões não negativas; a Zona B realiza essas razões
e em particular a já selecionada metade, sem alterar a seleção discreta.

## Normalização neutra: princípio explícito e resultado

`ResidualPrefixNormalization` constrói permutações por transposições e as
transporta pela bijeção prefixal. Invariância sob todas essas mudanças força
igualdade das contagens; soma finita e total `D` dão `weight(x) * b^k = D`.
A cota é comparada a `(1,b^k)` por multiplicação cruzada. A apresentação
canônica usa contagem unitária e calcula o total, não uma massa numérica.

Neutralidade é uma entrada adicional para atribuições arbitrárias e uma
propriedade provada da contagem canônica. Não se presume que uma permutação
do conjunto nu preserve a dinâmica com origem ou os valores reconstruídos.
Um contraexemplo de dois estados impede esconder essa distinção.
Os dez teoremas novos e três definições de transporte/cota têm axiomas vazios.

## Refinamento fechado antes da lei de escala

`ResidualPrefixRefinement` esquece apenas o resíduo mais profundo, não `r₀`.
Extensão, truncamento e leitura da coordenada nova são recursivos; suas leis
inversas provam uma bijeção da fibra de cada pai com `Fin b`. A construção
da fibra e sua cardinalidade não usam identidades de potências. Uma ponte
adicional identifica o truncamento com a extração de prefixos da torre
canônica, inclusive quando a cauda não nula permanece explícita.

A soma das cotas canônicas dos filhos é definida sobre essa parametrização.
Seu numerador vale `b` por soma finita; a identidade de potências verifica
depois a equivalência cruzada com a cota do pai. A lei não é premissa da soma.
`canonicalResidualDepthMass` nomeia a cota existente, independente do prefixo
representante, e herda unidade inicial e conservação pelo theorem da fibra.
Não define uma medida na torre infinita nem usa a rigidez quadrática.

As leis estruturais fazem sentido em `b=0`; sua fibra sobre o prefixo vazio
é vazia. Um theorem prova que agregar zero filhos não pode conservar a
unidade: uma família de massa coerente requer `b>0`.
Dezoito teoremas públicos novos e nove definições têm footprint vazio.

Próximos gates possíveis: agregações finitas mais gerais e interpretação
numérica da normalização. A unicidade de famílias arbitrárias baseada
somente na recorrência de massa não foi provada nesta rodada.
`docs/HUMAN_THEORY.md` acompanha a cadeia em linguagem matemática humana.

## Ponte massa → escala → rigidez fechada

`QuadraticMassCompatibility` importa somente as camadas locais de massa e
rigidez. A identificação `canonicalResidualDepthMass_eq_radixShare` usa a
contagem já derivada; não altera a definição de massa. Produto e potência
de apresentações são multiplicativos, distintos da agregação aditiva de
filhos em `repeatCountingShare`. Suas leis de composição são provadas.

`QuadraticAmplitudeScaleCompatibleAt` compara o produto de duas escalas
`k*p` com a potência `q` da massa em profundidade `k`. Normalização de escalas,
injetividade para `b>1` e o theorem aritmético anterior dão o capstone
`canonicalResidualDepthMass_quadraticCompatibility_iff_half`.
`emergentResidualDepthMass_quadraticCompatibility_iff_half` reutiliza o
primeiro passo não trivial para obter `b>1` da mesma capacidade emergente.

O requisito quadrático é a especificação de uma amplitude candidata; não foi
derivado de finitude, neutralidade ou conservação. Nenhuma hipótese nova de
igualdade de expoentes, métrica ou amplitude numérica é usada. `b=1` e `k=0`
não selecionam expoentes; `q=0` é excluído. Os dezessete teoremas públicos e
quatro definições novos têm footprint vazio. A realização numérica descrita
abaixo não reprova essa rigidez.

## Corte discreto e realização real

`FoundationalHalfScalingCapstone` contém dois teoremas de composição:
o capstone para uma capacidade emergente e a existência de tal capacidade
com o capstone, a partir da apresentação finita e do primeiro passo alterado.
Não acrescenta estruturas, princípios ou provas aritméticas. Seus dois
teoremas têm footprint vazio. **Fim da fundação discreta desta cadeia.**

`Analysis/RealDepthMass` realiza a apresentação formal existente em `ℝ`;
sua equivalência com divisão por `b^k` e potência negativa é provada depois.
`Analysis/RealQuadraticAmplitude` realiza a razão formal, identifica todas
as apresentações de metade e verifica o quadrado da amplitude. A identidade
vale para `b>0`; a rigidez discreta ainda exige `b>1`, `k>0`. Profundidade
zero e base um têm realização trivial, sem selecionar expoente.

O import `GeometryOfNumbers` e o audit fundacional permanecem discretos.
`GeometryOfNumbers.Analysis` é outro import público. O checker de headers
protege essa direção com o parser Lean, não uma regex de imports de uma linha.
`audit-foundation.sh` compila apenas seus alvos e exige footprint vazio;
`audit-analysis.sh` compila seus alvos e permite apenas os axiomas padrão.
Os quatorze teoremas analíticos usam `propext`, `Classical.choice`, `Quot.sound`.

A realização bidimensional/rotacional é acrescentada na etapa abaixo,
recebendo `A²=M` como theorem anterior, não como fonte de uma norma.
Continuam abertos lei de fase, norma, identificação com câmeras/brackets históricos, TFVD, Green, isometrias
e operadores. Não se cria uma medida analítica na torre infinita.

## Regras para as etapas seguintes

### Nova camada discreta, sem reabrir a seleção da escala

`Geometry/CenterLegReflection` define as pernas a partir do centro e raio,
nunca as relações desejadas como campos de um certificado. Reflection
troca as pernas e é involutiva. `IsCenterOf` caracteriza candidatos contra
pernas fixas pela reflexão, e sua equivalência com `left+right=2*candidate`
é provada. Existência e unicidade valem para o par construído; não para
qualquer par de inteiros, como confirma o teste de endpoints `0,1`.

O capstone `centerDefect_fixed_legs_shift` prova `-2*displacement` quando só
o candidato muda. `centerDefect_recentered` prova zero quando também se
reconstroem as pernas. `secondDifferenceAt` distingue nós fixos da configuração
construída em `centeredSecondDifference`; identidade recupera o defeito,
quadrado tem resposta `2*r*r`. Não se universaliza a anulação por simetria.

As entradas públicas agora seguem `Foundation → Geometry → Analysis`;
os arquivos de provas geométricas usam somente Init e as camadas locais
Foundation/Geometry. A fundação matemática e seu audit não foram modificados.
Na etapa abstrata essa organização não provava uma relação da torre com
centro–pernas. A célula ímpar e a relação de profundidades são construídas nas
etapas seguintes registradas abaixo. Também não se
identificaram bracket, Green, tilt ou estados vetoriais com a nova API.

21 teoremas públicos e sete definições são auditados separadamente, com
testes de sinal, raio negativo/zero e observável quadrático. A axiomática
permitida é somente `propext`/`Quot.sound`; todas as definições e a igualdade
definicional da identidade são vazias. O audit da fundação continua vazio.
Não foi criada uma álgebra inteira alternativa para esconder os axiomas
das provas de Init. Essa etapa não recebeu um crosswalk como hipótese.

### Crosswalk local carry → centro/pernas, fechado para capacidade ímpar

`BalancedCarryOffset` recebe os ciclos/resíduos gerados por stepping/reset.
O predicado explícito `IsOddCapacity b` fornece `b=2*h+1`, logo `b>0` e
nenhum resíduo empata em `2*r=b`. As funções de centro/offset exigem essa
hipótese: o ramo `else` não é uma convenção para o antipodal par.

A reconstrução existente fornece `n=q*b+r`; comparar `2*r` com `b` mantém
`(q*b,r)` ou troca para `((q+1)*b,r-b)`. Casts transportam a igualdade
natural para Int, sem reconstituir ciclos por divisão. O centro é múltiplo
da capacidade, e os limites assinados `-b<2*a<b` equivalem a `2*natAbs(a)<b`.
A unicidade usa que a diferença de centros é múltiplo de `b`, mas tem módulo
estritamente menor que `b`; não exige primalidade nem oddness, uma vez
que ambos os representantes estritos existem.

`CarryCenterLegCrosswalk` reaproveita `rightLeg`, `reflect`, `centerDefect`
e `secondDifferenceAt_identity`. A quantidade é a perna `c+a`, a reflexão
é `c-a`, e testar o centro deslocado dá `-2*δ` por composição, não nova
álgebra de defeito. `emergentCapacity_balancedCarry_spec` alinha explicitamente
essa construção ao primeiro retorno da mesma trajetória. Oddness permanece
uma hipótese de regime adicional; não é uma conclusão sobre todo retorno.

O resíduo zero permanece centro; não zero permanece perna não central.
O caso composto `b=9` confirma que primalidade não é input. `b=1` tem apenas
centros, `b=0` está excluído pelo domínio ímpar. Os dois theorems antipodais
de C2 provam ausência de solução estrita em `n=1` e não unicidade no bordo.
C2 não foi resolvido por uma escolha arbitrária.

Há 23 novos teoremas públicos e quatro definições com audit próprio; nenhum
axioma além de `propext`/`Quot.sound`, nenhuma escolha. As definições e o
contraexemplo explícito de não unicidade no bordo são vazios. A fundação
matemática, seu audit e a cadeia massa/metade não foram alterados.

O gate relacional de profundidades é fechado abaixo; máximo/terminação e ramo
par/C2 com regra própria permanecem posteriores. Não se portou uma igualdade
de valuations `effectiveDepth=centerDepth`, nem brackets, Green ou tilt.

### Profundidade relacional e seleção do único canal profundo

`Geometry/ResidualTowerDepth` define `ResidualTowerZeroPrefix` por recursão
nos dados da torre e `HasCarryDepthAtLeast b x k` aplicando esse teste à
torre canônica. Os primeiros `k` resíduos são zero; a cauda é livre.
Profundidade zero é verdadeira, e o sucessor equivale a resíduo zero seguido
da mesma relação no contador de ciclos. Não há valuation, máximo ou terminação
assumida. A API fica fora da Foundation para preservar seu congelamento absoluto.

Para `b>0`, prefixo zero equivale a valor prefixal zero. A reconstrução então
fornece `x=tail*b^k`. Inversamente, um witness de divisibilidade monta apenas
uma tupla comparativa de `k` zeros e a cauda; `residualTower_eq_canonical`
identifica essa tupla com a torre real. Assim `Depth≥k ↔ b^k ∣ x` é teorema,
não definição. Todos os nove teoremas públicos naturais têm footprint vazio,
com guard adicional e cobertura automática no script geométrico.

`Geometry/BalancedCarryDepthCrosswalk` só depois estende a relação para
inteiros por divisibilidade. A restrição aos naturais coincide com a relação
primitiva para capacidade positiva. `balancedCarry_unique` seleciona o offset
de qualquer candidato alinhado `n-a'`. Para `k>0`, `b ∣ b^k` reduz um nível
arbitrário a esse alinhamento, produzindo:

```text
b^k ∣ (n-a') ↔ a'=a ∧ b^k ∣ c          (a' estritamente balanceado)
∃ a' balanceado, Depth≥k(b,n-a') ↔ Depth≥k(b,c)
```

Há também um witness existencial com lei explícita de unicidade. Essa é a
versão relacional pré-valuation da identidade histórica; não define três
funções numéricas de profundidade. O corolário de massa mantém o mesmo `k`
na relação do centro e no numerador/denominador existentes `(1,b^k)`.
Não define massa da quantidade, nem amplitude global por quantidade.

Quantidade/centro zero e capacidade um sobrevivem em todos os níveis.
O contraexemplo `b=0,x=1,k=1` delimita o domínio positivo da equivalência.
A relação natural inclui capacidades pares; a seleção balanceada continua
ímpar. Os testes base `5` selecionam somente `-1` para `n=9` e verificam
os níveis `1,2`, mas não `3`, para centro `25` de `n=26`. C2 não foi resolvido.

Onze teoremas da ponte inteira são auditados com no máximo `propext` e
`Quot.sound`, sem escolha. Ao fechar essa etapa Geometry contava 64 teoremas e 14 definições
auditados. Foundation e Analysis matemáticas permanecem inalteradas.
Não foi abordado o gate opcional de terminação: ficam abertas tanto a prova
de término eventual da cauda quanto a seleção de uma profundidade finita
para quantidades não nulas em capacidade `b>1`.

### Primeiro gate real bidimensional, sem escolha da fase

`Analysis/RealQuadraticPlane` define o carrier coordenado `ℝ × ℝ`, a energia
`x²+y²` e a rotação `(x cosθ-y sinθ, x sinθ+y cosθ)`. Invariância é theorem
de álgebra e `sin²θ+cos²θ=1`, não campo nem uso de uma norma pronta.
Identidade em zero e composição por soma de ângulos também são provadas.
Não se introduz uma API de operadores ou uma parametrização física de θ.

`Analysis/RealCriticalDepthState` constrói primeiro a semente `(A_b(k),0)`
com a amplitude existente, prova energia igual ao quadrado e reutiliza a
identidade escalar para obter massa. Só depois rotaciona a semente e deriva
coordenadas explícitas e energia igual à massa para todo θ. Positividade da
amplitude usa potência real de base positiva; massa positiva já estava provada.

A ponte `balancedCarryDepth_realState_energy` recebe suporte do mesmo `k`
pelo centro, deixando documentado que essa hipótese é de proveniência,
não necessária para a álgebra. O capstone conjunto mostra o canal canônico,
campos da massa formal `(1,b^k)` e energia como realização dessa cota.
Não constrói um estado de `n`, nem escolhe profundidade máxima ou fase.

Hipótese radial: `b>0`. Base um e nível zero dão semente `(1,0)` e energia
unitária, sem reabrir a rigidez discreta. A ponte de centro exige capacidade
ímpar, mas a construção do plano não. O domínio não admite massa canônica
para `b=0`. Os testes verificam base `3`, nível `2`, quarto de volta,
energia preservada para `(3,4)` e o nível `2` do centro `25` de `26`.

Quinze teoremas públicos e cinco nomes de carrier/mapas são auditados nesta
etapa; ao fechar o plano Analysis contava 29 teoremas públicos. Footprint padrão de Mathlib,
sem axioma adicional. Foundation e Geometry ficam byte a byte inalteradas,
e os checkers continuam impedindo a dependência reversa.

R0 está **parcialmente** fechado: geometria radial/angular estática.
Lei de fase/espectro, estado global por quantidade, segunda diferença real,
norma, câmeras e demais camadas permanecem gates posteriores. Nenhum
logaritmo ou tempo foi introduzido nos novos objetos ou provas.

## Reflexão recíproca e bracket centrado local

`Analysis/QuadraticReflection` parte do centro como entrada e define a
involução `q↦q⁻¹`, seguida das pernas `C*q,C*q⁻¹`. Sua troca e a lei de
produto são teoremas. A especialização recebe `realCriticalAmplitude`,
reutiliza seu quadrado e identifica o produto com `realDepthMass`, inclusive
como realização literal da massa formal anterior. Não há nova massa.

`Analysis/QuadraticCenteredBracket` define primeiro o readout real de três
termos e depois o aplica às pernas. A forma fechada e a fatoração são
provadas. Em `C>0,q>0`, quadrado e inverso positivo dão não negatividade,
zero somente em `q=1` e positividade fora do centro. A reflexão apenas troca
as pernas, preservando o readout simétrico. A identidade funcional de
reflexão é da função local `F_C(q)=C*q`, não de uma função clássica.

A mesma arquitetura possui conservações distintas: pernas aditivas conservam
soma; pernas recíprocas conservam produto. A leitura aditiva da conservação
multiplicativa produz o bracket. Isso não identifica a geometria inteira
com a amplitude escalar nem constrói uma câmera.

O capstone de proveniência expõe suporte do canal canônico, campos formais
`(1,b^k)`, produto como realização da massa e bracket como readout das mesmas
pernas. A profundidade não é necessária para provar essas identidades.
Base positiva basta para a amplitude; a ponte de centro continua ímpar.
Zero profundidade e base um têm centro unitário sem reabrir seleção de
expoente. `q=0` não satisfaz a lei do produto e dá bracket `-2*C`.

31 teoremas públicos e oito definições entram no audit analítico; então 60
teoremas. Footprint padrão, sem axioma novo. Nessa etapa Foundation e Geometry ficam
inalteradas. Nenhum import histórico ou pacote novo entra na construção.
R1 era **parcial**: forma local fechada; câmera e agregação são acrescentadas
na etapa abaixo, sem identificação histórica. R0 mantém ângulo livre; `q` não
é `theta`. Não há lei de fase, parametrização exponencial, tempo ou
identificação analítica posterior nessa etapa.

## Câmera ímpar: geometria discreta antes da realização quadrática

Gate A está em `Geometry/OddCamera` e `Geometry/OddCameraBracket`, apenas
com Init e imports locais da Geometry/Foundation. `half` é dado computável;
`oddCapacity_exists_cameraHalf` abre o witness somente dentro de uma prova
de existência e unicidade, sem uma definição não computável da câmera.
`Fin half` enumera raios positivos sem duplicação; cada raio fornece duas
pernas da API existente, em lados opostos do centro. Reflexão troca o par.
A contagem recursiva de duas pernas por raio é identificada com `2*half`
e depois com `b-1`. Não há hipótese de primalidade.

A soma genérica `sumPositiveRadii` usa somente zero e adição para construir
a enumeração. Seus lemas necessários são especializados aos carriers Int
e real nas respectivas camadas; não se recria uma biblioteca de Finset.
O bracket discreto é soma das pernas menos `2*h` cópias do centro.
A saturação soma a segunda diferença existente e tem definição separada.
Sua igualdade é provada por distribuição finita e soma de constantes.
C3 reduz a uma segunda diferença; base `5` dá dois pares; base composta
`9` dá quatro. Observáveis arbitrários podem produzir valores negativos.

Gate B está em `Analysis/QuadraticCameraBracket`. Recebe `q_r` como entrada
livre, positiva no domínio, e define o total somando brackets locais.
O theorem por soma de termos não negativos e total zero elimina cada
defeito e usa o zero local para recuperar `q_r=1`. A fatoração total vem
depois da definição. Uma máscara booleana permite refletir pares de modo
independente; todos/um par são corolários, sem construir um grupo abstrato.

A versão crítica usa `b=oddCameraCapacity half`, não uma base desligada da
câmera. Cada par preserva a realização da mesma massa de nível `k`; não
se declara soma de massas ou energia de plano igual ao bracket. Suporte
carry-derived registra proveniência do índice, não necessidade algébrica.
Base um tem zero pares, com total zero e condição de equilíbrio vacuamente
verdadeira. C2 não recebe uma metade artificial e permanece aberto.

Ao encerrar a etapa de câmera livre, R1 era **parcial**: câmera ímpar e agregação
saturada fechadas, ainda sem uma lei `r↦q_r` ou ponte entre os valores
`F(c±r)` e as pernas `C*q_r^{±1}`. A identidade de saturação discreta não
fornece essa ponte. A família livre não é uma prova de que um observável
arbitrário possua tal realização. R0 permanece separado, sem fase nova.

23 teoremas e oito definições novos em Geometry (totais 87/22); 24 teoremas
e quatro definições na Analysis (84 teoremas ao todo). Guards incluem todos
os nomes novos. Geometry admite somente propext/Quot.sound, sem escolha;
Analysis mantém os três axiomas padrão, sem adicionais. Foundation, seus
capstones e sua auditoria vazia permanecem inalterados.

## R1: compatibilidade dos offsets e crosswalk do perfil fechados

Três módulos novos, todos em Analysis, compõem as APIs anteriores:

1. `MultiplicativeOffsetTransport`: especificação explícita `Q(0)=1`,
   composição `Q(a+b)=Q(a)*Q(b)` e passo positivo `Q(1)>0`. Não se diz que
   essa compatibilidade foi derivada da torre. Prova reciprocidade a partir
   de `a+(-a)=0`, classificação natural por indução, positividade global,
   classificação inteira e existência/unicidade do transporte `rho^z`.
2. `CenteredMultiplicativeProfile`: perfil `C*Q(c-x)` sobre pontos inteiros.
   Avaliações esquerda/centro/direita identificam literalmente as pernas
   quadráticas; produto e segunda diferença reutilizam leis locais anteriores.
3. `OddCameraQuadraticCrosswalk`: lift real com pernas/enumeração existentes,
   saturação genérica antes de especializar ao perfil. O capstone passa por
   soma das segundas diferenças → soma dos brackets quadráticos locais.

A nova compatibilidade reduz a família livre a `q_r=rho^r`, com UM passo
positivo livre. Ela não seleciona esse passo. `r` continua horizontal e `k`
vertical; não se usa amplitude, capacidade ou massa para identificar `rho`.
O perfil de offsets não é uma potência do argumento absoluto e não assume
`branchRatio` ou um tilt histórico. Não se introduzem parametrizações
analíticas posteriores para provar a classificação discreta.

Positividade do bracket do perfil decorre do crosswalk. O zero equivale a
`rho=1` somente em câmera não vazia, pois o raio 1 recupera o passo. Em
`half=0`, qualquer passo tem bracket zero. A inversão do passo troca pernas
e preserva o total pelo theorem estrutural de reflexão da câmera quadrática.
C3 tem corolário explícito leitura nos pontos = bracket local. Foram testados
capacidade composta 9, o total `11/12` para dois pares e `367/48` para quatro
pares (`C=1/3,rho=2`), além da troca pontual com passo `1/2` e do perfil
constante para passo `1`. As formas por divisão são corolários da fatoração.
O transporte importa somente `Mathlib.Data.Real.Basic`, com guard que exclui
`Real.log` e `Real.exp` desse módulo.

A especialização crítica reutiliza amplitude e massa já realizadas; o
suporte carry-derived registra o MESMO índice `k`, sem participar da
classificação horizontal. R1 fecha o crosswalk sob a especificação nova;
seleção do passo, comparações históricas e R2 permanecem posteriores.

47 teoremas públicos e nove definições do transporte/crosswalk entram no audit de Analysis,
com footprint limitado aos três axiomas padrão. Foundation/Geometry e seus
audits não são alterados. A direção de imports permanece unilateral.

- Reusar uma prova somente após comparar seu tipo e suas dependências.
- Manter mapas, estados, parâmetros e domínios antes de scalarizar.
- Separar gerador com frequências `log n` de operador de alturas.
- Para `VLV*`, provar isometria e domínio; não tratar demonstração numérica
  como teorema infinito.
- Não declarar compatibilidade literal entre cutoffs quando o whitening muda.
- Não fabricar momentos ou inserir uma lista externa de alturas.
- Uma fase só fecha quando seu capstone compila e sua auditoria passa.
- Nenhuma meta incompleta será representada por um placeholder de prova.


## Forma Centro–Pernas: dois gates fechados

| Gate | Estado | Resultado e fronteira |
| --- | --- | --- |
| Forma local | CLOSED | Definição vetorial pelas três posições; fatoração e energia quartica; independência angular; zero central sob energia positiva |
| Forma na câmera | CLOSED | Soma de energias locais; fatoração canal a canal; zero sem cancelamento; fator radial comum vezes energia inicial total |
| Atlas all-bases | OPEN | Falta investigar uma lei que distribua a mesma informação entre bases diferentes; massa dentro de uma base não fornece essa lei |

`CenterLegForm` já integra main desde `698778b`. `CenterLegCameraForm` usa
somente essa API e `sumPositiveRadii`; não introduz um carrier de atlas.
Ângulos locais permanecem na definição. Não se identifica soma de energias
com energia da soma dos vetores, nem soma ponderada de quadrados locais
com quadrado do bracket escalar total. Ambos os erros têm contraexemplos
formais no audit. Zero comum exige somente `q≠0` e energia inicial total
positiva; câmera vazia não seleciona `q`. A massa crítica da especialização
é anterior a essas formas. São 26 teoremas e seis definições adicionais,
auditados na mesma política analítica; nenhuma alteração em Foundation/Geometry.
