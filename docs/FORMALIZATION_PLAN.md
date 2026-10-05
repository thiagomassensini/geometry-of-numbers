# Plano de execução: proveniência real do carry

Fonte do plano: `PLANO_FORMALIZACAO_TEORIA_REAL_DO_CARRY.md`, fornecido pelo
autor em 2026-09-29. Este resumo orienta a implementação em
`geometry-of-numbers`, o repositório escolhido para esta rodada.
Não substitui os enunciados Lean nem declara fechadas as metas do plano.

Atualização da consolidação de 1–2/10/2026: o [índice de recuperação](RECOVERY_2026-10-02.md)
registra o checkpoint anterior das etapas C2 e Green/Parseval. Atualização de 3/10: as rodadas 9–17 foram recuperadas em Analysis deste repositório canônico; o carry é somente fonte histórica de leitura.
As seções de implementação posteriores conservam seus checkpoints históricos.

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

**Zona B — realização real e camadas downstream de análise:** realiza massa e amplitude e agora constrói o
estado de profundidade em `ℝ × ℝ`, com energia coordenada e rotação de ângulo
livre. Mathlib entra por `Analysis/`. As camadas downstream recuperadas agora incluem fase material, Hilbert, adjuntos, limites e normalização de frame; nenhuma delas redefine a fundação real.
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
| R2 | Reconstrução TFVD real, Green e retorno | CLOSED — reconstrução discreta/projetiva, gauge crítico e TFVD real com análise/síntese |
| R3 | Frame global, whitening e isometria | Source C2 global isométrica nesta árvore; análise raw e whitening canônico certificados na Analysis canônica recuperada, com Gram raw não identidade |
| R4 | Fatorização de câmeras pelo mesmo estado global | Source física C2 e proveniência fechadas; embedding concreto Green em Analysis. Não se presume uma fatorização geral ainda não provada |
| R5 | Gerador logarítmico e transporte autoadjunto | CLOSED na Analysis canônica recuperada para o material log clock: domínio maximal, transporte Parseval e grupos fortemente contínuos; órbita C2 global sem gate de domínio |
| R6 | Momentos provenientes de operador positivo real; Jacobi | Jets e dependência triangular finitos certificados em Analysis; identificação integral com completion e Jacobi históricos mantém gaps explícitos |
| R7 | Operador de alturas e ponte com dinâmica real | Construção finita positiva e ledger em Analysis; HISTORICAL_SCALARIZATION_MISMATCH na ponte histórica. Nenhuma identificação com o clock material |
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
| Atlas all-bases | INTERFACE ONLY | STRUCTURAL PASS: partição admissível implica conservação e preservação da Forma; seleção canônica entre bases continua OPEN |

`CenterLegForm` já integra main desde `698778b`. `CenterLegCameraForm` usa
somente essa API e `sumPositiveRadii`; não introduz um carrier de atlas.
Ângulos locais permanecem na definição. Não se identifica soma de energias
com energia da soma dos vetores, nem soma ponderada de quadrados locais
com quadrado do bracket escalar total. Ambos os erros têm contraexemplos
formais no audit. Zero comum exige somente `q≠0` e energia inicial total
positiva; câmera vazia não seleciona `q`. A massa crítica da especialização
é anterior a essas formas. São 26 teoremas e seis definições adicionais,
auditados na mesma política analítica; nenhuma alteração em Foundation/Geometry.


## Auditoria all-bases: STRUCTURAL PASS, seleção INTERFACE ONLY

A busca nos módulos Foundation/Geometry/Analysis identificou normalização e
conservação de prefixos DENTRO de uma base, mas nenhuma distribuição derivada
entre bases. `AtlasEnergyPartition` acrescenta uma interface explicitamente
parametrizada: pesos não negativos, envelope finito por coordenada, peso zero
fora do envelope e soma unitária. Finitude do suporte real, soma `finsum` de
pesos/energias e conservação dos estados ponderados são teoremas.

`CenterLegAtlasForm` soma câmeras existentes, cada qual com seus estados
ponderados e ângulos locais. Prova fatoração canal a canal, não negatividade,
zero sem cancelamento, independência angular, fator radial comum vezes energia
inicial total e zero iff `q=1` sob energia inicial positiva e `q≠0`.
Partições admissíveis distintas têm a mesma energia no defeito comum; isso
não seleciona nenhuma delas. O audit testa partições admissíveis distintas,
base composta 9, canais nulos, resolução vazia e o domínio excluído `q=0`.

**Menor gap:** derivar/selecionar uma distribuição entre bases a partir da
geometria residual, com a proveniência aritmética dos pesos. Nenhuma regra
logarítmica, valuation ou normalização arbitrária foi escolhida para fechar
esse gap. A interface não conta como existência canônica derivada.
O escopo provado resolve coordenadas finitas com rótulos em todas as bases
`b≥2`; soma infinita de entradas e identificação das câmeras ponderadas com
realizações carry de cada base não foram feitas. Nenhum Gram histórico,
completion ou packing foi transportado.


## Vozes primas: partição de quantidades, crosswalk de canais aberto

| Gate | Estado | Evidência e fronteira |
| --- | --- | --- |
| PRIME-DEPTH-CROSSWALK | CLOSED | Torre residual → divisibilidade já provada → thresholds de Nat.factorization, para primo p e n≠0 |
| PRIME-VOICE-DECOMPOSITION | CLOSED | Produto único de potências primas e soma finita das vozes igual a log n; exponentes caracterizados pela relação residual |
| PRIME-VOICE-PARTITION | NONSEED-ONLY | Pesos não negativos, suporte finito, soma finita e finsum iguais a 1 DERIVADOS para quantidades n>1 |
| PRIME-PARTITION→ATLAS | INDEX-CROSSWALK-OPEN | Quantidade n não é canal r; falta transporte semântico, e pesos literais em n=1 contradizem a interface total |

Resultado B: PRIME PARTITION PASS / INDEX GAP. A obstrução seed também é
formal: a família literal de pesos não pode instanciar AdmissibleAtlasPartition,
que exige soma unitária em TODO natural. Não houve fallback de base, deslocamento
de índice, alteração da interface ou construção ad hoc de seed. A arquitetura
seed-plus-quantidade não foi derivada dos estados críticos existentes.

O crosswalk discreto fica em Analysis para respeitar a proibição de imports
Mathlib em Geometry. Não usa Real.log nem redefine a profundidade. O módulo
PrimeCarryVoice introduz logaritmos somente downstream, pela fatoração única;
esses logaritmos não classificam o transporte horizontal nem selecionam rho.
São dois módulos, duas definições e 24 teoremas, com 26 nomes públicos auditados.
Foundation/Geometry, dependências e políticas de axiomas permanecem congeladas.

A Forma local e a câmera continuam CLOSED. O atlas coordenado continua
INTERFACE ONLY para uma instanciação aritmética dos canais atuais: a partição
prima de quantidades é um avanço derivado, mas ainda não fornece essa instância.
Os critérios parametrizados de energia/ângulos/zero da Forma permanecem válidos.
**Menor gap:** quantity-index → camera-channel-index crosswalk, com tratamento
legítimo do seed; não a identidade de fatoração ou um gap histórico de Parseval.
Reconstrução prima não prova combinação linear de câmeras compostas.


## R2 — reconstrução mínima encerrada

Antes de R2 ou posteriores, ler R2_TFVD_GREEN_VALVE_ROUTE.md.
Resultado A: FULL R2 PASS. Todos os capstones vivem em Analysis.

| Gate | Estado | Evidência |
| --- | --- | --- |
| R2-DISCRETE-FUNDAMENTAL-THEOREM | CLOSED | realDiscreteGreenReconstruction; kernel afim |
| R2-GREEN-KERNEL | CLOSED | one_sub_X_sq_mul_greenKernelSeries; mk_discrete_valve |
| R2-PROJECTIVE-GREEN | CLOSED | round-trips, jacobiano Green e derivative_toProjective_greenLogPotential |
| R2-MULTIPLICATIVE-VALVE | CLOSED | derivative_projectiveValveMass, ambos os round-trips e projectiveValveMass_add |
| R2-DISCRETE-PROJECTIVE-RECONSTRUCTION | CLOSED | realDiscreteProjectiveReconstructionEquiv |
| R2-CRITICAL-GAUGE | CLOSED | razão derivada da amplitude no nível um; realCarryWeightedSecondDifference_gauge e GreenSum_gauge |
| R2-REAL-TFVD | CLOSED | operadores contínuos em ℓ²(ℕ,ℝ), TrR=I, BR=0, GB+RTr=I |
| R2-ANALYSIS-SYNTHESIS | CLOSED | realCarryTfvdSynthesis_comp_analysis; especialização crítica |

R2 closes reconstruction. Head/tail and moment transport belong downstream.
R3 recebe análise/síntese; Gram T* T, normalização/whitening e isometria não
foram implementados. Os gaps de atlas/seed das rodadas anteriores continuam
abertos e independentes desta reconstrução. Nenhuma complexificação, dependência
histórica ou mudança em Foundation/Geometry foi usada para fechar R2.

### Recovery round 9: PASS_RESTRICTED_GRAM

Ported to local Analysis: `C2GlobalGreenBridge`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 10: PASS

Ported to local Analysis: `C2GreenPreStencilCanary`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 11: PASS

Ported to local Analysis: `C2BaseTwoGreenLedger`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 12: PASS

Ported to local Analysis: `C2GreenTemporalMeanCanary`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 13: PASS

Ported to local Analysis: `C2GreenWhiteningGenealogy`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 14: PASS_DOMAIN_GATE_OPEN

Ported to local Analysis: `GreenStateMaterialLogGenerator`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 15: PASS

Ported to local Analysis: `GreenParsevalMaterialLogOperator`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 16: PASS_C2_ORBIT

Ported to local Analysis: `GreenStateMaterialEvolution`, `GreenParsevalMaterialEvolution`. Original hypotheses, open gaps and no-go quantifiers preserved.

### Recovery round 17: HISTORICAL_SCALARIZATION_MISMATCH

Ported to local Analysis: `FiniteMaterialClockJets`, `FiniteClockHeightLedger`, `FiniteHistoricalChebyshev`. Original hypotheses, open gaps and no-go quantifiers preserved.


## Base-two exact whole-cell head/tail completion

Status: `PASS_EXACT_HEAD_TAIL`. Local module:
`GeometryOfNumbers.Analysis.BaseTwoExactHeadTailCompletion`;
report: `docs/BASE_TWO_EXACT_HEAD_TAIL_COMPLETION.md`.

| Gate | Status | Local theorem |
| --- | --- | --- |
| Existing critical material orbit | CLOSED | `criticalMaterialSample_eq_finiteMaterialOrbit` |
| Geometric camera-2 complete cells | CLOSED | `baseTwoCriticalCenterCell_eq_causalUnitBracket` |
| Literal existing finite-head readout | CLOSED | `baseTwoFiniteHead_eq_historicalFiniteHeadReadout` |
| Absolute summability of complete cells | CLOSED | `summable_norm_baseTwoCriticalCenterCell` |
| Derived whole omitted-cell tail | CLOSED | `baseTwoCriticalCompleteTail_hasSum` |
| Exact head + tail | CLOSED | `baseTwoFiniteHead_add_completeTail` |
| Arbitrary cutoff independence | CLOSED | `baseTwoCompletedSignal_cutoff_independent` |
| C2 endpoint incidence | CLOSED | `baseTwo_endpoint_incidence`; first omitted triple `(4M+3,4M+4,4M+5)` |
| Existing clock jets are jets of this head | CLOSED | `baseTwoFiniteHead_normalizedClockJet` |
| Replace downstream external tail | CLOSED in new base-two path | `baseTwoClosedResponseSeries_eq_synthesized`; general ledger unchanged |
| Infinite tail jet tower | CLOSED via synthesis and smooth subtraction | `baseTwoSynthesizedTailCoefficient_eq_normalizedTailJet`; no termwise derivative/sum claim |
| Modern C2/Green source to historical full scalarization | OPEN / mismatch active | This round identifies the historical head only |

The estimate preserves whole-cell second-difference cancellation and uses only
current local APIs and Mathlib. R2, Foundation, Geometry, moment transport and
finite-height modules are unchanged. Both historical files provide comparison
provenance only, with no historical package dependency.


## R6/R7: synthesis before scalarization, block 1

`BaseTwoSynthesizedClockCompletion`: `PASS_DERIVED_TAIL_JETS` at the normalized
iterated-derivative coefficient interface. Complete function equality precedes
all-order jet extraction. Tail coefficients are uniquely derived residuals;
no free tail is used to define them. Actual analytic/Taylor recovery and tail
termwise differentiation are not asserted. Ledger/moment specialization follows
in a separate validated increment; dressing and global Gram seams remain open.
See `SYNTHESIS_BEFORE_SCALARIZATION_CLOCK_MOMENTS.md`.


### Synthesized base-two response and moments — block 2

`BaseTwoSynthesizedClockMoments` closes the formal ledger seam: no free tail,
response/phi/moments cutoff-independent for fixed cameraFactor and completion,
unique log-derivative moment sequence under the existing phi(0) != 0 gate.
No Gram or height proof is used. Dressing remains external; the modern-source
crosswalk and complete-signal analytical recovery remain separate open gates.
The general externalTail_changes_phi_zero theorem remains unchanged.


### Synthesized complete-signal regularity — block 3

`BaseTwoCompletedSignalRegularity` closes local analyticity and all-order
regularity of the complete base-two signal using a locally uniform summable
whole-cell bound. The derived tail coefficient is the actual normalized jet
of the existing tail, by smooth subtraction after synthesis. No termwise
infinite-tail differentiation is required.

Status of the preceding synthesis round: `PASS_SYNTHESIZED_CLOCK_MOMENTS` at the historical material
orbit / fixed explicit dressing / nonzero phi(0) interface. The new base-two
path has no arbitrary tail input. Common-camera/completion dressing, modern
provenance-correct C2/Green source to the historical observable, and Gram/Hankel
positivity remain OPEN. Historical scalarization mismatch is REDUCED and still
active at those seams. Existing guardrail externalTail_changes_phi_zero remains.

### Canonical dressing / concrete moment seam — increment A

Exact base-two camera denominator, entire complex extension, real-line
nonvanishing and normalized Taylor germ: CLOSED in
`BaseTwoCanonicalCameraDressing`. Completion, dressed response all-order
crosswalk, concrete phi(0) and definitive moment sequence remain OPEN at this
increment. Dressing is downstream; no Gram positivity is asserted.

### Canonical dressing — increment B

Explicit polynomial/pi-exponential/Gamma completion, local analyticity,
normalized germ and nonzero center: CLOSED in
`BaseTwoCanonicalArchimedeanDressing`. No xi/zeta identification is imported.
All-order dressed-response coefficients and concrete phi(0) remain next gates;
completion never supplies a premise for the already-derived geometry.

### Concrete canonical response and moments — increment C

Status: `PASS_CANONICAL_DRESSING_MOMENTS`.
`BaseTwoCanonicalDressingMoments` closes the local analytic dressed function,
its all-order factorial-normalized response series, concrete real-even phi,
direct phi(0)>0 proof, unique formal log-derivative sequence and cutoff
independence. The canonical path has no free tail/cameraFactor/completion.
The general ledger and external-tail guardrail are unchanged.
No Gram/Hankel positivity is inferred. The next gate is the actual global
orthogonal Green jet/readout representation of these moments, preserving the
still-open modern depth-amplitude source to material-amplitude observable
crosswalk and the Taylor/Green jet seam. Historical mismatch is REDUCED, not
wholly erased. No height or spectral identification is claimed.


## Canonical Green moment Gram — current round

Starting main `9d6b687cc7a2b7d57e37c94cc644f1a79696ff0f`.

| Gate | Status | Evidence |
| --- | --- | --- |
| Neutral parity Gram → both Hankel PSD sections | CLOSED, generic | `hankelPair_posSemidef_of_parityMomentGram` |
| Neutral parity Gram + independent prefixes → both PD sections | CLOSED, generic | `hankelPair_posDef_of_parityMomentGram` |
| Actual synthesized Green first column = canonical moments | OPEN | Concrete readout identification remains an independent obligation |
| Concrete full parity Gram | OPEN | Not inferred from Parseval isometry or scalar analyticity |
| Concrete even/odd independence, all-order PSD/PD | OPEN | Generic implications alone do not prove their premises |

See `CANONICAL_GREEN_MOMENT_GRAM.md`. No source amplitude is changed;
no residual-zero assumption, scalar Gram or moment-manufactured carrier is added.


### Exact Parseval transport; canonical first column remains open

`CanonicalGreenMomentJetSeam` proves transport of normalized jets of the
existing full C2 vector orbit, invariance of their real pairings and first-column
residual, and equivalence of Hilbert regularity before and after Parseval.
The first strong derivative is equivalent to the existing logarithmic moment.
No generator power is applied without domain proof.

Status: `PASS_PARITY_GRAM_TRANSPORT_FIRST_COLUMN_OPEN`.
The orbit-jet first column is a diagnostic candidate, not a certified completed
boundary Green readout. Its zeroth pairing is exactly the core norm squared.
The actual vector completed/dressed boundary readout and its equality with the
canonical log-derivative column remain OPEN. Scalar analyticity does not prove
that identity. Concrete PSD, mixed orthogonality, independence and PD remain
OPEN; no downstream operator construction is started.

## Real TFVD center–leg seam (2026-10-03)

Neutral real polarized coefficient algebra is CLOSED in
`PolarizedMomentCoefficients.lean`. Concrete incidence/TFVD transport and the
completed canonical center–leg readout remain OPEN; no new Hankel positivity
is claimed. See `REAL_TFVD_CENTER_LEG_MOMENT_SEAM.md`.

Real C2 vertical-fiber analysis/synthesis and incidence independence are
CLOSED in `C2RealFiberTfvdIncidence.lean`. The faithful analysis retains core,
sign and both quadratures; depth is `j+2`. Its incidence vectors are not yet
completed canonical moment jets. The completed real center–leg readout and
canonical parity Gram remain OPEN.

The real completed center–leg target is now explicitly typed in
`RealTfvdCenterLegMomentSeam.lean`. The bare coordinate incidence basis is
proved **not** to realize a parity Hankel kernel (even `(0,2)` versus `(1,1)`);
this excludes that representation only. Status:
`PASS_REAL_TFVD_INCIDENCE_TRANSPORT_CENTER_LEG_OPEN`. Completed real bilinear
readout → canonical moments → canonical Gram/PSD/PD remains OPEN.

## Vertical quadratic norm → canonical moment Gram audit (2026-10-04)

Status: `NO_GO_ISOMETRIC_INCIDENCE_SYNTHESIS`.
Starting main `e0145b7f8e062de5e741e6225149c56e0654d701`.

`VerticalIncidenceGramObstruction` reconstructs whole branch states from both
real TFVD quadratures and their boundary data before taking inner products.
The reconstructed vector equals the input. Any real linear isometry of the
coordinate incidence family preserves its delta Gram and its independence.
Both own parity Gram prefixes are PosDef at every order; already the even
order-three matrix cannot equal a Hankel section of any moment sequence.
This is a no-go only for that representation and its isometric images.
It does not disprove canonical Hankel positivity or a completed vector readout.

CLOSED: exact full-vector TFVD reconstruction; incidence independence;
Gram positivity of incidence/isometric-image prefixes; generic correct parity
Gram + independence of the SAME family → Hankel PosDef.
OPEN: a geometrically completed vector family, defined before moments, whose
pairings equal `polarizedRealMomentCoefficient baseTwoCanonicalMomentSequence
(parityJetNumber i) (parityJetNumber j)` for all i,j; independent prefixes of
that actual completed family. No such family is constructed in this round.
Scalar synthesis/analyticity and arbitrary-CoreState clock-domain gates are
unchanged. No finite/global height or Jacobi step is implemented.
See `VERTICAL_GRAM_POSDEF_INVESTIGATION.md` for the exact two-entry obstruction.

## Symmetric Krylov → Hankel (2026-10-04), increment A

`SymmetricKrylovHankel` closes the generic sum-index identity for total symmetric
endomorphisms over ℝ/ℂ and the real spectral-moment Hankel representation.
First-column identification propagates to the whole kernel; PSD follows and
PD needs independence of that SAME Krylov prefix. The recurrence uniqueness
bridge requires an independently established log-derivative coefficient
relation. No canonical first column, completed vector, parity orthogonality or
canonical positivity is asserted. Finite orbit-jet factors are the next step.
See `SYMMETRIC_KRYLOV_CANONICAL_MOMENT_SEAM.md`.

### Finite clock jets → Krylov / parity spectral Gram — increment B

Status: `PASS_KRYLOV_HANKEL_FIRST_COLUMN_OPEN`.
`FiniteClockKrylovHankel` proves exact (-i)^r and r! crosswalks, skew symmetry
of the temporal generator, real Hankel representation of its auxiliary
spectral moments and real parity Gram of the even-power sequence (moments of
L²). Mixed orthogonality is DERIVED for quadrature jets, while a log 2 witness
shows it fails for raw even/odd powers. Both auxiliary parity Hankels are PSD.
No canonical moment Gram/positivity or arbitrary-vector Krylov independence
is asserted. Existing finite head readout is connected with all factors.
The completed vector itself and its spectral first column remain unidentified.
The alternative recurrence gate is exactly IsLogDerivativeMomentSequence
baseTwoCanonicalPhi q for the independently derived spectral q; it is not
assumed as canonical proof. No unbounded power or new domain claim is made.


## Completed vector response inventory / dressing gate (2026-10-04)

Status: `PASS_COMPLETED_VECTOR_LIFT_GATE_ISOLATED`, diagnostic only.
`BaseTwoCompletedVectorLiftGate` proves that the concrete scalar dressing
D=C/B is analytic and nonzero on the real line, acts linearly/injectively on
an existing complex vector carrier, and commutes with the existing Parseval
map. Its readout residual is D times the undressed full-synthesis residual.
Thus a dressed linear response lift is equivalent to the exact undressed
readout equality ell(X(t))=baseTwoCriticalCompleteSignal t. No such completed
X/readout pair is instantiated here. The actual finite vector readout still
needs D times the exact omitted whole-cell tail. The vector product-rule
residual is D'(t) X(t); keeping the same total clock requires this term zero.
CLOSED: scalar vector action, nonvanishing, residual equivalence, generator
correction, finite-head test. OPEN: full vector synthesis/boundary readout;
completed spectral first column; its regularity/domains and canonical Gram.
The historical seeded atlas has conditional boundary calibration, not an
available completed-vector theorem. See CANONICAL_COMPLETED_VECTOR_LIFT.md.


## Existing completed material-gradient signal lift (2026-10-04)

Status: `PASS_EXISTING_COMPLETED_VECTOR_SIGNAL_LIFT` (Banach signal lift only).
`BaseTwoCompletedGradientSignalLift` reconstructs the historical ordinary
completed material-gradient architecture locally from existing samples.
The seed and every consecutive gradient form a complete state in the standard
carrier ℂ × ℓ¹(ℕ,ℂ); finite prefix reconstruction recovers every material value.
The continuous linear base-two edge readout is proved equal to the already
synthesized baseTwoCriticalCompleteSignal, and concrete scalar dressing then
reads out baseTwoCanonicalResponse. No moment defines a vector. The same
ordinary coordinates are also ℓ², without a norm identification or a continuous
ℓ² summation claim. No whole-cell vector fallback was needed.
CLOSED: the previous undressed linear signal-readout gate for this concrete
seeded gradient state. OPEN: Hilbert/Green realization of this completed
observable with the required first-column moment metric, vector domains and
canonical Gram. The existing depth-amplitude source remains distinct.
Forensic types, scalar tail projections, historical conditional sewing and
seeded atlas provenance are in EXISTING_COMPLETED_VECTOR_SIGNAL_FORENSIC.md.


## Raw ℓ² complete-signal readout obstruction (2026-10-04)

`NO_GO_RAW_L2_COMPLETED_SIGNAL_READOUT` is proved by the finite signed-edge
witness: readout=2N and norm²=2N. `BaseTwoRawL2ReadoutObstruction` excludes
continuous extension of the existing ℓ¹ readout to raw material-edge ℓ²,
and any bounded analysis/boundary factorization agreeing on all deltas.
This does not exclude stronger-domain or source-specific geometric boundary
realizations. Current TFVD trace stores vertical value and slope; no theorem
identifies those with the global material-edge return. The historical finite
completion ledger keeps scalar tails separately from the finite Green port.
OPEN: a provenance-preserving geometric transform from the seeded complete
source to Hilbert interior + seed + derived boundary, realizing the existing
signal readout. No material edge is identified with vertical depth. Details:
COMPLETED_SIGNAL_HILBERT_BOUNDARY_AUDIT.md.


### Derived boundary target (same audit round)

`BaseTwoCompletedBoundaryLimit` proves that whole-cell edge-return prefixes
converge to `baseTwoCompletedBoundaryValue`, exactly the existing undressed
readout minus seed. Material-coordinate interior prefixes independently
converge in ℓ² to the completed gradient. No Hilbert boundary state is defined
by adding that scalar. OPEN: a geometric channel map producing this return
with provenance; the standard TFVD initial trace is not identified with it.
No moment/Gram/clock conclusion follows from these two completion limits.

## Completed signal Hilbert boundary realization

`BaseTwoCompletedBoundaryHilbert.lean` constructs the standard Hilbert sum of
seed, material-edge interior, and the existing geometrically derived return.
Prefix convergence and bounded seed-plus-boundary readout are proved locally;
the observable equals the complete base-two signal and the earlier Banach
readout. The raw ℓ² readout obstruction is unchanged. No material-edge/depth
identification, carrier isometry, autonomous generator, or moment Gram is
claimed. See `docs/COMPLETED_SIGNAL_HILBERT_BOUNDARY_REALIZATION.md`.

## Raw material-edge readout nonclosability

`BaseTwoRawL2ReadoutNonclosable.lean` strengthens the existing bounded-extension
no-go. The normalized finite signed witnesses converge to zero with output
one; every partial extension agreeing on deltas has `(0,1)` in its graph
closure and is not `LinearPMap.IsClosable`. This applies to raw ℓ² only and
does not obstruct the separately derived geometric boundary coordinate.

## Completed boundary component dynamics

`BaseTwoCompletedBoundaryDynamics.lean` proves seed constancy, each material-
edge coordinate derivative, the exact nonzero residual against diagonal
`log(j+1)` at the first edge, and the induced coordinate clock formula using
finite reconstruction. The boundary derivative follows from the already
synthesized analytic signal. Strong product-Hilbert differentiation and an
autonomous boundary operator remain open. No moment first-column or Gram
claim is made; see the completed Hilbert boundary realization report.

## Exact finite material-clock transport to seeded gradients

`FiniteSeedGradientClock.lean` constructs a linear samples ↔ seed+gradient
coordinate equivalence and transports the existing finite material clock by
conjugation. It proves the triangular coordinate action, strong finite orbit
equation, and synchronized C2 material cutoff. The material pullback pairing is
recorded separately; the standard metric is not replaced. Boundary graph,
standard-metric symmetry, and the infinite strong-domain seam are separate.
See `docs/COMPLETED_BOUNDARY_TRANSPORTED_CLOCK.md`.

### Completed boundary clock: finite graph and standard-metric test

`FiniteCompletedBoundaryClock` transports the finite material clock on the
redundant whole-cell boundary graph and proves its strong orbit equation.
The standard product graph metric is formally nonsymmetric (deltas at material
1 and 2, one complete cell). This is a metric/representation no-go, not a no-go
of the clock or complete theory. Infinite domain/strong orbit and identification
of a geometric symmetry metric remain open; no Krylov or Hankel inference.

### Strong completed material-gradient and clocked return

`CompletedMaterialGradientStrongClock` proves strong ℓ¹/ℓ² differentiation using
a summable norm majorant for vector first differences, then identifies the
triangular material clock coordinates. The boundary derivative is the sum of
clocked whole-cell returns, via the existing bounded ℓ¹ readout. Packaging a
partial clock on the geometric boundary graph remains the next step; no moment,
Hankel, metric or all-CoreState-domain inference.

### Completed boundary transported clock: strong equation and metric no-go

`CompletedBoundaryTransportedClock` defines the natural partial domain by
geometric boundary coherence, ℓ² triangular clock interior, and summable clocked
whole-cell return. The concrete completed state is in the domain at every time
and satisfies the strong full-product equation `Y' = -i L_boundary Y`.
Standard-product symmetry and self-adjointness are excluded on this actual
infinite domain by encoded material deltas at 1 and 2. Status:
`PASS_TRANSPORTED_CLOCK_NO_STANDARD_SYMMETRY`. No metric was changed. Before
Krylov, the infinite geometric/TFVD symmetry pairing and its domain/intertwining
must be identified; no canonical moment or Hankel consequence is asserted.

## Completed clock candidate obstructions (2026-10-04)

CompletedClockCandidateObstructions proves harmonic raw-node exclusion,
isometric standard-product intertwiner obstruction, and direct C2 source
amplitude mismatch on material 3/7 of the same core. These are scoped
representation tests, not obstructions to enriched geometric synthesis.
Proof inputs are local current modules and Mathlib; the three read-only
blueprints at carry revision 62b1c0d6b18e70b4c156c3bdf0253893fdb27a35
are listed in COMPLETED_CLOCK_GREEN_INTERTWINER.md. No dependency is added.

### Finite completed-clock Green intertwiner / energy obstruction

FiniteCompletedClockGreenIntertwiner retains graph data and its clock step,
reconstructs finite material nodes, embeds at exact PNat j+1, and reuses the
existing canonical Parseval map and ambient self-adjoint material clock.
Injectivity, domain membership and exact intertwining are local theorems.
The critical ordinary/enriched energies are harmonic/clock-weighted harmonic
prefixes and diverge; this specific candidate has no infinite Hilbert limit.
No arbitrary TFVD metric or old certificate is added. The general enriched
finite-energy transform remains open; no canonical-moment pairing is claimed.
The three authorized historical blueprints were architectural comparison only.
See COMPLETED_CLOCK_GREEN_INTERTWINER.md for the exact map and scoped no-go.

## Ordinary/logarithmic material-gradient crosswalk (2026-10-04)

`BaseTwoOrdinaryLogGradientCrosswalk` identifies the current consecutive
material edge n+1 -> n+2 with the explicit ordinary Dirichlet power difference,
and the existing triangular clock coordinate with its logarithmic difference
on s=1/2+it. The derivative is -i times the latter. A standard Hilbert pair of
the two existing ℓ² states and direct difference-prefix norm convergence are
proved without nodal decoding or new summability assumptions. Historical
formula comparison at carry revision 62b1c0d6b18e70b4c156c3bdf0253893fdb27a35
has zero index shift and uses only the three files listed in
`docs/ORDINARY_LOG_GRADIENT_CROSSWALK.md`; no dependency is added.
Status: `PASS_ORDINARY_LOG_GRADIENT_CROSSWALK_TFVD_MAP_OPEN`.
The remaining map is a provenance-preserving, reconstructible real analysis
from this material-edge pair to the two C2 real vertical fiber channels,
including quadratures and boundary data. Material edges are not relabelled as
depth. The nodal divergence no-go is preserved and does not automatically
exclude these completed differences. No moment/Gram/symmetric-clock claim.

## Physical base-two edge/C2 address chart (2026-10-04)

`BaseTwoPhysicalEdgeC2Address` explicitly identifies the two complete-cell
edges (residues 2/3 mod 4) with their odd endpoints and the existing C2 address
chart. Its arithmetic inverse requires no choice. Direction, original cell
center and true center-depth are recovered exactly; material edge is never
called depth. The Hilbert restriction/residual and TFVD input are the next
increment. No amplitude, moment or metric identification is asserted.
See `docs/BASE_TWO_PHYSICAL_EDGE_C2_TFVD_BRIDGE.md`.

### Physical/residual edge Hilbert split and genuine C2 TFVD input

`BaseTwoPhysicalEdgeTfvdBridge` closes the physical material-edge input seam:
contractive restriction, existing two-quadrature packaging, and exact C2
address reindexing precede fiber TFVD. The actual C2 physical state + residual
is lossless and preserves the unweighted squared norm; the joint TFVD +
residual analysis is injective by the existing R2 synthesis. Ordinary/log
states use the existing completed gradient/clock vectors. The concrete
summable whole-cell return is reexpressed in physical coordinates, without
claiming a bounded global boundary sum. Strong ordinary derivatives transport
to each actual TFVD fiber including trace, with -i before realification.
The critical base-two ratio is the existing derived vertical amplitude ratio,
not a new gradient weight. Status: `PASS_BASE_TWO_PHYSICAL_EDGE_C2_TFVD_BRIDGE`.
Next: joint physical TFVD + retained residual -> geometric Green/Naimark,
clock intertwining and symmetry test. No moment, metric, nodal decoding,
C2 amplitude-source substitution or edge=depth assumption enters this proof.
All proof inputs are current local modules/Mathlib/existing Green coordinate
mask; no historical dependency. See BASE_TWO_PHYSICAL_EDGE_C2_TFVD_BRIDGE.md.

### Physical center-clock defect: local finite energy

The physical center-clock defect is now defined by subtraction from the certified transported clock. Left/right formulas use one decoded center; its unweighted L2 membership follows from a square-summable log-gap bound. Green domain and Parseval transport are the next increment of this round.

### Center-clock correction: exact Green/Parseval transport

The exact Green/Parseval center-clock decomposition and concrete ordinary-gradient generator domain are closed. The center sample retains seed + physical + residual prefixes. This does not assert symmetry of the completed clock. Next: pre-stencil sector localization, followed in a separate round by a symmetric block-coupling test.

### Center-clock defect in both unchanged pre-stencil sectors

PASS_PHYSICAL_CENTER_CLOCK_DEFECT_PRESTENCIL: local left/right center corrections, L2/C2 packaging, concrete Green maximal domain and exact Green/Parseval decomposition are closed. The unchanged pre-stencil has both nonzero sectors (seed itself zero). No symmetry of the completed clock follows. Next: geometric center coupling with matching adjoint/domains; bounded Hardy coupling remains open.

### Finite center-coupling physical symmetry test

First-cell physical center self-coupling is proved nonsymmetric in the standard physical Hilbert metric. Matrix [[log4-log3,0],[log5-log4,0]] comes from geometric center reconstruction, not the orbit defect. This result must be integrated before the Hardy-bound investigation.
