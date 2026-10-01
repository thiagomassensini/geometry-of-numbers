# Plano de execução: proveniência real do carry

Fonte do plano: `PLANO_FORMALIZACAO_TEORIA_REAL_DO_CARRY.md`, fornecido pelo
autor em 2026-09-29. Este resumo orienta a implementação em
`geometry-of-numbers`, o repositório escolhido para esta rodada.
Não substitui os enunciados Lean nem declara fechadas as metas do plano.

## Zonas de confiança

**Zona A — fundação discreta:** quantidade, carry, profundidade,
massa/expoentes e rigidez quadrática. O núcleo de seleção da escala está
encerrado em `FoundationalHalfScalingCapstone`. Isso não fecha outras metas
históricas do plano, como a identificação de profundidades centro/carry. Axiomas transitivamente usados:
**nenhum**. Nem `Classical.choice`, nem `propext`, nem `Quot.sound`.
As provas atuais importam apenas `Init`.

**Geometria discreta adicional — `Geometry/`:** centro–pernas, reflexão e
segunda diferença sobre `Int`, somente com Init nos arquivos matemáticos.
Sua auditoria permite `propext` e `Quot.sound`, rejeitando escolha e qualquer
outro axioma. Não pertence ao capstone axiom-free de seleção da escala.

**Zona B — análise real:** aberta somente para realizar massa e amplitude
escalares. Mathlib entra por `Analysis/`; raízes, rotações, Hilbert, adjuntos,
limites e cálculo funcional não são novas construções desta rodada.
Os axiomas usuais são exibidos, não ocultados. Nenhuma representação
complexa justificará um resultado fundacional.

## Ordem e estado

| Fase | Conteúdo | Estado nesta árvore |
| --- | --- | --- |
| F0 | Fidelidade → recorrência → primeiro retorno → carry → torre | Primeiro retorno, reset, torre finita, capacidade prefixal e fibras de refinamento fechados; crosswalk clássico ainda aberto |
| F1 | Centro–pernas, profundidade e resíduo | Geometria abstrata e crosswalk de uma célula carry para capacidade ímpar fechados; profundidades e ramo antipodal par/C2 ainda abertos |
| F2 | Massa/amplitude e rigidez algébrica do expoente `1/2` | Núcleo discreto encerrado em capstone; massa e amplitude reais realizadas em camada separada, com amplitude² = massa |
| R0 | Rotação e estado espectral reais | Não iniciada |
| R1 | Câmeras e brackets reais | Não iniciada |
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

Continuam abertos: realização vetorial/rotacional, norma, câmeras, brackets,
TFVD, Green, isometrias e operadores. A identidade escalar `A²=M` não fecha
nenhum deles. Também não se cria uma medida analítica na torre infinita.

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
centro–pernas. A célula ímpar é construída abaixo; a relação de profundidades
continua pendente. Também não se
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

Próximos gates: ramo par/C2 com regra própria e crosswalk de profundidades.
Não se portaram `effectiveDepth=centerDepth`, brackets, Green ou tilt.

- Reusar uma prova somente após comparar seu tipo e suas dependências.
- Manter mapas, estados, parâmetros e domínios antes de scalarizar.
- Separar gerador com frequências `log n` de operador de alturas.
- Para `VLV*`, provar isometria e domínio; não tratar demonstração numérica
  como teorema infinito.
- Não declarar compatibilidade literal entre cutoffs quando o whitening muda.
- Não fabricar momentos ou inserir uma lista externa de alturas.
- Uma fase só fecha quando seu capstone compila e sua auditoria passa.
- Nenhuma meta incompleta será representada por um placeholder de prova.
