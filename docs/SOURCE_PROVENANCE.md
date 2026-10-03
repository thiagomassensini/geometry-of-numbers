# Proveniência da primeira porta

## Fonte consultada

Repositório: `thiagomassensini/quantity-representation-foundations`.
Commit consultado: `66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`.

| Objeto local | Fonte e adaptação |
| --- | --- |
| `FaithfulRepresentation` | `FiniteStateObstruction.lean`; injetividade escrita diretamente, sem importar Mathlib |
| `sameLocal_forces_extension_difference` | `InformationEscape.lean`; prova por injetividade e igualdade de pares |
| `faithfulRepresentation_comp` | Consequência elementar da mesma definição; composição de injetividades |
| `UnitTrajectory`, `LocalRecurrence` | `UnitDynamicsLocalRecurrence.lean`; quantidades abstratas e relógio natural externo |
| `localRecurrence_forces_extension_difference` | Parte pontual de `unitTrajectory_localRecurrence_forces_extensionDifference`; recebe o evento de recorrência, cuja existência é derivada separadamente na camada finita |
| `AutonomousLocalDynamics`, `PositiveLocalReturn` | `FirstLocalReturnCapacity.lean`; mantidas as hipóteses de autonomia e injetividade |
| `positiveLocalReturn_implies_periodic_readout` | Mesmo enunciado da fonte; indução direta no relógio, sem biblioteca de iterações |
| `FiniteLocalPresentation`, `finiteCodeCollision` | Apresentação construtiva da finitude e prova indutiva da colisão, substituindo a passagem clássica da fonte por cardinalidade finita |
| `unitTrajectory_forces_localRecurrence` | Mesmo conteúdo de recorrência da fonte, com orçamento explícito de códigos e limite para o tempo da colisão |
| `autonomousLocalDynamics_has_positiveReturn` | Mesmo conteúdo da fonte; cancelamento do prefixo comum por injetividade, sem biblioteca de iterações |
| `EmergentLocalCapacity` | `FirstLocalReturnCapacity.lean`; somente o predicado de primeiro retorno, sem presumir sua existência |
| `emergentLocalCapacity_unique` | Consequência da especificação mínima do primeiro retorno por antissimetria |
| `emergentLocalCapacity_gt_one_of_first_step_changes` | Lema de `FoundationalCapstone.lean` portado para a interface anterior ao carry, sem importar o capstone |
| `boundedLeastOrAbsent`, `exists_emergentLocalCapacity`, `existsUnique_emergentLocalCapacity` | Busca limitada por indução e aplicação ao retorno local; substituem `Nat.find` clássico por comparação de códigos naturais |
| `exists_emergentLocalCapacity_gt_one` | Composição da existência construtiva com o lema já portado de primeiro passo não trivial |
| `IsCycleDecomposition`, `nextCycleCoordinates`, `cycleCoordinatesRec` | `EmergentCycleDecomposition.lean` e `EmergentQuotientRemainder.lean`; recursão por incremento/reset, sem divisão ou módulo |
| `completedCycleCount`, `cycleResidual` | As projeções chamadas `emergentQuotient` e `emergentRemainder` na fonte; nomes locais enfatizam o significado anterior ao crosswalk clássico |
| `cycleCoordinatesRec_spec`, `cycleDecomposition_unique`, `cycleDecomposition_eq_recursive` | Especificação e unicidade da fonte; provas reescritas sem `omega` e com cancelamento aditivo por indução |
| `cycle_step_inside`, `cycle_step_at_boundary`, `cycle_step_dichotomy` | Leis operacionais da recursão da fonte, com exclusividade dos regimes em coordenadas válidas |
| `firstSaturation_coordinates` | Especialização da unicidade ao par `(1,0)`, sem assumir o reset como uma normalização clássica |
| `cycleResidual_controls_localReadout` | `emergentRemainder_controls_localReadout`; redução por periodicidade no contador de ciclos |
| `localReturn_iff_cycleResidual_zero` | Consequência elementar da redução do readout, limite do resíduo e minimalidade do retorno |
| `cycle_reset_forces_extension_difference` | Composição da periodicidade com a distinção já provada no canal de extensão fiel |
| `ResidualTowerCoordinates`, `emergentResidualTower` | Adaptação de `IteratedEmergentPositionalExpansion.lean`: recursão por profundidade diretamente sobre as coordenadas de ciclo já portadas; resíduos e cauda armazenados numa tupla dependente |
| `emergentResidualTower_bounded`, `emergentResidualTower_value` | Limites e reconstrução por indução na profundidade, usando apenas a especificação de uma célula |
| `residualTower_unique`, `residualTower_eq_canonical` | Unicidade de cada célula iterada; nenhuma expansão posicional pronta é premissa |
| `residualTowerValue_eq_prefix_add_scaled_tail`, `emergentResidualTower_expansion` | Conteúdo de `emergent_positional_expansion_with_tail`, com soma ponderada recursiva em vez de Finset; potências introduzidas só no theorem de reconstrução |
| `truncateResidualTower`, `emergentResidualTower_truncate` | Recompõe os níveis superiores na cauda inferior; a coerência resulta da reconstrução, sem projeções por módulo |
| `emergentResidualTower_first_residual_preserves_observation` | Reutiliza a ponte dinâmica de uma célula; não atribui às extensões arbitrárias a dinâmica dos contadores construídos |
| `ResidualPrefix`, `residualPrefixTower`, `residualPrefixValue` | Construção local sobre a torre já portada: produto recursivo de resíduos em `Fin b`, embutido na torre com cauda zero |
| `residualPrefix_value_lt_pow`, `residualTower_tail_eq_zero_of_lt_pow` | Indução sobre o prefixo e consequência da reconstrução exata da torre; sem divisão ou módulo |
| `residualPrefixEncode`, `residualPrefixDecode`, suas inversas | Avaliação do prefixo e extração da torre canônica; reconstrução e unicidade existentes certificam ambas as inversas |
| `residualPrefixEquivFin`, `residualPrefix_cardinality`, `existsUnique_residualPrefix_for_fin` | Bijeção computável explícita com `Fin (b^k)`; capacidade certificada, não postulada nem obtida contando a cauda ilimitada |

Nenhum resultado local depende de imports do repositório-fonte.
As generalizações de universos não alteram o conteúdo das provas.

## Por que não importar os capstones diretamente?

`FiniteStateObstruction.lean` importa `Mathlib` inteiro. A cadeia do capstone
operacional passa por `CarryGeometry`. As equivalências entre códigos opacos
do capstone universal são construídas como definições não computáveis.
`existsUnique_emergentLocalCapacity` usa um bloco `classical` e `Nat.find`.

Isso não é um defeito da formalização histórica. Também não basta olhar um
`import` ou a palavra `noncomputable` para determinar o footprint de um teorema:
é preciso auditá-lo. Aqui a política mais estrita da Zona A exige uma porta
construtiva e seu próprio `#print axioms`, não uma mudança de nome do capstone.

Outra fonte consultada, ainda **não portada**:
`thiagomassensini/native-carry-geometry`, commit
`43c7348908c573da826d9dba7d59102931e6a45a`.
Sua auditoria versionada registra `Classical.choice`, `Quot.sound` e `propext`
para `centerOffsetDecomposition_existsUnique`. Portanto esse teorema também
não fecha automaticamente a futura F1 axiom-free.

## Rigidez quadrática discreta

Fonte: `thiagomassensini/carry-geometry`, commit
`3a64ccebfa3849251b2d564432d693ed19a4b74b`, especialmente
`CarryGeometry/QuadraticAmplitude.lean`.

A prova histórica de `deformedAmplitude_sq_eq_carryMass_iff` obtém a
igualdade dos expoentes por injetividade de `Real.rpow`. A direção de
unicidade não usa a amplitude previamente definida com expoente metade.
O módulo local `QuadraticAmplitudeExponent.lean` isola somente o passo
aritmético dessa prova, apresentando o expoente por naturais `p, q` e
traduzindo a compatibilidade em `2 * (k * p) = k * q`.

Não foram importados `Real.rpow`, `ℚ`, `ℝ`, probabilidades ou amplitudes
numéricas. O denominador positivo é preservado na especificação. Nenhuma
redução a fração irredutível ou identificação por quociente é necessária.

A auditoria detectou `propext` em lemas gerais de aritmética inteira e em
`Nat.mul_assoc` da biblioteca desta versão do Lean. Por isso o núcleo usa
apenas uma identidade específica de duplicação, provada por indução e
associatividade/comutatividade da adição. O footprint transitivo dos quatro
teoremas públicos de rigidez é vazio.

## Limite do resultado atual

Fecharam-se o começo pré-posicional, finitude apresentada → recorrência →
retorno positivo → primeiro retorno único, além da rigidez discreta dos
expoentes. A capacidade satisfaz `1 < b ≤ N` quando o primeiro passo muda;
o limite `N` é orçamento de códigos, não uma base previamente postulada.

A busca usa decidibilidade de comparações naturais, nunca igualdade escolhida
classicamente no tipo local. Nesta versão do Lean, `omega` e o decisor genérico
`Nat.decidableExistsFin` trazem axiomas; não são usados nestas provas.
Os sete novos teoremas públicos foram auditados com footprint vazio.

O reset com memória de ciclos já foi portado: a recursão preserva a contagem,
seu par é único e o resíduo controla a mesma observação local. Retorno ao
estado local inicial equivale a resíduo zero; a extensão fiel distingue os
endpoints. Dez teoremas novos certificam essa camada sem axiomas.
Não se identificou uma extensão arbitrária com o contador de ciclos.

Foi portada a torre residual de profundidade finita, com limites, reconstrução,
unicidade e truncamento coerente. A escala positiva `b^k` da cauda é derivada
da reconstrução. A construção e seus oito teoremas usam apenas `Init`; os
lemas multiplicativos necessários foram provados sem o `Nat.mul_assoc` e o
`Nat.add_mul` da biblioteca, cujos footprints nesta versão contêm `propext`.

Foi construída a capacidade prefixal exata: o tipo limitado recursivo tem
uma codificação fiel e sobrejetiva em `Fin (b^k)`, com duas inversas explícitas.
`Init` não fornece a API `Equiv` de Mathlib; os mapas e suas provas são
empacotados diretamente. Dez teoremas públicos novos e esse empacotamento
têm footprint vazio. O limite `n < b^k` força cauda zero, sem afirmar que toda
cauda termina em alguma profundidade.

Não se portaram a eliminação eventual da cauda ou o crosswalk clássico de normalização carry.
O conteúdo relacional de profundidades carry/centro–pernas é reconstruído
na etapa final registrada abaixo, sem importar valuations. A geometria abstrata e
depois a célula carry balanceada ímpar foram construídas na camada separada
registrada abaixo; o ramo par não foi portado.
A realização da amplitude em potências reais está agora na Zona B abaixo. Não há prova de
autoadjunticidade nesta árvore. Essas fronteiras constam do README e do plano.

## Normalização formal do prefixo

O módulo `ResidualPrefixNormalization.lean` é uma construção local sobre a
bijeção já provada. Não foi copiado ou importado de um repositório histórico.
Usa apenas a cadeia local e `Init`.

| Objeto | Proveniência e limite |
| --- | --- |
| `StateRelabeling`, `finiteLabelTransposition`, `residualPrefixRelabeling` | Mapas e inversas explícitos; transposições finitas transportadas pela codificação prefixal existente |
| `RelabelingInvariant` | Princípio adicional de neutralidade da atribuição no conjunto nu; não deduzido da dinâmica nem confundido com covariance de pesos |
| `finiteLabel_relabelingInvariant_iff_constant`, `residualPrefix_relabelingInvariant_iff_constant` | Uniformidade provada aplicando a invariância à troca de quaisquer dois estados |
| `finiteLabelTotal` | Adição recursiva sobre códigos finitos; nenhuma API de medida ou quociente |
| `finiteCapacity_does_not_force_uniformity` | Contraexemplo explícito `(1,0)` com total positivo; cardinalidade não implica neutralidade |
| `FormalCountingShare`, `SameCountingShare` | Numerador/denominador positivo e comparação cruzada; sem construir números racionais |
| `canonicalResidualPrefixCountingShare` | Conta cada estado uma vez e obtém o denominador pela soma; sua invariância e a identificação `(1,b^k)` são provadas |
| `residualPrefix_normalizedShare_unique` | Neutralidade + contagens naturais com denominador comum + total normalizado implicam a mesma cota formal; não cobre medidas numéricas arbitrárias |

A hipótese de invariância é logicamente equivalente à constância neste
conjunto finito. Essa equivalência é exposta, não ocultada: a motivação
estrutural é uma política de contagem que não consulta a identidade do estado.
A cardinalidade anterior não a produz para toda atribuição. A contagem
unitária fornece uma realização concreta dessa política, e o teorema de
unicidade mostra independência de sua escala de apresentação.

Os dez teoremas públicos e as três definições de transporte/cota são auditados
com footprint vazio. A auditoria detectou `propext` em `Nat.one_ne_zero`;
a mesma contradição foi escrita com `Nat.zero_ne_one` e simetria da igualdade,
preservando o footprint vazio. Não há dependência histórica nova.

## Refinamento e conservação das cotas

`ResidualPrefixRefinement.lean` foi construído localmente sobre os prefixos
e a normalização anteriores. Nenhum módulo histórico foi importado ou
consultado como fonte de prova nova nesta etapa.

| Objeto | Proveniência e limite |
| --- | --- |
| `truncateResidualPrefix`, `extendResidualPrefix`, `topResidual` | Recursão no tipo já existente; preservam os resíduos baixos e removem/adicionam somente o mais profundo |
| `truncateResidualPrefix_of_canonicalTower` | Indução usando a construção original de ciclos; alinha refinamento à extração da torre, sem hipótese de cauda zero |
| `ResidualPrefixRefinementFiber` | Preimagem efetiva do truncamento; não contém cardinalidade como campo |
| `residualPrefixRefinementEquivFin`, `residualPrefixRefinement_fiber_cardinality` | As três leis das operações provam a parametrização completa e sem duplicação por `Fin b`; não derivadas de uma identidade de potências |
| `residualPrefixValue_extend` | A reconstrução existente identifica a escala da coordenada nova depois de sua construção |
| `residualPrefixRefinementAggregateShare` | Soma dos numeradores das cotas dos filhos efetivos da fibra, com denominador comum canônico; conservação não é campo |
| `residualPrefix_refinement_conserves_share` | Soma finita computa `b` filhos; aritmética de potências verifica a equivalência cruzada das cotas |
| `canonicalResidualDepthMass` | Nome para a cota canônica existente num representante; igualdade com a cota de qualquer prefixo elimina privilégio do representante |
| `canonicalResidualDepthMass_zero`, `canonicalResidualDepthMass_refinement` | Unidade inicial e conservação herdadas; não são axiomas nem definem uma medida numérica infinita |
| `zeroRefinement_cannot_conserve_unit` | Exclui coerência com unidade inicial numa fibra vazia de capacidade zero |

Não foi acrescentado princípio estrutural: a neutralidade permanece aquela
da etapa anterior. As cotas são comparadas por `SameCountingShare`, não por
igualdade dos pares agregados. A identificação do novo nome de massa com a
apresentação canônica anterior é literal; a conservação não exige igualdade
de apresentações, embora ela possa ocorrer em casos particulares como `b=1`.

Os dezoito teoremas públicos e nove definições novos têm footprint vazio.
Identidades multiplicativas específicas repetem as provas indutivas já
usadas na torre, em vez de recorrer aos lemas gerais com footprint não vazio.
A unicidade anterior da normalização continua ponto a ponto; não foi
substituída por uma alegação de unicidade de qualquer família recursiva.

## Ponte da massa formal à compatibilidade quadrática

`QuadraticMassCompatibility.lean` é uma composição local, autocontida, das
camadas `ResidualPrefixRefinement` e `QuadraticAmplitudeExponent`. A inspiração
histórica massa/amplitude permanece a de `carry-geometry`, commit
`3a64ccebfa3849251b2d564432d693ed19a4b74b`, já registrada acima; não houve
novo import histórico nem consulta a uma realização analítica como premissa.

| Objeto | Proveniência e limite |
| --- | --- |
| `radixShare`, `canonicalResidualDepthMass_eq_radixShare` | Apresentação posterior da massa geométrica existente; igualdade literal provada pela identificação de seu numerador e denominador |
| `multiplyCountingShares`, `powerCountingShare` | Operações sobre apresentações naturais; composição multiplicativa, distinta de somar cotas de filhos |
| `canonicalResidualDepthMass_power_eq_radixShare` | A massa real do nível `k` aparece como entrada, e sua composição `q` vezes é identificada com escala `k*q` |
| `radixShare_same_iff_exponent_eq` | Igualdade cruzada reduz a igualdade de capacidades; crescimento estrito das potências naturais recupera o expoente somente para `b>1` |
| `QuadraticAmplitudeScaleCompatibleAt` | Requisito semântico novo e explícito de composição quadrática; compara cotas, não define a igualdade de expoentes nem assume metade |
| `quadraticAmplitudeScaleCompatibleAt_iff_carryCompatibleAt` | Redução provada da comparação geométrica à interface aritmética existente |
| `canonicalResidualDepthMass_quadraticCompatibility_iff_half` | Composição da ponte com `quadraticCarryCompatibleAt_iff_half`, sem reprovar a aritmética de metade |
| `emergentResidualDepthMass_quadraticCompatibility_iff_half` | Usa o mesmo primeiro retorno; `b>1` vem do theorem pré-carry de primeiro passo não trivial |
| Casos `b=1`, `k=0`, `q=0` | Dois primeiros não selecionam expoente; o último é inválido. Não se cria massa positiva para `b=0` |

A auditoria local encontrou `propext` em `Nat.pow_add`, `Nat.pow_mul` e no
theorem de crescimento das potências; `Nat.pow_right_inj` também trouxe
`Classical.choice` e `Quot.sound`. Foram usadas provas indutivas específicas
de composição/crescimento. Reescrever um `iff` dentro de proposições também
introduziu `propext`; aplicar suas duas direções explicitamente removeu essa
dependência. Os dezessete teoremas públicos e quatro definições finais têm
footprint vazio. Não há amplitude real, quociente racional ou métrica nessa
ponte, e a contagem isoladamente não foi apresentada como prova de que uma
lei observável deve ser quadrática.

## Capstone discreto final e abertura da Zona B

`Foundation/FoundationalHalfScalingCapstone.lean` é somente costura local:
capacidade não trivial, seleção pela mesma massa e existência a partir da
apresentação finita. Não introduz import histórico nem nova hipótese. Os
dois teoremas públicos foram acrescentados ao audit vazio da Zona A.

Referência histórica adicional consultada: `thiagomassensini/carry-geometry`,
commit `1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4`,
`CarryGeometry/Mass.lean` e `CarryGeometry/QuadraticAmplitude.lean`.
A referência contém a técnica `Real.rpow_mul_natCast` para verificar o quadrado
da amplitude. Não importamos `CarryGeometry`, nem sua definição de massa por
potência como origem da massa nova. Aqui a definição numérica realiza
`canonicalResidualDepthMass`, construída anteriormente pela torre e contagem.
Não portamos a seleção de expoentes reais por `Real.rpow_right_inj`.

| Objeto novo | Proveniência e fronteira |
| --- | --- |
| `realizeCountingShare` | Divisão real sobre a apresentação fundacional com denominador positivo; equivalência de realizações é provada pela comparação cruzada existente |
| `realDepthMass`, `realize_canonicalResidualDepthMass` | Realização da massa local anterior; `(b : ℝ)^(-k)` é conclusão, não a definição da massa geométrica |
| `realizeFormalExponent`, `formalHalf_realizes_half` | Interpretação de `2*p=q` após a seleção discreta; não há nova prova de seleção analítica |
| `realCriticalAmplitude`, `formalHalf_realizes_realCriticalAmplitude` | Usa a apresentação formal `(1,2)`; outras apresentações de metade dão o mesmo valor real |
| `realCriticalAmplitude_sq_eq_realDepthMass` | Técnica elementar de composição de potências reais também presente na referência; a massa do lado direito é a realização da massa fundacional |
| `quadraticScaleCompatible_realizes_realCriticalAmplitude` | Composição direta com a classificação da Zona A, sem usar `A²=M` para justificá-la retroativamente |

A única dependência externa nova é Mathlib oficial, commit fixo
`81a5d257c8e410db227a6665ed08f64fea08e997` (`v4.32.0`), compatível com
o Lean fixado no projeto. Nenhum repositório histórico entra no manifest.
O audit analítico lista os axiomas padrão `propext`, `Classical.choice` e
`Quot.sound` e rejeita outros. A auditoria discreta continua vazia e separada.
O checker de imports usa o parser da própria distribuição Lean para impedir
dependências de Mathlib ou Analysis na fundação e no import público discreto.

Foram revisadas todas as notas Markdown rastreadas do projeto: README,
versão humana, plano, proveniência e instruções AGENTS. A pasta pessoal
`.obsidian/` é local e não foi importada, alterada ou versionada.

## Geometria discreta centro–pernas e segunda diferença

Foram consultadas cópias locais das dependências históricas de
`carry-self-adjoint-operator`, HEAD `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`:

| Fonte e commit | Conteúdo consultado e adaptação |
| --- | --- |
| `CPFormal`, `65d50f6db1208708e109982ba97e1d51d3039956`, `Finite/SymmetricPair.lean` | Pernas `c-r`, `c+r`, soma `2*c` e troca por inversão do raio; inspiração direta, sem importar Mathlib ou copiar uma estrutura redundante |
| Mesma fonte, `Finite/Bracket.lean` | `centeredSecondDifference` abstrata aditiva e invariância sob raio negativo; aqui a API inicial é somente `Int → Int`, separada da operação sobre três nós fixos |
| `GreenFrame`, `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`, `Analysis/GreenBounds.lean` | Forma de três termos `greenStencil`; somente referência de orientação. Não foram portados estimativas, energias ou uma identificação com Green |
| `FiniteNativeCarryOperator`, `00e9d6beb17226545abf5ddf90bbfede6c7146b0`, `Operator/FiniteReal.lean` | `centeredBracket` como realização posterior em outro carrier; não portamos estados rotacionais, amplitudes, câmeras ou esse bracket |

A consulta prévia de `native-carry-geometry` permanece registrada acima:
`centerOffsetDecomposition_existsUnique` tem footprint com `Classical.choice`,
`Quot.sound` e `propext`. **Não foi portado**, nem usado para alegar que a
nova geometria tem footprint vazio. Não houve nova importação histórica;
essas bibliotecas não entram no manifest do projeto.

`CenterLegReflection` e `CenteredSecondDifference` são provas locais com Init.
O defeito de centro com pernas fixas e a distinção de recentramento são
explicitados como novas consequências elementares da configuração, não
como uma identificação com o carry ou com observáveis históricos.
A verificação `f(x)=x*x` impede confundir resposta não linear e miscentering.

O probe desta versão encontrou `propext` nos lemas aditivos/multiplicativos
usuais de Int. As provas lineares por `omega` usam `propext` e `Quot.sound`.
Aplicar esse tactic diretamente a equivalências também introduziu escolha;
separar construtivamente as duas direções antes da aritmética eliminou essa
dependência. O audit final rejeita escolha ou qualquer axioma além dos dois
permitidos; sete definições e a ponte definicional da identidade são vazias.
Nenhuma dessas provas ou axiomas retorna à fundação congelada.

A profundidade/massa/metade já foram derivadas sem centro–pernas nesta árvore.
Não foi inventada uma ponte retroativa para alterar essa proveniência.

## Crosswalk de uma célula carry para centro–offset balanceado

Referências consultadas: a mesma cópia local de `CPFormal`, commit
`65d50f6db1208708e109982ba97e1d51d3039956`, em
`Genuine/BalancedOffsets.lean`, `Carry/CpBalancedResidue.lean` e
`Carry/CpGlobalIncidence.lean`.

| Referência histórica | Uso e diferença da implementação local |
| --- | --- |
| `balancedOffsets`, `BalancedOffset` | Motivação para a janela simétrica. Não importamos Finset, não excluímos zero e não usamos `(p-1)/2` para construir os offsets |
| `balancedOffsetEquivNonzeroResidue` | A fonte usa `ZMod.valMinAbs`, não computabilidade e primalidade/oddness. Não foi portada: os resíduos locais já vêm de stepping/reset |
| `centerOfNonmultiple`, `dvd_centerOfNonmultiple`, `existsUnique_incidence` | Motivação para alinhamento e canonicidade. Novas provas usam `completedCycleCount`, `cycleResidual` e limites estritos; cobrem também resíduo zero |

A primalidade foi eliminada: o regime suficiente é capacidade ímpar,
expressa como `b=2*h+1`. Esse testemunho não é a divisão por dois, nem foi
deduzido da emergência de uma capacidade arbitrária. A comparação `2*r<b`
seleciona o centro atual ou seguinte. Nenhum módulo histórico entra como
dependência lógica, e os centros não são definidos por quociente/modulo.

`balancedCenterOffset_unique` é uma prova local sobre múltiplos inteiros.
Usa os lemas de Init `Int.dvd_sub` e `Int.le_of_dvd` (ambos com `propext`)
para excluir uma diferença não nula de centros dentro da janela estrita.
Esses lemas não redefinem a decomposição emergente. A referência histórica
`centerOffsetDecomposition_existsUnique` não foi importada ou simplesmente
rebatizada; seu footprint anterior permanece registrado, fora da Zona A.

Os 23 teoremas públicos novos têm footprint contido em `propext` e
`Quot.sound`; nenhum depende de escolha. As quatro definições e o witness
antipodal explícito de bordo são vazios. A família canônica não tem input
par: em C2 provamos tanto a ausência de representante estrito para `1`
quanto as duas apresentações distintas no bordo. Não construímos uma
resolução C2, uma identificação de profundidades ou observáveis históricos
nessa etapa de uma célula. A identificação relacional foi acrescentada depois.

## Profundidade relacional derivada da torre

Referência histórica consultada: cópia local de `CPFormal`, commit
`65d50f6db1208708e109982ba97e1d51d3039956`,
`CPFormal/Carry/CpDepth.lean` e `CPFormal/Carry/C2Depth.lean`.
Nenhum import dessa fonte entra na prova nova ou no manifest.

| Objeto histórico | Reconstrução local e limite |
| --- | --- |
| `offsetDepth p n a := padicValInt p (n-a)` | Não portado como definição. `HasCarryDepthAtLeast` consulta o prefixo zero da torre natural; a versão inteira por divisibilidade vem somente depois da equivalência provada |
| `dvd_sub_iff_eq_offset` | Motivação do canal único. `balancedCarry_offset_unique_of_dvd` aplica a unicidade local de centro/offset à decomposição candidata `(n-a')+a'`, sem ZMod ou primalidade |
| `effectiveDepth` como supremo, `centerDepth` como valuation | Nenhum máximo ou valuation foi importado ou definido; enunciados são por todos os níveis positivos |
| `effectiveDepth_eq_centerDepth` | Conteúdo relacional reconstruído por `balancedCarry_positive_depth_iff`, equivalência existencial e witness único; o mesmo offset expõe exatamente os níveis do centro |
| Convenção histórica `padicValInt ... 0 = 0` | Não adotada. Quantidade e centro zero sobrevivem em todo nível; não se atribui profundidade máxima finita a zero |
| `C2Depth`, escolha de vizinho e análise módulo quatro | Consultado apenas para delimitar a ponte par futura. Não portado, não usado para resolver o antipodal nem para definir a relação natural |

O registro anterior de `native-carry-geometry`, commit
`43c7348908c573da826d9dba7d59102931e6a45a`, permanece referência histórica;
seu `Arithmetic/CarryDepth.lean` não foi consultado nesta rodada nem importado.
As fontes de **prova** da nova relação são os módulos locais
`EmergentResidualTower` (expansão e unicidade) e `BalancedCarryOffset`
(unicidade geométrica já provada). A consulta histórica serviu para comparar
enunciados e convenções, não para substituir a proveniência da torre.

`Geometry/ResidualTowerDepth` mantém Foundation congelada e usa somente
sua API anterior. Um tuple comparativo de zeros e cauda identifica por
unicidade qualquer witness de divisibilidade com a torre real. Não é uma
nova dinâmica. Nove teoremas públicos têm footprint vazio; a aritmética
necessária usa aplicações explícitas de equivalências e lemas naturais de
Init com footprint vazio. Nenhuma prova nova usa `Nat.find` ou fatorização.

`Geometry/BalancedCarryDepthCrosswalk` estende a relação para Int só depois
da caracterização natural e prova compatibilidade dos casts. Onze teoremas
públicos usam no máximo `propext` e `Quot.sound`; nenhum usa escolha.
As três definições novas têm footprint vazio. O audit geral cobre todos os
teoremas e um guard adicional rejeita qualquer axioma no submódulo natural.
Nenhum resultado retorna como premissa da massa ou da seleção de metade.

Primalidade não reaparece: capacidade positiva basta para a torre e capacidade
ímpar basta para a seleção do centro já construído. O índice `k` é compartilhado
com a massa formal anterior; não há massa da quantidade ou amplitude global
por quantidade nova. Terminação, máximo e resolução C2 permanecem gates futuros.

## Plano real quadrático e rotação de ângulo livre

Esta etapa é uma construção local sobre `Analysis/RealQuadraticAmplitude`
e `Geometry/BalancedCarryDepthCrosswalk`, não uma porta de estado histórico.
Não houve nova consulta a repositórios históricos nem dependência lógica
deles. As referências anteriores permanecem registradas; não foram copiadas
especializações por quantidade, logaritmo ou tempo espectral.

Fonte de trigonometria: Mathlib oficial já fixada em
`81a5d257c8e410db227a6665ed08f64fea08e997`,
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` e sua API real.
Reutilizam-se `Real.sin_sq_add_cos_sq`, `Real.cos_add`, `Real.sin_add`,
os valores em zero e, somente em testes, `Real.cos_pi_div_two` e
`Real.sin_pi_div_two`. Álgebra usa `ring`; nenhum pacote novo entra no manifest.

| Objeto local | Proveniência e limite |
| --- | --- |
| `RealPlaneState`, `realPlaneEnergy` | Produto coordenado e polinômio explícito; não se identifica a norma pronta do produto com a energia |
| `rotateRealPlane` | Fórmula real usual com orientação `(1,0) → (cosθ,sinθ)`; θ é arbitrário, não fase selecionada |
| `rotateRealPlane_energy` | Expansão algébrica e identidade trigonométrica; invariância é provada, não assumida |
| `rotateRealPlane_zero`, `rotateRealPlane_add` | Valores em zero e fórmulas de adição; não definem uma lei física para θ |
| `realCriticalDepthSeed`, `realCriticalDepthSeed_energy` | Usa a amplitude local anterior e seu theorem de quadrado; nenhuma nova prova de seleção de metade |
| `realCriticalAmplitude_pos` | Consequência de `Real.rpow_pos_of_pos` aplicada à realização existente |
| `realCriticalDepthState`, `realCriticalDepthState_energy` | Rotaciona somente a semente; índice de profundidade e energia preservados, sem objeto global de quantidade |
| `balancedCarryDepth_realState_energy` | Suporte pelo centro registra proveniência do mesmo `k`; a identidade algébrica não usa essa hipótese |
| `balancedCarryDepth_realState_realizes_formalMass` | Composição com o corolário local de massa; mantém campos formais e realização real, sem uma nova massa de `n` |

Os quinze teoremas novos têm exatamente os axiomas padrão `propext`,
`Classical.choice` e `Quot.sound`. Cinco nomes de carrier/mapas também são
verificados pelo guard analítico. Foundation e Geometry matemáticas e seus
audits não foram modificados, nem o estado foi usado para selecionar a escala.
Não se construiu produto interno, norma, lei de fase, câmera ou operador.

Os imports transitivos de Mathlib mantêm sua infraestrutura analítica padrão;
a ausência de logaritmo/complexos refere-se aos novos objetos e argumentos
de prova, não a uma alegação de que tais conceitos estejam ausentes de toda
a implementação transitiva da biblioteca. Nenhuma especialização física
ou identificação de energia com norma foi extraída dessa infraestrutura.

## Reflexão quadrática e bracket local derivado

`Analysis/QuadraticReflection` e `Analysis/QuadraticCenteredBracket` foram
construídos localmente sobre a amplitude, massa e suporte de profundidade
anteriores. Nenhum repositório histórico foi consultado como fonte de nova
prova nesta rodada; as referências a `CPFormal/Finite/Bracket.lean` e às
pernas aditivas continuam registradas acima. Não foram portadas câmeras,
brackets agregados ou emparelhamentos históricos.

| Objeto novo | Origem e limite |
| --- | --- |
| `reciprocalReflection`, pernas e troca | Inversão real e multiplicação; segunda realização da arquitetura de reflexão, sem parametrização exponencial |
| `quadraticReflectedLegs_product` | Rearranjo algébrico e cancelamento do inverso em `q≠0` |
| `criticalQuadraticLegs_product` | Reutiliza `realCriticalAmplitude_sq_eq_realDepthMass`, sem redefinir o centro por uma raiz |
| `criticalQuadraticLegs_product_realizes_formalMass` | A definição anterior de massa real realiza a cota da fundação; não se inventa massa nova |
| `quadraticReflection_product` e versão crítica | A função da perna esquerda avaliada em parâmetros recíprocos; identidade local, não identificação com função clássica |
| `realCenteredReadout`, `quadraticCenteredBracket` | Readout de três termos aplicado às pernas derivadas; não copiado de `centeredSecondDifference` como definição primitiva |
| Forma fechada, fatoração, positividade e zero | Álgebra real de Mathlib; quadrado e inverso positivo, sem cálculo ou convexidade |
| `quadraticCenteredBracket_reflection` | Troca estrutural das pernas seguida da simetria do readout |
| Ponte carry-depth | Apenas composição da API local anterior; suporte do índice não é usado para provar a lei algébrica |

O paralelo com a geometria aditiva é documentado e a versão real
`realCenteredReadout_additiveLegs` é provada: conservação da soma e conservação
do produto são distintas. Não foi afirmada igualdade entre o novo bracket
e qualquer câmera histórica. Não se copiam amplitude global por quantidade,
fase, logaritmo, tempo ou uma especialização física do parâmetro recíproco.

Mathlib é a mesma dependência já fixada; `ring`, `field_simp`, cancelamento
do inverso e positividade são as ferramentas de prova. Nenhuma biblioteca
histórica ou pacote novo entra no manifest. A inversão total em zero é
explicitamente distinguida do domínio válido do produto. `q=0` dá readout
`-2*C`, e a positividade/zero único são enunciados somente em `C>0,q>0`.

31 teoremas públicos e oito definições novos são guardados. Seus footprints
contêm somente `propext`, `Classical.choice` e `Quot.sound`. Não há axioma
novo, alteração matemática na Foundation ou Geometry, nem dependência
reversa. A nova forma local não justifica retroativamente a seleção de metade.

## Câmera ímpar e soma saturada de brackets locais

Esta etapa é uma construção local sobre `CenterLegReflection`,
`CenteredSecondDifference` e `QuadraticCenteredBracket`. Não houve nova
consulta histórica como fonte de prova, import de repositório histórico
ou alteração de dependências. As referências previamente consultadas a
`CPFormal/Finite/Bracket.lean` no commit
`65d50f6db1208708e109982ba97e1d51d3039956` permanecem registradas acima.

A comparação arquitetural solicitada é:

```text
camada histórica Cp: câmera prima, balancedOffsets, pareamento por Finset
camada nova: capacidade ímpar, half explícito, pares de raios positivos
```

Isso não afirma que todo lema genérico de `Finite/Bracket` exigia primalidade.
A nova identidade é independente de primalidade: nem o código nem os
enunciados usam essa hipótese. O teste composto `b=9` verifica a diferença.
Não portamos a enumeração histórica de offsets ou sua seleção computacional.

| Objeto novo | Fonte da prova e limite |
| --- | --- |
| `sumPositiveRadii` | Recursão local em Nat, somente Init; a mesma enumeração é usada com Int e real |
| `positiveCameraRadius`, `oddCameraPair` | Índice `Fin half` lido como `val+1`, pernas existentes; cobertura, injetividade, lados estritos e reflexão provados |
| `oddCapacity_exists_cameraHalf` | Witness aberto somente numa prova; não se extrai por escolha para definir a câmera |
| `oddCameraLegCount` | Soma duas pernas por raio antes de identificar `2*h=b-1` |
| `oddCameraBracket_eq_saturatedSecondDifference` | Soma de diferenças e de constantes sobre o mesmo intervalo; nenhuma identidade histórica entra como premissa |
| `quadraticCameraBracket` | Soma dos brackets locais já derivados, não definida pela fatoração |
| Zero global | Indução na soma real não negativa, seguida do zero único local; não se usa convexidade ou cálculo |
| Reflexões independentes | Invariância local somada por máscara booleana fornecida; nenhum grupo ou fase nova |
| Versão crítica e suporte | Capacidade da câmera define a base da amplitude anterior; o mesmo índice k é certificado pelo centro, sem nova massa |

Foi mantido o carrier `Int → Int` da segunda diferença discreta; só os lemas
necessários da soma foram especializados. Não se introduziu um grupo aditivo
abstrato que exigisse Mathlib em Geometry. A máscara e os valores `q_r` são
dados livres; a igualdade `F(c±r)=C*q_r^{±1}` não foi assumida ou provada.

O audit detectou escolha quando `omega` resolveu diretamente a conjunção
dos limites do raio. Construir a conjunção explicitamente e provar as duas
desigualdades separadamente removeu essa dependência. O guard final permite
apenas `propext`/`Quot.sound` nas 23 provas geométricas novas; oito definições
são vazias. Os 24 teoremas/quatro definições analíticos usam apenas os
axiomas padrão permitidos. Todos os nomes públicos entram nos audits.
Foundation, seleção de metade e sua auditoria vazia permanecem congeladas.

## Compatibilidade multiplicativa dos offsets e crosswalk real do perfil

Na busca anterior à implementação, sobre a etapa `c8bae78`, não existia uma
interface local que transportasse a soma de offsets para multiplicação. A
implementação foi introduzida no commit `5a1bd24` e foi encontrada e reutilizada
na revisão atual, sem criar uma segunda especificação. Não houve consulta
histórica nova como fonte de prova. A especificação
`IsPositiveMultiplicativeOffsetTransport` é uma entrada semântica NOVA:
unidade em zero, preservação de soma como produto e passo unitário positivo.
Não é apresentada como uma conclusão da torre, massa ou reflexão isolada.

| Objeto/resultado | Fonte local da construção ou prova |
| --- | --- |
| Produto com offset negativo e reciprocidade | Soma `a+(-a)=0`, unidade e cancelamento real; inversão não é campo da especificação |
| Classificação natural | Indução e composição, seguida de `pow_succ` |
| Positividade e classificação inteira | Classificação natural + reciprocidade nos negativos; nenhuma classificação analítica contínua |
| Transporte canônico e unicidade | Potência inteira de Mathlib (`zpow_add₀`, `zpow_one`), classificação anterior e extensionalidade |
| Perfil `C*Q(c-x)` | Orientação explicitamente declarada; pernas de `CenterLegReflection` já existentes |
| Produto crítico do perfil | Identificação literal das avaliações com pernas quadráticas e theorem anterior da massa |
| Saturação real genérica | MESMA enumeração recursiva/pernas de Geometry, distribuição finita e soma de constantes |
| Crosswalk global | Saturação genérica → crosswalk local → soma dos brackets existentes; não expansão da fórmula fatorada |
| Zero no passo unitário | Zero global anterior da câmera quadrática + presença do raio 1 quando `half>0` |
| Inversão do passo | `inv_pow` e invariância estrutural da câmera quadrática; troca das avaliações também provada |

A construção difere de usar `branchRatio`, `cpLegTilt` ou uma potência do
argumento absoluto como premissa. Não assume `q_r=branchRatio^r` nem
`F(x)=x^(-delta)`. A potência `rho^r` emerge da compatibilidade de offsets
aditivos inteiros, com `rho=Q(1)>0` ainda livre. Nenhum transporte histórico
foi identificado com o novo sem um crosswalk adicional.

O raio horizontal não é profundidade vertical: não se coloca `k` no expoente
de `rho`, nem se identifica `rho` com razão entre amplitudes de níveis.
O capstone de suporte mantém a mesma massa formal no produto por par e não
participa da classificação do transporte. Não se usa log/exp para selecionar
ou classificar o passo; não se abre fase ou uma leitura posterior.

Todos os novos módulos estão em Analysis. Foundation, Geometry, scripts,
manifest e dependências históricas permanecem inalterados. São 47 teoremas
públicos e nove definições guardadas, footprint limitado a `propext`,
`Classical.choice`, `Quot.sound`. A fonte histórica registrada nas etapas
anteriores continua referência de comparação, não dependência lógica.

A revisão removeu do transporte o import das pernas quadráticas: sua única
dependência direta é `Mathlib.Data.Real.Basic`, com guard explícito de ausência
de `Real.log`/`Real.exp`. Os corolários por divisão derivam das fatorações já
provadas; o corolário C3 une saturação genérica e crosswalk local. Os testes
acrescentados verificam as quatro pernas com passo `1/2`, o perfil constante
para passo `1` e o total racional `367/48` na capacidade composta 9.


## Forma Centro–Pernas local e sua câmera

A forma local em `CenterLegForm` foi integrada em `698778b`. A construção
coordenada reutiliza `RealPlaneState`, `rotateRealPlane`, o readout escalar e
a reflexão recíproca existentes. Define posições e síntese vetorial antes
de provar fatoração. A energia sob escala é álgebra de `x²+y²`; a eliminação
angular usa explicitamente `rotateRealPlane_energy`. A especialização crítica
reutiliza a energia da semente e o quadrado da amplitude anteriormente provado.
Não fornece nova seleção da massa, metade ou parâmetro angular.

A câmera em `CenterLegCameraForm` soma literalmente energias locais pela
enumeração existente `sumPositiveRadii`. Fatoração, independência angular e
zero canal a canal compõem teoremas anteriores, incluindo
`sumPositiveRadii_real_zero_iff`. O defeito comum sai da soma por distribuição;
seu critério de zero usa energia inicial total positiva, sem exigir todos
os estados positivos. O caso vazio continua degenerado.

O crosswalk com a câmera escalar é soma ponderada dos quadrados de brackets
locais unitários. Sob positividade local apropriada, os critérios de zero
coincidem, sem igualdade entre readouts. Dois vetores opostos dão energias
somadas `2` e energia da soma `0`; dois canais unitários em `q=2` dão energia
`1/2` e quadrado do bracket total `1`. São exemplos Lean no audit, não
hipóteses de prova. Nenhum operador, norma abstrata ou fonte histórica foi
importado para fechar essas identidades. A próxima fronteira é uma lei
entre bases, ausente destas construções dentro de uma câmera.

Os 26 teoremas e seis definições têm guards analíticos e `#print axioms`,
permitindo apenas `propext`, `Classical.choice`, `Quot.sound`. As camadas
Foundation/Geometry e as dependências externas permanecem inalteradas.


## Atlas coordenado de energia: interface nova e auditoria histórica

Checkpoint das Formas local/câmera: `cf10920be982fe6a45df726829624c7df9f541c8`.
A rodada do atlas foi desenvolvida em `atlas-energy` a partir desse main.
A busca local por atlas, multibase, all-bases, partição, pesos, normalização
e conservação encontrou apenas normalizações internas a cada base e nenhum
princípio que selecione pesos entre bases. A tabela de módulos também foi
inspecionada: não havia carrier público de atlas antes desta rodada.

| Referência consultada | Versão e arquivos |
| --- | --- |
| green-frame-theorem | Clone local `green-frame-theorem-limit`, origin do repo solicitado, `12445c08087fa0c5fc5b2350f3455e09bc6b8b42`; PositionalDepth; ElementaryAtlasCoordinates, Summability, Camera, Isometry; HorizontalResolution |
| native-carry-spectral-weyl | `2236bc5d881b7945ff1737e4b6d158ab733ea532`; Infinite/GramKernel, CameraCompletion, Naimark |
| native-carry-c3-crosswalk | `d9e9e3a7469cb2a95ad3a07d08d0c1a860377ec0`; PrimeAllBasesCameraForm, RealPlaneCameraExtension, ArithmeticNonlocalTrace |
| Dois arquivos C3 ausentes do clone atual | Snapshot local do MESMO repo em `carry-hp-notes-audit-20260904/snapshots/native-carry-c3-crosswalk`, versão registrada em snapshots.json `1e9e06e1d51d176a909c187828f7c880e5d1207d`; CompletedTfvdNaimarkFeasibility e CompletedTfvdGreenIntertwining |

Esses arquivos foram lidos como referência, sem compilar/importar seus
pacotes. Nenhum theorem deles é premissa dos novos resultados. As fontes
mostram três objetos diferentes: (1) elementary atlas GreenFrame, coordenadas
weighted-ℓ² com partição e Parseval literal; (2) CameraHilbert Spectral-Weyl,
Gram intrínseco não diagonal e completion/Naimark; (3) C3, extension prime-to-
all-bases, packing injetivo e preservação de energia/zero sob packaging.
Não foi provada identificação entre esses objetos, nem entre eles e o novo.

O GreenFrame escolhe profundidade por `padicValNat` e atividade por
`depth_b(n) * log b`, depois normaliza. Essa seleção NÃO foi copiada.
A profundidade local continua definida pela torre residual, e nenhum
`Real.log`/`Real.exp` entra nos novos módulos. Não há peso chamado canônico.
Nenhuma dependência nova foi adicionada ao lakefile ou manifest.

`AdmissibleAtlasPartition` é uma NOVA entrada semântica explícita, não um
resultado da torre: peso real, envelope finito por coordenada, não negatividade,
anulação fora do envelope e soma unitária. Seu índice `AtlasBase` representa
naturais `b≥2`, sem primalidade; não exige evento `b|n` nem determina a
capacidade ímpar da câmera em cada rótulo. A origem de qualquer instanciação
aritmética ainda deve ser provada. As partições numéricas no audit são somente
witnesses de teste e não uma lei de seleção.

A raiz quadrada escala o `RealPlaneState` já existente. A identidade de energia
usa `scaleRealPlane_energy` e `Real.sq_sqrt`; conservação usa a soma unitária.
A união recursiva de suportes segue `sumPositiveRadii`, e a troca das somas
é finita. A energia do atlas vem literalmente de `centerLegCameraEnergy`;
o fator radial comum sai da soma e só então a conservação identifica a energia
inicial. A eliminação angular reutiliza o theorem da câmera e, transitivamente,
a rotação local. Zero iff centro reutiliza o critério comum da câmera.
Não se introduzem norma abstrata, Gram, completion ou leis entre profundidades.

Resultado: STRUCTURAL PASS. Conservação e transporte da Forma estão provados
para a interface; seleção de partição all-bases permanece INTERFACE ONLY.
Há 25 teoremas, quatro definições, um carrier e uma estrutura novos, todos
com guards e impressão de axiomas. O footprint continua limitado aos três
axiomas padrão de Analysis. Foundation e Geometry permanecem inalteradas.


## Crosswalk residual primo e partição de vozes não seed

Checkpoint inicial: `f0c4b240e57ff7b5d4f38cfabee0de15e65f682f`, atlas parametrizado.
Branch da rodada: `prime-voice-atlas`. Referência histórica consultada: clone
local `primos`, HEAD `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`.

Arquivos Lean lidos como referência:

- `CPFormal/Carry/CpMultibaseCameraAtlas.lean`
- `CPFormal/Carry/CpMultibaseCameraAtlasHilbert.lean`
- `CPFormal/Analytic/CpPrimeCarryDefectBessel.lean`
- `CPFormal/Analytic/CpPrimeAdimensionalLsbCrosswalk.lean`
- `CPFormal/Analytic/CpGenuineSimpleRootLsbLedgerBessel.lean`
- `CPFormal/Analytic/CpGenuineSimpleRootLsbLedgerExactDuality.lean`

Notas consultadas: `docs/recovered/2026-08-01/ADIMENSIONALIZACAO_LSB_MULTIBASE_PRIMA.md`
(profundidade e energia), `C2_EQUACAO_ANGULAR_PROJETIVA_MULTIBASE.md` (frame
logarítmico e distinção das projeções) e `docs/CLAIM_LEDGER.md` (status das
pontes). As rotas históricas Bessel/LSB/Green não foram transportadas.
Nenhum código ou theorem do Primus foi importado ou copiado; nenhuma dependência
externa foi acrescentada. Em particular, os gaps LSB-PARSEVAL-GREEN-CROSSWALK,
HIL-001 e HIL-002 não são premissas do resultado novo.

A entrada causal nova é o theorem LOCAL já existente
`hasCarryDepthAtLeast_iff_dvd_pow`. Composto com
`Nat.Prime.pow_dvd_iff_le_factorization` do Mathlib, dá a equivalência para
primo p, n≠0 e todo k. Nat.factorization não define a profundidade residual;
padicValNat não substitui a torre. A própria API clássica tem sua implementação
bibliotecária, sem que sua representação seja promovida à definição geométrica.
O crosswalk usa somente o módulo de fatoração Basic do Mathlib, sem Real.log,
e fica em Analysis porque Geometry exclui Mathlib pela política vigente.
Não ampliamos a política nem os imports de Geometry.

A reconstrução multiplicativa usa Nat.prod_factorization_pow_eq_self.
A decomposição das vozes usa Real.log_nat_eq_sum_factorization, cuja prova
bibliotecária aplica logaritmo ao produto reconstruído; não replica a prova
histórica. O expoente que essa representação lê é identificado pela família
de thresholds residual. A soma dos pesos normalizados decorre dessa identidade
e da positividade de log n para n>1. É uma seleção DERIVADA de pesos primos
para quantidades não seed, não uma normalização externa entre todas as bases.

O denominador difere da soma all-natural-bases do GreenFrame: contém somente
as coordenadas primas da fatoração única e é exatamente log n. Não identificamos
os dois atlas. Reconstrução por coordenadas primas não prova que câmeras
compostas sejam combinações lineares no carrier geométrico novo.

A incompatibilidade com AdmissibleAtlasPartition foi mantida explícita:
quantidade n e raio/canal r não têm crosswalk; em n=1, todas as vozes/pesos
são zero. Um theorem refuta a tentativa de instanciar a família literal em
todo natural. Não se criou seed nem se alterou a obrigação unitária.
Resultado B, com partição prima NONSEED-ONLY e INDEX-CROSSWALK-OPEN para o atlas.
Não há nova instância canônica da Forma Centro–Pernas.

Os 26 nomes novos (24 teoremas e duas definições) possuem guards e #print axioms
na política padrão de Analysis. Foundation, Geometry e lakefile/manifest
permanecem inalterados. Os testes incluem 12, 64, 5, 1, zero, nível zero,
base 2, primo ímpar e peso zero de rótulo composto.


## R2 — genealogia recuperada e reescrita local

Checkpoint novo: `4cc4261fb2910c72d35e1746c983a28999f6d7eb`.
Branch: `r2-real-tfvd-green-valve`, em worktree isolado.

| Corpus | SHA exato das fontes consultadas |
| --- | --- |
| carry-self-adjoint-operator | `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa` |
| primos | `e2a723b4ec3e645539de0b9ca881951d93259cda` |

O checkout primos existente era anterior aos bridges solicitados. A consulta
usou `git show` do main acima; o checkout e suas alterações foram preservados.
No carry, usaram-se objetos COMMITADOS do HEAD indicado, não arquivos dirty.
O main remoto observado do carry era `8e85d06c44f31457e231d4f4528f2af4f5bfacb3`;
essa versão não foi a fonte do porte R2. Os SHAs da tabela são os efetivamente lidos.

### Arquivos lidos integralmente

Em `CarrySelfAdjointOperator/`, todos no SHA carry acima:

- `CanonicalTowerChannel.lean`
- `CausalBracketStateUniqueness.lean`
- `CompletedC3ValveNaturality.lean`
- `DiscreteProjectiveReconstruction.lean`
- `DiscreteValve.lean`
- `DiscreteValveSeries.lean`
- `GreenMultiplicativeValveBridge.lean`
- `GreenMultiplicativeValveMass.lean`
- `MultiplicativeValve.lean`
- `ProjectiveDepthCoordinate.lean`
- `ProjectiveDepthEquivalence.lean`
- `ProjectiveDepthInverse.lean`
- `ProjectiveValveAlgebra.lean`
- `ProjectiveValveEquivalence.lean`
- `ProjectiveValveFundamentalTheorem.lean`

Em `CPFormal/Analytic/`, todos no SHA primos acima:

- `CpCarryL2UnilateralShift.lean`
- `CpCarryWeightedVerticalBracketTrace.lean`
- `CpCarryWeightedVerticalGreen.lean`
- `CpCarryWeightedVerticalReturn.lean`
- `CpCarryWeightedVerticalTfvd.lean`
- `CpCarryWeightedVerticalTfvdFinite.lean`
- `CpCarryWeightedVerticalTfvdIdentity.lean`
- `CpNativeCarryMobiusLogDerivativeGuardrail.lean`
- `CpPrimeDepthLogWaveBridge.lean`
- `CpPrimeTowerCarryMangoldtBridge.lean`
- `CpUniversalCarryStructuralPersistence.lean`

### Crosswalk recuperado → núcleo local

| Fonte histórica e theorem | Reescrita local / decisão |
| --- | --- |
| DiscreteValve: `discrete_valve`, `bracket_eq_zero_iff_affine` | RealDiscreteValve: `realDiscreteGreenReconstruction`, kernel afim; manteve-se a generalidade AddCommGroup sem abstração nova |
| DiscreteValveSeries: `one_sub_X_sq_mul_greenKernelSeries`, `mk_discrete_valve` | RealDiscreteValveSeries: mesmas identidades multiplicativas em séries formais |
| CausalBracketStateUniqueness: `causalBracketReconstruction`, `causalUnitBracket_reconstruction`, `eq_of_seed_eq_of_causalUnitBracket_eq` | Somente recorrência causal e unicidade necessárias, dentro de RealDiscreteValve; nenhuma câmera histórica ou estado analítico |
| ProjectiveDepthCoordinate/Inverse/Equivalence | RealProjectiveGreenValve: coordenadas inversas, transportes, round-trips e jacobianos |
| GreenMultiplicativeValveBridge/Mass: `derivative_toProjective_greenLogPotential`, `derivative_projectiveGreenMass` | Potencial e massa Green reais por especialização; cancelamento exato sem limite |
| MultiplicativeValve + CanonicalTowerChannel | RealTowerValve: deconvolução triangular, integração e seus inversos; omitidas especializações aritméticas e operações finitas não necessárias |
| ProjectiveValveFundamentalTheorem/Equivalence/Algebra | RealMultiplicativeValve: ODE normalizada, unicidade, massa↔curvatura e lei soma→produto; sem flows/orbits/spans |
| DiscreteProjectiveReconstruction | RealDiscreteProjectiveReconstruction: mesmos dois dados de bordo e massa normalizada; campo local `projectiveMass` |
| CompletedC3ValveNaturality: primeiros theorems de gauge | RealCarryTfvd: versão real, eta independente, e crosswalk Green escalar↔Green aditivo |
| CpCarryWeightedVerticalGreen + CpCarryL2UnilateralShift | RealCarryGreenKernel/L2: somabilidade, bound, shifts e Green em ℓ²(ℕ,ℝ) |
| CpCarryWeightedVerticalBracketTrace/Return/Tfvd/TfvdFinite/TfvdIdentity | RealCarryWeightedValve: trace/return, bracket/return, coordenadas Green e GB+RTr=I, todos sobre ℝ |
| CpUniversalCarryStructuralPersistence: núcleo base-neutral | Capstone local para toda base b≥2; não portado o certificado histórico maior |

A busca anterior ao porte procurou realizações reais/genéricas equivalentes
nas árvores CPFormal e CarrySelfAdjointOperator. O núcleo discreto/projetivo
já era genérico; isso foi preservado. Não foi encontrada uma TFVD real ℓ²
com esses mesmos operadores. Na implementação vertical consultada, ℂ é o
campo escalar da construção de shifts; as provas foram reescritas em ℝ e
compiladas localmente. Não foi introduzida complexificação nem dependência
lógica de um repositório histórico. Mathlib permaneceu no SHA já fixado.

`bracket_eq_realCenteredReadout` é o crosswalk ao readout real local anterior:
o mesmo stencil 1,-2,1 atua agora no índice vertical. Não identifica eixos.
`criticalVerticalAmplitudeRatio` usa `realCriticalAmplitude b 1`, cuja origem
local é torre→massa formal→metade→realização; não copia primeCarryAmplitudeRatio.

### Consistência downstream, sem porte

PR 47 do primos: `Formalize prime-tower carry / von Mangoldt bridge`, MERGED,
merge SHA `298a54f7be6111b6f83c4fee4de3bf3fed9f4a95`.
Os três bridges aritméticos foram lidos para registrar sua fronteira. Nenhum
Lambda/Mangoldt, Möbius, LSeries, Zeta, wave/Dirichlet ou consequência de zeros
foi portado. O crosswalk primo e `log_eq_sum_primeCarryVoice` já existem
localmente e não são premissas da TFVD. Também não foram portadas as camadas
C3 completion, cumulantes ou momentos dos módulos históricos maiores.

Os hashes dos conteúdos consultados estão em `R2_SOURCE_MANIFEST.json`.
Todos os nomes públicos novos recebem guards e #print axioms no audit.


## Canário downstream: relógio material logarítmico × TFVD vertical

Rodada 2026-10-02, branch `audit-material-log-tfvd`, sem commit/merge/push.
Fonte consultada: carry-self-adjoint-operator,
`cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
Dependência CPFormal auditada em
`65d50f6db1208708e109982ba97e1d51d3039956`.

- `NativeLogEvolution.lean`: os quatro fatos de gerador/log-basis/orbit/finite
  evolution solicitados; somente existência e convenção material/signo auditadas.
- CPFormal `CpInfiniteRealSpectralGenerator.lean`: frequência `log(n+1)` e
  fase com sinal negativo; `CpRealSpectralGenerator.lean`: evolução finita.
- CPFormal `CpNativeCarryLogPhaseOrbit.lean` e `CpRealSpectralOperator.lean`:
  material n enumera o ponto positivo n+1; fatoração da semente na órbita.
- `PositionalDepthRefinement.lean`, `FinitePositionalObservableShift.lean`,
  `C2FiberDepthLogTransport.lean` e CPFormal `C2OddCorePushforward.lean`:
  quantidade fixa/chart-depth e fibra crescente/core-depth são distintos.

Porte local: SOMENTE a fórmula real do ângulo material `-t log(n+1)` e o
canário solicitado de duas quadraturas por fibra vertical real. Nenhum import
histórico; nenhum resultado de autoadjunção ou consequência espectral é usado
nas provas do novo canário. Intertwining e roundtrip são derivados da
linearidade real e do theorem R2 existente, sem identificar material n com k.
A fonte nativa ainda não possui encoder identificado nesse carrier analítico.
A torre discreta retém quantidade/depth; isso não fornece por si o encoder ℓ².

Detalhes, nomes, status e axiomas:
[MATERIAL_LOG_TFVD_CANARY.md](MATERIAL_LOG_TFVD_CANARY.md).

## Auditoria da fonte ponderada: material sample versus profundidade

Rodada 2026-10-02, branch de trabalho audit-weighted-source-diagonal,
baseline geometry-of-numbers 93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f.
Sem commit, merge ou push. R2 permaneceu inalterado.

Snapshots históricos somente para leitura/auditoria:

- carry-self-adjoint-operator: cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa;
- primos: 8c4b7fdf65a49d1d0febe8193d56e2cfb2191260;
- dependência CPFormal no carry: 65d50f6db1208708e109982ba97e1d51d3039956.

Fontes obrigatórias lidas:

- CPFormal/Analytic/CpNativeCarryWeightedSpectralState.lean:
  definição e apply por rfl, trace, bracket e especialização de amplitude
  por base. O conteúdo é idêntico nos dois snapshots CPFormal; SHA256
  ede53efc04e972b04d80178e23ad41b6fc552b2e68f8e15b4dd7a1b542ab24bc.
- CarrySelfAdjointOperator/NativeLogEvolution.lean: o índice material
  enumera o ponto positivo n+1, com relógio log(n+1).
- CarrySelfAdjointOperator/C2FiberDepthLogTransport.lean: centro 2^k m,
  incremento vertical log 2 e correções logarítmicas preservadas nas pernas.
- CarrySelfAdjointOperator/PrimeDepthTfvdLogJetCrosswalk.lean: ledger primo,
  log-factorization e igualdade de prefixos mantendo os samples existentes.
- CarrySelfAdjointOperator/MultibaseCameraLogTfvdChannelTransport.lean:
  câmera p versus slot de log-slope; naturalidade da soma de canais e TFVD.

Fontes complementares efetivamente usadas no diagnóstico:

- CarrySelfAdjointOperator/C2AlignedBoxOddCoreCrosswalk.lean:
  factorization canônica, core positivo/ímpar e depth do centro alinhado.
- CPFormal/Carry/PositionalDecomposition.lean: quotient/residue, reconstrução
  única em janela escolhida e profundidade máxima/core.
- CPFormal/Carry/C2Adjacent.lean e CPFormal/Carry/C2Depth.lean:
  oddLegEquivIncidence, centro adjacente e effectiveDepth_eq_centerDepth.
- CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean:
  distinção entre escala/log e profundidade de divisão exata.
- CPFormal/Analytic/CpRealSpectralOperator.lean e CpReflectedEndpoint.lean:
  origem de realSpectralState e enumeração material positiva n+1.
- CPFormal/Analytic/CpCarryL2UnilateralShift.lean e
  CpCarryWeightedVerticalBracketTrace.lean: carriers e slots do trace/bracket.
- CarrySelfAdjointOperator/NativeDepthCpLogJetCommutatorCrosswalk.lean:
  consulta pontual da dependência de clock numa torre, sem usar resultados
  radiais/zero-confinement downstream.
- Referências ao weighted state em C3ProjectiveCompletedJetBridge,
  C3ProjectiveHilbertReadoutKernel e KernelConstructionAudit foram buscadas
  para verificar se forneciam reindexação posicional; não fornecem a ponte
  exigida. Nenhuma conclusão de completion/kernel foi usada como premissa.

Crosswalk local usado para os DOIS certificados novos:
GeometryOfNumbers.Analysis.primeResidualDepth_iff_le_factorization.
As APIs Foundation emergentResidualTower/value/expansion/uniqueness e
Geometry HasCarryDepthAtLeast/divisibility foram auditadas sem alterações.
O único porte matemático desta rodada é a composição desse crosswalk já
local com a fatorização de 3 em Mathlib. Nenhuma definição histórica de
fonte foi copiada e nenhum import histórico foi adicionado.

Resultado: SEMANTIC_DIAGONAL_GAP, leitura diagonal apenas
DIAGONAL_ONLY_REPRESENTATION. Nenhum theorem recuperado identifica
sample n com a profundidade posicional de n+1. A leitura universal de
profundidade binária intrínseca foi refutada por
sampleTwo_materialThree_binaryDepth_iff e
materialSampleIndex_not_intrinsicBinaryDepth.
Isso não invalida a fonte unidimensional e não prova inexistência de
qualquer encoder; impede afirmar o encoder pretendido nesta rodada.

Relatório: [HISTORICAL_WEIGHTED_SOURCE_DIAGONAL_AUDIT.md](HISTORICAL_WEIGHTED_SOURCE_DIAGONAL_AUDIT.md).
Tabela anterior à construção: [WEIGHTED_SOURCE_GATE_ZERO.md](WEIGHTED_SOURCE_GATE_ZERO.md).
Manifesto com SHA256, referências arquivadas, logs e resultados:
weighted_source_audit_work local e weighted-source-diagonal-artifacts no llm.

## Fibra C2: dinâmica real de contração e rotação

Rodada 2026-10-02; branch canary-c2-fiber-real-dynamics, baseline local
93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f.
Sem commit, merge ou push. R2 e todos os canários anteriores preservados.

Única fonte histórica consultada nesta rodada:
carry-self-adjoint-operator,
cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa,
CarrySelfAdjointOperator/C2FiberDepthLogTransport.lean.
Nenhum import do repositório histórico foi adicionado.

Crosswalk de proveniência para C2FiberRealDynamics:

| Origem | Papel original | Alvo local / justificativa |
| --- | --- | --- |
| c2FiberPoint/centered/succ | Core fixo m, depth variável k, offset epsilon | Coordenada literal e doubling; centro convertido ao natural 2^k m |
| c2FiberPoint_centered_log/increment | Log do centro de fibra crescente | Reescritos por Real.log_mul/log_pow e ring, com m>0 |
| c2FiberPoint_log_center_defect/increment_defect | Correção exata da perna | Defect explícito local; hipóteses físicas x_k,x_(k+1)>0 fortalecem o não anulamento histórico |
| right_log_defect_pos/right_log_increment_lt | Correção realmente não nula e incremento distinto no exemplo | Positividade geral do defect direito e exemplo exato log 9-log 5<log 2, sem aproximação |
| Geometry.hasCarryDepthAtLeast_iff_dvd_pow, já local | Proveniência residual de profundidade | Suporte de k para 2^k m e ausência em k+1 sob core ímpar; não é identificação de sample |
| realCriticalDepthState/energy, já local | Amplitude de depth e rotação livre | Estado físico pointwise seleciona ângulo por log do ponto da fibra; energia reutilizada sem alteração |
| realCriticalAmplitude_succ_verticalRatio, já local | Razão consecutiva da amplitude já derivada | Passo real com eta=criticalVerticalAmplitudeRatio 2 |
| rotateRealPlane_add/scaleRealPlane, já locais | Ação angular real e escala de coordenadas | Core/depth angular, fixed step e step composto com defect; duas pequenas lemmas privadas de composição |

Não foram portados sampling matrices, commutadores, Newton/Green modes ou
outros resultados do restante do módulo histórico. Nenhuma fonte diagonal
foi recuperada. A escolha de fase usa o ponto material 2^k m+epsilon,
não um sample arbitrário. O estado exige core e material point positivos.
Odd m identifica k com a profundidade intrínseca exata; sem oddness o
enunciado de proveniência garante somente um nível suportado.

Resultado: CENTER_FIXED_STEP=PASS, LEG_EXACT_CORRECTION=PASS.
A iteração do passo central é theorem por indução a partir da source
geométrica independente, não sua definição. As correções das pernas
permanecem exatas.

Auditoria downstream: a TFVD R2 continua escalar em eta. O peso rotacional
eta R_omega é apenas um próximo-alvo documental, sem implementação.
THREE_PHASE_CENTER_LEG_GATE permanece OPEN: o readout de ângulo comum
não foi aplicado às três fases logarítmicas físicas.

27 nomes públicos e exemplos formais adicionados ao Analysis/Audit.
Footprints permitidos; nenhum axioma extra.
Relatório: [C2_FIBER_REAL_DYNAMICS_CANARY.md](C2_FIBER_REAL_DYNAMICS_CANARY.md).
Hashes, scripts e logs: c2_fiber_real_dynamics_work local e
c2-fiber-real-dynamics-artifacts no llm.

## Massa quadrática do ramo C2 como energia de órbita real

Rodada 2026-10-02, branch canary-c2-branch-orbit; baseline
93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f.
Sem commit, merge ou push. R2 e os canários anteriores preservados.

Histórico somente para leitura:
formalizacao_C2 em dc35555879e3c0f188508c729c4a0ea31be246fb.
LeanC2/Operators/BranchBarrier.lean e LeanC2/Operators/Tilt.lean estão
sem alterações nesse checkout; outras alterações históricas não foram tocadas.
Nenhum import histórico ou build do checkout histórico foi usado.

BranchBarrier consultado integralmente: branchWeightSigma,
branchNormSqSigma, branchWeightSigma_half, branchNormSq_closed_form,
branchNormSq_half, branchNormSq_lt_one_of_half_lt,
branchNormSq_gt_one_of_pos_of_lt_half, branchNormSq_barrier_eq_one e
branchNormSq_barrier. Wrappers complexos não foram portados.

Crosswalk para C2BranchOrbitCanary:

| Origem | Papel | Alvo / justificativa local |
| --- | --- | --- |
| branchWeightSigma = 2^(-2 sigma) | Razão quadrática radial histórica | Quadrado da razão comparativa 2^(-sigma); c2RadialEnergyRatio_eq_legacyBranchWeight |
| branchNormSqSigma = 2 tsum q^(j+2) | Massa das duas direções desde depth 2 | Massa DEFINIDA pela energia da órbita com t; c2BranchOrbitMass_eq_legacyBranchNormSq |
| Primeiro depth histórico j+2 | Admissão C2 de centro divisível por quatro | Para core ímpar, 4 dvd 2^k*m iff 2≤k; preserva a restrição histórica sem afirmar unicidade de toda regra de admissão |
| Dois ramos | Offsets C2 -1,+1 | Pontos distintos/cardinalidade dois nas coordenadas locais; não soma vetorial nem fases iguais |
| realCriticalDepthSeed 2 0, preexistente | Seed unitário real (1,0) | Usado sem normalização nova na órbita iterada |
| realCriticalDepthState/amplitude e c2CenterFiberStep, preexistentes | Objeto crítico já derivado | Igualdade de funções F_(1/2,t)=c2CenterFiberStep t, anterior à classificação de massa |
| Barreira histórica | Série geométrica real | Somabilidade para sigma>0, forma fechada e três critérios reconstruídos em Lean |

A família em sigma é exclusivamente deformação/comparison family downstream.
Não usa massa unitária para definir/selecionar amplitude crítica nem para
modificar a fundação da metade. O tempo permanece na definição da massa,
e sua eliminação é theorem por invariância angular.
O peso radial q_branch não é a deformação recíproca da Forma Centro–Pernas.

Tilt foi auditado depois do fechamento da órbita/massa:
tiltBracket e normalizedTiltCurvature são leituras locais de curvatura.
bracket_tilt_zero_iff_delta_zero e normalizedTiltCurvature_zero_iff_delta_zero
mostram o mesmo locus da massa menos 1 quando delta=sigma-1/2, sigma>0,c>1.
Os sinais são opostos fora da metade; não foi forçada igualdade.
Classificação: TILT_ZERO_LOCUS_ONLY_MATCHES_BRANCH_DEFECT.
Nenhuma definição ou prova de Tilt foi importada/portada.

29 nomes públicos, 10 exemplos formais e guards/prints no Audit.
Relatório: [C2_BRANCH_ORBIT_CANARY.md](C2_BRANCH_ORBIT_CANARY.md).
Hashes dos conteúdos, logs, footprints e preservação:
c2_branch_orbit_work local e c2-branch-orbit-artifacts no llm.

## Realização Hilbert real do operador de ramo C2

Rodada downstream na branch `canary-c2-branch-isometry`, sem commit/merge/push.
Base geometry-of-numbers: `93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`.
Implementação: `Analysis/C2BranchIsometryCanary.lean`; relatório:
`docs/C2_BRANCH_ISOMETRY_CANARY.md`.

- formalizacao_C2, SHA `dc35555879e3c0f188508c729c4a0ea31be246fb`:
  `operadores/cp_branch_operator.py`, leitura integral. Especificação C2:
  duas direções, k0=2, coeficiente exp(-k(sigma+it)log2), massa quadrática
  geométrica. Python não executado nem usado como prova.
- Recuperação local, sem mudanças: `C2BranchOrbitCanary`, energia iterada,
  somabilidade, crosswalk legacy, massa crítica e igualdade do passo crítico;
  `C2FiberRealDynamics`, passo central preexistente.
- Mathlib da versão fixada em lake-manifest: `PiL2`, `l2Space`, `Adjoint`,
  séries reais/produtos. Carrier euclidiano, identidade de norma l2 e
  `LinearIsometry.adjoint_comp_self`. Nenhuma geometria nova importada.

Auditoria da relação com Parseval (somente leitura, nunca dependência da prova):

- carry-self-adjoint-operator, SHA
  `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`:
  `CarrySelfAdjointOperator/BR2GreenFrameDslopeLimitBridge.lean`,
  trechos de definição da análise CLM e Parseval, linhas 20–74.
- Dependência GreenFrame desse checkout, SHA
  `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`:
  `GreenFrame/Concrete/Analysis/CanonicalParseval.lean`,
  `ConcreteSplitOperators.lean`, `ConcreteSplitBounds.lean`,
  `GreenDepthSplit.lean`, `GreenDepthSectorEnergy.lean`,
  `GreenAnalysisVector.lean`, `GreenStencilComplex.lean`,
  `InfinitePartition.lean` e `FrameOperator.lean`, trechos de tipos,
  definições e empacotamento. `T=((seed,residual,G1),G>=2)` tem coordenadas
  de stencil Green, sem inclusão/intertwining de W encontrada.
- Buscas de consistência em `primos`, SHA
  `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`, CPFormal/Analytic,
  não forneceram o objeto Parseval procurado; nenhum módulo portado.

Classificação limitada aos objetos auditados: `NO_RELATION_FOUND` entre
este W e um bloco do T concreto. A isometria e `W*W=I` de W foram
construídas independentemente da normalização Parseval. R2 permanece fechado.

## Source material física C2 por incidência e correção exata das pernas

Branch `canary-c2-physical-material`; base geometry-of-numbers
`93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`. Sem commit/merge/push.
Módulo `Analysis/C2PhysicalBranchCanary.lean`; relatório
`docs/C2_PHYSICAL_BRANCH_CANARY.md`.

Referência histórica única para endereçamento: formalizacao_C2,
`LeanC2/Foundations/Dyadic.lean`, commit
`dc35555879e3c0f188508c729c4a0ea31be246fb`.
O arquivo está modificado: conteúdo consultado SHA256
`a7b17be4ee2a41064886ef4179495aa229c3ee73da8e5028f382e9a717944c98`.
A alteração troca o import Basic por BasicCore. HEAD, working copy e diff
arquivados; fonte histórica não alterada nem importada como prova.
Lidos BranchSign/toInt, natDescendant/cast/address_unique,
keff_left_leg/right_leg, bracket_bijection_odd_ge_three e seus lemas.

Crosswalk local: Fin 2 de direções preexistente, depth j+2, natural
2^(j+2)m ±1, injetividade para core positivo fixo, thresholds de profundidade
relacional dos dois vizinhos para core ímpar e recuperação do core por divisão.
Não portados v2/padicValNat/keff nem a bijeção global de todos os cores.
Provas usam a relação Geometry.HasCarryDepthAtLeast e seus capstones locais.

Reutilizados sem mudança C2FiberRealDynamics, C2BranchOrbitCanary e
C2BranchIsometryCanary. O log-defect das pernas é preservado literalmente;
incidência por extensão zero e rotação coordenada são isometrias distintas.
Source crítica e identidade do adjunto são composições de isometrias.

Auditoria adicional explicitamente solicitada do tipo de entrada GreenFrame:
dependência do checkout carry-self-adjoint-operator, SHA
`cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`,
`GreenFrame/Concrete/Analysis/GreenStencilComplex.lean:16` (State) e
`ConcreteSplitOperators.lean:20–65` (tipo/definição de concreteAnalysisOperator).
Leitura somente de tipos/definições; nenhum import ou porte desses módulos.
Mesmo índice PNat; R² euclidiano por material é a realificação natural.
Empacotamento complexo e conexão da nova source ao T concreto não implementados.
Classificação READY_FOR_GREEN_ANALYSIS_INPUT apenas quanto a índice/carrier.

PASS; PROVENANCE_GAP_CLOSED_FOR_FIXED_C2_CORE. Nenhuma recuperação da source
histórica diagonal q^n ψ_t(n), nenhum resultado TFVD/Green/Parseval novo.
39 nomes públicos auditados; logs, conteúdo histórico dirty e hashes
arquivados em c2_physical_branch_work / c2-physical-branch-artifacts.

## Global odd-material C2 physical source canary (2026-10-02)

Working branch: `canary-c2-global-odd-source`; base HEAD
`93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`. No commit, merge or push.

New module: `Analysis/C2GlobalPhysicalBranchCanary.lean`. It continues the
unchanged `C2PhysicalBranchCanary` using its critical local isometry, exact leg
phase correction, incidence coordinates and relational leg-depth recovery.
The new explicit inverse selects the neighbor divisible by four and its odd
complement. `PrimeResidualDepthCrosswalk.lean` certifies the use of the classical
factorization exponent as a representation of the already-existing relational
thresholds. This does not replace Geometry's depth definition with valuation.

Read-only historical reference: `formalizacao_C2/LeanC2/Foundations/Dyadic.lean`,
HEAD `dc35555879e3c0f188508c729c4a0ea31be246fb`, dirty working-content SHA256
`a7b17be4ee2a41064886ef4179495aa229c3ee73da8e5028f382e9a717944c98`.
Consulted `bracket_bijection_odd_ge_three_exists`,
`natDescendant_address_unique`, `bracket_bijection_odd_ge_three`; no historical
import or theorem is a dependency. The new inverse is explicitly arithmetic;
no `Classical.choose` selects an address or enumerates cores.

Norm construction: local real linear isometries → square-summability over the
product index (nonnegative Fubini) → global real linear isometry → bijective
material reindexing. The local geometric series is not reproved. Each single
core agrees with the preexisting physical operator at every odd material
coordinate, including zeros off its range.

Final index-only audit: historical GreenFrame dependency at
`cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`,
`GreenFrame/Concrete/Analysis/GreenStencilComplex.lean`, declaration `State`:
`ℓ²(PNat, ℂ)`. This is a read-only type comparison, not a proof import or an
identification with any analysis operator.

Scope: positive odd cores and odd material integers at least three. Seed one
and the even sector are excluded. Amplitude is `2^(-k/2)` at the decoded branch
depth; phase is rotation by `-t*log(n)` at the material point. Never replace
this amplitude by `n^(-1/2)`. The historical diagonal source is not recovered.
See `docs/C2_GLOBAL_PHYSICAL_BRANCH_CANARY.md` for proofs and validation.

## Recovery round 9 — PASS_RESTRICTED_GRAM

Read-only source: `/home/thlinux/carry-c2-source-raw-green` at `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`; uncommitted source is identified by SHA-256.

- `GeometryOfNumbers/Analysis/C2GlobalGreenBridge.lean` ← `/home/thlinux/carry-c2-source-raw-green/CarrySelfAdjointOperator/C2GlobalGreenBridge.lean`; SHA-256 `ceba5dc151babe1aa9b142361efcc6d29b80ed38fc0008683980e8990573c55b`.
- `GeometryOfNumbers/Analysis/C2GlobalGreenBridgeAudit.lean` ← `/home/thlinux/carry-c2-source-raw-green/CarrySelfAdjointOperator/C2GlobalGreenBridgeAudit.lean`; SHA-256 `d36fb60543a174e30d42aeb48e8d15d813a1526aa1e5f1cf5678512c9ec5264c`.
- `docs/C2_GLOBAL_GREEN_BRIDGE.md` ← `/home/thlinux/carry-c2-source-raw-green/docs/C2_GLOBAL_GREEN_BRIDGE.md`; SHA-256 `d99082a14362b7d6276e41c60b2f99903ddb44575dc7fb4c3e523dd9465d6126`.

Only path/namespace adaptation; no import of the historical carry project. Foundation and Geometry remain unchanged.

## Recovery round 10 — PASS

Read-only source: `/home/thlinux/carry-c2-source-raw-green` at `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`; uncommitted source is identified by SHA-256.

- `GeometryOfNumbers/Analysis/C2GreenPreStencilCanary.lean` ← `/home/thlinux/carry-c2-source-raw-green/CarrySelfAdjointOperator/C2GreenPreStencilCanary.lean`; SHA-256 `9137ad25dd338b468f1b31e40e0a98dfdabef002d4e8e30dcfdbf5c22e5720ec`.
- `GeometryOfNumbers/Analysis/C2GreenPreStencilCanaryAudit.lean` ← `/home/thlinux/carry-c2-source-raw-green/CarrySelfAdjointOperator/C2GreenPreStencilCanaryAudit.lean`; SHA-256 `77a3267b59821cbbe7420ae70ccc6de50d365165000af0c866c94c56e1fb43cb`.
- `docs/C2_GREEN_PRE_STENCIL_AUDIT.md` ← `/home/thlinux/carry-c2-source-raw-green/docs/C2_GREEN_PRE_STENCIL_AUDIT.md`; SHA-256 `e29bf329f8d72fd37605a354f8ef71e4fd24146e7363639a47df57e847178255`.

Only path/namespace adaptation; no import of the historical carry project. Foundation and Geometry remain unchanged.
