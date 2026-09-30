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

Não se portaram a eliminação eventual da cauda, o crosswalk clássico de normalização carry, centro–pernas
ou realização da amplitude em potências reais. Não há prova de
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
