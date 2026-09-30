# Geometry of Numbers — teoria real do carry

Formalização da quantidade sob mudanças de representação posicional.
A pergunta-guia é: **o que permanece quando a câmera/base muda?**

Este repositório começa pela proveniência, não por um operador:

```text
quantidade → transporte/carry → centro–pernas → profundidade
          → massa → amplitude quadrática → expoente 1/2
          → representação real → câmeras → TFVD → realização global
          → operador logarítmico autoadjunto
```

O nome do repositório não afirma que a geometria clássica dos números já
está formalizada aqui. O escopo é o plano de trabalho da geometria real do carry.

## Estado verificado

**Projeto compilando; recorrência, primeiro retorno, ciclo/reset, torre residual,
capacidade prefixal, normalização neutra e conservação por refinamento fechados;
ponte da massa formal à rigidez quadrática discreta fechada.**

O núcleo atual depende apenas de `Init`, sem Mathlib e sem dependências de
outros repositórios. Noventa teoremas públicos e dezessete definições
de transporte, bijeção, fibra, cota e massa estão auditados com lista de axiomas vazia.
A camada inicial contém:

- `sameLocal_forces_extension_difference`: a distinção que coincide no canal
  local deve permanecer na extensão de uma representação fiel;
- `faithfulRepresentation_comp`: mudanças fiéis de coordenadas preservam
  a fidelidade;
- `localRecurrence_forces_extension_difference`: uma recorrência local em
  uma trajetória injetiva exige diferença no canal de extensão;
- `positiveLocalReturn_implies_periodic_readout`: um retorno existente se
  propaga por autonomia para um período do canal observado.

Os dois últimos recebem um evento de recorrência/retorno. A camada seguinte
agora deriva esses eventos de uma apresentação finita explícita:

```text
FiniteLocalPresentation (encoding injetivo em Fin N)
    → colisão entre N+1 observações
    + dinâmica local autônoma e passo injetivo
    → retorno positivo b ≤ N
    → menor retorno único
    + primeiro passo não trivial
    → 1 < b ≤ N
```

`unitTrajectory_forces_localRecurrence` e
`autonomousLocalDynamics_has_positiveReturn` fecham as duas primeiras setas.
`existsUnique_emergentLocalCapacity` deriva a existência e a unicidade do
menor retorno por busca limitada, sem `Nat.find`, enumeração escolhida
classicamente ou hipóteses de carry. O orçamento de códigos `N` não é
identificado com a capacidade emergente `b`.

A interface `EmergentLocalCapacity` foi portada antes de qualquer carry.
`emergentLocalCapacity_unique` prova unicidade de capacidades dadas;
`emergentLocalCapacity_gt_one_of_first_step_changes` prova `1 < b` quando
o primeiro passo local muda. Nenhum desses resultados usa
`FoundationalCapstoneAt`, dígitos ou um certificado que já contenha carry.

`EmergentCycleTransport` constrói as coordenadas do relógio por recursão
unitária, sem divisão ou módulo. A cada passo, o resíduo avança ou, ao atingir
`b`, volta a zero e o contador de ciclos aumenta exatamente uma unidade.
Provaram-se:

- conservação e limite: `n = completedCycleCount b n * b + cycleResidual b n`,
  com `cycleResidual b n < b`;
- unicidade de qualquer par que satisfaça essas duas condições;
- primeiro ciclo completo: `cycleCoordinatesRec b b = (1, 0)` em termos das
  duas projeções;
- a mesma observação local em `n` e no resíduo calculado;
- retorno à observação inicial se, e somente se, o resíduo é zero;
- uma extensão global fiel distingue os endpoints de cada ciclo local.

Isso fecha o reset com memória do ciclo e conservação da contagem. Não
identifica uma extensão arbitrária com o contador de ciclos, nem importa
`carry-geometry` para chamar essa construção de uma normalização. O crosswalk
clássico com divisão/módulo ainda não foi portado.

`EmergentResidualTower` repete a mesma operação no contador de ciclos. Em
profundidade `k`, seu dado é `(r₀, ..., rₖ₋₁, qₖ)`, com cauda explícita.
A construção não usa potências, expansão posicional pronta ou massa.
Provaram-se limites dos resíduos, reconstrução exata, unicidade e coerência
por truncamento. Depois da construção, a reconstrução implica:

```text
n = prefixValue(r₀, ..., rₖ₋₁) + qₖ * b^k
prefixValue = r₀ + b*r₁ + ... + b^(k-1)*rₖ₋₁
```

Assim, `b^k` surge como escala acumulada da cauda na reconstrução, não como
hipótese definindo a torre. `residualTower_eq_canonical` também garante que
qualquer tupla limitada é recuperada a partir de seu valor reconstruído.
Os níveis superiores operam sobre os contadores construídos; não se postulou
uma nova dinâmica autônoma em cada extensão arbitrária.

`ResidualTowerCapacity` separa explicitamente o prefixo limitado da cauda:
`ResidualPrefix b 0 = PUnit` e
`ResidualPrefix b (k+1) = Fin b × ResidualPrefix b k`.
Sua avaliação é a reconstrução da torre com cauda zero. Provaram-se:

- `residualPrefix_value_lt_pow`: cada prefixo tem valor menor que `b^k`;
- `residualTower_tail_eq_zero_of_lt_pow`: `n < b^k` força cauda zero;
- `residualPrefix_encode_decode` e `residualPrefix_decode_encode`: a avaliação
  e a extração do prefixo da torre canônica são inversas;
- `residualPrefix_cardinality`: a codificação em `Fin (b^k)` é fiel e sobrejetiva;
- `existsUnique_residualPrefix_for_fin`: cada código possui um único prefixo.

`residualPrefixEquivFin` empacota os dois mapas e suas inversas. Como `Init`
não fornece o tipo `Equiv` de Mathlib, essa bijeção é apresentada diretamente,
sem importar uma biblioteca de cardinalidade. Isso certifica exatamente `b^k`
prefixos. O carrier completo mantém uma cauda natural ilimitada e não é esse
conjunto finito. A eliminação eventual da cauda para `b > 1` ainda não foi provada.

`ResidualPrefixNormalization` não infere uniformidade apenas da capacidade.
Formaliza um contraexemplo com pesos `(1,0)` em dois estados e torna explícito
o princípio adicional: a normalização por contagem não privilegia nenhum
estado por sua identidade. Transposições de rótulos provam que uma atribuição
invariante tem cotas iguais. Isso é neutralidade sobre o conjunto dos estados,
não uma afirmação de que toda permutação preserve a dinâmica ou a reconstrução.

Para contagens naturais com denominador comum positivo `D`, total normalizado
e invariância, provamos `weight(x) * b^k = D`. A comparação formal por
multiplicação cruzada identifica cada cota com `(1,b^k)`, sem construir um
quociente. A contagem canônica atribui uma unidade a cada estado e calcula
seu denominador por soma finita. Sua invariância é provada; a unicidade vale
como cota, não como par numerador/denominador. Não se afirmou uniformidade
de medidas arbitrárias.

`ResidualPrefixRefinement` constrói truncamento e extensão na extremidade
mais profunda, preservando `r₀,...,rₖ₋₁`. Suas inversas parametrizam por
`Fin b` a fibra efetiva de refinamentos de cada pai, sem usar potências nessa
construção. O truncamento também coincide com a extração dos prefixos da
torre canônica, mesmo quando a cauda não é zero.

A agregação soma os numeradores das cotas dos filhos dessa fibra e conserva
o denominador comum. Prova-se que essa agregação representa a mesma cota do
pai: `(b,b^(k+1))` é equivalente a `(1,b^k)`, não necessariamente igual como
apresentação. Só depois disso, `canonicalResidualDepthMass` nomeia a cota
existente; independência do representante, unidade inicial e conservação
por refinamento são provadas. É massa formal nos níveis finitos, não uma
medida numérica ou enumeravelmente aditiva na torre infinita.

As leis estruturais da fibra também valem para capacidade zero, onde o
prefixo vazio não tem filhos. A conservação de uma unidade inicial por uma
fibra vazia é formalmente impossível; a massa coerente exige `b > 0`.

O módulo `QuadraticAmplitudeExponent` apresenta um expoente não negativo por
dois naturais `p, q`, com `q > 0`, sem formar `p/q`. Seu núcleo prova:

```lean
theorem quadraticExponentEquation_iff_half
    (k p q : Nat) (hk : 0 < k) :
    2 * (k * p) = k * q ↔ 2 * p = q
```

`quadratic_carry_exponent_iff_half` reúne a compatibilidade em todas as
profundidades positivas. O resultado seleciona a razão formal, não uma
apresentação reduzida: tanto `(1, 2)` quanto `(2, 4)` representam metade.
Denominador zero é excluído; profundidade zero não seleciona expoente.

`QuadraticMassCompatibility` conecta agora essa rigidez à massa já derivada.
Primeiro identifica literalmente `canonicalResidualDepthMass b k hb` com
`radixShare b k hb`, a apresentação `(1,b^k)`. A composição de `q` cópias
da massa tem escala `k*q`. Uma escala candidata `k*p`, composta consigo
mesma, tem escala `2*(k*p)`. A compatibilidade é definida por comparação
cruzada dessas cotas, mencionando a massa geométrica na própria definição;
não é definida pela equação dos expoentes.

Para `1 < b`, a injetividade das potências naturais deriva essa equação.
Para `k > 0`, o módulo aritmético anterior seleciona `2*p=q` sem nova prova
do cancelamento. O capstone público é:

```lean
theorem canonicalResidualDepthMass_quadraticCompatibility_iff_half
    (b k p q : Nat) (hb : 1 < b) (hk : 0 < k) :
    QuadraticAmplitudeScaleCompatibleAt b k p q
      (Nat.lt_trans Nat.zero_lt_one hb) ↔
      FormalExponentRepresentsHalf p q
```

Composição quadrática é um requisito semântico explícito para uma amplitude
candidata, não uma conclusão da contagem isoladamente. Seu expoente formal
compatível é forçado; nenhuma amplitude numérica foi construída. Em `b=1`
ou `k=0`, qualquer razão válida passa o teste e nenhum expoente é selecionado.
`q=0` é inválido, e `b=0` não fornece a massa com denominador positivo.

**Essa ponte não fecha a teoria inteira.** A capacidade agora
existe sob as hipóteses explícitas acima; seu reset e sua torre de profundidade
finita já têm coordenadas únicas, e os prefixos têm capacidade exata `b^k`.
Sua normalização formal por contagem agora está construída, com neutralidade
explicitamente separada da cardinalidade, e sua conservação entre profundidades
foi provada pelo refinamento. Sua ligação à compatibilidade quadrática formal
está fechada; ainda falta a realização numérica. Também não se provou aqui
a passagem da igualdade de potências reais para a igualdade de expoentes.
Não há realização em `ℚ`/`ℝ`, TFVD,
isometria ou autoadjunticidade nesta árvore ainda.

## Executar

Requer Elan; a versão do Lean está fixada em `lean-toolchain`.
Não é necessário baixar Mathlib.

```bash
lake build
lake env lean GeometryOfNumbers/Foundation/Audit.lean
bash scripts/audit-foundation.sh
```

O alvo de auditoria participa do build padrão. Além de `#print axioms`,
`#assert_no_axioms` rejeita qualquer dependência de axiomas nos teoremas
fundacionais listados — inclusive os axiomas usuais de Mathlib.

## Organização e fronteiras

- [Versão humana da teoria](docs/HUMAN_THEORY.md): narrativa matemática contínua,
  das entradas dinâmicas à seleção formal do expoente, com hipóteses e limites explícitos.
- [Plano de execução](docs/FORMALIZATION_PLAN.md): ordem causal e critérios
  de saída, distinguindo resultados atuais de metas.
- [Proveniência das portas](docs/SOURCE_PROVENANCE.md): fontes, commits,
  adaptações e por que os capstones históricos não foram simplesmente importados.
- `GeometryOfNumbers/Foundation/`: Zona A, sem axiomas.
- `Real/`, `Operator/`, `Height/`, `Limit/`: fases futuras, ainda não criadas.

O gerador logarítmico e o operador de alturas são objetos diferentes.
Os operadores não serão usados para justificar retroativamente a geometria.
Representações complexas e comparações com funções clássicas ficam fora
do núcleo e não são premissas deste projeto.
