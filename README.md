# Geometry of Numbers — teoria real do carry

Formalização da quantidade sob mudanças de representação posicional.
A pergunta-guia é: **o que permanece quando a câmera/base muda?**

Este repositório começa pela proveniência, não por um operador. A cadeia
fundacional efetivamente construída é:

```text
dinâmica local finita → primeiro retorno → ciclos/reset → torre residual
→ prefixos/profundidade → capacidade → normalização neutra → massa formal
→ refinamento coerente → compatibilidade quadrática de escala → metade
```

A geometria centro–pernas foi construída **depois**, como camada adicional:

```text
centro e raio inteiros → pernas simétricas → reflexão involutiva
→ teste de centro contra pernas fixas → segunda diferença de observáveis
```

O crosswalk de **uma célula** agora fecha: ciclos/resíduo existentes →
offset estritamente balanceado → centro alinhado → par refletido, para
capacidade ímpar. A profundidade relacional agora é derivada da torre, e somente
o offset canônico expõe a profundidade do centro em qualquer nível positivo.
Essa geometria não justificou retroativamente a massa ou metade. A realização real da escala
já existe. Agora há também um estado real de profundidade com energia
quadrática preservada por rotação de ângulo livre. A reflexão recíproca agora
constrói pernas com produto igual à massa; o readout centrado dessas pernas
deriva um bracket local não negativo. A câmera ímpar agora reúne pares de
raios positivos e seu bracket discreto é a soma saturada de segundas diferenças.
A realização quadrática soma defeitos não negativos por par. Uma compatibilidade
semântica explícita agora liga offsets aditivos a um transporte multiplicativo:
ela classifica as deformações como `q_r=rho^r` e fecha o crosswalk dos valores
de um perfil centrado. A seleção do passo positivo `rho`, a fase e o estado
global permanecem abertos; essa compatibilidade não foi derivada da torre.

O nome do repositório não afirma que a geometria clássica dos números já
está formalizada aqui. O escopo é o plano de trabalho da geometria real do carry.

## Estado verificado

**R2 CLOSED:** reconstrução discreta/projetiva, gauge crítico e TFVD real com
análise/síntese exata; veja os capstones R2 ao final.

**Projeto compilando; recorrência, primeiro retorno, ciclo/reset, torre residual,
capacidade prefixal, normalização neutra e conservação por refinamento fechados;
ponte da massa formal à rigidez quadrática discreta fechada e consolidada em
capstone. Zona B aberta: massa real, amplitude real e identidade do quadrado
compiladas; primeiro estado bidimensional com energia `x²+y²` e rotação livre
também fechado, sem construção de norma ou produto interno. Geometria discreta centro–pernas,
reflexão e segunda diferença compiladas e auditadas separadamente, com
crosswalk balanceado de uma célula para capacidades ímpares, sem primalidade.
Relação de profundidade por zeros sucessivos e identificação relacional do
único canal profundo com o centro fechadas, sem valuation ou máximo.
Reflexão quadrática recíproca e bracket local derivados, com produto conservado,
fatoração, positividade, zero central único e invariância por reflexão.
Câmera ímpar sem primalidade, identidade discreta de saturação e realização
quadrática com deformações livres fechadas; zero total equivale a equilíbrio
de todos os pares, com reflexão independente de cada um.**

O núcleo da Zona A depende apenas de `Init`, sem Mathlib ou imports históricos.
Noventa e dois teoremas públicos e dezessete definições
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
compatível é forçado; nenhuma amplitude numérica é construída na Zona A. Em `b=1`
ou `k=0`, qualquer razão válida passa o teste e nenhum expoente é selecionado.
`q=0` é inválido, e `b=0` não fornece a massa com denominador positivo.

**Essa ponte não fecha a teoria inteira.** A capacidade agora
existe sob as hipóteses explícitas acima; seu reset e sua torre de profundidade
finita já têm coordenadas únicas, e os prefixos têm capacidade exata `b^k`.
Sua normalização formal por contagem agora está construída, com neutralidade
explicitamente separada da cardinalidade, e sua conservação entre profundidades
foi provada pelo refinamento. Sua ligação à compatibilidade quadrática formal
está fechada. A realização numérica real também está disponível, na camada
separada descrita abaixo; não foi usada para selecionar o expoente.
O estado angular de profundidade está construído abaixo, sem lei de fase.
Esse checkpoint inicial não continha TFVD/Green; R2 acrescenta agora sua reconstrução real exata, descrita abaixo. Isometria e autoadjunticidade permanecem posteriores.

## Corte da Zona A e abertura da Zona B

**Fim da fundação discreta de seleção da escala, com footprint vazio.**
`FoundationalHalfScalingCapstone` compõe somente resultados anteriores.
`foundational_half_scaling_capstone` usa a capacidade emergente da própria
trajetória; `exists_foundational_half_scaling_capstone` produz essa capacidade
a partir da apresentação finita e do primeiro passo não trivial, com o limite
do orçamento e a seleção formal em todas as profundidades positivas.
Autonomia e injetividade continuam explícitas, e o requisito quadrático não
é apresentado como consequência da contagem isoladamente.

Os três imports públicos têm papéis distintos:

```text
GeometryOfNumbers           — somente Foundation; axiomas vazios
GeometryOfNumbers.Geometry  — Foundation + geometria Int; audit separado
GeometryOfNumbers.Analysis  — reúne Geometry + realização real com Mathlib
```

`realizeCountingShare` interpreta uma apresentação por divisão em `ℝ` e
preserva exatamente `SameCountingShare`. A massa real é definida por:

```lean
def realDepthMass (b k : ℕ) (hb : 0 < b) : ℝ :=
  realizeCountingShare (canonicalResidualDepthMass b k hb)
```

Só depois, `realize_canonicalResidualDepthMass` prova que essa realização é
`(b : ℝ) ^ (-(k : ℝ))`. `formalHalf_realizes_half` interpreta `2*p=q`
como `(p : ℝ)/(q : ℝ) = 1/2`; todas essas apresentações realizam a mesma
`realCriticalAmplitude`, cujo valor é `(b : ℝ) ^ (-(k : ℝ)/2)`.
`realCriticalAmplitude_sq_eq_realDepthMass` verifica seu quadrado.

A identidade analítica exige apenas `b>0`. Para `b=1` ou `k=0`, os valores
são `1`; isso não fornece a rigidez ausente nesses casos na Zona A. Não se
realiza uma massa canônica para `b=0`. Os quatorze teoremas dessa ponte escalar estão
auditados separadamente: usam `propext`, `Classical.choice` e `Quot.sound`,
sem axiomas adicionais. Essa camada não é anunciada como axiom-free e não
define uma medida infinita ou uma norma. A construção coordenada do plano
real é uma etapa posterior registrada abaixo, não fonte dessa ponte escalar.

## Reflexão quadrática e bracket local

Os módulos `Analysis/QuadraticReflection.lean` e
`Analysis/QuadraticCenteredBracket.lean` compõem somente a amplitude e massa
existentes. Para `C=A_b(k)>0` e `q>0`, definem primeiro a reflexão e as pernas:

```text
reciprocalReflection q = q⁻¹
L_C(q) = C*q, R_C(q) = C*q⁻¹
L_C(q⁻¹) = R_C(q), R_C(q⁻¹) = L_C(q)
L_C(q)*R_C(q) = C² = M_b(k)
```

A lei funcional `F_C(q)*F_C(q⁻¹)=C²` usa `F_C=L_C`. Não é uma identificação
com uma função clássica. `criticalQuadraticLegs_product_realizes_formalMass`
mostra que a massa preservada é literalmente a realização da cota fundacional.

Só depois das pernas define-se o readout `D(L,C,R)=L-2*C+R` e o bracket
como sua aplicação. Os teoremas, não as definições, dão:

```text
B_C(q) = C*(q+q⁻¹-2) = C*(q-1)²*q⁻¹
B_C(q) ≥ 0, B_C(q)=0 ↔ q=1, B_C(q)>0 se q≠1
B_C(q⁻¹) = B_C(q)
```

A invariância vem da troca das pernas. Na geometria aditiva, `c-a,c+a`
conservam a soma `2*c`; aqui `C*q,C*q⁻¹` conservam o produto `C²`.
O bracket lê a segunda configuração com a forma aditiva da primeira.
Não há nova seleção de metade nem construção de norma.

O suporte do centro carry-derived registra somente a proveniência de `k`.
`q` atua nas pernas escalares; o ângulo livre `theta` do plano permanece
independente. Não se introduz parametrização física, logaritmo, tempo ou
identificação com bracket de câmera. Nível zero e capacidade um dão centro e
massa unitários. Inversão em Lean é total, mas `q=0` é excluído da lei do
produto: ali o bracket vale `-2*C`, não um defeito não negativo desse regime.

Essa etapa local acrescentou 31 teoremas e oito definições ao audit analítico,
que então contava 60 teoremas. A etapa de câmera abaixo aumenta esse total
para 84. Não houve axioma adicional ou mudança na fundação.

## Câmera ímpar e saturação por pares

`Geometry/OddCamera.lean` recebe `half=h` como dado: capacidade `b=2*h+1`,
raios `1,...,h` e pares `(c-r,c+r)` indexados por `Fin h`. Limites, cobertura,
ausência de repetição e troca por reflexão são provados. A fundação
não é alterada e nenhuma escolha extrai `h` de uma proposição existencial.
Uma soma recursiva genérica enumera exatamente esses raios; não há Finset
ou Mathlib em Geometry. Contar duas pernas por raio dá `2*h=b-1` como theorem.

`Geometry/OddCameraBracket.lean` mantém observáveis `Int → Int`. Define
primeiro a soma das pernas, depois o bracket independentemente da saturação:

```text
LegSum_h(F,c) = sum_r [F(c-r)+F(c+r)]
CameraBracket_h(F,c) = LegSum_h(F,c) - 2*h*F(c)
Saturated_h(F,c) = sum_r centeredSecondDifference(F,c,r)
CameraBracket_h(F,c) = Saturated_h(F,c)   -- theorem
```

Primalidade não participa: capacidade composta `9` tem quatro pares e oito
pernas. C3 tem um par e reduz literalmente ao stencil de raio `1`.
Capacidade `1` tem câmera vazia e bracket zero; C2 não é câmera ímpar e
seu crosswalk continua aberto. Um observável arbitrário não dá positividade
automática: há teste discreto com bracket negativo.

`Analysis/QuadraticCameraBracket.lean` usa a MESMA soma e os mesmos índices,
mas recebe uma família livre `q : Nat → ℝ`, positiva somente em `1≤r≤h`.
Cada termo reutiliza as pernas e o bracket locais. A definição é soma de
brackets, não soma da fatoração desejada; prova-se:

```text
B_quad(h,C,q) = sum_r B_C(q_r)
             = quadraticLegSum - 2*h*C
             = C * sum_r [(q_r-1)^2*q_r⁻¹]
para C>0 e q_r>0 no domínio:
B_quad ≥ 0
B_quad = 0 ↔ todos os q_r do domínio são 1
```

Uma máscara booleana pode inverter qualquer subconjunto dos pares sem mudar
o total; inverter um par ou todos são corolários. Cada par preserva `C²`,
não se somam massas para obter esse bracket. A especialização crítica usa
a capacidade da própria câmera `2*h+1` e a amplitude anterior no mesmo `k`.
O capstone de suporte mostra campos da massa formal, produto por par como
realização dessa massa e total como soma dos defeitos locais.

**Raio e deformação são distintos.** `r` desloca o argumento de `F` na câmera
discreta; `q_r` modifica os valores escalares na realização quadrática.
Na etapa de família livre, não se assumiu `F(c±r)=C*q_r^{±1}` nem uma lei
`r↦q_r`. A etapa seguinte fecha essa ponte para um perfil específico sob
compatibilidade multiplicativa explícita; não para qualquer observável.
O total de defeito não é identificado com a energia coordenada do plano
nem com a massa central.

A etapa acrescentou 23 teoremas/oito definições discretas e 24 teoremas/quatro
definições analíticas. Geometry tem 87 teoremas e 22 definições auditadas,
sem escolha; Analysis então tinha 84 teoremas, com os mesmos três axiomas padrão.
Foundation continua congelada e com footprint vazio.

## Transporte dos offsets e crosswalk real da câmera

Toda a nova ponte vive em Analysis; Foundation e Geometry permanecem
inalteradas. A busca local não encontrou uma interface anterior de composição
aditiva dos offsets para composição multiplicativa. A nova especificação é:

```text
IsPositiveMultiplicativeOffsetTransport Q:
  Q(0)=1
  Q(a+b)=Q(a)*Q(b)
  Q(1)>0
```

É uma entrada semântica adicional, não consequência gratuita da simetria,
da torre ou da massa. `MultiplicativeOffsetTransport` prova:

```text
Q(a)*Q(-a)=1; Q(a)≠0; Q(-a)=Q(a)⁻¹; Q(a)>0
Q(r)=Q(1)^r                -- indução natural
Q(z)=Q(1)^z                -- extensão inteira, sem log/exp
rho>0 → Q_rho(z)=rho^z     -- transporte existente e único com Q(1)=rho
```

`CenteredMultiplicativeProfile` orienta o offset como `c-x` e define
`F(x)=C*Q(c-x)`. Assim esquerda, centro e direita têm valores
`C*rho^r`, `C`, `C*(rho^r)⁻¹`. O produto refletido é `C²`; com a amplitude
crítica anterior, é exatamente a massa real do mesmo nível `k`.

`OddCameraQuadraticCrosswalk` levanta a câmera para `Int → ℝ`, com as MESMAS
pernas e soma recursiva de Geometry. Primeiro prova saturação para um
observável real qualquer; depois especializa ao perfil:

```text
Delta²_real F(c,r) = quadraticCenteredBracket(C,Q(r))
RealCameraBracket_h(F,c) = QuadraticCameraBracket_h(C,r↦Q(r))
                        = QuadraticCameraBracket_h(C,r↦rho^r)
                        = C * sum_r [(rho^r-1)^2*(rho^r)⁻¹]
C>0, rho>0 → bracket≥0
C>0, rho>0, h>0 → (bracket=0 ↔ rho=1)
rho↦rho⁻¹ troca as pernas e preserva o total
```

A igualdade global passa por saturação e crosswalk local, não pela expansão
bruta da fórmula final. Para `h=0`, o total é zero para qualquer passo.
As formas locais/globais por divisão são corolários explícitos da fatoração.
O módulo de transporte importa somente `Mathlib.Data.Real.Basic`, com guard
`assert_not_exists Real.log Real.exp`; a classificação independe da amplitude.
C3 tem um corolário com a cadeia literal leitura nos pontos = bracket local.
C3 reduz ao bracket local no passo `rho`; capacidade composta `9` funciona
sem primalidade. O teste `C=1/3,h=2,rho=2` dá deformações `2,4`, brackets
`1/6,3/4` e total `11/12`, invariante sob inversão do passo.
As quatro avaliações com passo `1/2` também são testadas. Com `half=4`,
capacidade `9`, `C=1/3` e `rho=2`, o total formal é `367/48`.

**R1: crosswalk fechado sob compatibilidade explícita; seleção de `rho`
continua aberta.** `r` compõe offsets horizontais; `k` indexa massa/amplitude
verticais. Nenhuma lei relacionando esses índices ou selecionando `rho` pela
amplitude foi provada. O perfil não é uma potência do argumento absoluto,
nem uma identificação com razões históricas. Não se introduziram fase,
log/exp, tempo ou leituras posteriores nos novos objetos/provas.

São 47 teoremas e nove definições do transporte/crosswalk, todos guardados no
audit analítico (131 teoremas públicos no total), com apenas os três axiomas padrão.
Nenhum resultado novo é usado para justificar retroativamente a fundação.

## Geometria discreta centro–pernas

`Geometry/CenterLegReflection.lean` recebe apenas `center radius : Int`.
As pernas `c-r` e `c+r` são definidas, e sua soma `2*c` é provada. O raio pode
ser negativo ou zero, sem truncamento. `reflect c x = 2*c-x` fixa o centro,
troca as pernas e é involutiva. `IsCenterOf` expressa essa troca para pernas
fixas; equivale à soma igual a `2*candidate`. O centro construído é único;
não se afirma que todo par inteiro tenha um centro inteiro.

O teste `centerDefect left candidate right = left - 2*candidate + right` dá:

```text
pernas fixas:   D(c-r, c+δ, c+r) = -2*δ
pernas novas:   D((c+δ)-r, c+δ, (c+δ)+r) = 0
```

`Geometry/CenteredSecondDifference.lean` define `secondDifferenceAt` sobre
três nós e `centeredSecondDifference` sobre as pernas construídas. A identidade
recupera exatamente o defeito de centro. Já `f(x)=x*x` tem resposta `2*r*r`
mesmo em simetria: resposta/curvatura de um observável não é necessariamente
assimetria geométrica. Os exemplos verificam `(7,10,13)`, teste em `11` dando
`-2`, recentramento `(8,11,14)` dando zero, reflexão e resposta quadrática `18`.

As sete definições da geometria abstrata têm footprint vazio. Seus 21 teoremas públicos são auditados;
a ponte definicional da identidade tem footprint vazio e os demais usam
`propext` e `Quot.sound`, **sem `Classical.choice`**. Esses axiomas vêm da
aritmética/provas de Init; não foi necessário importar Mathlib nesta camada.
Isso não é uma extensão da auditoria vazia da Zona A. Não foram identificados
brackets, Green ou tilt com esses objetos.

## Do carry emergente ao centro balanceado

`Geometry/BalancedCarryOffset.lean` usa literalmente
`q = completedCycleCount b n` e `r = cycleResidual b n`. Com
`IsOddCapacity b := ∃ h : Nat, b = 2*h+1`, a comparação por duplicação
não pode empatar. A construção é:

```text
2*r < b:  center = q*b,       offset = r
b < 2*r:  center = (q+1)*b,   offset = r-b  (subtração inteira)
```

Não há divisão/módulo, base posicional externa ou import histórico na
construção. `balancedCarry_spec` prova `n=center+offset`, `b ∣ center` e
`2*offset.natAbs < b`. A unicidade `balancedCenterOffset_unique` vale para
qualquer par de decomposições alinhadas com offsets estritos, sem hipótese
de paridade; oddness é usada para a existência para todo resíduo.

`Geometry/CarryCenterLegCrosswalk.lean` prova que `rightLeg center offset = n`
e `reflect center n = leftLeg center offset = center-offset`. Por composição
com a geometria abstrata, o defeito do centro correto é zero e o teste de
`center+δ`, com as mesmas pernas, é `-2*δ`. A segunda diferença da identidade
herda essa mesma fórmula, sem outra definição de defeito.

`emergentCapacity_balancedCarry_spec` recebe o primeiro retorno da trajetória
e expõe os ciclos originais junto da especificação geométrica. **Não deriva
oddness da fundação**: uma capacidade emergente pode ser par. Primalidade
não aparece; o teste com capacidade composta `9` também compila.

Resíduo zero dá offset zero, centro igual à quantidade e reflexão fixa.
Resíduo não zero dá offset não zero e quantidade distinta do centro.
Para capacidade `1` a construção é trivial; `0` não é ímpar positiva.
O antipodal `b=2,n=1` não tem representante estrito; permitindo
`2*|offset|=b`, `1=0+1=2-1` tem centros distintos. Nenhum lado foi escolhido:
as funções canônicas exigem oddness. **C2 continua um crosswalk futuro.**

Os 23 teoremas e quatro definições novos entram no audit próprio. As
definições têm footprint vazio; os teoremas usam no máximo `propext` e
`Quot.sound`, sem escolha. Essa etapa tinha 44 teoremas públicos e onze
definições auditadas. A Foundation e sua axiomática continuam intocadas.

## Profundidade relacional da torre e do centro

`Geometry/ResidualTowerDepth.lean` consulta os resíduos de
`emergentResidualTower b k x`. `HasCarryDepthAtLeast b x k` significa que
todos os primeiros `k` resíduos são zero, sem restringir a cauda. Vale:

```text
Depth≥0(b,x)
Depth≥k+1(b,x) ↔ cycleResidual b x = 0 ∧ Depth≥k(b,completedCycleCount b x)
para b>0: Depth≥k(b,x) ↔ b^k ∣ x
sob Depth≥k: x = tail_k(x) * b^k
```

Divisibilidade não é a definição: reconstrução prova a direção direta;
unicidade da torre identifica uma tupla de prefixo zero na direção inversa.
Os nove teoremas públicos desse módulo têm footprint vazio, com guard próprio
no audit geométrico. Ele é uma extensão conservativa fora de Foundation;
nenhum arquivo da fundação ou do capstone de metade foi alterado.

Só depois, `HasIntegerCarryDepthAtLeast b x k := (b : Int)^k ∣ x` estende a
relação aos argumentos assinados. Sua restrição aos naturais coincide com
a relação da torre para `b>0`, sem construir uma torre inteira paralela.
`Geometry/BalancedCarryDepthCrosswalk.lean` usa `n=c+a` e a unicidade existente:

```text
para capacidade ímpar, offset balanceado a' e k>0:
b^k ∣ (n-a') ↔ a'=a ∧ b^k ∣ c
∃ a' balanceado com Depth≥k(b,n-a') ↔ Depth≥k(b,c)
```

Quando existe um witness, ele é único e canônico. O mesmo índice `k` aparece
na massa formal existente `(1,b^k)`; isso não define massa de `n` nem converte
a amplitude por profundidade em amplitude global de `n`.

Quantidade zero, centro zero e capacidade `1` sobrevivem em todos os níveis.
Em `b=0` a recursão total não descreve carry positivo: um contraexemplo mostra
que seu teste de prefixo zero não caracteriza divisibilidade. A relação natural
também vale em capacidades pares positivas; o centro balanceado continua no
regime ímpar. **C2, terminação e funções de profundidade máxima ficam abertos.**

Ao fechar o crosswalk, Geometry contava 64 teoremas e 14 definições auditadas. O módulo
natural é vazio; a ponte inteira/balanceada usa no máximo `propext`/`Quot.sound`,
sem escolha. Os testes verificam a seleção `9 → (10,-1)` em base `5`, os
níveis `1,2` mas não `3` de `26 → (25,1)`, e um caso natural par `2,8,3`.

## Primeiro estado quadrático real: raio derivado, ângulo livre

`Analysis/RealQuadraticPlane.lean` usa `RealPlaneState := ℝ × ℝ` e define
explicitamente `realPlaneEnergy (x,y) := x²+y²`. Não usa a norma do produto
como energia nem constrói uma estrutura de Hilbert. A rotação escolhida é:

```text
R_theta(x,y) = (x*cos theta - y*sin theta, x*sin theta + y*cos theta)
```

`rotateRealPlane_energy` prova invariância por álgebra e `sin²+cos²=1`.
`rotateRealPlane_zero` e `rotateRealPlane_add` provam identidade e composição
angular; nenhuma dessas leis seleciona um ângulo ou uma parametrização.

`Analysis/RealCriticalDepthState.lean` recebe a amplitude escalar existente:

```text
seed(b,k) = (realCriticalAmplitude b k hb, 0)
state(b,k,theta) = R_theta(seed(b,k))
                = (A_b(k)*cos theta, A_b(k)*sin theta)
E(seed(b,k)) = E(state(b,k,theta)) = realDepthMass b k hb
```

A identidade da semente reutiliza `realCriticalAmplitude_sq_eq_realDepthMass`;
não reprova seleção ou potências. `realCriticalAmplitude_pos` registra
positividade. `k=0` e `b=1` produzem semente `(1,0)` e energia `1` em qualquer
ângulo, sem selecionar um expoente ou canal carry nesses casos.

`balancedCarryDepth_realState_energy` recebe suporte de `k` pelo centro
canônico. Essa hipótese documenta proveniência do índice e é explicitamente
desnecessária para a identidade algébrica. O capstone
`balancedCarryDepth_realState_realizes_formalMass` expõe o canal canônico,
os campos `(1,b^k)` da massa formal e a energia como realização dessa cota.
O estado não recebe `n` como índice; não é um estado global de um inteiro.

A escala radial já possui proveniência na torre e na massa. **O ângulo ainda
é um parâmetro livre; esta etapa não seleciona uma lei de fase.** Na etapa
do plano não se introduziram logaritmo, tempo, operador, bracket ou Green. A energia foi
introduzida depois da amplitude, não usada para justificar metade.

Quinze teoremas públicos novos e cinco nomes de carrier/mapas entram no audit
analítico, com somente os três axiomas padrão. Ao fechar o plano, Analysis
contava 29 teoremas públicos auditados; a reflexão acima aumenta esse total
para 60, a câmera para 84 e o transporte/crosswalk para 131. Foundation
permanece inalterada; a câmera amplia somente Geometry e Analysis. Os testes
incluem base `3`, nível `2`, semente `(1/3,0)`, energia `1/9`, ângulo zero,
quarto de volta `(0,1/3)`, e o suporte do nível `2` pelo centro `25` de `26`.

## Executar

Requer Elan; a versão do Lean está fixada em `lean-toolchain`.
Mathlib está fixada no commit `81a5d257c8e410db227a6665ed08f64fea08e997`
(versão `v4.32.0`); a dependência serve à Zona B, não às provas da Zona A.

```bash
lake update
lake build
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

As três auditorias Lean participam do build padrão e têm scripts separados.
Na fundação, além de `#print axioms`,
`#assert_no_axioms` rejeita qualquer dependência de axiomas nos teoremas
fundacionais listados — inclusive os axiomas usuais de Mathlib. Na análise,
`#assert_analysis_axioms` permite somente os três axiomas padrão indicados.
`scripts/check-foundation-imports.lean` usa o parser Lean para impedir imports
analíticos/Mathlib na fundação ou em seu import público, inclusive multilinha.
O checker separado de Geometry admite apenas Init, Foundation e Geometry,
exceto a ferramenta Lean usada pelo audit; análise e fontes históricas não
podem retornar como dependências. A direção das entradas é
`Foundation → Geometry → Analysis`. A entrada Geometry contém agora o
crosswalk de uma célula ímpar e a identificação relacional de profundidades,
provada nos módulos acima; a direção de imports, por si só, não prova essas
identificações nem qualquer realização analítica da geometria.

## Organização e fronteiras

- [Versão humana da teoria](docs/HUMAN_THEORY.md): narrativa matemática contínua,
  das entradas dinâmicas à seleção formal e sua realização real, com limites explícitos.
- [Plano de execução](docs/FORMALIZATION_PLAN.md): ordem causal e critérios
  de saída, distinguindo resultados atuais de metas.
- [Proveniência das portas](docs/SOURCE_PROVENANCE.md): fontes, commits,
  adaptações e por que os capstones históricos não foram simplesmente importados.
- `GeometryOfNumbers/Foundation/`: Zona A, sem axiomas.
- `GeometryOfNumbers/Geometry/`: geometria discreta sobre `Int`, audit próprio.
- `GeometryOfNumbers/Analysis/`: Zona B, escalares e plano quadrático real, audit separado.
- Lei angular/espectral, seleção do passo horizontal positivo `rho`, crosswalk com
  câmeras históricas, operadores e limites: fases futuras.

O gerador logarítmico e o operador de alturas são objetos diferentes.
Os operadores não serão usados para justificar retroativamente a geometria.
Representações complexas e comparações com funções clássicas ficam fora
do núcleo e não são premissas deste projeto.


## Forma Centro–Pernas local e resolvida por câmera

`Analysis/CenterLegForm` constrói primeiro as posições reais
`q R_theta v`, `R_theta v`, `q⁻¹ R_theta v` e seu readout vetorial. Para
`q≠0`, prova `E(D)=(q-1)^4/q² · E(v)` usando a energia coordenada e a
invariância da rotação existente. A energia independe do ângulo livre.

`Analysis/CenterLegCameraForm` preserva esses canais e soma suas energias.
Para defeito radial comum, o total é o mesmo fator vezes a energia inicial
resolvida. Com energia inicial positiva, zera exatamente em `q=1`.
Soma de energias difere de energia da soma; o crosswalk escalar é soma
ponderada dos quadrados de brackets locais, sem identificação com o quadrado
do bracket total. Os dois guardrails têm contraexemplos formais.

Esses gates locais e de câmera estão fechados, com 26 teoremas e seis
definições adicionais na auditoria padrão de Analysis. A distribuição
entre bases exige uma lei própria e permanece uma fronteira separada.


## Distribuição entre bases: conservação sob interface explícita

`Analysis/AtlasEnergyPartition` recebe uma partição de unidade não negativa,
com suporte finito por coordenada, sobre rótulos `b≥2`. Escala os estados reais
por `sqrt(weight)` e prova conservação exata da energia coordenada. Para uma
entrada finitamente resolvida, `Analysis/CenterLegAtlasForm` soma as câmeras
ponderadas e prova

$$
\mathcal E_{\rm atlas}=\frac{(q-1)^4}{q^2}\mathcal E_{\rm input}\quad(q\ne0).
$$

Todos os ângulos locais desaparecem da energia por theorem. Energia inicial
total positiva dá zero iff `q=1`, permitindo canais de peso zero.
**STRUCTURAL PASS / INTERFACE ONLY:** a geometria atual ainda não seleciona
uma partição all-bases canônica. O resultado é real, coordenado e finito nas
entradas; não importa os três atlas históricos nem uma lei entre profundidades.


## Profundidade residual e vozes primas de quantidades

`Analysis/PrimeResidualDepthCrosswalk` prova, para primo `p` e `n≠0`,
`HasCarryDepthAtLeast p n k ↔ k ≤ n.factorization p`, passando pelo theorem
anterior da torre sobre divisibilidade. A fatoração é representação posterior;
zero mantém profundidade residual em todo nível. As famílias de thresholds
primos determinam uma quantidade não nula, reconstruída pelo produto único.

`Analysis/PrimeCarryVoice` prova `log n = ∑ v_p(n) log p` e deriva os pesos
`v_p(n) log p / log n`, não negativos, com suporte finito e soma um para `n>1`.
**PRIME PARTITION PASS / INDEX GAP:** a partição canônica de quantidades não
seed ainda não instancia o atlas indexado pelos canais da câmera. Falta o
crosswalk quantidade→canal; em `n=1` os pesos somam zero, e a incompatibilidade
com a interface total foi provada. A Forma Centro–Pernas continua com o atlas
parametrizado anterior. Nenhum peso de fallback, seed ou dependência histórica
foi introduzido; Foundation e Geometry permanecem congeladas.


## R2 — reconstrução exata real: CLOSED

A segunda diferença, o Green com retorno de bordo, a TFVD real e a válvula
projetiva são apresentações compatíveis da reconstrução do mesmo estado.

- `DiscreteValve.realDiscreteGreenReconstruction`: curvatura + valor/inclinação
  iniciais reconstroem toda sequência.
- `DiscreteValve.mk_discrete_valve`: reconstrução em séries formais, com
  `(1-X)^2 G1 = 1`.
- `ProjectiveDepth.greenKernel_subst_inverse_mul_inverseDerivative`: Y=X/(1-X)
  absorve Green pelo jacobiano.
- `ProjectiveValve.projectiveValveEquiv`: massa normalizada e curvatura são
  inversas; A'=DA e soma de curvaturas vira produto de massas.
- `DiscreteProjective.realDiscreteProjectiveReconstructionEquiv`:
  estado ≃ (valor inicial, inclinação inicial, massa projetiva).
- `realCriticalCarryTfvdGreenValveCapstone`: gauge pela amplitude b^(-k/2),
  TFVD GB+RTr=I em ℓ²(ℕ,ℝ), e S∘T=I como interface para R3.

Leia [a rota normativa R2](docs/R2_TFVD_GREEN_VALVE_ROUTE.md) e
[a auditoria técnica](docs/R2_IMPLEMENTATION_AUDIT.md).
Raio horizontal não é profundidade vertical; deformação q não é razão eta.
R2 fecha reconstrução. Head/tail, momentos e normalização/isometria global
permanecem downstream. Nenhuma conclusão espectral é feita.
