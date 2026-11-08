# C5 — orçamento intervalar dos sinais da fonte original (2026-11-08)

## Obrigação Lean ainda aberta

As hipóteses exatas que impedem a conclusão incondicional são:

```lean
CarrySigmaObstruction.sigmaC00495SourceBoxes :
  ∀ n, n < 15 → sigmaRatBallContains
    (sigmaC00495CoefficientBall n)
    (completedSigmaDisplacedSourceCoefficient (99 / 2000) n)

CarrySigmaObstruction.sigmaC01SourceBoxes :
  ∀ n, n < 13 → sigmaRatBallContains
    (sigmaC01CoefficientBall n)
    (completedSigmaDisplacedSourceCoefficient (1 / 10) n)
```

Elas ainda não têm prova. `sigmaPadeD_signs_at_99_2000_of_source_boxes` e
`sigmaPadeD_signs_at_1_10_of_source_boxes` são teoremas condicionais a essas
hipóteses. Portanto, **os sinais da fonte original não estão certificados**.

## O que já está provado e não deve ser refeito

- A C4 dá a recorrência polinomial escalada sem divisão
  `pₙ = −(n+1)cₙ₊₁c₀ⁿ − Σⱼ₌₀ⁿ⁻¹ cⱼ₊₁ pₙ₋₁₋ⱼ c₀ʲ`, com
  `pₙ = c₀ⁿ⁺¹ (2·completedSigmaLogJet d n)`. A identidade de menores é
  `pₛpₛ₊₂ − pₛ₊₁² = 4c₀²ˢ⁺⁴ sigmaPadeD d s`.
- A aritmética das bolas racionais, a propagação pela recorrência e as margens
  de sinal dos menores já estão provadas em Lean 4.32. A auditoria O3 só contém
  `propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx`, `admit`,
  axiomas próprios ou `native_decide` nesses resultados.
- O domínio analítico da fonte original no disco Cauchy e os limites de pesos
  de interpolação já estão integrados. Também há caixas Gamma certificadas em
  nós selecionados, e a fórmula Euler–Maclaurin de zeta já está formalizada.
- A tabela Bernoulli está certificada formalmente até 192/601 e integrada pela
  PR #313. O teorema cumulativo 224 já está compilado e auditado na branch
  `codex/c5-zeta-bernoulli-prefix224-20261108`; a PR #315 o integra. Não repetir
  prefixos anteriores nem relançar o build já concluído.

## Orçamento racional já disponível em O3

As caixas de coeficientes no módulo Lean têm os seguintes maiores diâmetros
absolutos (duas vezes o raio racional):

| Deslocamento | Coeficientes | Maior largura das bolas O3 |
|---|---:|---:|
| `99/2000` | `c₀,…,c₁₄` | `1 × 10⁻⁹⁰` |
| `1/10` | `c₀,…,c₁₂` | aproximadamente `4.0628267 × 10⁻⁸⁸` |

Propagando **essas bolas condicionais** pela recorrência C4 e pelos produtos do
menor, a aritmética racional do módulo fornece:

| Deslocamento | Janela | Intervalo do menor escalado `pₛpₛ₊₂−pₛ₊₁²` | Largura aproximada |
|---|---:|---:|---:|
| `99/2000` | `s=10` | centro `4.7334633 × 10⁻⁷⁶`, raio `2.8879040 × 10⁻¹³²` | `5.7758080 × 10⁻¹³²` |
| `99/2000` | `s=11` | centro `−2.7064148 × 10⁻⁸⁰`, raio `1.0601430 × 10⁻¹³⁴` | `2.1202860 × 10⁻¹³⁴` |
| `1/10` | `s=8` | centro `1.3895272 × 10⁻⁶²`, raio `5.7881391 × 10⁻¹²¹` | `1.1576278 × 10⁻¹²⁰` |
| `1/10` | `s=9` | centro `−3.9157532 × 10⁻⁶⁸`, raio `8.5901013 × 10⁻¹²³` | `1.7180203 × 10⁻¹²²` |

Os limites exatos são os racionais definidos por
`sigmaRatBallLower`/`sigmaRatBallUpper` em `SigmaFiniteRationalIntervalSigns.lean`;
os números exibidos aqui são arredondados para leitura. `norm_num` fecha os
sinais exatos para todos os menores anteriores e para a janela final. Assim,
**a caixa O3 já existente não se alarga demais ao passar pela recorrência e
pelo determinante**. Isso ainda é condicional à inclusão dos coeficientes.

Como referência independente, o replay arquivado do gerador intervalar da C2 e
do verificador por frações racionais reporta os seguintes extremos para os
determinantes originais:

| Fonte experimental | Determinante | Intervalo racional reportado | Largura | Margem até zero |
|---|---:|---:|---:|---:|
| C2, `d=0.0495` | `D₁₀` | `[4.382953952339149273675878781, 4.382953952339149273675878782] × 10⁻⁶²` | `10⁻⁸⁹` | `4.3829… × 10⁻⁶²` positiva |
| C2, `d=0.0495` | `D₁₁` | `[−4.102383393213308015363590069, −4.102383393213308015363590068] × 10⁻⁶⁵` | `10⁻⁹²` | `4.1023… × 10⁻⁶⁵` negativa |
| C2, `d=0.1` | `D₈` | `[4.767785674945961332237907753, 4.767785674945961332237907754] × 10⁻⁵¹` | `10⁻⁷⁸` | `4.7677… × 10⁻⁵¹` positiva |
| C2, `d=0.1` | `D₉` | `[−2.197940531642680210826376627, −2.197940531642680210826376626] × 10⁻⁵⁵` | `10⁻⁸²` | `2.1979… × 10⁻⁵⁵` negativa |

Essas últimas caixas vêm da reprodução em `evidence/rational-boxes/reproduction-20261107/`;
seu verificador racional fecha exatamente as operações sobre os extremos
exportados, mas **a origem `mpmath.iv` ainda não está certificada em Lean**.
São diagnóstico do tamanho de margem necessário, não uma prova nova da fonte.

## Os cinco termos cruzados não podem ser descartados

Para `d=0.0495`, `s=10`, escreva `hₙ=pₙ+eₙ`, onde `pₙ` é o modelo de dois
modos e `eₙ` seu resíduo. A identidade exata é

```text
D_s(h) − D_s(p) =
    p_s e_{s+2} + e_s p_{s+2} − 2 p_{s+1} e_{s+1}
  + e_s e_{s+2} − e_{s+1}².
```

Os cinco valores reexecutados em alta precisão são, respectivamente,
`+2.205275255e−62`, `+2.179084854e−61`, `−1.385166861e−61`,
`+7.91893726e−68` e `−7.904487883e−68`. Eles corrigem o valor do modelo
`D₁₀(p) ≈ −5.76150124324e−62` para o valor positivo da fonte completa
`D₁₀(h) ≈ +4.38295395233914927e−62`. O menor original só fica negativo em
`s=11`, com `D₁₁ ≈ −4.10238339321e−65`.

Esses números são diagnóstico experimental, não certificado Lean. A rota formal
O2/O3 não subtrai um modelo de modos: usa diretamente a recorrência C4 e bolas
para todos os coeficientes. A multiplicação das bolas contém explicitamente
`|a|r_b + |b|r_a + r_a r_b`, preservando os termos de cruzamento durante a
propagação e o menor. Se a identidade acima for usada em trabalho posterior,
os cinco termos devem receber caixas absolutas próprias.

O erro material da cauda C2 `T_L(w)` (cauda exata de Hurwitz após a cabeça
finita) e o resíduo de modos `eₙ=hₙ−pₙ` são objetos diferentes. A genealogia
continua sendo: geometria C2 → bracket centrado → cabeça finita + cauda exata →
fator da câmera → escalar nativo → completação original → coeficientes C4 →
determinantes. Não substituir essa fonte por zeros/polos nem misturar `T_L`
com `eₙ`.

## Primeiro ponto ainda sem certificação e fortalecimento proposto

Não foi encontrado um estágio **já formalizado** cuja caixa O3 fique larga
demais: as larguras e margens acima mostram folga no transporte C4/determinante.
O primeiro ponto sem certificado é anterior, na avaliação da fonte nos nós:
as 516 coordenadas exportadas de zeta nos 129 nós ainda não têm prova Lean que
as ligue às caixas `c5RationalZetaCenteredNodeBox`; `CSV`/`#eval` só demonstra
que a exportação cobre os dados. `mpmath.iv` tampouco fornece por si só a
inclusão analítica necessária. Gamma está certificada apenas em nós já
listados nos checkpoints, e ainda falta compor todas as funções e o fator da
fonte até os coeficientes.

Fortalecimento mínimo, preservando a missão e os resultados existentes:

1. integrar o prefixo 224 da PR #315; depois avançar os blocos cumulativos da
   tabela Bernoulli até 601, sem refazer prefixos provados;
2. usar a igualdade formal da tabela para provar **um nó piloto** por uma
   expressão finita Euler–Maclaurin em intervalos racionais complexos, somando
   o resto analítico já formalizado e fechando a igualdade com a caixa exportada;
3. comparar, nesse nó, as larguras absolutas intermediárias com os limites
   necessários para caber nas caixas de coeficientes; se falhar, localizar a
   primeira composição que alarga a caixa (avaliação nodal, zeta/Gamma,
   interpolação ou Cauchy) e estreitar só essa etapa;
4. compor o nó com Gamma, fator da câmera e a cabeça/cauda **originais**; depois
   transportar as caixas à interpolação e às inclusões `sigmaC00495SourceBoxes`
   e `sigmaC01SourceBoxes`.

Até a prova das duas inclusões, os sinais de C2/C5 permanecem condicionais.

## Referências de proveniência

- [Anatomia dos cinco cruzamentos na C2](https://github.com/thiagomassensini/momentos/blob/research/sigma-pade-dimension-depth-20261104/investigations/c2_sigma_cross_term_anatomy_20261106/RELATORIO_ANATOMIA_CRUZAMENTOS_2026-11-06.md)
- [Certificação intervalar finita C2/C4 e limites explícitos](https://github.com/thiagomassensini/momentos/blob/research/sigma-pade-dimension-depth-20261104/investigations/c2_first_negative_interval_certificate_20261106/RELATORIO_CERTIFICADO_FINITO_C2_2026-11-06.md)
- Replay arquivado dos sinais condicionais e seus logs: `evidence/rational-boxes/reproduction-20261107/`.
