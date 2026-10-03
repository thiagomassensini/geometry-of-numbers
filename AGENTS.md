# Instruções de trabalho

- Preservar a proveniência quantidade → carry e distinguir a fundação de escala
  já encerrada da geometria adicional. Centro–pernas não foi premissa da massa
  ou de metade. Nunca importar um operador como justificativa da fundação.
- Ler `docs/FORMALIZATION_PLAN.md` e `docs/SOURCE_PROVENANCE.md` antes de portar
  módulos históricos.
- Zona A: `GeometryOfNumbers/Foundation/`. Manter a auditoria transitiva de
  axiomas vazia. Adicionar todo teorema público novo ao audit explícito.
- Não importar Mathlib/analítica na fundação atual nem dependências complexas.
- O import `GeometryOfNumbers` é exclusivamente discreto. A Zona B usa
  `GeometryOfNumbers.Analysis`; nunca importar essa camada na fundação.
- `GeometryOfNumbers.Geometry` é a entrada separada para centro–pernas,
  reflexão e segunda diferença sobre `Int`. Não importá-la na Foundation.
  A entrada Analysis reúne Geometry. O crosswalk de uma célula usa os ciclos
  existentes, com capacidade ímpar. A profundidade relacional consulta zeros
  sucessivos da torre; sua equivalência com divisibilidade é um teorema.
  Não importar valuation nem substituir essa relação por um máximo finito.
- Não importar primalidade histórica para o balanceamento. Oddness é hipótese
  explícita de regime, não conclusão da emergência da capacidade. Preservar
  resíduo zero como centro; não atribuir lado arbitrário ao antipodal par/C2.
- Auditar a geometria com `bash scripts/audit-geometry.sh`: definições sem
  axiomas; teoremas permitem somente `propext` e `Quot.sound` da aritmética
  inteira de Init. Não anunciar footprint vazio para toda essa camada nem permitir
  escolha. A extensão `Geometry/ResidualTowerDepth.lean` tem guard adicional de
  footprint vazio para cada teorema público; Foundation permanece congelada.
  A versão inteira da profundidade estende a equivalência natural já provada;
  não criar uma segunda torre. Zero e capacidade um sobrevivem em todo nível.
  A seleção do offset requer nível positivo; não resolver o antipodal C2 aqui.
- Auditar a Zona B separadamente com `bash scripts/audit-analysis.sh`;
  seus axiomas padrão não são permitidos na auditoria vazia da Zona A.
- O estado real atual é de profundidade: `(b,k,theta)`, com energia explícita
  `x²+y²`. A amplitude vem da realização anterior; energia não seleciona
  retroativamente metade. O ângulo é livre, sem lei física ou espectral.
  Não transformar suporte de `k` pelo centro em estado global de `n`;
  a hipótese de suporte registra proveniência, não necessidade algébrica.
  Não usar a norma pronta do produto como definição dessa energia.
- A reflexão quadrática usa o centro da amplitude anterior: `C*q,C*q⁻¹`.
  Seu produto conserva a massa; o bracket local é definido pelo readout das
  pernas, nunca pela fatoração desejada. Positividade/zero único exigem
  `C>0,q>0`; produto/fatoração exigem `q≠0`. A inversão total em zero não
  resolve esse domínio. Manter `q` independente do ângulo livre; nenhum
  parâmetro físico ou bracket histórico é identificado por essa construção.
  Não usar o bracket para selecionar retroativamente metade ou uma norma.
- A câmera ímpar recebe `half` explicitamente e tem capacidade `2*half+1`.
  Nunca extrair esse dado por escolha nem acrescentar primalidade.
  Geometry usa soma recursiva dos raios `1,...,half` e observáveis inteiros;
  bracket por pernas menos cópias do centro e soma saturada têm definições
  independentes. A câmera quadrática abstrata recebe `q_r` livre positivo;
  o crosswalk do perfil usa a compatibilidade explícita abaixo para provar
  `q_r=Q(r)=rho^r` e as avaliações das pernas.
  Reflexão independente conserva o total; a massa é conservada por PAR,
  não somada ou identificada com esse total. Câmera vazia não seleciona
  expoente; C2 e seleção do passo de deformação permanecem gates separados.
- A ponte atual exige EXPLICITAMENTE `Q(0)=1`, `Q(a+b)=Q(a)*Q(b)` e
  `Q(1)>0`: nova compatibilidade semântica, não conclusão da torre/reflexão.
  Reciprocidade, positividade global e `Q(r)=rho^r` são teoremas; `rho`
  permanece livre. Perfil orientado por `center-point`, esquerda com `Q(r)`.
  O lift real da câmera prova saturação para qualquer observável antes do
  crosswalk do perfil. Não identificar esse caráter do offset com uma
  potência do ponto absoluto, razão histórica ou amplitude vertical.
  Raio horizontal `r` não é profundidade vertical `k`; câmera vazia não
  seleciona o passo. Não introduzir log/exp para classificar offsets inteiros.
  O módulo de transporte importa somente `Mathlib.Data.Real.Basic` e guarda
  a ausência de `Real.log`/`Real.exp`; preservar essa independência dos
  módulos de amplitude e das pernas quadráticas.
- Não introduzir escapes de confiança, placeholders ou axiomas novos.
- Os nomes do plano são metas, não evidência de existência de provas.
- Registrar a fonte/commit e quaisquer hipóteses operacionais de uma porta.
- Não declarar uma fase fechada por ter definido uma estrutura com as metas
  como campos.
- Verificar com `bash scripts/audit-foundation.sh`.
- Não fazer commit/push sem pedido do usuário; não incluir alterações paralelas.


## Guardrails da Forma Centro–Pernas

- Definir as posições e o readout vetorial geometricamente antes de fatorar.
  Energia continua sendo `x²+y²`; reutilizar sua invariância rotacional.
- Preservar estado, deformação e ângulo por canal até a leitura energética.
  Ângulos locais continuam na definição mesmo quando desaparecem da energia.
- Somar energias locais; nunca substituir essa soma por energia da soma dos
  vetores. Vetores opostos fornecem um contraexemplo formal.
- O crosswalk escalar é soma ponderada de quadrados de brackets locais,
  não quadrado do bracket total. Coincidência de zeros exige suas hipóteses.
- No defeito comum, o critério de zero usa energia inicial total positiva;
  não exigir que todos os canais sejam não triviais. Câmera vazia permanece
  degenerada e não seleciona o defeito radial.
- A especialização crítica reutiliza massa/amplitude anteriores; estas formas
  não justificam retroativamente metade nem selecionam ângulo ou parâmetro.


## Guardrails do atlas coordenado parametrizado

- `AdmissibleAtlasPartition` é entrada semântica explícita. Conservação de
  energia é theorem derivado dela; seleção canônica pela torre permanece aberta.
  Não anunciar FULL PASS apenas por receber soma unitária na interface.
- Distinguir conservação de prefixos dentro de uma base de distribuição da
  mesma informação entre bases. Não definir profundidade por `padicValNat`
  nem selecionar pesos por log/exp histórico sem derivação interna.
- Rótulos `AtlasBase` não provam eventos carry ou capacidade ímpar por base.
  O atlas atual resolve finitos canais, com suporte finito por coordenada;
  não anunciar uma completion ou soma infinita de entradas.
- Preservar base e canal até a energia local. Não substituir sua soma por
  energia de síntese vetorial. Peso zero não identifica o defeito de um canal.
- Separar partição coordenada/Parseval, Gram intrínseco não diagonal e packing
  de proveniência históricos; qualquer identificação requer theorem próprio.


## Guardrails do crosswalk primo downstream

- Factorization/valuation só pode representar a profundidade após theorem de
  equivalência relacional; nunca redefinir retroativamente a torre. O crosswalk
  atual usa primo p e n≠0, preservando zero com profundidade em todo nível.
- Manter o crosswalk discreto com Mathlib em Analysis enquanto Geometry excluir
  essa dependência. Não introduzir logaritmo nesse módulo discreto.
- Quantidade n e índice de canal/raio r não se identificam sem crosswalk.
  A partição prima derivada tem soma um somente para quantidades n>1;
  em um todos os pesos são zero. Não reparar essa obstrução com base arbitrária,
  deslocamento de índice ou alteração silenciosa da interface total do atlas.
- Logaritmos das vozes são leitura downstream da fatoração única; não são
  origem da profundidade, classificação dos offsets ou seleção do passo rho.
- Reconstrução por exponentes primos não prova combinação linear das câmeras
  compostas nem injetividade de uma síntese escalar real arbitrária.

## Leitura obrigatória de R2 e posteriores

Antes de qualquer trabalho na fase R2 ou posterior, leia
`docs/R2_TFVD_GREEN_VALVE_ROUTE.md`.

Horizontal radius ≠ vertical depth: odd-camera radius / horizontal displacement
is not vertical carry depth (`r_horizontal ≠ k_vertical`).
Center-leg deformation ≠ vertical amplitude ratio: the center-leg reciprocal
parameter `q` is not the TFVD ratio `eta_b = b^(-1/2)`
(`q_center-leg ≠ eta_vertical`). Use distinct names. No theorem identifies them.


## R6/R7 — no premature scalarization

No premature scalarization: intermediary channel/readout data may not be
identified with the global observable before exact synthesis/reconstruction
has been proved. A failed prematurely scalarized candidate is a no-go for
that representation, not automatically a no-go for the complete theory.

Preserve the causal order: provenance → complete channels → exact head/tail
synthesis → jets/scalar readout → log derivative → moments. Derived tail
coefficients are residuals of the synthesized observable; do not substitute
an independently supplied tail or conflate a head jet with a complete jet.
