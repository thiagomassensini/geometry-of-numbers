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
