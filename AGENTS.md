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
  existentes, com capacidade ímpar; não implica identificação de profundidades.
- Não importar primalidade histórica para o balanceamento. Oddness é hipótese
  explícita de regime, não conclusão da emergência da capacidade. Preservar
  resíduo zero como centro; não atribuir lado arbitrário ao antipodal par/C2.
- Auditar a geometria com `bash scripts/audit-geometry.sh`: definições sem
  axiomas; teoremas permitem somente `propext` e `Quot.sound` da aritmética
  inteira de Init. Não anunciar footprint vazio nessa camada nem permitir escolha.
- Auditar a Zona B separadamente com `bash scripts/audit-analysis.sh`;
  seus axiomas padrão não são permitidos na auditoria vazia da Zona A.
- Não introduzir escapes de confiança, placeholders ou axiomas novos.
- Os nomes do plano são metas, não evidência de existência de provas.
- Registrar a fonte/commit e quaisquer hipóteses operacionais de uma porta.
- Não declarar uma fase fechada por ter definido uma estrutura com as metas
  como campos.
- Verificar com `bash scripts/audit-foundation.sh`.
- Não fazer commit/push sem pedido do usuário; não incluir alterações paralelas.
