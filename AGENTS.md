# Instruções de trabalho

- Preservar a ordem quantidade → carry → geometria → métrica → representação
  real → operador. Nunca importar um operador como justificativa da fundação.
- Ler `docs/FORMALIZATION_PLAN.md` e `docs/SOURCE_PROVENANCE.md` antes de portar
  módulos históricos.
- Zona A: `GeometryOfNumbers/Foundation/`. Manter a auditoria transitiva de
  axiomas vazia. Adicionar todo teorema público novo ao audit explícito.
- Não importar Mathlib/analítica na fundação atual nem dependências complexas.
- Não introduzir escapes de confiança, placeholders ou axiomas novos.
- Os nomes do plano são metas, não evidência de existência de provas.
- Registrar a fonte/commit e quaisquer hipóteses operacionais de uma porta.
- Não declarar uma fase fechada por ter definido uma estrutura com as metas
  como campos.
- Verificar com `bash scripts/audit-foundation.sh`.
- Não fazer commit/push sem pedido do usuário; não incluir alterações paralelas.
