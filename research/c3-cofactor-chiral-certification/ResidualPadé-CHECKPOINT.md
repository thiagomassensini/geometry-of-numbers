# Checkpoint — residual diferencial sem divisões

- GoN snapshot: `6c5c97b03925c398bf77a561d6e76b14563265e0` (#324), branch
  `codex/pade-sem-divisao-20261112`; Lean `4.32.0`.
- `ResidualPadé.lean` formaliza o cofator reverso de comprimento fixo, a
  truncação `Nbar`, o defeito de coeficientes em `2n`, o transporte pela
  recorrência formal e o corolário normalizado sob `det G ≠ 0`.
- `ResidualNative.lean` adapta `native_source_recurrence`, identifica o pivô
  com `sourceMomentSchur` e registra os blocos `(s,n)=(0,3),(1,3)` e as
  regressões pedidas. Também mostra que os graus 6 e 7 da derivada usam
  `7*c₇` e `8*c₈`, respectivamente.
- `ResidualAudit.lean` imprime os footprints dos teoremas genéricos e nativos.
- O verificador original `verificar_revisao_hardy_pade_c3.py` foi recebido nos
  anexos em 2026-11-13 e executado com `--exact`; passou em 120 casos
  (81 invertíveis, 39 singulares, 15 vazios). A saída preservada em
  `residual_pade_original_exact_results.json` tem seção `exact` idêntica à do
  JSON anexado.
- `verify_residual_pade_exact.py --exact` passou em 120 casos racionais
  reconstruídos; é uma verificação suplementar. A prova Lean geral continua
  sendo a evidência principal.
- O validador de repositório
  `CARRY_ROOT=/home/thlinux/carry-self-adjoint-operator CARRY_PR145_CACHE=/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112/research/c3-odd-head-source/.cache:/home/thlinux/geometry-of-numbers-c3-source-orientation/research/c3-source-orientation/.cache bash research/c3-cofactor-chiral-certification/validate.sh`
  terminou com exit code `0`: compilações C3, correlação racional,
  `lake build --wfail`, audits de Foundation/Geometry/Analysis e
  `git diff --check` passaram.

Os três módulos Lean novos e a identidade geral local foram compilados
explicitamente com `-DwarningAsError=true`. Na primeira execução os arquivos
originais de verificação ainda não estavam disponíveis; após o envio, rodei
`--exact` e comparei seu resultado com o JSON fornecido. Não rodei `--numeric`.

Não houve alterações no checkout principal, nos pins nem nos arquivos Lean
existentes do snapshot. A prova e as checagens `--exact` não usam sinal, Hardy
ou avaliação de Gamma. O `validate.sh` histórico também executou seus
diagnósticos C3/Gamma preexistentes, sem que eles sejam dependências dos
teoremas novos.
