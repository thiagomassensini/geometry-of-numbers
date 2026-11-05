# Relatório consolidado — missão de negatividade transversal sigma

**Estado inicial, 2026-11-05:** C0 foi publicado em `5ad667a06007ac3d56a5b208473e01dcabcb5c64`, PR #153 aberta; checkpoints matemáticos C1, C1B, C2, C3 e C4 ainda abertos nesta branch baseada em `main@21b3dace…`.

## Pergunta e escopo

Compor as provas Lean existentes para obter direções negativas de `sigmaMatrix` e persistência dimensional, além da negatividade eventual de menores Padé originais em `d=1/5`. Preservar a característica completada, os jets e a matriz originais. Não provar RH nem positividade canônica central.

## Estado recuperado

O módulo `SigmaZeroObstruction.lean` na branch `agent/native-moving-schur-sigma@9392ebac…` demonstra negatividade finita sob a hipótese de um zero nativo positivo; ele não descarrega essa hipótese. Os lemas de convergência Padé e o certificado de isolamento de altura 50 estão em branches separadas e ainda não foram integrados na `main`. Os resultados publicados de curvatura #139–#142 já estão na `main`, mas não provam os checkpoints desta missão.

## Resultado desta atualização

Foi criado um checkout limpo da `main` atual e gravado o inventário Git/dependências/PRs em `MERGE_INVENTORY.md` e `evidence/c0-inventory.md`. O commit C0 foi publicado e a PR #153 está aberta. O GitHub não retornou status checks nem workflows para o commit; CI não está sendo tratado como aprovado. O estado detalhado encontra-se em `SESSION_STATE.md`; a retomada concreta, em `NEXT_STEPS.md`.

## Status dos checkpoints

| Checkpoint | Estado | Evidência atual |
|---|---|---|
| C0 — recuperação/inventário | Documentado; publicação do checkpoint pendente | `MERGE_INVENTORY.md`, `evidence/c0-inventory.md` |
| C1 — direção para todo `0<|d|<1/4` | Aberto; precisa descarregar o zero | `THEOREM_MAP.md` |
| C1B — persistência em dimensões maiores | Aberto | `THEOREM_MAP.md` |
| C2 — menores originais eventualmente negativos em `1/5` | Aberto; teoremas/isolamento existem em branches não integradas | `THEOREM_MAP.md` |
| C3 — setores par e ímpar | Aberto | `THEOREM_MAP.md` |
| C4 — série deslocada/Bézout | Não iniciado | `THEOREM_MAP.md` |

## Validação

O Lean 4.32.0 está instalado e a memória disponível é aproximadamente 51.9 GiB. Nenhum build Lean foi executado nesta branch até aqui. As worktrees preexistentes e seus arquivos locais foram preservados; nenhuma fonte foi portada ou alterada ainda.
