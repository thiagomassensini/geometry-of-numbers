# Próximos passos para retomada

1. Validar estes registros C0, atualizar `SESSION_STATE.md` com o commit e SHA remoto, fazer push da branch `agent/sigma-allorder-negative-certified-20261105` e abrir PR de inventário para `main`.
2. Antes de portar qualquer módulo, ler `docs/FORMALIZATION_PLAN.md` e `docs/SOURCE_PROVENANCE.md` conforme `AGENTS.md`.
3. Comparar a assinatura e cadeia transitiva de `exists_sigmaMatrix_negative_direction_of_zero` com a `main`; rastrear a ponte à altura positiva pelo módulo de continuação nativa e por `HardyFirstZero.first_zero_on_line`.
4. O port de C1 deve usar somente fontes e pins Lean 4.32 explícitos. Não copiar `.olean`, não introduzir hipótese equivalente à conclusão, e não importar a branch de pesquisa inteira.
5. Se a ponte de fonte não existir nas versões dependentes da `main`, registrar a primeira declaração ausente com sua assinatura e dependência; só então escolher um port mínimo revisável.
6. Depois de C1 fechado: provar o lema de extensão por zeros (C1B), compor C2 com a decomposição original e o certificado de altura 50, e transportar C3 aos setores par/ímpar. Após cada um, compilar, auditar, registrar, publicar e propor PR conforme a política da missão.
7. Fazer C4 por último; antes, ler `docs/R2_TFVD_GREEN_VALVE_ROUTE.md` se a exploração entrar na rota R2/TFVD.

Comandos já conferidos para recuperação operacional: `git worktree list --porcelain`; `git status --short --branch`; `git log -n 20 --oneline --decorate`; `git rev-list --left-right --count origin/main...<branch>`; `git ls-remote origin refs/heads/main`.
