# Checkpoint — certificação cofactorial C3

- Fase atual: Checkpoint 0 concluído; iniciando Missão A (identidade cofactorial abstrata).
- Repositório: `thiagomassensini/geometry-of-numbers`; worktree isolado `/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112`.
- Branch: `agent/c3-cofactor-chiral-certification-20261112`; base `origin/main` = `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`.
- PR #316 e PR #317 confirmadas no histórico de `origin/main`; PR #317 registra merge da #316.
- Estado original `/home/thlinux/geometry-of-numbers` preservado: dois itens não rastreados preexistentes, não alterados.
- Pins: Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Reuso preparado: `research/tfvd-bezout-order-compensation/` (inclui congruência/Schur e identidade de determinante afim), `research/c3-dimension-three/C3Tail256.lean`, caixas Gamma C3 e transporte quiral existente.
- Novo código ainda não criado; este arquivo registra apenas reconhecimento e proveniência.
- Comandos já passaram: `git fetch origin`; `git worktree add ... origin/main`; conferência de HEAD, branch, pins e histórico das PRs.
- Arquivos criados nesta fase: `research/c3-cofactor-chiral-certification/CHECKPOINT.md`.
- Commit atual/base: `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`.
- Falhas: nenhuma nesta fase.
- Próximo passo exato: formalizar para matriz simétrica em blocos a identidade `det B = det(A) * E(u) - rᵀ adj(A) r`, inclusive com prefixo singular, e compilar o módulo isoladamente.
- Obrigação matemática aberta: prova algébrica sem inversa; sinal C3 e caixas `c₀,…,c₆` seguem totalmente abertos nesta branch.
