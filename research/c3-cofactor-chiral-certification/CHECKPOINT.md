# Checkpoint — certificação cofactorial C3

- Fase atual: Checkpoint 1 parcial concluído; prosseguir ao gate racional e regressões.
- Repositório: `thiagomassensini/geometry-of-numbers`; worktree isolado `/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112`.
- Branch: `agent/c3-cofactor-chiral-certification-20261112`; base `origin/main` = `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`.
- PRs #316 e #317 confirmadas no histórico; pins Lean `v4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Árvore original preservada com os dois untracked preexistentes; todo código novo está no worktree isolado.
- Commit Checkpoint 0: `8c4287e` (reconhecimento, branch e proveniência), publicado.
- Arquivo criado: `research/c3-cofactor-chiral-certification/CofactorIdentity.lean`.
- Provados: `odd_third_cofactor_identity`, `odd_third_cofactor_vector_identity` e `odd_third_cofactor_vector_quadratic`.
- Escopo provado: identidade cofactorial para matriz simétrica 3×3 e prefixo 2×2 arbitrário, inclusive singular; identidade do vetor cofactorial no mesmo caso.
- Validação: compilação Lean direta com `-DwarningAsError=true` passou; os três `#print axioms` mostram apenas `propext`, `Classical.choice`, `Quot.sound`.
- Falhas: nenhuma na especialização 3×3. A prova uniforme para prefixos de dimensão arbitrária ainda não foi formalizada.
- Commit atual antes deste checkpoint: `8c4287e`; novo commit contém o módulo acima e esta atualização.
- Próximo passo exato: demonstrar a condição polinomial racional de positividade para o terceiro ímpar e canários positivos/negativos/singulares, sem assumir o sinal alvo.
- Obrigações abertas: prova uniforme cofactorial; caixas originais até `c₆`; desigualdade estrita para a fonte; C3/48 e transporte quiral.
