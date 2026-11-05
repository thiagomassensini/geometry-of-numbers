# Estado da missão — negatividade transversal all-order

**Atualizado:** 2026-11-05

**Objetivo ativo:** C0 e C1 estão integrados. C1B está provado e validado localmente; publicar e integrar esse checkpoint, depois fechar C2 e C3 em entregas separadas. Investigar C4 somente depois. Não demonstrar RH nem positividade canônica central.

## Checkout e base

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Worktree ativa: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`.
- Branch atual: `agent/sigma-c1b-persistent-negative-20261105`, criada sobre a `main` que contém C1.
- Base integrada C1 / `origin/main`: `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`.
- C0 foi integrado pela PR #153, merge commit `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- C1 foi integrado pela PR #154. Commit de prova: `c2706339b15db390bf8f5f50535016bd1aca8cb8`; merge commit: `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`.
- CI da PR #154: workflow `42101466137`, conclusão `success`; build da raiz com warnings-as-errors e auditorias de kernel hospedadas passaram.
- A referência local da worktree foi restaurada a partir do merge commit validado; as entradas vazias originais foram preservadas em `/tmp/c1-ref-recovery.RFKurx`.

## Dependências e ambiente

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Carry source pin: `carry-self-adjoint-operator@045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; CPFormal, Geometry e demais dependências estão registrados no script C1 e na proveniência C1.
- O certificado do primeiro zero vem de `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`; licenças e patch de compatibilidade foram preservados.
- O build focado compara os pins de fontes transitivas e recompila a cadeia local em diretório temporário; os imports de dependências externas usam caches dos checkouts com pins explícitos.
- Depois do aumento da VM, havia aproximadamente 60 GiB de `MemAvailable`, acima do gate de 30 GiB do script.

## Checkpoints e teoremas

- **C0 — integrado:** inventário e estado persistido, PR #153, merge commit `2a3e899…`.
- **C1 — integrado e validado:** `CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift`, para todo `0 < |d| < 1/4`, produz uma direção negativa finita da `sigmaMatrix` original. PR #154, commit de prova `c270633…`, CI hospedado aprovado no run `42101466137`.
- **C1B — provado e validado localmente; publicação pendente:**
  - `sigmaMatrix_prefix_submatrix` identifica exatamente a seção menor como bloco principal prefixo da seção maior.
  - `certified_sigma_negative_directions_persist` prova que, para cada deslocamento de C1, existe um limiar `N` tal que toda seção `M ≥ N` tem uma direção negativa.
  - `certified_sigma_not_posSemidef_persist` prova a falha de `PosSemidef` para todas essas dimensões.
  - A prova usa que matrizes semidefinidas positivas passam a submatrizes principais; a simetria da matriz converte a falha em uma direção quadrática negativa em cada dimensão.
- **C2 — aberto:** negatividade eventual dos menores originais em `d=1/5`, via decomposição Padé e isolamento certificado.
- **C3 — aberto:** transporte às torres par e ímpar, após C2.
- **C4 — não iniciado:** fonte deslocada, fator 2 e Bézout; depende da conclusão dos anteriores.

## Compilação e auditoria

- C1: build raiz completo em Lean 4.32 passou com 8.857/8.857 jobs sem cache; build focado e auditoria de proveniência estão em `evidence/c1-*`.
- C1: checker recursivo confirmou 1.278 módulos-fonte não-Mathlib contra os commits/pins registrados.
- C1/C1B: `SIGMA_OUTPUT_DIR=/tmp/sigma-c1b-persistent-20261105 research/native-moving-schur-sigma/compile_c1.sh` passou de ponta a ponta. O checker aceitou 109 relatórios de axiomas, todos limitados a `propext`, `Classical.choice` e `Quot.sound`.
- Evidência C1B: `evidence/c1b-focused-build.log`, `evidence/c1b-source-sha256.txt` e `evidence/c1b-validation.md`.
- Os módulos Lean C1 e C1B foram compilados de novo em saída temporária; nenhum `.olean` foi adicionado ao Git.
- A CI hospedada confirmada é a da PR #154/C1. O C1B ainda precisa de sua própria PR e execução hospedada.

## Próxima ação concreta

Revisar o diff e `git diff --check`; commitar somente o módulo C1B, atualização do script, documentação e evidências desta missão; publicar `agent/sigma-c1b-persistent-negative-20261105`, abrir PR para `main`, conferir a CI e integrar após aprovação dos gates. Em seguida iniciar C2 em uma branch separada. As demais worktrees e alterações locais permanecem preservadas.
