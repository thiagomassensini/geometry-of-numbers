# C1B — registro de validação

- Base de código: `main` após C1, merge commit `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`.
- Toolchain e dependências: Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; pins adicionais conferidos por `compile_c1.sh`.
- Comando executado: `SIGMA_OUTPUT_DIR=/tmp/sigma-c1b-persistent-20261105 research/native-moving-schur-sigma/compile_c1.sh`.
- Resultado: sucesso, incluindo a recompilação do fechamento C1 e do módulo `SigmaPersistentNegativeDirection.lean`, varredura de fontes e checker de axiomas.
- Axiomas: o checker aceitou 109 relatórios; cada um usa somente `propext`, `Classical.choice` e `Quot.sound`. Os três teoremas C1B aparecem explicitamente no log.
- Placeholder/axiomas novos: a varredura do script não encontrou `sorry`, `admit`, `native_decide`, `sorryAx` nem declaração `axiom` nas fontes verificadas.
- Memória: havia aproximadamente 56–60 GiB de `MemAvailable`, acima do limite de 30 GiB do script.
- Log integral: `c1b-focused-build.log`. Hashes dos arquivos de código e script: `c1b-source-sha256.txt`.
- Publicação: C1B foi integrada à `main` pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`; não há publicação pendente. A CI hospedada concluída com sucesso (`42101466137`) corresponde à PR #154/C1 e não é atribuída à PR #155.
