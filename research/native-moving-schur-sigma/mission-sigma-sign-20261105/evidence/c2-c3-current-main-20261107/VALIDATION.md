# Revalidação C2/C3 após reinício

**Estado:** concluída em 2026-11-07. C2 e C3 já estavam integrados à `main` pelas PRs #157 e #159; esta execução recompilou a closure e repetiu as auditorias após o aumento de memória da VM. Não houve alteração nas provas.

## Conferência da `main` após PR #240

Em `2026-11-07`, `origin/main` avançou para `89710ecaf940f1a7887cd133451916edd76bddcb`. Os cinco módulos C2/C3 compilados nesta validação foram comparados entre a revisão registrada abaixo (`b604c06`) e essa ponta atual; `git diff` não encontrou alterações neles. A listagem completa das mudanças Lean sob `research/native-moving-schur-sigma` mostra somente módulos C5 novos; nenhum fonte existente da closure C2/C3 mudou (`current-main-lean-source-diff.txt`). Os hashes abaixo continuam iguais no snapshot compilado e na `main` atual, então esta validação continua cobrindo a closure C2/C3 vigente. A conferência dos cinco módulos foi reproduzida com `git diff --quiet b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1 89710ecaf940f1a7887cd133451916edd76bddcb -- research/native-moving-schur-sigma/SigmaRHHeightBridge.lean research/native-moving-schur-sigma/SigmaHeight50Integration.lean research/native-moving-schur-sigma/SigmaPadeEventualNegativity.lean research/native-moving-schur-sigma/SigmaParityNegativeDirection.lean research/native-moving-schur-sigma/SigmaPadeAudit.lean`; o comando terminou com código zero. O checkpoint separado da tentativa 4.35 permanece publicado na PR #221 como incompleto; nenhuma migração Geometry/Carry foi retomada.

## Revisões e pins

- `origin/main` conferida: `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1` (após PR #235).
- Checkout das fontes compiladas: `codex/sigma-c2c3-priority-20261107@f848c8a34b5f6859d5d8c0419bac214f972278f7`, já integrado à `main` pela PR #221. Os cinco módulos C2/C3 listados em `source-pins-and-hashes.txt` têm os mesmos hashes nesse checkout e na `main` atual; o delta posterior é composto por módulos e registros C5.
- Integração de altura 50: referência publicada em Lean 4.32 no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
- Toolchain: Lean `4.32.0`, `-DwarningAsError=true`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Certificado altura-50: `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`.
- Árvore reutilizada de dependências Lean 4.32: `67aea3263426cc8f9787f34aa7833a5650dde175`.
- `MemAvailable` observado após o reinício: aproximadamente 60 GiB, acima do limite de 30 GiB.

## Resultados

- `SigmaRHHeightBridge.lean` e `SigmaHeight50Integration.lean` recompilaram.
- `SigmaPadeEventualNegativity.lean` recompilou. O checker aceitou `exists_eventually_negative_sigmaPadeD_from_height50_certificate` com somente `propext`, `Classical.choice` e `Quot.sound`.
- `SigmaParityNegativeDirection.lean` recompilou. O checker aceitou os quatro relatórios públicos de janela/direção com somente os mesmos axiomas padrão.
- `SigmaPadeAudit.lean` refez a auditoria transitiva: 133 raízes públicas e 70.861 dependências de tipos/corpos, sem axiomas além dos três padrão.
- A definição `CarrySigmaObstruction.sigmaLineZero` continua única em `SigmaCertifiedNegativeDirection.lean`.

## Teoremas conferidos

C2 prova, nos momentos originais, sem hipótese de sinal adicional e mantendo o resto:

```lean
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0
```

`SigmaPadeEventualNegativity.lean` compõe `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`. `completedSigmaLogJet` e `sigmaPadeD` permanecem os originais.

C3 usa `p = 2i` e `p = 2i + 1` para cobrir explicitamente os setores par e ímpar. Cada janela negativa `2 × 2` é transportada pela persistência C1B a toda dimensão `M ≥ i + 2`. Não foi calculada a primeira profundidade de falha.

## Reconfirmação após PR #241 (2026-11-07)

A ponta atual de `origin/main` é `24f61b01732f44599869350c4bf675c3f3a3dcb6`. Executei `git diff --quiet b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1 24f61b01732f44599869350c4bf675c3f3a3dcb6 --` sobre `SigmaRHHeightBridge.lean`, `SigmaHeight50Integration.lean`, `SigmaPadeEventualNegativity.lean`, `SigmaParityNegativeDirection.lean` e `SigmaPadeAudit.lean`; o código de saída foi zero, sem diferenças. Assim, a compilação 4.32 e a auditoria transitiva arquivadas continuam cobrindo a closure C2/C3 atual. `git grep 'def sigmaLineZero' origin/main -- research/native-moving-schur-sigma` encontra somente a definição em `SigmaCertifiedNegativeDirection.lean`.

## Comandos reproduzidos

Com `SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main`, `CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369`, `SIGMA_HEIGHT50_BUILD` apontando para `research/native-moving-schur-sigma/.cache/c3-validation/final-run/{integration,external}`, `LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean` e `SIGMA_OUTPUT_DIR` apontando para um diretório de saída limpo:

```bash
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaRHHeightBridge
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaHeight50Integration
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeEventualNegativity
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaParityNegativeDirection
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeAudit
python3 research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/c2-c3-post-reboot-20261106/check_c2_axioms.py "$SIGMA_OUTPUT_DIR/c2-build.log"
python3 research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/c3-parity/check_c3_axioms.py "$SIGMA_OUTPUT_DIR/c3-build.log"
```

Os logs, saídas dos dois verificadores e os hashes de fontes/logs estão nesta pasta. Nenhum `.olean` é necessário para a retomada. O checkpoint Lean 4.35 continua separado e explicitamente incompleto em `../lean435-validation-incomplete/`; C2 não tem bloqueio na rota publicada 4.32, portanto não se iniciou migração geral de Geometry/Carry.
