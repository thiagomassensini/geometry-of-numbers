# C2/C3 recompiladas na main atual

**Base das fontes:** `origin/main@08a413f34dd5588ed3d021351af27f3f55e0c072`.
**Toolchain:** Lean 4.32.0, `-DwarningAsError=true`.
**Carry:** `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
**Estado de publicação:** C2 e C3 já estão integrados pelas PRs #157 e #159. Esta execução atualiza a evidência na revisão atual da `main`; não cria uma nova prova nem altera os teoremas.

## Resultados

- `SigmaRHHeightBridge.lean` e `SigmaHeight50Integration.lean` recompilaram a partir dos fontes da revisão atual, sobre a integração publicada 4.32. Os relatórios de axiomas dessas duas unidades usam somente `propext`, `Classical.choice` e `Quot.sound`.
- `SigmaPadeEventualNegativity.lean` recompilou sobre a bridge e a integração recém-compiladas. `check_c2_axioms.py` aceitou `exists_eventually_negative_sigmaPadeD_from_height50_certificate` com apenas `propext`, `Classical.choice` e `Quot.sound`.
- `SigmaParityNegativeDirection.lean` recompilou. `check_c3_axioms.py` aceitou os quatro resultados públicos de janela/direção, com apenas os mesmos três axiomas padrão.
- `SigmaPadeAudit.lean` recompilou e refez a auditoria transitiva: 133 raízes públicas, 70.861 dependências de tipos/corpos, nenhuma dependência de axioma fora dos três padrão. A auditoria confirmou a proveniência da característica original, de `completedSigmaLogJet` e de `sigmaMatrix`.
- `CarrySigmaObstruction.sigmaLineZero` tem uma única definição, em `SigmaCertifiedNegativeDirection.lean`, reutilizada pela bridge C2.

O alvo C2 permanece, nos momentos originais:

```text
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0.
```

A prova preserva `completedSigmaLogJet`, `sigmaPadeD` e o resto exponencial. Ela compõe o isolamento derivado do certificado altura-50, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`; não introduz hipóteses de sinal. A primeira referência continua sendo a integração publicada em Lean 4.32 no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, que inclui `SigmaHeight50Integration.lean`.

C3 usa `p=2i` e `p=2i+1` para cobrir explicitamente os setores par e ímpar. Cada janela negativa de tamanho 2 é transportada às dimensões `M ≥ i+2` pela persistência integrada em C1B. Não foi necessário calcular a primeira profundidade de falha.

## Comandos executados

Os módulos foram compilados separadamente pelo script versionado, usando o cache 4.32 de dependências em `geometry-of-numbers-sigma-c2-c3-main@67aea3263426cc8f9787f34aa7833a5650dde175`; a saída de C2 foi incluída no caminho de módulo para compilar C3 e a auditoria.

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR=/home/thlinux/worktrees/geometry-of-numbers-sigma-priority-c2c3-20261107/research/native-moving-schur-sigma/.cache/c2c3-priority-20261107
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/final-run/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/final-run/external
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaRHHeightBridge > "$SIGMA_OUTPUT_DIR/bridge-build.log" 2>&1
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaHeight50Integration > "$SIGMA_OUTPUT_DIR/height50-integration-build.log" 2>&1
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeEventualNegativity > "$SIGMA_OUTPUT_DIR/c2-build.log" 2>&1
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaParityNegativeDirection > "$SIGMA_OUTPUT_DIR/c3-build.log" 2>&1
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaPadeAudit > "$SIGMA_OUTPUT_DIR/transitive-audit.log" 2>&1

python3 research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/c2-c3-post-reboot-20261106/check_c2_axioms.py \
  research/native-moving-schur-sigma/.cache/c2c3-priority-20261107/c2-build.log
python3 research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/c3-parity/check_c3_axioms.py \
  research/native-moving-schur-sigma/.cache/c2c3-priority-20261107/c3-build.log
```

Os cinco logs resultantes estão versionados neste diretório. O estado observado antes do build era aproximadamente 60 GiB de memória disponível, acima do gate de 30 GiB do script.

## Checkpoint 4.35

A tentativa 4.35 continua marcada como **incompleta** e já está versionada em `../lean435-validation-incomplete/`. A integridade gzip de `tracked-source-overrides.patch.gz`, `geometry-pins-4.35.patch.gz` e `logs-lean435.tar.gz` foi conferida; o arquivo de logs contém `direct-latest-error.log`, os dois status do scheduler, o log externo e o log raiz. O README preserva os pins, o primeiro módulo e a declaração que falharam nessa tentativa e os comandos para reconstrução. Como a rota 4.32 recompilou C2/C3, não há bloqueio concreto nessa rota e nenhuma migração geral de Geometry/Carry foi iniciada.
