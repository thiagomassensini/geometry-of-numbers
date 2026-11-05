# Estado da missão — negatividade transversal all-order

**Atualizado:** 2026-11-05

**Objetivo ativo:** publicar e integrar C1; depois provar C1B, C2 e C3 em checkpoints separados. Investigar C4 somente depois. Não demonstrar RH nem positividade canônica central.

## Checkout e base

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Worktree ativa: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`.
- Branch atual: `agent/sigma-c1-certified-20261105`.
- HEAD local atual: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa` (base antes do commit C1).
- `origin/main`: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- C0 foi integrado pela PR #153; merge commit da `main`: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- PR #153: https://github.com/thiagomassensini/geometry-of-numbers/pull/153 — `MERGED` em 2026-11-05. A branch antiga de C0 foi preservada.
- O checkpoint C1 está validado localmente, mas ainda não foi commitado, publicado ou aberto em PR.

## Dependências e ambiente

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Geometry base e fontes usadas pelo build completo: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Carry fonte pin: `carry-self-adjoint-operator@045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; o checkout de build em `/home/thlinux/carry-self-adjoint-operator` está em `8f15ec76e5a95eb0c61da3a114729363a1d6a477` e contém trabalho local não relacionado, preservado sem alterações.
- Pins exigidos pelo manifesto Carry: CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`, NativeCarrySpectralWeyl `298d83c9351e308a5213b9f5ac32e44087f98a9f`, NativeCarryC3Crosswalk `150cfc7fb08da96bf8117f15869cc2b819d593c2`, FiniteNativeCarryOperator `00e9d6beb17226545abf5ddf90bbfede6c7146b0`, e Geometry `d7cc54f5c485320f1fada33118e9e6101488819a` no manifesto Carry. As interfaces Geometry necessárias a C1 são fornecidas e compiladas da base desta worktree, os dois pins estão registrados separadamente.
- O certificado de primeiro zero foi copiado como fonte de `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`; avisos de licença e patch de compatibilidade Lean 4.32 foram preservados.
- `check_c1_pins.py` comparou 1.278 módulos-fonte não-Mathlib alcançáveis com os respectivos pins; resultado em `evidence/c1-source-pin-audit.txt`.
- Memória disponível durante as compilações: aproximadamente 49–54 GB, acima do limite de 30 GiB.

## Checkpoints e teoremas

- **C0 — concluído e integrado:** inventário e estado persistido, PR #153, merge commit `2a3e899…`.
- **C1 — concluído localmente; publicação pendente:**
  - `CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift`.
  - Reutiliza `HardyFirstZero.first_zero_on_line`, `operatorHeightParameter`, `sigmaLineZero`, `completedNativeCharacteristicContinuation_zero_iff_zeta`, `completedNativeCharacteristicContinuation_eq_native` no strip e `exists_sigmaMatrix_negative_direction_of_zero`.
  - Conclusão sobre a `sigmaMatrix` original para todo `0 < |d| < 1/4`; o teorema não afirma persistência para toda dimensão maior.
  - Axiomas impressos do corolário final e do certificado: somente `propext`, `Classical.choice`, `Quot.sound`. Auditoria automática: 106 relatórios aceitos; nenhum `sorryAx`, `sorry`, `admit`, `native_decide` ou axioma customizado nos fontes C1.
  - Build completo da raiz passou. Evidências: `evidence/c1-root-build.log`, `evidence/c1-focused-build.log`, `evidence/c1-source-pin-audit.txt` e `evidence/c1-source-sha256.txt`.
- **C1B — aberto:** prolongar por zeros a direção e provar não-positividade semidefinida em todas as dimensões maiores.
- **C2 — aberto:** provar negatividade eventual dos menores originais em `d=1/5` via decomposição Padé e isolamento certificado.
- **C3 — aberto:** transportar a negatividade eventual às torres par e ímpar.
- **C4 — não iniciado:** fonte deslocada, fator 2 e Bézout; depende da conclusão dos anteriores.

## Arquivos do checkpoint C1

- Novos módulos: `SigmaNativeZeroBridge.lean`, `SigmaCertifiedNegativeDirection.lean`.
- Fontes copiadas por proveniência: `SigmaZeroObstruction.lean`, `MomentComplexification.lean`, `MomentLogConvexity.lean`, `SigmaNativeContinuation.lean` e o fechamento Lean do certificado de primeiro zero em `height50-certified/`.
- Scripts: `compile_c1.sh`, `check_c1_axioms.py`, `check_c1_pins.py`.
- Documentação e evidências: arquivos desta pasta `mission-sigma-sign-20261105/`.
- Nenhum `.olean` foi copiado ou adicionado ao Git.

## Compilação e auditoria

- Build raiz completo, iniciado em cache ausente no checkout novo: `elan run leanprover/lean4:v4.32.0 lake build --wfail`; concluiu 8.857/8.857 jobs com sucesso. Uma execução subsequente capturada após o cache aquecido também passou (`lake build --wfail`, 8.850 jobs).
- Compilação focada: `SIGMA_OUTPUT_DIR=/tmp/sigma-c1-certified-20261105 research/native-moving-schur-sigma/compile_c1.sh`.
- A compilação focada recompila para saída temporária os fontes locais relevantes, os fontes portados e o fechamento mínimo do certificado. Os imports externos Lean/Mathlib/Carry são lidos de caches `.lake` com toolchain e versões explícitas; portanto este comando é um build focado com proveniência auditada, não uma recompilação limpa de todas as dependências externas.
- Último erro de compilação: nenhum na execução final. Erros anteriores de caminho de fonte e escopos Lean foram corrigidos antes do log final.

## Próxima ação concreta

Executar `git diff --check`, revisar os arquivos adicionados, commitá-los apenas nesta worktree, publicar `agent/sigma-c1-certified-20261105`, abrir PR para `main` e conferir status/CI. Fazer merge somente se os gates da missão estiverem satisfeitos; depois criar a próxima base C1B a partir da `main` integrada. As demais worktrees e alterações locais previamente inventariadas permanecem preservadas.
