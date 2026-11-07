# Conferência do estado C2/C3 na main atual

**Revisão consultada:** `origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8` (merge da PR #288). Esta anotação registra uma recompilação focada e auditoria sobre a revisão atual; nenhuma prova C2/C3 foi alterada.

## Integrações publicadas

- C1B: PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2: PR #157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
- C3: PR #159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
- Checkpoint durável da tentativa Lean 4.35 incompleta: PR #221, merge `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`.
- Reconciliação anterior de estado C2/C3: PR #284, merge `11f5ea452f6d41f4a1545ecf614cea39730f58a0`.

Não há prova nem publicação C1B/C2/C3 pendente na revisão consultada.

## C2

O alvo permanece, nos momentos originais:

```lean
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0
```

A integração Lean 4.32 publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, incluindo `SigmaHeight50Integration.lean`, foi a primeira referência. A prova publicada na PR #157 compõe o isolamento certificado `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, a decomposição completa do resto `completedNative_sigmaRemainder_square_decomposition_of_isolation`, o limite normalizado `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`. Ela preserva `completedSigmaLogJet`, `sigmaPadeD` e o resto exponencial e não adiciona hipótese de sinal.

## C3

`exists_even_sigma_negative_directions_from_pade` escolhe as janelas `p = 2i`; `exists_odd_sigma_negative_directions_from_pade` escolhe `p = 2i + 1`. Em cada setor, a direção negativa da janela é transportada pela persistência C1B a todas as dimensões `M ≥ i₀ + 2`.

## Evidência Lean 4.32 aplicável à revisão atual

Os cinco módulos Lean foram recompilados diretamente de `origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8`, com Lean 4.32 e `-DwarningAsError=true`. Seus hashes estão em `source-pins-and-hashes.txt`. Os cinco logs de build estão em `build-logs/`; os verificadores C2/C3 aceitaram somente `propext`, `Classical.choice` e `Quot.sound`, e `SigmaPadeAudit.lean` refez a auditoria de 133 raízes públicas e 70.861 dependências. A execução reaproveitou a árvore Mathlib/Geometry fixada em `geometry-of-numbers-sigma-c2-c3-main@67aea3263426cc8f9787f34aa7833a5650dde175`, o pin Carry e os outputs do certificado altura 50 indicados no arquivo de pins. A comparação entre essa árvore e a main atual não encontrou módulos Lean preexistentes modificados sob `research/native-moving-schur-sigma`; o delta traz módulos C5 novos e registros, sem alteração da closure C2/C3 usada aqui. Os logs e verificadores da execução pós-reinício anterior permanecem em `../c2-c3-current-main-20261107/`. `CarrySigmaObstruction.sigmaLineZero` continua com uma única definição, em `SigmaCertifiedNegativeDirection.lean`.

Comandos executados (o script manteve o gate de disponibilidade de 30 GiB; a execução foi sequencial e `MemAvailable` antes da rodada era aproximadamente 58 GiB):

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-live-main-20261107
TASK="$GEOM/research/native-moving-schur-sigma"
EVIDENCE="$TASK/mission-sigma-sign-20261105/evidence/c2-c3-live-main-20261107"
OUTPUT="$TASK/.cache/c2-c3-live-main-20261107"
REF=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main
CARRY=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
HEIGHT50="$REF/research/native-moving-schur-sigma/.cache/c3-validation/final-run/integration:$REF/research/native-moving-schur-sigma/.cache/c3-validation/final-run/external"
for module in SigmaRHHeightBridge SigmaHeight50Integration SigmaPadeEventualNegativity SigmaParityNegativeDirection SigmaPadeAudit; do
  env SIGMA_REFERENCE_ROOT="$REF" CARRY_LEAN_ROOT="$CARRY" SIGMA_OUTPUT_DIR="$OUTPUT" SIGMA_HEIGHT50_BUILD="$HEIGHT50" LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean bash "$TASK/compile_sigma_pade.sh" "$module" > "$EVIDENCE/build-logs/$module.log" 2>&1
done
python3 "$TASK/mission-sigma-sign-20261105/evidence/c2-c3-post-reboot-20261106/check_c2_axioms.py" "$EVIDENCE/build-logs/SigmaPadeEventualNegativity.log"
python3 "$TASK/mission-sigma-sign-20261105/evidence/c3-parity/check_c3_axioms.py" "$EVIDENCE/build-logs/SigmaParityNegativeDirection.log"
```

## Checkpoint 4.35

O checkpoint publicado em `../lean435-validation-incomplete/` está rotulado como incompleto. Os patches de Geometry/Carry, pins, manifest de módulos, scheduler, logs, falha mais recente e comandos de retomada continuam versionados. `gzip -t` validou os dois patches comprimidos e o arquivo de logs; o tar contém `direct-latest-error.log`, os dois logs de estado do scheduler e `root-build.log`. O README preserva os comandos para reconstruir a tentativa. A tentativa não foi retomada: C2 não apresenta impedimento na rota 4.32, logo não há fundamento para uma migração geral de Geometry/Carry. Não foi calculada a primeira profundidade de falha; ela não é necessária para a negatividade eventual.
