# Retomar primeiro — missão C5

## Retomada mais recente — 2026-11-07 UTC, cobertura zeta adaptativa local

```text
MISSION: C5 — certificar as primeiras janelas negativas da fonte C2 original.
CURRENT PHASE: composição das caixas nodais com a fonte original e inclusão O3.
CURRENT SUBTASK: escolher `nExp`/`p`, exportar retângulos racionais, compor zeta/Gamma/fator de π com a cabeça C2 e sua cauda exata.
LAST VERIFIED THEOREM: `CarrySigmaObstruction.c5RationalZetaAdaptiveNodeConjugateBox_contains_at`.
LAST COMPILED FILE: `SigmaC5RationalNodeInstantiateAudit.lean` (Lean 4.32.0, warnings como erros).
LAST PROOF BRANCH: `codex/c5-node-instantiation-20261107`, baseada na main `296e899e70bee78c54a3278e73e9bd89eaafaa58`; checkpoint ainda local, sem PR.
LAST PUBLISHED COMMIT: PR #208, merge `296e899e70bee78c54a3278e73e9bd89eaafaa58`.
OPEN PR: nenhuma para este checkpoint; código e evidência estão locais.
WHAT IS PROVED: condições adaptativas de log/exp construídas para todos os `1≤m≤100`; caixas de `riemannZeta` nos 129 nós `b=j/100000` para todo `a∈[2/5,3/5]`, mais os nós conjugados. Cauda Euler–Maclaurin preservada e inflação `<10^-250`. Auditoria de 21 raízes, somente axiomas padrão.
WHAT REMAINS: achatamento de extremos numéricos, composição com Gamma, π e fonte C2, e inclusões dos coeficientes em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 está incompleta.
EVIDENCE: `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`; logs limpos em `evidence/rational-boxes/c5-node-instantiation-clean-20261107/`.
EXACT NEXT MATHEMATICAL OBLIGATION: escolher precisão suficiente para os sinais O3, produzir os extremos racionais de cada nó e compor a fonte C2 original mantendo a cabeça e a cauda exata.
DO NOT REPEAT: C1B/C2/C3/C4; transporte polinomial C4; domínio/cota analítica; faixa de π e fator exponencial; limites dos pesos 0–14; erro Gamma `10^-259`; EM ordem 300; ponte Gamma racional genérica; caixa racional genérica e cobertura adaptativa dos 129 nós já compiladas.
```

A reprodução experimental mais recente e o ajuste de compatibilidade aplicado
somente numa cópia temporária estão documentados em
`evidence/interval-certificate/reproduction-2026-11-06.md`. Use esses logs como
checagem condicional, não como inclusão formal dos coeficientes.

Logs e hashes do subpasso Gamma: `evidence/rational-boxes/c5-gamma-rational-core-validation.md`.
Ele ainda não fornece extremos numéricos para qualquer nó nem prova a inclusão nas caixas O3.

O avaliador genérico foi integrado pela PR #207 como checkpoint explicitamente
incompleto; aquela etapa ainda não instanciava os nós. A cobertura adaptativa
formal foi construída depois e está registrada no checkpoint local acima.
Hipóteses, logs, pins e hashes do avaliador genérico original permanecem em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

## Estado mais recente — 2026-11-06

A PR #195 integrou `SigmaC5PiInterval.lean` e `SigmaC5PiExp.lean`, com commit
de prova `321ae94` e merge `0032b10295bfeaadb29d0387f9b99dde9b160ac3`. O build
limpo e a auditoria Lean 4.32 passaram; os detalhes e comandos estão em
`evidence/rational-boxes/c5-pi-completion-factor-validation.md`. O fator
exponencial original dependente de `log π` está incluído em uma caixa, sob as
hipóteses declaradas sobre a caixa de `s`. A avaliação da Gamma, da cauda C2 e
dos 129 nós permanece aberta.

Na retomada da avaliação dos nós, preserve a rota exata via
`nativeScalar_eq_riemannZeta` e a ponte da cabeça C2 mais cauda exata. O
primeiro lema numérico ausente é um Euler–Maclaurin de ordem alta em Lean:
`HardyFirstZero.zeta_em4_error` só dá ordem 4 e, com `N=100`, limita o erro a
cerca de `1.351·10⁻⁸` no contorno. O relatório do diagnóstico e a próxima
sequência estão em
`evidence/rational-boxes/c5-original-source-zeta-route-audit.md`.

A PR #191 integrou a cota `10^100` no merge
`88a52ba3a6bda7a78b8317d892b6f7bc640c863f`; a PR #192 integrou a cota mais
forte `10^13`, merge `654dbb0bd7bb7d400cf0c4cab61bea1873995db4`. O contorno de
Cauchy usa raio `38/100`, e a análise racional exata com esse majorante dá
erro `<10^-501`. Detalhes, hashes e logs estão em
`evidence/rational-boxes/analytic-bounds-10pow13-validation.md`.

`SigmaC5PiBounds.lean` foi integrada pela PR #193, commit de prova `45bc923`,
merge `2567ab0204c46c4ce04fca601c99e47e810e18b9`. Build limpo e auditoria
Lean 4.32 passaram para a faixa racional exata de π derivada da série de
`arctan` e da identidade de Machin. A trilha reproduzível está em
`evidence/rational-boxes/c5-pi-bounds-validation.md`.

`SigmaC5PiInterval.lean` e `SigmaC5PiExp.lean` já estão integradas pela PR
#195; consulte `evidence/rational-boxes/c5-pi-completion-factor-validation.md`
para reproduzir o build e a auditoria.

O4/C5 continua incompleta: certificar a avaliação da fonte original nos 129
nós e provar a inclusão dos coeficientes nas caixas O3. Não refazer C1B, C2,
C3, C4, O3, o domínio analítico, a ponte Gamma, os limites de pesos ou a faixa
racional de π já provada.

### Retomar o build da cota analítica

Da raiz da worktree C5, com os checkouts fixados disponíveis:

Se `C5_SOURCE_ANALYTIC_OUTPUT` ainda não existir, compile primeiro
`SigmaC5SourceAnalytic` com o comando de domínio registrado mais abaixo neste
arquivo.

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_SOURCE_ANALYTIC_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-source-analytic-clean-retry1-20261106
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-analytic-bounds-10pow13-repro-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_SOURCE_ANALYTIC_OUTPUT:$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5AnalyticBounds \
    > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log"
  exit "$C5_STATUS"
fi
python3 "$C5_SOURCE_ROOT/check_c5_analytic_bounds_axioms.py" \
  "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log" \
  > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-axiom-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaC5AnalyticBounds.lean" \
  "$C5_SOURCE_ROOT/check_c5_analytic_bounds_axioms.py" \
  "$C5_OUTPUT/SigmaC5AnalyticBounds.olean" \
  > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-source-olean-sha256.txt"
```

O comando `compile_sigma_pade.sh` verifica a revisão limpa do Carry
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, usa Lean 4.32 e exige pelo menos
30 GiB de memória disponível durante a compilação.

**MISSÃO:** certificar as primeiras janelas negativas da fonte C2 original,
para `d=99/2000` e `d=1/10`. A validação segue incompleta até que as caixas
racionais contenham os coeficientes originais.

## Snapshot histórico — início do trabalho C5, antes das PRs #189–#192

- A `origin/main` consultada está em `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- A prova do domínio analítico foi integrada pela PR #189: commit de prova
  `e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge
  `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- Branch de estado pós-merge: `codex/c5-state-after-pr189-20261106`.
- A prova local `SigmaC5SourceAnalytic.lean` fecha o domínio analítico no disco
  aberto de raio `2/5` para `|d|≤1/10`; Lean 4.32 compilou o arquivo com
  `warningAsError=true`, e os quatro `#print axioms` passaram com axiomas padrão.
- Registro daquele checkpoint: a ponte estabelecia apenas o domínio e ainda
  não havia cota do módulo. A cota foi provada depois; as inclusões nas caixas
  continuam pendentes.

- C1–C4 e O3 estão integradas. O3 prova os sinais finais apenas sob as
  hipóteses explícitas de inclusão nas caixas.
- Em Lean 4.32 estão provados os limites dos pesos escalados de graus `0..14`:
  grau zero `=1`, grau um `<10^11`, e todo `2≤n≤14` tem soma `<10^145`.
- `c5InterpolationWeightSum_lt_ten_145` é a última declaração validada.
- A PR #187 integrou essa prova: commit `6424f4334edd5c776997116403043635fa0c8f83`, merge na `main` `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Build limpo com `warningAsError=true`: `evidence/rational-boxes/c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`.
- Auditoria transitiva de 23 teoremas: somente `propext`, `Classical.choice` e
  `Quot.sound`. O checker fail-closed passou; logs e hashes estão ao lado.
- O estado atual foi retomado em `codex/c5-state-after-pr187-20261106`, sobre
  `origin/main` no merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Pins: Lean `leanprover/lean4:v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- C1B/C2/C3/C4 e provas C5 anteriores não devem ser refeitas. A PR #185
  integrou o limite de grau um no merge
  `c840ba35711ac8f938fa24c191f2af60f505480d`; #184 integrou o checkpoint
  explicitamente incompleto em `5528ddc8093a22682c87f3f9c6575e30e90a7011`.

## O que continua aberto — snapshot anterior ao avanço da cota

Naquele snapshot faltava provar uma cota numérica uniforme, além de certificar
a avaliação racional da fonte nos 129 nós e provar a inclusão dos coeficientes
originais nas caixas O3. A cota numérica já foi provada, conforme o estado mais
recente acima; as avaliações e inclusões continuam pendentes. A saída
`mpmath.iv` continua sendo evidência computacional, não prova de inclusão.

Preservar a fonte C2 original, a cabeça e a cauda exponencial exata. A ponte
Euler-Gamma de erro `10⁻²⁵⁹` está provada. A cota dos pesos `<10^145` é uniforme
e suficiente para a margem estimada; não é necessário recuperar o limite
exploratório `10^124`.

## Próximo passo histórico — cota já provada

O passo seguinte naquele checkpoint era provar a cota do módulo. Ela agora está
provada localmente na bola aberta de raio `39/100`; o passo corrente é
certificar as avaliações nos 129 nós e a inclusão nas caixas. Consulte
`evidence/rational-boxes/analytic-bounds-validation.md`.

## Retomada histórica do subpasso de domínio

- Último teorema validado: `CarrySigmaObstruction.displacedProductC_analyticOnNhd_ball`.
- Arquivo compilado: `research/native-moving-schur-sigma/SigmaC5SourceAnalytic.lean`.
- Prova integrada à `main` pela PR #189.
- Branch de estado: `codex/c5-state-after-pr189-20261106`, baseada no merge
  `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- PR aberta: nenhuma. A próxima PR deve atacar a cota explícita do módulo.
- Não refazer C1B, C2, C3, C4, a recorrência de transporte, O3, a ponte Gamma
  ou os limites dos pesos 0–14.
- Obrigação matemática exata: derivar uma cota explícita do módulo usando a
  expressão original C2 completada, com as remoções de singularidade em
  `s=0` e `s=1` justificadas. O domínio analítico sozinho não basta para
  limitar o resto da interpolação.

Comando de inventário para começar a obrigação seguinte:

```bash
rg -n 'nativeXiCompletionFactor|completedNativeOperatorCharacteristic|nativeScalarDomain|finiteHead_add_exactTail' \\
  /home/thlinux/worktrees/carry-sigma-c2-pinned-045369/CarrySelfAdjointOperator \\
  research/native-moving-schur-sigma
```

Build e auditoria do módulo de domínio:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-source-analytic-repro-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5SourceAnalytic \\
    > "$C5_EVIDENCE/c5-source-analytic-repro-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\\n' >> "$C5_EVIDENCE/c5-source-analytic-repro-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-source-analytic-repro-build.log"
  exit "$C5_STATUS"
fi
python3 "$C5_SOURCE_ROOT/check_c5_source_analytic_axioms.py" \\
  "$C5_EVIDENCE/c5-source-analytic-repro-build.log" \\
  > "$C5_EVIDENCE/c5-source-analytic-repro-axiom-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaC5SourceAnalytic.lean" \\
  "$C5_OUTPUT/SigmaC5SourceAnalytic.olean" \\
  > "$C5_EVIDENCE/c5-source-analytic-repro-source-olean-sha256.txt"
```

## Comando de build e auditoria

Da raiz da worktree C5:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree2-14-final-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
    > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
  exit "$C5_STATUS"
fi
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaRationalInterpolation.lean" \
  "$C5_OUTPUT/SigmaRationalInterpolation.olean" \
  "$C5_OUTPUT/interpolation-audit.olean" \
  > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt"
```

The checker report and hashes already committed with the validation record are
`interpolation-audit-degree2-14-final-clean-check.log` and
`c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt`.
