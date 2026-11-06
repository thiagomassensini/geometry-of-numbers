# C5 — ponte Gamma por núcleo racional exato

**Status:** build e auditoria Lean locais passaram. A ponte é genérica; não é
uma avaliação dos 129 nós e não prova inclusão de coeficientes nas caixas O3.

## Resultado

Em `SigmaC5GammaRationalCore.lean`, `RatComplex` representa exatamente
`ℚ+iℚ`. `gammaFinite_eq_rationalCore` prova que, para entradas racionais,

```text
gammaFinite N T (a + b i) = T^(a + b i) * ratComplexToComplex (core N T a b).
```

Assim, a soma finita com cancelamento grande é mantida como uma soma racional
exata. `gammaFiniteRationalCoreInterval_contains` prova a inclusão da caixa de
raio zero para esse valor. `gammaFiniteInterval_contains` combina essa caixa
com o avaliador formal de potência `dirichletTermBox2`, sob as hipóteses
explícitas de redução de `log`, de faixa de `exp` e de limite da norma. Para
`N=3072`, `T=620`, `gamma3072Interval_contains` infla a caixa da aproximação
finita pelo erro provado `10^-259` e conclui a inclusão da Gamma original.

Os seis roots auditados são:

- `ratComplexToComplex_mul` e `ratComplexToComplex_inv`;
- `gammaFinite_eq_rationalCore`;
- `gammaFiniteRationalCoreInterval_contains`;
- `gammaFiniteInterval_contains`;
- `gamma3072Interval_contains`.

O checker fail-closed verificou os seis roots através dos dois logs de build,
com 11 relatórios ao todo. Todos dependem apenas de `propext`,
`Classical.choice` e `Quot.sound`. Os builds usam `warningAsError=true`.

## Validação reproduzível

- Toolchain: Lean 4.32.0.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `SigmaGammaEulerIntegral` e `ZetaLean.IntervalCExp` vieram dos caches de
  apoio listados no comando abaixo; o primeiro fornece o erro Gamma `10^-259`,
  o segundo as inclusões racionais de `T^z`.
- Memória observada na execução: cerca de 60 GiB disponíveis; o runner exige
  pelo menos 30 GiB.
- Build da ponte: `c5-gamma-rational-core-try5-build.log`.
- Build da auditoria isolada: `c5-gamma-rational-core-audit-try6-build.log`.
- Resultado fail-closed: `c5-gamma-rational-core-final-axiom-check.log`.
- SHA-256 dos fontes, checker e `.olean`: `c5-gamma-rational-core-source-olean-sha256.txt`.

O checker compara as raízes exigidas, rejeita `sorryAx`, erros Lean e axiomas
fora da lista padrão. As falhas anteriores ficam preservadas nos logs `try1` a
`try4`; o build final bem-sucedido é `try5`.

## O que falta para O4

O teorema não instancia ainda os 129 argumentos `w±`, nem calcula os extremos
racionais de `gammaFiniteRationalCore` e `T^z` nesses pontos. Também não inclui
`riemannZeta w±` em caixas: o primeiro resultado disponível,
`HardyFirstZero.zeta_em4_error`, tem ordem 4 e não fornece precisão suficiente
para O3. Portanto a ponte não avalia a característica C2 completa e não prova
`sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes`. Os sinais de O3 continuam
condicionais; C5 não está concluída.

## Comando usado

Da raiz da worktree C5:

```bash
C5_SOURCE_ROOT="$PWD/research/native-moving-schur-sigma"
C5_EVIDENCE="$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes"
C5_OUTPUT="$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-rational-core-final-clean-20261106"
C5_EULER_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-3072-clean"
C5_INTERVAL_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean"
export SIGMA_REFERENCE_ROOT="/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105"
export CARRY_LEAN_ROOT="/home/thlinux/worktrees/carry-sigma-c2-pinned-045369"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export SIGMA_HEIGHT50_BUILD="$C5_EULER_CACHE:$C5_INTERVAL_CACHE"
export LEAN_BIN="$(elan which lean)"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCore
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCoreAudit
python3 "$C5_SOURCE_ROOT/check_c5_gamma_rational_core_axioms.py" \
  "$C5_EVIDENCE/c5-gamma-rational-core-try5-build.log" \
  "$C5_EVIDENCE/c5-gamma-rational-core-audit-try6-build.log"
```
