# C5 — `log π` e exponencial da completação

**Estado:** integrada pela PR #195 (commit de prova `321ae94`, merge
`0032b10295bfeaadb29d0387f9b99dde9b160ac3`). O4/C5 continua incompleta: não há
avaliações certificadas nos 129 nós nem inclusão dos coeficientes C2 nas caixas
O3.

## Resultado formal

`SigmaC5PiInterval.lean` usa a faixa exata de π integrada pela PR #193 e prova
`c5_pi_error_lt_quarter`. A faixa racional de `π/4` fica dentro do domínio da
série de log intervalar já certificada em `ZetaLean.IntervalExp`. Somando
`2 log 2`, `c5_pi_log_interval_contains` mostra que `c5PiLogInterval n`
contém o `Real.log Real.pi` original, para todo `n`.

`SigmaC5PiExp.lean` inclui esse intervalo na caixa complexa, transporta-o pelo
fator `-s/2` e aplica o teorema existente `ComplexInterval.contains_expCr`.
Assim, `c5_completion_exp_interval_contains` certifica a caixa para

```text
Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
```

sempre que o chamador fornece a caixa do parâmetro `s` e o limite racional de
norma exigido pelo avaliador `expCr`. Esse é exatamente o fator exponencial
arquimediano da definição original `completedNativeOperatorCharacteristic`.
Esta etapa não avalia ainda o fator Gamma, a cauda Hurwitz C2 ou o valor total
da característica em nenhum nó.

## Build e auditoria

- Lean `leanprover/lean4:v4.32.0`.
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `SigmaC5PiInterval.lean` e sua auditoria: build limpo e auditoria em
  `c5-pi-interval-build-try4.log` e `c5-pi-interval-audit-try4.log`.
- `SigmaC5PiExp.lean` e sua auditoria: build limpo e auditoria em
  `c5-pi-exp-build-try2.log` e `c5-pi-exp-audit-try2.log`.
- As cinco raízes auditadas mostram somente `propext`, `Classical.choice` e
  `Quot.sound`.
- Fontes, auditores e oleans: `c5-pi-completion-factor-source-olean-sha256.txt`.
- As tentativas iniciais que encontraram erros de tipo ou warnings e foram
  corrigidas permanecem nos logs `c5-pi-interval-build-try1.log` até `try3.log`
  e `c5-pi-exp-build-try1.log`.

Para reproduzir, primeiro compile `SigmaC5PiBounds` conforme
`c5-pi-bounds-validation.md`; depois use a saída desse módulo e os módulos
intervalares pinados na variável `SIGMA_HEIGHT50_BUILD`:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_PI_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-pi-bounds-clean-20261106
C5_INTERVAL_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-pi-interval-clean-20261106
C5_EXP_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-pi-exp-clean-20261106
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_PI_OUTPUT:$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
export SIGMA_OUTPUT_DIR="$C5_INTERVAL_OUTPUT"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiInterval
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiIntervalAudit
export SIGMA_HEIGHT50_BUILD="$C5_INTERVAL_OUTPUT:$C5_PI_OUTPUT:$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
export SIGMA_OUTPUT_DIR="$C5_EXP_OUTPUT"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiExp
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiExpAudit
```
