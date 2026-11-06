# C5 — faixa racional de π por Machin

**Estado:** prova local validada; checkpoint preparatório, ainda sem avaliação
dos 129 nós e sem inclusão dos coeficientes C2 nas caixas.

## Resultado

`SigmaC5PiBounds.lean` prova, para todo racional `0 ≤ q < 1`, o limite do erro
da soma alternada finita para `Real.arctan q`. A prova usa
`Real.hasSum_arctan` e `alternating_series_error_bound`.

Com `N=170` em `q=1/5`, `N=55` em `q=1/239` e a identidade de Machin do
Mathlib, `c5_pi_rational_enclosure` demonstra

```text
|Real.pi - (c5PiCenter : ℝ)| ≤ (c5PiError : ℝ)
```

onde `c5PiCenter` e `c5PiError` são racionais exatos definidos no módulo:

```text
c5PiCenter = 16 * c5AtanPartial 170 (1/5) - 4 * c5AtanPartial 55 (1/239)
c5PiError  = 16 * c5AtanRemainder 170 (1/5) + 4 * c5AtanRemainder 55 (1/239)
```

O módulo ainda não prova uma simplificação decimal de `c5PiError`; a
desigualdade acima usa diretamente a expressão racional exata. Este resultado
é infraestrutura para certificar os valores da fonte e não conclui a inclusão
nas caixas.

## Build e auditoria

- Lean `leanprover/lean4:v4.32.0`.
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Build limpo com `warningAsError=true`: `c5-pi-bounds-clean-build.log`,
  `BUILD_EXIT=0`.
- Auditoria de `c5_arctan_partial_enclosure` e `c5_pi_rational_enclosure`:
  `c5-pi-bounds-axiom-audit.log`, somente `propext`, `Classical.choice` e
  `Quot.sound`.
- Fonte, auditoria e oleans: `c5-pi-bounds-source-olean-sha256.txt`.
- Compilação reproduzível: da raiz do checkout C5, execute o comando abaixo
  com os pins descritos acima e com pelo menos 30 GiB disponíveis:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-pi-bounds-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
mkdir -p "$C5_OUTPUT" "$C5_EVIDENCE"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiBounds
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5PiBoundsAudit
```

## Logs históricos

As tentativas `c5-pi-bounds-build-try1.log` até `try6.log` foram preservadas
como trilha de desenvolvimento, incluindo os erros de elaboração já corrigidos.
Uma tentativa de fechar também uma cota decimal direta para `c5PiError` foi
removida da prova porque o `norm_num` não concluiu a comparação racional
expandida; o diagnóstico está em `c5-pi-error-decimal-proof-rejected.log`. A
prova principal da faixa racional exata não depende dessa simplificação.
