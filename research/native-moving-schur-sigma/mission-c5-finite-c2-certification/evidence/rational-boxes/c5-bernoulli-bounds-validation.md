# C5 — limite do núcleo de Bernoulli (checkpoint parcial)

**Status:** dois lemas auxiliares provados em Lean 4.32 e auditados; ainda não
foi demonstrada a identidade geral de Euler–Maclaurin nem a inclusão dos
coeficientes da fonte C2 nas caixas O3.

## Resultados formais

`SigmaC5ZetaBernoulliBounds.lean` prova:

- `SigmaC5Zeta.natPowSeries_le_two`: para `k ≥ 2`,
  `∑' n, 1/(n+1)^k ≤ 2`, pela comparação integral da série p.
- `SigmaC5Zeta.bernoulliFun_abs_le_four_factorial_div_six_pow`: para
  `x ∈ [0,1]` e `k ≥ 2`,
  `|bernoulliFun k x| ≤ 4·k!/6^k`, a partir da série de Fourier formalizada
  na Mathlib, do limite da série p e de `π > 3`.

A cota é para o polinômio de Bernoulli no intervalo unitário. A extensão
periódica, a identidade de Euler–Maclaurin de ordem arbitrária, sua aplicação
à zeta/Hurwitz nos pontos C5 e a conversão a intervalos racionais ainda
precisam ser formalizadas. Portanto, este lema sozinho não avalia nenhum dos
129 nós e não fecha O4.

## Validação reproduzível

- Lean `leanprover/lean4:v4.32.0` (binário `leanprover--lean4---v4.32.0`).
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Referência geometry/C2: checkout local `geometry-of-numbers-sigma-c2-c3-main`;
  o build usa a biblioteca Mathlib da closure certificada Lean 4.32.
- Comando: `bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5ZetaBernoulliBounds`, com `SIGMA_OUTPUT_DIR` apontando para um diretório de saída novo e `SIGMA_HEIGHT50_BUILD` para o `.lake/build/lib/lean` pinado.
- Resultado: `BUILD_EXIT=0`, com `warningAsError=true`.
- Auditoria fail-closed: exatamente as duas declarações acima; ambas dependem
  somente de `propext`, `Classical.choice` e `Quot.sound`.
- Build, checker e hashes desta reprodução estão em
  `c5-bernoulli-bounds-postmain-build.log`,
  `c5-bernoulli-bounds-postmain-axiom-check.log` e
  `c5-bernoulli-bounds-postmain-source-olean-sha256.txt`.
- O primeiro build exploratório com falha foi preservado em
  `c5-bernoulli-bounds-first-build.log`; a reprodução anterior aprovada está
  em `c5-bernoulli-bounds-build.log`.

## Próxima obrigação

Provar em Lean o resto Euler–Maclaurin de ordem alta para
`riemannZeta`/Hurwitz, usando o limite de Bernoulli para limitar o resto; em
seguida, obter caixas racionais nos argumentos dos 129 nós sem substituir a
cabeça C2, a cauda geométrica exata ou a completação original.
