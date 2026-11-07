# C5 — primeira caixa para a função Gamma completa

## Resultado deste checkpoint

`SigmaC5GammaFirstNodeCertificate.lean` prova que a caixa racional
`c5GammaCoreFirstNodeBox` contém `Complex.Gamma (1/5 : ℂ)`. A construção
compõe, na ordem:

1. a potência complexa real-base `240^(1/5)` por `dirichletTermBox2`;
2. a caixa do núcleo racional `gammaFiniteRationalCore 1024 240 (1/5) 0`,
   já certificada em 16 blocos de 64 termos;
3. o limite formal `gamma_finite_1024_240_error`;
4. a inflação racional de raio `10⁻⁹⁹`.

O novo teorema de composição é
`CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains`. A cota do argumento
da potência é derivada em Lean das séries racionais de `logSum`, `logRem` e
`logQ`; não é uma estimativa decimal externa.

## Validação

- Toolchain: Lean 4.32.0 (`warningAsError=true`).
- Build final: `build-attempt11.log`, código de saída 0.
- Auditoria `#print axioms` das duas raízes públicas: somente
  `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx`, axioma próprio ou
  `native_decide`.
- SHA-256 do fonte auditado:
  `1147934df954be735242d97dca54346b19d45c6a1835a991b384557ece957ad8`.
- SHA-256 do log final:
  `c66accf0f78372100f71bf89a2488ccf3ebe8df7a2e47a0b2e8dd69be7ca7808`.
- As dez tentativas anteriores foram preservadas neste diretório; a falha de
  expansão ingênua da série de log está em
  `build-attempt5-high-precision-norm-failure.log`.

Comando reproduzível no worktree C5:

```bash
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106 \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-gamma-first-node-20261107" \
SIGMA_HEIGHT50_BUILD="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106:$PWD/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot" \
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaFirstNodeCertificate
```

## Limites explícitos

Este resultado cobre um ponto real: `Γ(1/5)`. Não prova as outras 128
avaliações complexas de Gamma, os outros pontos reais necessários à distância
`99/2000`, nenhum valor de zeta, nem as inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. Os certificados condicionais O3
e os sinais esperados continuam condicionais. C5 não está concluída.

## Próxima obrigação

Estender a certificação do núcleo racional ao próximo ponto real da fonte,
`901/4000 = (1/2 - 99/2000)/2`, e depois à malha complexa necessária para
compor Gamma com as caixas de zeta e o fator nativo da fonte original. A prova
de inclusão dos coeficientes C2 e os teoremas de sinais finais continuam como
critério de conclusão.
