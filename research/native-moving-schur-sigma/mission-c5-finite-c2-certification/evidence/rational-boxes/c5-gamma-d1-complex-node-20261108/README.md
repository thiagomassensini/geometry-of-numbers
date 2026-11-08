# C5 — Gamma complexa no primeiro ponto de `d=1/10`

## Resultado

`SigmaC5GammaComplexNodeDOneComplexGammaCertificate.lean` prova que a caixa
racional `c5GammaComplexNodeDOneComplexBox` contém
`Complex.Gamma (1/5 + (3/20) * Complex.I)`. Esse é o primeiro argumento
complexo da malha de deslocamento `d=1/10` na altura de Cauchy `3/10`; a caixa
real em `1/5` já estava integrada.

A prova separa `gammaFinite 1024 240` em 16 blocos de 64 termos do núcleo
racional, certifica os 32 pisos (partes real e imaginária), compõe a caixa de
`240^z` e inclui o erro analítico `gamma_finite_1024_240_error ≤ 10⁻⁹⁹`.

## Build e auditoria

- Lean 4.32.0 com `warningAsError=true`; os cinco módulos listados em
  `clean-build/` terminaram com `BUILD_EXIT=0`.
- Auditoria fail-closed: 14 relatórios, somente `propext`, `Classical.choice` e
  `Quot.sound`; sem `sorryAx`, axiomas próprios ou `native_decide`.
- Maior RSS entre os cinco módulos: aproximadamente 8.4 GiB.
- A reprodução pelo script também passou (`reproduction/verification-20261108/`); os logs preservam a segunda execução completa.
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Caches Lean auxiliares foram usados a partir dos worktrees fixados no script;
  cada referência é verificada antes da reprodução.
- Fontes, checker, script e logs têm hashes em `SHA256SUMS.txt`.

Reproduza com:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-d1-complex-node-20261108/reproduce-clean.sh
```

## Limite deste checkpoint

Isto fecha somente a caixa Gamma neste nó. O ponto complementar
`3/10 + 3i/20` da mesma malha, a composição com zeta e os demais fatores da
fonte C2 original ainda faltam. `sigmaC00495SourceBoxes`,
`sigmaC01SourceBoxes` e os sinais finais continuam sem prova; C5 permanece
incompleta.
