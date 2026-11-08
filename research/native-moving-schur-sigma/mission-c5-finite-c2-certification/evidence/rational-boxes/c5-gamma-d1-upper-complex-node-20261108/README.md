# C5 — Gamma complexa no ponto complementar de `d=1/10`

## Resultado

`SigmaC5GammaComplexNodeDOneUpperComplexGammaCertificate.lean` prova que a
caixa racional `c5GammaComplexNodeDOneUpperComplexBox` contém
`Complex.Gamma (3/10 + (3/20) * Complex.I)`, o ponto complementar ao
`1/5 + 3i/20` da mesma malha, na altura de Cauchy `3/10`.

O núcleo racional de `gammaFinite 1024 240` usa 16 blocos de 64 parcelas, com
os 32 pisos certificados. A composição inclui `240^z` e o erro analítico
`gamma_finite_1024_240_error ≤ 10⁻⁹⁹`.

Para este ponto, a cota anterior `|logQ|≤18` não bastava para o avaliador de
potência de raio `8`. O módulo `SigmaC5GammaDOneUpperLogBounds.lean` prova
`|logQ 384 8 240|≤10`: os extremos de `log2I 384` são limitados por `1`, e o
resto `log1` por `2`. Daí o limite da norma da potência fica abaixo de `8`.
Essa cota é derivada dentro de Lean e não introduz hipótese adicional.

## Build e auditoria

- Seis módulos passaram em Lean 4.32.0 com `warningAsError=true`; todos têm
  `BUILD_EXIT=0` em `clean-build/`.
- A auditoria fail-closed aceitou 16 relatórios, somente `propext`,
  `Classical.choice` e `Quot.sound`; sem `sorryAx`, axiomas próprios ou
  `native_decide`.
- Pico de RSS: aproximadamente 8.4 GiB.
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Os pins dos caches auxiliares e os comandos estão fixados em
  `reproduce-clean.sh`.
- A primeira composição deixou o fator `18` no objetivo após refinar a cota;
  o Lean rejeitou a incompatibilidade. O log foi preservado em
  `attempts/first-gamma-composition-failure.log`; a desigualdade foi corrigida
  para usar o fator `10` provado.
- Código, checker, pins, hashes e logs: `SHA256SUMS.txt`.

Reproduza em cache isolado com:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108/reproduce-clean.sh
```

## Limite deste checkpoint

Ele fecha a caixa Gamma neste ponto, junto com o nó `1/5+3i/20` já integrado.
Não fecha a avaliação nodal de zeta, os demais nós de interpolação, a
composição com a fonte C2 original, as inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` nem os sinais finais. C5 segue
incompleta.
