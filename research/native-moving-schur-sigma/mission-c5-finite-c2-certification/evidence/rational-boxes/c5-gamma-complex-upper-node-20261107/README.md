# C5 — segundo nó complexo de Gamma

## Resultado

O módulo `SigmaC5GammaComplexNodeUpperGammaCertificate.lean` prova que a caixa
racional `c5GammaComplexNodeUpperBox` contém

```text
Complex.Gamma (1099/4000 + (3/20) * Complex.I)
```

Este é o argumento complexo complementar ao primeiro nó para `d=99/2000`, na
altura de Cauchy `3/10`. O núcleo racional usa 16 blocos de 64 termos, com os
pisos reais e imaginários certificados individualmente. A caixa composta
inclui `240^z`, o núcleo `gammaFiniteRationalCore 1024 240 (1099/4000) (3/20)`
e o erro analítico `gamma_finite_1024_240_error`, inflado por `10⁻⁹⁹`.

## Build e auditoria

- Lean 4.32.0 com `warningAsError=true`.
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Os cinco módulos em `clean-build-r1/` terminaram em `BUILD_EXIT=0`.
- Os 14 relatórios de axiomas (11 declarações novas e três auxiliares
  recompiladas) usam somente `propext`, `Classical.choice` e `Quot.sound`;
  sem `sorryAx`, axiomas próprios ou `native_decide`.
- Pico de RSS: 11.5 GiB, abaixo do limite de build de 30 GiB.
- A tentativa inicial falha por ter selecionado um `.olean` antigo, anterior à
  exportação de `c5GammaSecondRealPoint_logQ_absBound`, e por dois numeradores
  copiados incorretamente. Está preservada em `attempts/`.

Reproduza pelo comando:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-complex-upper-node-20261107/reproduce-clean.sh
```

Os pinos, fontes Lean, checker e logs aprovados têm hashes em `SHA256SUMS.txt`.

## Limite deste checkpoint

Ele prova um segundo ponto complexo, sem fechar as caixas de zeta na fronteira
de Cauchy nem as inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
C5 e os sinais finais permanecem incompletos.
