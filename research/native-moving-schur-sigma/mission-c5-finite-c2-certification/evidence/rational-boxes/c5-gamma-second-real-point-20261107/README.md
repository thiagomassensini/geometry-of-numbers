# C5 — segunda caixa Gamma em ponto real: `901/4000`

## Resultado

A prova `CarrySigmaObstruction.c5GammaSecondRealPointBox_contains` certifica
uma caixa que contém `Complex.Gamma (901/4000 : ℂ)`. Ela compõe:

1. os pisos racionais dos 16 blocos de 64 termos de
   `gammaFiniteRationalCore 1024 240 (901/4000) 0`;
2. a caixa racional do núcleo escalado por `2^1024`;
3. a potência `240^(901/4000)`, avaliada por `dirichletTermBox2` com a cota de
   norma `≤ 8`;
4. o erro formal `gamma_finite_1024_240_error` e a inflação de raio `10⁻⁹⁹`.

A largura do núcleo racional é exatamente `16/2^1024`, pois cada um dos 16
blocos tem um erro de piso menor que 1. O limite de log usado na potência é
provado por séries racionais; para este ponto, usa-se `kE = 3`.

## Validação local

- Toolchain: Lean 4.32.0; `compile_sigma_pade.sh` define
  `warningAsError=true`.
- Os quatro módulos foram compilados em ordem: probe, certificado dos 16
  pisos, combinação da caixa racional e composição da caixa Gamma. Todos os
  logs terminam com código de saída 0.
- `#print axioms` nas raízes públicas do certificado, da combinação e da caixa
  Gamma mostra somente `propext`, `Classical.choice`, `Quot.sound`; sem
  `sorryAx`, axiomas próprios ou `native_decide`.
- Pins: Geometry de referência
  `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- MemAvailable observado antes da compilação: `63391316 kB` (~60,5 GiB); o
  build manteve o limite de 30 GiB do script.
- A PR #287 integrou o checkpoint: commit de prova
  `7f3d880e73f5383718cf2442b915e8cd866139cf`, merge na `main`
  `742eb6fd03311adbb80507867c47e726fd648a21`.
- O GitHub não reportou checks hospedados para a PR #287; a validação formal registrada é a compilação local acima.

## Fontes e logs

Fontes no diretório `research/native-moving-schur-sigma/`:

- `SigmaC5GammaSecondRealPointProbe.lean`
- `SigmaC5GammaSecondRealPointCertificate.lean`
- `SigmaC5GammaSecondRealPointCombine.lean`
- `SigmaC5GammaSecondRealPointGammaCertificate.lean`

Sondas e logs preservados aqui:

- `probe-attempt1.log`
- `certificate-attempt1.log`
- `combine-attempt1.log`
- `gamma-attempt1.log`

Não houve falhas de compilação Lean nesta sequência; os arquivos são as
execuções efetivamente usadas para auditar o resultado. O comando completo está
em `reproduce.sh`.

## SHA-256

- Probe: `8b9abf367bc03c3e2add0cb488f1575928e6237bb59c424519e7a3d40249adea`
- Certificado dos pisos: `71b9e1e4aca8c3abbc98e8ac2a7524c1f8ce3ec5ac859642c9b29444ecc66880`
- Combinação racional: `77ee5d320d29f4f4abafbe397ae3db176b59bf75cab9022cf313db5bfa116348`
- Caixa Gamma: `931ca3014a0443fe40bd213c5f9f0dc2cae4a864b986b49a86f46e34cf005411`
- Log da sonda: `47a687b3df193796eea28b2706c0843fab634a5e9e5bee328be6e601958c9b89`
- Log do certificado: `e956873fecceb9c7d6ce1d456d7c63a3257886b34712707ef549328985f430c0`
- Log da combinação: `098eb12dbd450c3540388c255d82331177c87aaee1574c8cfa0a9af1086b8c85`
- Log da composição Gamma: `3295e1361bce5a68859a4f4d73a035af3512fdaf7dc3248883a892c34284c4b8`

## Alcance

A prova cobre apenas um segundo ponto real de Gamma. Ela ainda não cobre os
pontos complexos da malha da fonte, os fatores nativos e de zeta, as quadraturas
nem `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 continua incompleta; os
certificados condicionais O3 não foram alterados.
