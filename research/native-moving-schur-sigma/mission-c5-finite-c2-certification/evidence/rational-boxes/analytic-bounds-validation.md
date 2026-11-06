# C5 O4 — cota explícita do módulo da fonte original

## Resultado validado localmente

`SigmaC5AnalyticBounds.lean` prova em Lean 4.32:

```text
CarrySigmaObstruction.displacedProductC_norm_le_10pow100_on_ball_39
```

Para `|d|≤1/10` e `z∈Metric.ball 0 (39/100)`, a fonte deslocada original
satisfaz `‖displacedProductC d z‖≤10^100`. A demonstração limita cada
característica completada original por `2·10^6` no domínio necessário e
multiplica as duas cotas. Ela usa a Gamma complexa original, a característica
nativa C2 e a completação existente; não troca a fonte pelos polos de um
modelo nem remove a cauda.

A cota Lean vale no disco aberto de raio `39/100`. Para Cauchy, o contorno
exterior escolhido tem raio `38/100`; seu disco fechado está estritamente
dentro da região onde a cota vale. Ele também está dentro do disco analítico
aberto de raio `2/5`, provado em `SigmaC5SourceAnalytic.lean` e integrado pela
PR #189 (merge `3513a3b3854b105419d4f2cef245efac7ce88ba0`).

## Build e auditoria

- Toolchain: Lean `leanprover/lean4:v4.32.0`.
- Build final em diretório limpo: `c5-analytic-bounds-final-clean-build.log`,
  com `BUILD_EXIT=0` e `warningAsError=true`.
- A auditoria fail-closed registra três raízes: `complexGamma_norm_le_100`,
  `complexGamma_norm_le_1000` e a cota pública da fonte. O checker aceitou
  somente `propext`, `Classical.choice` e `Quot.sound`;
  saída em `c5-analytic-bounds-final-clean-axiom-check.log`.
- O checker é `research/native-moving-schur-sigma/check_c5_analytic_bounds_axioms.py`.
- SHA-256 da fonte Lean:
  `4304d3efec5b4a3b52f107a7129fef18deb31897658a93d230024da3839d87eb`.
- SHA-256 do checker:
  `b5957a654a856407e4f953e7eb7b86074b37d781be2b76c4b1ea621d396fa1f2`.
- SHA-256 do `.olean` final:
  `63aa6b0c17bc5e03269c4f624811da2a986fb509f2382ad043bfa278cf306845`.
  Os três hashes também estão em `c5-analytic-bounds-final-clean-source-olean-sha256.txt`.

Comando de retomada e pins estão em `RESTART_HERE.md`. As tentativas de prova
anteriores foram preservadas nos logs `c5-analytic-bounds-try*-build.log`; o
registro final bem-sucedido é o log `final-clean` acima.

## Margem da interpolação racional

`analyze_rational_interpolation.py` foi executado com frações exatas e raio
exterior `38/100`. `rational-interpolation-analysis-radius-38.log` registra
que, usando o módulo `10^100`, a contribuição da cauda de interpolação para
graus `0..14` permanece `<10^-410`. A amplificação do erro certificado da
Gamma `10^-259` permanece `<10^-135`; a soma máxima dos pesos racionais exatos
continua `<10^124`. O log anterior para raio `39/100` é preservado como
histórico, mas não é usado porque o lema Lean fornece a cota apenas para
`|z|<39/100`.

## Limites do resultado

O4 permanece aberta. Este resultado não fornece caixas para os valores da
fonte nos 129 nós `j/100000`, não prova a inclusão dos coeficientes C2 nas
caixas O3 e não conclui os sinais incondicionais de `sigmaPadeD`. A validação
C5 segue explicitamente incompleta.
