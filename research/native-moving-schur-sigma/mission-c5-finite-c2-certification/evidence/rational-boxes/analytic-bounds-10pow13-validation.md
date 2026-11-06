# C5 O4 — majorante explícito apertado

## Resultado validado localmente

`SigmaC5AnalyticBounds.lean` prova
`CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39`:

```text
|d| ≤ 1/10,  z ∈ Metric.ball 0 (39/100)
    ⟹ ‖displacedProductC d z‖ ≤ 10^13.
```

Cada característica completada original tem norma no máximo `2,000,000` no
domínio correspondente. O produto fica no máximo `4·10^12≤10^13`. A conclusão
anterior `...norm_le_10pow100_on_ball_39`, integrada pela PR #191, é mantida
como wrapper compatível derivado deste limite mais forte. A cabeça C2, a cauda
nativa e a completação original permanecem inalteradas.

## Build e auditoria

- Lean `leanprover/lean4:v4.32.0`, build limpo com warnings como erros:
  `c5-analytic-bounds-10pow13-clean-build.log`, `BUILD_EXIT=0`.
- O checker fail-closed auditou quatro declarações: as duas cotas Gamma, a
  cota `10^13` e seu wrapper `10^100`. A saída é
  `c5-analytic-bounds-10pow13-clean-axiom-check.log`; todos usam somente
  `propext`, `Classical.choice` e `Quot.sound`.
- SHA-256 de fontes e `.olean` está em
  `c5-analytic-bounds-10pow13-clean-source-olean-sha256.txt`.

## Efeito na interpolação

`analyze_rational_interpolation.py` usa o majorante `10^13` e contorno Cauchy
`38/100`, que está dentro da bola aberta `39/100` do lema Lean. A análise
racional exata dá erro de interpolação `<10^-501` para graus `0..14`; a
amplificação do erro Gamma `10^-259` continua `<10^-135`. Saída:
`rational-interpolation-analysis-10pow13-radius-38.log`.

## Escopo restante

O majorante mais forte não avalia a fonte nos 129 nós e não prova as caixas
para os coeficientes C2. O4 permanece aberta e os sinais finais de `sigmaPadeD`
continuam condicionais às hipóteses O3 de inclusão.
