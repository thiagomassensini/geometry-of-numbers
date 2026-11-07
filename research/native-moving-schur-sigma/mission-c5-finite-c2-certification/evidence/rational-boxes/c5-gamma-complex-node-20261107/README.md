# C5 checkpoint — primeiro nó complexo da Gamma

## Resultado formal

Em Lean 4.32.0, `c5GammaComplexNodeBox_contains` prova que uma caixa racional
contém

```text
Complex.Gamma (901/4000 + (3/20) * Complex.I)
```

O ponto é o primeiro nó complexo usado na malha C2 para `d = 99/2000`, na
altura de Cauchy `3/10`. A caixa compõe o fator `240^z`, o núcleo racional
`gammaFiniteRationalCore 1024 240 (901/4000) (3/20)` e o erro analítico
`gamma_finite_1024_240_error`, com inflação `10⁻⁹⁹`. Os dois lados do retângulo
do núcleo têm largura `16 / 2^1024`, obtida somando 16 blocos certificados de
64 termos, nas partes real e imaginária.

A composição usa `gammaFinite_eq_rationalCore`, a caixa certificada da
potência `dirichletTermBox2` e o resto publicado da Gamma. O bound de
`log(240)` é exportado pela declaração
`c5GammaSecondRealPoint_logQ_absBound`; a raiz dessa declaração também foi
auditada nesta compilação.

## Build limpo e auditoria

- Toolchain: Lean 4.32.0, com `warningAsError=true`.
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Os cinco módulos de `clean-build-r1/` terminaram com `BUILD_EXIT=0`.
- As raízes públicas impressas nos logs dependem somente de `propext`,
  `Classical.choice` e `Quot.sound`. Não aparece `sorryAx`, axioma próprio ou
  `native_decide`.
- O limite de memória do script foi mantido em 30 GiB; o pico observado ficou
  abaixo de 12 GiB.

Reproduza com:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-complex-node-20261107/reproduce-clean.sh
```

Os fontes e as saídas do build limpo têm hashes em `SHA256SUMS.txt`. As
tentativas anteriores estão preservadas em `attempts/`; incluem a falha de
busca de módulo do build direto, a configuração inicial de aritmética e os
ajustes de coerção racional que levaram ao build aprovado.

## Escopo deste checkpoint

Este resultado certifica um valor de Gamma em um nó complexo. Ainda faltam os
outros nós da malha, as caixas formais de zeta/Hurwitz e do fator nativo, a
composição da fonte C2 original nos coeficientes e a eliminação das hipóteses
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. Os sinais de `sigmaPadeD`
continuam condicionais às caixas; C5 permanece incompleta.
