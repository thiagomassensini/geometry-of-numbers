# C5 — limite dos pesos de interpolação, graus 2 a 14

**Status:** prova Lean compilada e auditada; checkpoint incompleto pronto para
publicação. Esta etapa não prova a inclusão dos coeficientes C2 originais nas
caixas O3.

## Resultado formal

`SigmaRationalInterpolation.lean` prova a fatoração das bases de Lagrange em
fatores lineares positivos e limita simbolicamente seus coeficientes. Para
`n≥1`, a soma absoluta dos coeficientes de grau `n` das 129 bases é no máximo
`4·2^n`. Portanto, para cada `2≤n≤14`, a soma absoluta dos pesos escalados
`(100000)^(2n)·coeff_n` é estritamente menor que `10^145`:

```lean
c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow
c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight
c5InterpolationCoeffAbsSum_le_four_mul_two_pow
c5InterpolationWeightSum_lt_ten_145
```

A primeira base usa `∏(1-X/k²)` e a cota `Σ 1/k²≤2`. Para `j>0`, a base
fatora como seu coeficiente linear vezes `X` vezes um produto sobre o mesmo
tipo de fatores; o coeficiente linear agregado já tem soma absoluta `≤6`.
Assim, os coeficientes de graus `2..14` ficam limitados por `4·2^n`. A escala
é no máximo `10^140`, e `4·2^n<10^5` para `n≤14`, dando o limite publicado.
Não há expansão por avaliação nativa nem hipóteses numéricas sobre os
coeficientes da fonte.

## Validação reproduzível

- Lean `leanprover/lean4:v4.32.0`.
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Build limpo com `warningAsError=true`: `c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`.
- Auditoria transitiva de 23 raízes: `interpolation-audit-degree2-14-final-clean.log`; checker fail-closed passou em `interpolation-audit-degree2-14-final-clean-check.log`.
- Footprint permitido: `propext`, `Classical.choice`, `Quot.sound`.
- SHA-256 do arquivo fonte, `.olean` da prova e `.olean` da auditoria:
  `c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt`.

O comando de reprodução está em `RESTART_HERE.md`. Os logs de tentativas
intermediárias desta continuação permanecem no diretório ignorado
`.lake/build/research/native-moving-schur-sigma/c5-degree2-14-20261106/`; o
artefato durável da validação bem-sucedida está em `c5-degree2-14-final-clean-20261106`
na worktree local e os seus hashes foram registrados acima. A prova, logs,
pins e comando para retomada acompanham este checkpoint.

## O que segue aberto

Falta uma cota analítica formal para a densidade da fonte C2 no disco de raio
`2/5`, a avaliação racional nos 129 nós e a inclusão dos coeficientes originais
nas caixas O3. As conclusões de O3 permanecem condicionais até fechar essa
inclusão. Esta entrega não declara a missão C5 concluída.
