# C5 — auditoria da rota exata da fonte e da lacuna de zeta

## Atualização — prova de zeta de ordem 300 e primeira caixa Gamma (2026-11-07)

A conclusão antiga abaixo sobre inexistência de Euler–Maclaurin de ordem alta
foi superada pela rota formal já presente em Lean 4.32. O módulo
`SigmaC5RationalNodeCenteredInstantiate.lean` prova
`c5RationalZetaCenteredNodeBox_contains` para a malha inteira de argumentos
`a + i b` no domínio usado: usa a expansão de Euler–Maclaurin de ordem 300,
o resto `emZetaHighTail_norm_le_node`, a tabela de Bernoulli demonstrada e
caixas intervalares racionais. Assim, a avaliação de zeta isolada não é mais o
primeiro bloqueio.

Também foi provado localmente
`CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains`, que contém
`Γ(1/5)` com base no núcleo racional em 16 blocos e na cota formal do erro de
`gammaFinite`. Build, auditoria e logs estão em
`evidence/rational-boxes/c5-gamma-first-node-20261107/README.md`.

## Lacuna real remanescente

A prova genérica de caixa para zeta e a caixa de um ponto para Gamma ainda não
foram compostas com os fatores da característica C2 completada e com a
quadratura que define os coeficientes da fonte deslocada. Faltam Gamma nos
demais pontos da malha, a propagação intervalar até cada coeficiente e a prova
de `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. Os sinais O3 permanecem
condicionais. Este checkpoint não fecha a inclusão intervalar da fonte.

**Estado:** checkpoint de investigação, não validação numérica. Nenhuma
inclusão dos coeficientes originais nas caixas O3 foi provada neste passo.

## Fonte que deve ser avaliada

A revisão Lean 4.32 usa a característica completada original. O teorema
`CarrySelfAdjointOperator.completedNativeOperatorCharacteristic_eq_completedRiemannZeta`
reescreve-a, no `genuineCriticalStrip`, como o fator nativo de completação
multiplicado por `riemannZeta`. A identificação do escalar é
`nativeScalar_eq_riemannZeta`; a apresentação geométrica C2 mantém a cabeça
finita e a cauda exata na ponte
`canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar`.
Logo, reduzir a avaliação a zeta é uma reescrita da fonte exata já provada, e
não uma substituição por um modelo de polos.

Para os nós racionais `tⱼ = j/100000` (`0 ≤ j ≤ 128`), os argumentos da zeta
na fonte deslocada são `w± = 1/2 ± d + i tⱼ`. As partes reais ficam em
`[2/5, 3/5]`; os pontos pertencem ao domínio original. Isso deixa a avaliação
certificada de `riemannZeta w±` e da Gamma finita como trabalho numérico, sem
alterar `completedNativeOperatorCharacteristic` ou `displacedProductC`.

## Primeiro gargalo formal localizado

Na revisão Mathlib pinada, o resultado Euler–Maclaurin localizado para zeta é
`HardyFirstZero.zeta_em4_error`, em
`height50-certified/hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean`.
Ele fornece só a correção de ordem 4 e um resto proporcional a
`(N-1)^(-Re(s)-3)`. Na borda inferior do contorno Cauchy, `Re(s)=0.1495` e
`|s|<3/2`; com `N=100`, o limite desse teorema é aproximadamente
`1.351·10⁻⁸`. Isso não chega à precisão das caixas de coeficientes usadas em
O3. Fazer `N` enorme também não fornece uma avaliação prática da soma finita.

Na revisão fixada e nos módulos locais pesquisados não foi encontrado um lema
de Euler–Maclaurin de ordem alta para `riemannZeta`/Hurwitz zeta com resto
quantitativo adequado. A fórmula de ordem 80 do avaliador Python não constitui
prova Lean; `mpmath.iv` ainda não está ligado ao kernel. Essa ausência é o
primeiro bloqueio matemático após a reescrita exata da fonte. O passo Gamma
também exige a inclusão intervalar da expressão finita `gammaFinite 3072 620`
nos nós; o limite analítico `10⁻²⁵⁹` já está provado, mas a soma finita ainda
não foi avaliada em caixas formais.

## Próxima entrega necessária

Provar e auditar em Lean 4.32 um resto de Euler–Maclaurin/Hurwitz de ordem alta
para o domínio dos nós e do contorno. Em seguida, compor a série finita e os
termos Bernoulli com `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp`, avaliar
`gammaFinite 3072 620` por uma rota racional estável, e transportar os
retângulos às caixas O3. A auditoria aqui não encontrou um erro de compilação:
o lema de ordem alta e sua tradução intervalar ainda não existem nesta rota.

## Base reproduzível

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Fórmula experimental, sem prova Lean: `investigations/c2_first_negative_interval_certificate_20261106/c2_em_interval.py` no checkout Momentos isolado; usa `N=100`, `p=80` para Hurwitz.
- Limite de Euler para Gamma já provado: `SigmaC5Gamma.gamma_finite_3072_620_error`.

Este checkpoint não altera os módulos Lean, não afirma sinais incondicionais e
não fecha O4/C5.
