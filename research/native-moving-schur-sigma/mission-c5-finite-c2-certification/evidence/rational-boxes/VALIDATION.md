# C5 O4 — domínio analítico e estado da certificação

`SigmaC5SourceAnalytic.lean` prova em Lean 4.32 que a fonte original
`displacedProductC d` é analítica no disco aberto `|z|<2/5`, para
`|d|≤1/10`. O resultado é obtido mostrando que cada argumento deslocado fica
no domínio de altura onde a característica completada original é analítica.
As especializações para `d=99/2000` e `d=1/10` também foram compiladas.

Build limpo com warnings como erros e checker fail-closed de quatro relatórios
de axiomas passaram; somente `propext`, `Classical.choice` e `Quot.sound`
aparecem. Logs, hashes e escopo estão em
`source-analytic-domain-validation.md`.
O incremento foi integrado pela PR #189, commit de prova
`e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge
`3513a3b3854b105419d4f2cef245efac7ce88ba0`.

Essa etapa estabelece o domínio para Cauchy. Ainda não prova uma cota
numérica do módulo, os valores nos 129 nós ou as inclusões dos coeficientes
originais nas caixas. Portanto, os resultados O3 abaixo seguem condicionais.

# C5 O3 — bolas racionais e sinais condicionais

## Resultado

O3 está provada e auditada em Lean 4.32. As caixas dos coeficientes, extraídas
como centro e raio racionais exatos dos intervalos decimais já arquivados,
propagam-se pela recorrência polinomial sem divisão de C4. A propagação cobre os
momentos escalados e cada menor solicitado; as desigualdades finais são fechadas
por aritmética racional no kernel Lean.

- Em `d=99/2000`, os menores têm limite inferior positivo para todo `s<11`, e
  o limite superior do menor em `s=11` é negativo.
- Em `d=1/10`, os menores têm limite inferior positivo para todo `s<9`, e o
  limite superior do menor em `s=9` é negativo.
- `sigmaPadeD_signs_at_99_2000_of_source_boxes` e
  `sigmaPadeD_signs_at_1_10_of_source_boxes` transferem esses sinais ao
  `sigmaPadeD` original sob `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.

Essas hipóteses afirmam que os coeficientes originais
`completedSigmaDisplacedSourceCoefficient` pertencem às caixas fornecidas. O3
não as prova. Portanto, nenhum dos dois resultados de primeira janela é ainda
incondicional; a obrigação aberta é O4.

## Build reproduzível

Toolchain `leanprover/lean4:v4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`,
checkout Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O wrapper também
confere que o checkout Carry usa Lean 4.32 e não tem modificações rastreadas.

Os seis módulos foram compilados em sequência para a pasta limpa
`.lake/build/research/native-moving-schur-sigma/c5-rational-clean/`, com
`warningAsError=true`:

```bash
RATIONAL_BUILD=$PWD/.lake/build/research/native-moving-schur-sigma/c5-rational-clean
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main
SIGMA_OUTPUT_DIR=$RATIONAL_BUILD
SIGMA_HEIGHT50_BUILD=$RATIONAL_BUILD:$PWD/.lake/build/research/native-moving-schur-sigma/c5-lean432-clean:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c1:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c4-main-clean
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_REFERENCE_ROOT SIGMA_OUTPUT_DIR SIGMA_HEIGHT50_BUILD CARRY_LEAN_ROOT
for module in SigmaFiniteRationalIntervals SigmaFiniteRationalIntervalBoxes SigmaFiniteRationalIntervalTransport SigmaFiniteRationalIntervalSigns SigmaFiniteRationalIntervalCertificates SigmaFiniteRationalIntervalAudit; do
  bash research/native-moving-schur-sigma/compile_sigma_pade.sh "$module"
done
python3 research/native-moving-schur-sigma/check_c5_rational_axioms.py \
  research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/axiom-audit.log
```

Cada invocação de compilação saiu com código 0. Lean não imprime texto em
compilações bem-sucedidas; os logs individuais ficam vazios quando não há
warnings. `build-summary.log` registra a presença dos seis `.olean`, cujos
hashes estão em `source-and-olean-sha256.txt`. `axiom-audit.log` lista 13 raízes
e `axiom-audit-check.log` registra o resultado do verificador fail-closed.

## Auditoria de axiomas

As 13 raízes auditadas incluem as operações de produto/potência das bolas, a
validade e propagação da recorrência, a contenção dos menores, os quatro sinais
fechados por `norm_num` e os dois teoremas condicionais sobre `sigmaPadeD`.
Todas dependem somente de `propext`, `Classical.choice` e `Quot.sound`.

## Limite seguinte

O4 precisa provar as duas proposições de inclusão das caixas para a fonte
original, preservando a cabeça C2, a cauda exponencial exata e a completação
original. A avaliação numérica existente utiliza `mpmath.iv`; nem esse backend
nem suas operações complexas elementares estão certificados em Lean. Não use
os sinais condicionais como uma prova incondicional até fechar essa inclusão.

### Infraestrutura intervalar reutilizável encontrada

O repositório já contém `height50-certified/lean/ZetaLean/Rigor.lean`,
`IntervalExp.lean` e `IntervalCExp.lean`: bolas retangulares racionais e
inclusões comprovadas para `log` real, `exp` real/complexo e termos
`m^{-s}`. Os três módulos foram recompilados em Lean 4.32 com warnings como
erros em saída limpa. A auditoria de `contains_logQ`, `contains_expI`,
`contains_expC` e `contains_dirichletTerm` mostra apenas `propext`,
`Classical.choice` e `Quot.sound`. Logs e hashes estão junto desta validação.

Build reproduzível, executado na raiz do checkout C5, usando o checkout de
referência `geometry-of-numbers-sigma-allorder-negative-certified-20261105`
(HEAD `caa07002306b555fea5624cc11ab2ea5811a4324`, Lean 4.32, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`):

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma/height50-certified/lean
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
C5_EVIDENCE=$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT/ZetaLean"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_MATHLIB_PATH"
for module in Rigor IntervalExp IntervalCExp; do
  "$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_SOURCE_ROOT" \
    -o "$C5_OUTPUT/ZetaLean/$module.olean" \
    "$C5_SOURCE_ROOT/ZetaLean/$module.lean" \
    > "$C5_EVIDENCE/reused-$module.log" 2>&1
done
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/reused-interval-audit.olean" \
  "$C5_EVIDENCE/reused-interval-audit.lean" \
  > "$C5_EVIDENCE/reused-interval-audit.log" 2>&1
```

Os três logs de build estão vazios (sem avisos nem erros); o log da auditoria
registra as quatro raízes e seus axiomas padrão permitidos.

### Ponte Euler-Gamma provada

`research/native-moving-schur-sigma/SigmaGammaEulerIntegral.lean` prova uma
aproximação da **Gamma original** pela expressão explícita
`SigmaC5Gamma.gammaFinite 512 81 z`. A prova mantém a integral original, limita
o erro da série de Taylor para `exp(-x)` no trecho compacto e acrescenta o
limite da cauda `exp(-81)`. Em particular,
`SigmaC5Gamma.gamma_finite_512_error` prova
`‖Complex.Gamma z - gammaFinite 512 81 z‖ ≤ 10⁻³²` para
`1495/20000 ≤ Re(z) ≤ 1`. O domínio inclui `z=w/2` em ambos os discos Cauchy
usados pelo avaliador C2.

Build e auditoria reproduzíveis, a partir da raiz do checkout C5. O ambiente de
referência é `geometry-of-numbers-sigma-allorder-negative-certified-20261105`
(HEAD `caa07002306b555fea5624cc11ab2ea5811a4324`, Lean 4.32, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`):

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-clean
C5_EVIDENCE=$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_MATHLIB_PATH"
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_SOURCE_ROOT" \
  -o "$C5_OUTPUT/SigmaGammaEulerIntegral.olean" \
  "$C5_SOURCE_ROOT/SigmaGammaEulerIntegral.lean" \
  > "$C5_EVIDENCE/gamma-euler-build.log" 2>&1
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/gamma-euler-audit.olean" \
  "$C5_EVIDENCE/gamma-euler-audit.lean" \
  > "$C5_EVIDENCE/gamma-euler-audit.log" 2>&1
```

O build final terminou sem warnings nem erros. As oito raízes auditadas usam
somente `propext`, `Classical.choice`, `Quot.sound`. As tentativas iniciais de
compilação e seus erros já resolvidos foram preservados em
`gamma-euler-prototype-errors.log` e `gamma-euler-numeric-errors.log`.
Hashes de fontes e `.olean` estão em `source-and-olean-sha256.txt`.

**O que continua faltando:** caixas racionais estreitas para `gammaFinite` nas
pequenas caixas complexas dos pontos Cauchy. A soma direta tem cancelamento
grande; deve-se expandir em Taylor em torno do centro racional e limitar o
resto. Ainda faltam a avaliação certificada de Hurwitz, a extração Cauchy e a
ponte com os coeficientes da fonte C2 original. A identidade formal
`Zeta23.DigammaSeries.inv_gamma_eq_prod` pelo produto de Weierstrass permanece
uma rota alternativa, mas nenhuma hipótese `sigmaC00495SourceBoxes` ou
`sigmaC01SourceBoxes` foi provada.

### Ponte Euler-Gamma de precisão alta

O lema adicional `SigmaC5Gamma.gamma_finite_1024_240_error` prova
`‖Complex.Gamma z - gammaFinite 1024 240 z‖ ≤ 10⁻⁹⁹` para
`1495/20000 ≤ Re(z) ≤ 1`. A prova separa o erro de Taylor `≤10⁻¹²⁰` da cauda
`exp(-240)≤10⁻¹⁰⁰`. Assim, a aproximação da Gamma deixa de ser o limitante de
precisão das caixas existentes. A avaliação racional da expressão finita
continua aberta.

Build e auditoria, a partir da raiz do checkout C5, com Lean 4.32.0,
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` e base geometry
`72586b6223579ee1b37a6077ad6f2a0eceaf919c` (PR #173):

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-1024-clean
C5_EVIDENCE=$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_MATHLIB_PATH"
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_SOURCE_ROOT" \
  -o "$C5_OUTPUT/SigmaGammaEulerIntegral.olean" \
  "$C5_SOURCE_ROOT/SigmaGammaEulerIntegral.lean" \
  > "$C5_EVIDENCE/gamma-euler-1024-retry2-build.log" 2>&1
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/gamma-euler-audit.olean" \
  "$C5_EVIDENCE/gamma-euler-audit.lean" \
  > "$C5_EVIDENCE/gamma-euler-1024-retry2-audit.log" 2>&1
```

Ambos comandos terminaram com código 0 e logs vazios. A auditoria registra dez
raízes, todas usando somente `propext`, `Classical.choice` e `Quot.sound`.
As tentativas anteriores de build, incluindo os erros corrigidos, também foram
preservadas nos logs `gamma-euler-1024-build.log` e
`gamma-euler-1024-retry1-build.log`.

### Precisão de interpolação racional

O lema `SigmaC5Gamma.gamma_finite_3072_620_error` reduz o erro uniforme para
`10⁻²⁵⁹`. A parte do Taylor da exponencial é limitada por `10⁻³⁰⁰`; a cauda
Euler é limitada por `exp(-620)≤10⁻²⁶⁰`. Build e auditoria usam Lean 4.32.0,
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` e base geometry
`992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec` (PR #175):

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-3072-clean
C5_EVIDENCE=$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_MATHLIB_PATH"
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_SOURCE_ROOT" \
  -o "$C5_OUTPUT/SigmaGammaEulerIntegral.olean" \
  "$C5_SOURCE_ROOT/SigmaGammaEulerIntegral.lean" \
  > "$C5_EVIDENCE/gamma-euler-3072-build.log" 2>&1
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/gamma-euler-audit.olean" \
  "$C5_EVIDENCE/gamma-euler-audit.lean" \
  > "$C5_EVIDENCE/gamma-euler-3072-audit.log" 2>&1
```

Ambos comandos terminaram com código 0; as doze raízes da auditoria dependem
somente de `propext`, `Classical.choice` e `Quot.sound`.

A rota de interpolação em 129 nós racionais está descrita pela análise
exploratória reprodutível `analyze_rational_interpolation.py`. A identidade
algébrica de Lagrange agora está formalizada em `SigmaRationalInterpolation.lean`:
o módulo prova a reconstrução exata para polinômios de grau menor que 129 e a
expressão de seus coeficientes como somas ponderadas. Também prova que a soma
absoluta do peso escalado de grau zero é exatamente `1`. Os limites numéricos
dos pesos dos graus `1..14` calculados com `fractions.Fraction` ainda não foram
formalizados. Para grau um, a derivada das bases tem expressão finita formal;
uma tentativa de computar a desigualdade diretamente excedeu o limite de passos
de `simp`, com erro preservado em `interpolation-weight-degree1-prototype.log`.
Em particular, o limite analítico `|completedSigmaDensity d t|≤10^100` em
`|t|≤2/5` continua sendo uma obrigação, não uma hipótese provada.

### Identidade algébrica da interpolação — Lean 4.32

O módulo `research/native-moving-schur-sigma/SigmaRationalInterpolation.lean`
define os nós `j²` para `0≤j≤128`, prova sua injetividade e os teoremas
`c5InterpolationPolynomial_coeff`, `c5_interpolate_polynomial` e
`c5InterpolationPolynomial_coeff_of_degree_lt`. Os pesos escalados aparecem
como `c5InterpolationWeight` e `c5InterpolationWeightSum`;
`c5InterpolationWeightSum_zero_eq_one` fecha o caso de grau zero.
`c5Coeff_one_eq_derivative_eval_zero` e
`c5LagrangeBasis_derivative_eval_zero` formalizam o caso estrutural de grau um.

Build limpo, executado a partir da raiz do checkout geometry C5:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-weight-degree1-structural-clean-20261106
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
SIGMA_REFERENCE_ROOT=$C5_REFERENCE_ROOT
CARRY_LEAN_ROOT=$C5_CARRY_ROOT
SIGMA_OUTPUT_DIR=$C5_OUTPUT
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_OUTPUT_DIR
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
  > "$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-interpolation-build.log" 2>&1
```

Auditoria transitiva e verificador fail-closed:

```bash
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit.log" \
  > "$C5_EVIDENCE/interpolation-audit-check.log"
```

O build saiu sem warnings nem erros. Quatorze raízes foram auditadas, todas com
apenas `propext`, `Classical.choice` e `Quot.sound`; o checker aceitou as
quatorze.
As fontes e os `.olean` têm hashes em `source-and-olean-sha256.txt`.

## Atualização integrada — limites dos pesos de graus 2–14

O módulo de interpolação prova agora `c5InterpolationCoeffAbsSum_le_four_mul_two_pow`
e `c5InterpolationWeightSum_lt_ten_145`: para cada `2≤n≤14`, a soma absoluta
dos pesos escalados é `<10^145`. O build limpo Lean 4.32 passou com
`warningAsError=true`; a auditoria de 23 raízes e o checker fail-closed também
passaram. Os logs, hashes e a demonstração do limite estão em
`c5-interpolation-degree2-14-final-clean-*` e
`degree2-14-weight-bound-validation.md`.
O incremento foi integrado pela PR #187: commit `6424f4334edd5c776997116403043635fa0c8f83`,
merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.

Esta etapa remove a obrigação dos limites dos pesos. Continua em aberto a cota
analítica da densidade C2 no disco de raio `2/5`, a avaliação certificada nos
129 nós e a inclusão dos coeficientes da fonte original nas caixas O3. A
certificação C5 ainda é incompleta.
