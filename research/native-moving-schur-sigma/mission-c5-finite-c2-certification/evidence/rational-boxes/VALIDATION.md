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
`aa116108384a6834647e350e68fc25e81113a90a`:

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
