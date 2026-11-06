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

Essa infraestrutura ainda não enuncia uma inclusão para `Complex.Gamma`. O
primeiro elo analítico ausente é uma caixa racional uniforme para `Gamma z` no
retângulo necessário para `z = w/2`, `0.1495 ≤ Re(w) ≤ 0.9495` e `|Im(w)| ≤
0.4`. A rotina Python desloca `z` por 80, usa 75 correções e acrescenta o
resto `4(150)!/(6^150·150·149·80^149)`, mas ainda não há teorema Lean ligando
essa aproximação à função `Complex.Gamma` da completação C2.

Há uma alternativa formal já existente: `Zeta23.DigammaSeries.inv_gamma_eq_prod`
em `height50-certified/lean/vendor/zeta23/Zeta23/GammaFacts/Series.lean` prova
a identidade infinita de Weierstrass para `1/Γ`. O uso numérico dela também
precisaria de um limite racional eficiente para a cauda do produto e do fator
exponencial. A rota ainda está em avaliação; nenhuma das duas abordagens foi
composta às estimativas de Hurwitz e à extração Cauchy. Portanto, não há ainda
prova de inclusão para os coeficientes originais.
