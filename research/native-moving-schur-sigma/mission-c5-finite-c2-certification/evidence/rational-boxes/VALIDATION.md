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
