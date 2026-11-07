# C5 — termo nodal `m=2`, transição Taylor `n=3→4` (parcial)

## Resultado validado

No nó `(a,j)=(2/5,0)`,
`SigmaC5M2TaylorStateStage4Certificate.lean` prova

```lean
c5RoundedExpStateC 896 c5M2TaylorArgExport 4 = c5M2Stage4
```

A potência do estágio 3 e o argumento são ambos não-positivos; a prova usa a
regra formal de multiplicação para esse caso. O quarto termo usa o coeficiente
`1/3! = 1/6`; a escala, seu coarsening, a soma e o arredondamento final são
verificados por frações racionais exatas.

Lean 4.32.0 com `warningAsError=true` compilou o módulo. As cinco declarações
auditadas (`c5M2Stage4PowerCoarsenExport`, `c5M2Stage4PowerCorrect`,
`c5M2Stage4TermCoarsenExport`, `c5M2Stage4SumCorrect` e
`c5RoundedExpStateC_stage4_correct`) usam somente `propext`,
`Classical.choice` e `Quot.sound`; o log não contém `sorryAx`. A saída integral
está em `state-stage4-build.log`.

O teorema cobre somente a recorrência Taylor até `n=4` para o nó `(2/5,0)`.
Não prova os demais 188 termos, as quadraturas, a caixa completa
`c5CenteredDirichletTermBox`, a ponte CSV–Lean, as inclusões da fonte C2 ou os
sinais finais C5.

## Pins e ambiente

- Base da `main`: `61ffbda123b474184a6756deee9bbf57b2daa41c` (PR #246).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0`.
- `MemAvailable` observado: aproximadamente 60 GiB; o wrapper exige 30 GiB.
- SHA-256 do `.olean` compilado: `29235984d76d93b7ed2e750fcb1bfd86c00e926737bf57cb0e5b4cc2f64f7ee9`.

## Reprodução

Use a configuração de ambiente e compile as dependências até `n=3` conforme
`../c5-m2-dirichlet-term-stage3-20261107/README.md`. Então, da raiz da
worktree:

```bash
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage4Certificate
```

O wrapper usa `warningAsError=true` e exige o checkout Carry pinado e limpo. O
build aprovado está preservado em `state-stage4-build.log`. Não houve tentativa
de prova Lean que falhasse nesta etapa.

Os arquivos e logs do checkpoint estão listados em `SHA256SUMS.txt`. A
integração continua pendente até a PR desta etapa ser incorporada.
