# C5 — termo nodal `m=2`, transição Taylor `n=4→5` (parcial)

## Resultado validado

No nó `(a,j)=(2/5,0)`,
`SigmaC5M2TaylorStateStage5Certificate.lean` prova

```lean
c5RoundedExpStateC_stage5_correct
```

O quinto estado usa o produto de um intervalo não-negativo com o argumento
não-positivo, e o coeficiente exato `1/4! = 1/24`. A prova verifica o termo
escalado e arredondado, atualiza a soma e fecha a transição para `n=5` por
aritmética racional.

O build Lean 4.32.0 com `warningAsError=true` passou. As cinco declarações
auditadas (`c5M2Stage5PowerCoarsenExport`, `c5M2Stage5PowerCorrect`,
`c5M2Stage5TermCoarsenExport`, `c5M2Stage5SumCorrect` e
`c5RoundedExpStateC_stage5_correct`) usam somente `propext`,
`Classical.choice` e `Quot.sound`; o build aceito não contém `sorryAx`. Log
integral: `state-stage5-build.log`.

O resultado cobre apenas a recorrência de Taylor até `n=5` para um nó. Não
prova os 187 termos restantes, as quadraturas do avaliador, a caixa completa
`c5CenteredDirichletTermBox`, a ponte CSV–Lean, a inclusão dos coeficientes C2
ou os sinais finais.

## Pins e ambiente

- Base da `main`: `442b4904c41d47a63825040a3e42c3fef75763d4` (PR #248).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0`.
- `MemAvailable` observado: `63354860 kB`; o wrapper requer pelo menos 30 GiB.
- SHA-256 do `.olean` compilado: `e672d1ee759e6f210164de4dd09f82e57c9c5e4f01183035bd0d7979adbf882e`.

## Reprodução

Configure as mesmas variáveis e compile as dependências até `n=4` descritas
em `../c5-m2-dirichlet-term-stage4-20261107/README.md`. Depois, da raiz da
worktree:

```bash
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage5Certificate
```

O wrapper verifica que o checkout Carry está limpo e pinado e compila com
`warningAsError=true`. O build aceito está preservado em
`state-stage5-build.log`; não houve tentativa de prova Lean que falhasse.

A PR #249 integrou o resultado: commit de prova
`1782048f05c43fc31e491fa7192105235b34a14e`, merge na `main`
`58b9a61532f79f6aa51ebfb48edaacf728be3738`. O GitHub não reportou checks
hospedados. Os arquivos do checkpoint estão listados em `SHA256SUMS.txt`; C5
continua incompleta até que a avaliação do nó e as inclusões da fonte C2 sejam provadas.
