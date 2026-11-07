# C5 — termo nodal `m=2`, transição Taylor `n=2→3` (parcial)

## Resultado validado

No nó `(a,j)=(2/5,0)`, o módulo
`SigmaC5M2TaylorStateStage3Certificate.lean` prova

```lean
c5RoundedExpStateC 896 c5M2TaylorArgExport 3 = c5M2Stage3
```

A transição usa três reduções explícitas: multiplicação de um intervalo
não-negativo por um não-positivo, escala exata por `1/2` do termo de Taylor e
arredondamento para 896 bits. A soma acumulada também é atualizada e conferida
contra os racionais exportados.

O build Lean 4.32.0 com `warningAsError=true` passou. As cinco declarações
auditadas (`c5M2Stage3PowerCoarsenExport`, `c5M2Stage3PowerCorrect`,
`c5M2Stage3TermCoarsenExport`, `c5M2Stage3SumCorrect` e
`c5RoundedExpStateC_stage3_correct`) usam somente `propext`,
`Classical.choice` e `Quot.sound`; não há `sorryAx` no build aprovado. O log
está em `state-stage3-build2.log`.

Este resultado prova somente a recorrência Taylor até `n=3` para um nó. Não
prova os 192 termos, as quatro quadraturas da exponencial, o termo nodal
completo `c5CenteredDirichletTermBox`, a ponte CSV–Lean, a inclusão dos
coeficientes originais C2 ou os sinais finais. Os valores exatos dos estados
exportados por `#eval` estão no checkpoint anterior
`../c5-m2-dirichlet-term-stage2-20261107/state-export.log`; são dados de
trabalho, não substituem as igualdades provadas.

## Pins e ambiente

- Base da `main`: `418d440c6b7c1feff274ae17156595d186942d0e` (PR #244).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0`.
- `MemAvailable` observado: 60.4 GiB; o wrapper exige 30 GiB.
- SHA-256 do `.olean` compilado: `ff2c1ccd4b3d4b0fc28ac7b1ba86cb3b305808fbabc29d16047d2d16ed6d2289`.

## Reprodução

Use a configuração de ambiente e compile as dependências `n=0,1,2` conforme
`../c5-m2-dirichlet-term-stage2-20261107/README.md`. Em seguida, da raiz da
worktree:

```bash
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage3Certificate
```

O comando de compilação usa `warningAsError=true` e o wrapper verifica o pin
limpo do Carry. O log integral da execução aceita está em
`state-stage3-build2.log`.

## Tentativa intermediária inválida

`attempts/state-stage3-build1.log` preserva a primeira compilação. Ela mostrou
um aviso de variável não usada e duas metas abertas na soma porque a tática não
desdobrou a definição intermediária `c5M2Stage2SumReExport`. A fonte atual
removeu o nome não usado e desdobrou explicitamente as caixas da soma; o build
aprovado é o `state-stage3-build2.log`.

Os arquivos e logs deste diretório estão listados em `SHA256SUMS.txt`. Para
retomar, siga o README do estágio 2 e então compile este módulo.
