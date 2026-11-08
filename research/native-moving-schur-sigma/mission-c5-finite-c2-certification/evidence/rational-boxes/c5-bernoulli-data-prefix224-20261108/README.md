# C5 — candidato ao prefixo Bernoulli 224 (build pendente)

## Escopo e estado

Esta etapa estende `CarrySigmaObstruction.c5BernoulliPrimeTable_192_eq_data`
aos índices 0–223 com `CarrySigmaObstruction.c5BernoulliPrimeTable_224_eq_data`.
O prefixo 192 permanece o último integrado e validado. Este candidato não conta
como provado até a compilação limpa e a auditoria isolada passarem.

A tabela tem 601 entradas. O candidato cobre 224; se validado, 377 ainda
ficarão sem prova formal. A ponte CSV–Lean das caixas de zeta, as inclusões
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`, a composição com a fonte
original e os sinais finais seguem como obrigações separadas.

## Ambiente fixado

- Lean 4.32.0, toolchain commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
  Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Base `main`: `513b73b54d232d7f0375ca3a2381b749fc17dba3` (PR #313 e registro
  pós-merge do prefixo 192).
- Referências de reprodução: Geometry
  `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- A compilação usa o `.olean` integrado do prefixo 192, preservado no cache
  indicado por `C5_PREFIX192_CACHE`, e mantém os caches anteriores no caminho
  `SIGMA_HEIGHT50_BUILD`. Todos os caminhos são configuráveis no reprodutor.
- Branch `codex/c5-zeta-bernoulli-prefix224-20261108`; prova candidata e
  auditoria estão no commit de checkpoint registrado no Git.

## Estado do runner

Antes da execução, `runner-status.txt` contém `NOT_STARTED`. O comando de
retomada é:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix224-20261108/run-detached.sh
```

Acompanhe `runner-status.txt` e `run-state.txt`; não relance enquanto o status
for `RUNNING`. A execução limpa escreve logs, resultado, auditoria e SHA-256.

## Critério de validação

A reprodução compila a prova e o auditor em Lean 4.32.0 com
`warningAsError=true`. A auditoria aceita somente `propext`, `Classical.choice`
e `Quot.sound`, rejeitando `sorryAx`, `native_decide`, axiomas próprios e erros
de compilação. Nenhum resultado deve ser contado como provado antes de ambos
os passos passarem.
