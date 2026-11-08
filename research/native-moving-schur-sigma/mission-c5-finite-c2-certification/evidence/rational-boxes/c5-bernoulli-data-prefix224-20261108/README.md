# C5 — candidato ao prefixo Bernoulli 224 (build pendente)

## Escopo e estado

Esta etapa estende `CarrySigmaObstruction.c5BernoulliPrimeTable_192_eq_data`
aos índices 0–223 com `CarrySigmaObstruction.c5BernoulliPrimeTable_224_eq_data`.
O prefixo 192 permanece o último integrado e validado. A primeira compilação
limpa falhou após 1h56m46s por listas `simp` incompletas; o log e o erro foram
preservados em `attempts/first-build-failure-20261108/`. O candidato não conta
como provado e a auditoria isolada ainda não foi executada.

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
  indicado por `C5_PREFIX192_CACHE` (SHA-256 em `pins.txt`), e mantém os
  caches anteriores em `SIGMA_HEIGHT50_BUILD`. Todos os caminhos são configuráveis no reprodutor.
- Branch `codex/c5-zeta-bernoulli-prefix224-20261108`; prova candidata e
  auditoria estão no checkpoint `84d5fc5854d66a9fe4dc50c1334705d528bf61af`, confirmado no remoto antes da compilação.

## Estado do runner

A primeira tentativa foi iniciada em `2026-11-08T14:34:55Z` na sessão tmux
`c5-bernoulli-prefix224-20261108` (pane PID 108840, Lean PID 108950) e terminou
com `EXIT=1`. A correção foi publicada no commit `1e0feaaf0609ab1733c8a32cea2ec15ded9a5dba`; a segunda execução está ativa. Para acompanhar:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix224-20261108/run-detached.sh
```

Acompanhe `runner-status.txt`, `run-state.txt` e os logs. O runner atual é
`c5-bernoulli-prefix224-20261108`, pane PID 151047, Lean PID 151152, iniciado
às 16:42:48 UTC. A primeira falha foi causada pela omissão de
`c5BernoulliPrimeDataPrefix160`; ela foi corrigida e preservada no histórico.

## Critério de validação

A reprodução limpa compila a prova e o auditor em Lean 4.32.0 com
`warningAsError=true`. A auditoria aceita somente `propext`, `Classical.choice`
e `Quot.sound`, rejeitando `sorryAx`, `native_decide`, axiomas próprios e erros
de compilação. Nenhum resultado deve ser contado como provado antes de ambos
os passos passarem.
