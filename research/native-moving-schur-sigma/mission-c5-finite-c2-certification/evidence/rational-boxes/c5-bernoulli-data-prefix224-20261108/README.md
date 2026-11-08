# C5 — prefixo Bernoulli 224 validado, aguardando integração

## Escopo e estado

`CarrySigmaObstruction.c5BernoulliPrimeTable_224_eq_data` estende a igualdade
formal da tabela Bernoulli aos índices 0–223, a partir do prefixo 192 integrado
pela PR #313. A reprodução limpa terminou com `CLEAN_BUILD=PASS`,
`AXIOM_AUDIT=PASS` e `EXIT=0` em Lean 4.32.0, com `warningAsError=true`.
A auditoria transitiva encontrou somente `propext`, `Classical.choice` e
`Quot.sound`; o candidato não usa `sorryAx`, `admit`, axiomas próprios ou
`native_decide`.

O build limpo demorou 5h05m; pico RSS de 21,529,692 KiB (aprox. 20.53 GiB).
A compilação isolada do auditor demorou 4.55s; pico RSS de 3,252,052 KiB. Os
logs completos, `RESULT.txt`, auditoria, estado do runner e hashes estão nesta
pasta. O `sha256sum -c SHA256SUMS.txt` final passou para todos os artefatos.
O runner inicialmente incluiu o próprio arquivo temporário no manifesto; o
manifesto foi regenerado excluindo `SHA256SUMS.txt` e `SHA256SUMS.txt.tmp` e
verificado integralmente.

A primeira compilação, antes da correção, falhou após 1h56m46s porque faltava
`c5BernoulliPrimeDataPrefix160` nas listas de simplificação. O log e o erro
permanecem preservados em `attempts/first-build-failure-20261108/`.

A tabela tem 601 entradas. Com este candidato, 224/601 estão formalmente
provadas nesta branch; 377 continuam abertas. A `main` ainda contém 192/601
até a integração da PR deste checkpoint. A ponte CSV–Lean das caixas de zeta,
as inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`, a composição da
fonte original e os sinais finais seguem abertas. Este resultado **não**
certifica sinais C2/C5 nem altera as duas inclusões em aberto.

## Ambiente fixado

- Lean 4.32.0, toolchain commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
  Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Base `main`: `513b73b54d232d7f0375ca3a2381b749fc17dba3` (PR #313 e registro
  pós-merge do prefixo 192).
- Referências de reprodução: Geometry
  `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- A compilação usa o `.olean` integrado do prefixo 192, preservado no cache
  indicado por `C5_PREFIX192_CACHE` (SHA-256 em `pins.txt`), e mantém os caches
  anteriores em `SIGMA_HEIGHT50_BUILD`. Todos os caminhos são configuráveis no
  reprodutor.
- Branch `codex/c5-zeta-bernoulli-prefix224-20261108`. O commit validado e a
  PR correspondente serão registrados aqui após a publicação do checkpoint.

## Runner e resultado

- Tentativa 1: início `2026-11-08T14:34:55Z`, tmux
  `c5-bernoulli-prefix224-20261108`, pane PID 108840, Lean PID 108950; `EXIT=1`.
  A falha e seu hash estão arquivados em `attempts/first-build-failure-20261108/`.
- Retry: início `2026-11-08T16:42:48Z`, tmux
  `c5-bernoulli-prefix224-20261108`, pane PID 151047, Lean PID 151152; terminou
  `2026-11-08T21:47:48Z` com `EXIT=0`.
- `SigmaC5BernoulliDataCertificate224-clean-build.log` contém a compilação da
  prova; `SigmaC5BernoulliDataCertificate224Audit-clean-build.log` contém a
  compilação isolada de auditoria; `axiom-audit.log` registra os axiomas
  transitivos permitidos.

## Reproduzir

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix224-20261108/run-detached.sh
```

O reprodutor verifica os pins do `.olean` prefixo 192, limpa os artefatos desta
execução, recompila a prova e o auditor com `warningAsError=true` e executa o
checker fail-closed. Não reutilize a primeira tentativa falha como validação.

## Próxima obrigação

Depois de integrar o prefixo 224, avançar a igualdade cumulativa da tabela até
601 e provar a ponte entre as caixas exportadas e a avaliação zeta Lean em um
nó piloto. Em seguida, compor as caixas nodais com Gamma, câmera e a fonte C2
original até provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. O
orçamento intervalar e as margens condicionais estão em
`../../../C5_SOURCE_SIGN_BUDGET_20261108.md`.
