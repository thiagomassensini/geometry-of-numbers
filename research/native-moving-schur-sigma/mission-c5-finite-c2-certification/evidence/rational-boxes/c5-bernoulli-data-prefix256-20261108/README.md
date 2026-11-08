# C5 — próximo bloco cumulativo da tabela Bernoulli: prefixo 256

## Estado do checkpoint

O alvo é `CarrySigmaObstruction.c5BernoulliPrimeTable_256_eq_data`, que estende
o resultado integrado do prefixo 224 aos índices 224–255. A tabela-fonte já
contém `c5BernoulliPrimeDataPrefix256`; o certificado deve provar a igualdade
por recorrência exata em `ℚ`, sem refazer prefixos anteriores.

O build começou em `2026-11-08T22:08:26Z`, na sessão tmux
`c5-bernoulli-prefix256-20261108`, com status `RUNNING`. Nenhum resultado 256
será considerado validado até a compilação limpa, auditoria transitiva de
axiomas e checagem integral dos hashes passarem. `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes` continuam sem prova; o prefixo Bernoulli não certifica os
sinais da fonte original.

## Base e toolchain

- `main` de base: `8f5631a7808ad7c73491b558a894566e1d39899c` (prefixo 224 e
  registro pós-merge da PR #315).
- Geometry: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry:
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, `warningAsError=true`.
- O `.olean` do certificado 224 está fixado em `pins.txt`; sua caixa e os
  caches predecessores são somente entradas de build e não substituem as
  fontes/versionamentos registrados.

## Arquivos e retomada

- Prova: `research/native-moving-schur-sigma/SigmaC5BernoulliDataCertificate256.lean`.
- Auditor: `research/native-moving-schur-sigma/SigmaC5BernoulliDataCertificate256Audit.lean`.
- Reprodutor: `reproduce-clean.sh`; execução retomável em tmux:
  `run-detached.sh`.
- Logs, resumo, auditoria e manifesto serão gravados nesta pasta. O log e a
  falha da tentativa anterior do prefixo 224 estão preservados no diretório
  irmão `c5-bernoulli-data-prefix224-20261108/`.

Ao concluir, registrar o teorema exato, `EXIT`, `CLEAN_BUILD`, resultado da
auditoria, conjunto de axiomas, tempo, pico RSS e hashes. Não alegar que os
sinais originais C2 estão certificados enquanto as duas inclusões da fonte
permanecerem abertas.
