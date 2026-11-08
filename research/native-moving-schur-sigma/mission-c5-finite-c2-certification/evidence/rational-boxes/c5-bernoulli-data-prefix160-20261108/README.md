# C5 — certificado parcial do prefixo de 160 entradas da tabela de Bernoulli

## Resultado

Esta etapa estendeu `c5BernoulliPrimeTable_128_eq_data` aos índices 0–159 com
`c5BernoulliPrimeTable_160_eq_data`. O resultado continua parcial: 441 das 601
entradas ainda não estão formalmente certificadas. A ponte CSV–Lean das caixas
de zeta, as inclusões da fonte C5 e os sinais finais permanecem obrigações
separadas.

## Ambiente fixado

- Lean 4.32.0, toolchain commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
  Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Geometry reference `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- O certificado-base de 128 entradas foi integrado pela PR #309: prova
  `b6f26114502116c65fe2482ebda3464e4b1fc645`, merge
  `c7782c54b78f97b1ea3f5a61f6e0ceefe75f2f11`.
- A reprodução importa o `.olean` de 128 entradas salvo no caminho
  `C5_PREFIX128_CACHE` em `reproduce-clean.sh`; esse caminho é substituível por
  variável de ambiente. Os caches 64 e 96 anteriores também são dependências
  fixadas no script.

## Reprodução e auditoria

Execute `bash reproduce-clean.sh`. O script compila o certificado 160 e um
módulo separado de `#print axioms`, usando uma pasta de saída nova; grava
tempos e pico de RSS nos logs e verifica os axiomas com `check-axioms.py`.
`SHA256SUMS.txt` registra as fontes, os logs e os arquivos de reprodução.

O check exato dos 601 literais racionais da sonda já passou no checkpoint do
prefixo 128; seu resultado está em
`../c5-bernoulli-data-prefix128-20261108/data-table-check.log`. Esta etapa
reutiliza a mesma tabela literal, acrescentando somente o teorema cumulativo
0–159.

## Resultado validado (2026-11-08)

`CarrySigmaObstruction.c5BernoulliPrimeTable_160_eq_data` compilou em uma
reprodução limpa com Lean 4.32.0 e `warningAsError=true`. A auditoria isolada
do `#print axioms` passou: somente `propext`, `Classical.choice` e
`Quot.sound`; sem `sorryAx` ou axiomas próprios. A reprodução terminou com
`EXIT=0`, `CLEAN_BUILD=PASS` e `AXIOM_AUDIT=PASS`.

- Teorema: `research/native-moving-schur-sigma/SigmaC5BernoulliDataCertificate160.lean`.
- Auditor: `SigmaC5BernoulliDataCertificate160Audit.lean`.
- Tempo da prova cumulativa: 1h56m34s; pico RSS: 12,572,772 KiB (aprox. 11.99 GiB).
- Auditoria isolada: 4.23s; pico RSS: 3,236,680 KiB.
- SHA-256 do arquivo Lean da prova: `371c80b9add3cb8365d991393ef53b38678edf9175229907a8b1cab9b15b969e`.
- A tabela agora tem 160/601 igualdades formalmente certificadas; 441 continuam abertas.

Este é um checkpoint parcial. A prova só valida a igualdade da recorrência de
Bernoulli com os dados racionais até o índice 159. A ponte das caixas de zeta,
as inclusões da fonte C2 e os dois sinais finais não são demonstrados aqui.
Commit de prova `5f9cb0eeab2b6f70fda12aa62f62047e7206eec5`; integrada pela PR
#312 no merge `cb829d98d799df72f07c9aff03e9d93871da6f77`.

## Tentativas anteriores

A primeira execução em primeiro plano desapareceu depois de cerca de 45
minutos, sem log final nem `.olean`; o código de saída é desconhecido. O pico
observado foi 6,345,220 KiB de RSS, com CPU ativa. A segunda tentativa de
execução destacada também foi encerrada junto do executor, antes do compilador
Lean iniciar. Ambas as interrupções e os logs vazios estão preservados em
`attempts/`; nenhuma conta como compilação válida nem como falha da prova.

A reprodução usada foi iniciada por `bash run-detached.sh`, que criou uma
sessão tmux separada. `runner-status.txt`, `run-state.txt`, os logs, o resultado
e os hashes preservam o encerramento. A validação do prefixo 160 passou, mas C5
continua incompleta até a tabela inteira, a ponte das caixas, as inclusões da
fonte e os dois sinais finais estarem certificados.
