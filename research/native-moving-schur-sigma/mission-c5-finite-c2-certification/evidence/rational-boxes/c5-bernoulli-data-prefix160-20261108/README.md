# C5 — certificado parcial do prefixo de 160 entradas da tabela de Bernoulli

## Resultado

Esta etapa tenta estender `c5BernoulliPrimeTable_128_eq_data` aos índices
0–159 com `c5BernoulliPrimeTable_160_eq_data`. O resultado continua parcial:
mesmo depois desta igualdade, 441 das 601 entradas ainda não estarão
formalmente certificadas. A ponte CSV–Lean das caixas de zeta, as inclusões da
fonte C5 e os sinais finais permanecem obrigações separadas.

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

## Tentativa anterior e estado

A primeira execução em primeiro plano desapareceu depois de cerca de 45
minutos, sem log final nem `.olean`; o código de saída é desconhecido. O pico
observado foi 6,345,220 KiB de RSS, com CPU ativa. A segunda tentativa de
execução destacada também foi encerrada junto do executor, antes do compilador
Lean iniciar. Ambas as interrupções e os logs vazios estão preservados em
`attempts/`; nenhuma conta como compilação válida nem como falha da prova.

A reprodução atual é iniciada por `bash run-detached.sh`, que cria uma sessão
tmux separada e grava seu nome, PID, horário e código de saída em arquivos
desta pasta. Consulte `runner-status.txt` e `run-state.txt` para acompanhar a
execução. Até a compilação e a auditoria passarem, nenhum resultado do prefixo
160 deve ser contabilizado. C5 continua incompleta até que a tabela inteira,
a ponte das caixas, as inclusões da fonte e os dois sinais finais estejam
certificados.
