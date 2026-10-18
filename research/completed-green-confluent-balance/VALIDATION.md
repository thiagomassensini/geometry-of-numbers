# Validação final

Todos os nove comandos de `validate.py` passaram. As fontes novas ficaram estáveis durante esta validação; seus hashes estão no manifesto referenciado pelo log.

| Check | Duração (s) | Exit |
| --- | ---: | ---: |
| `python3 research/completed-green-confluent-balance/check_sources.py` | 0.071 | 0 |
| `lake build --wfail GeometryOfNumbers.Analysis.CarryMaterialForcingGreenEnergy GeometryOfNumbers.Analysis.CarryMaterialForcingGreenEnergyAudit` | 8.371 | 0 |
| `bash research/completed-green-confluent-balance/compile_module.sh SourceBalance` | 13.52 | 0 |
| `bash research/completed-green-confluent-balance/compile_module.sh Audit` | 11.277 | 0 |
| `lake build --wfail` | 40.503 | 0 |
| `bash scripts/audit-foundation.sh` | 7.38 | 0 |
| `bash scripts/audit-geometry.sh` | 10.948 | 0 |
| `bash scripts/audit-analysis.sh` | 45.699 | 0 |
| `git diff --check` | 0.01 | 0 |

As 15 raízes da biblioteca (12 teoremas e 3 definições) passaram o guard de tipos/corpos com fechamento de **5383** declarações. As 15 raízes de pesquisa (13 teoremas e 2 definições) passaram com fechamento de **5608** declarações. Os fechamentos se sobrepõem; não são somados. Todos os axiomas impressos são `propext`, `Classical.choice`, `Quot.sound`.

`verify_evidence.py` também passou, conferindo os nove exit codes, os hashes dos logs comprimidos/descomprimidos e o manifesto de fontes. Os checks são executados no host `llm`. Compilações anteriores de desenvolvimento não substituem esses nove comandos finais.

Não há prova de positividade canônica all-order. O status matemático é PARTIAL da compensação física e OPEN do sinal restante. Nenhuma campanha numérica foi executada.
