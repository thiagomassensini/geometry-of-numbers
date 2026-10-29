# Validação final

Todos os nove checks remotos passaram com as fontes finais, mais o teste simbólico original executado no desktop local.

| Check remoto | Duração (s) | Exit |
| --- | ---: | ---: |
| `python3 research/carry-scale-covariance/check_sources.py` | 0.069 | 0 |
| `lake build --wfail GeometryOfNumbers.Analysis.CarryScaleCovarianceAudit` | 7.26 | 0 |
| `bash research/carry-scale-covariance/compile_module.sh NativeScaleSeam` | 10.43 | 0 |
| `bash research/carry-scale-covariance/compile_module.sh Audit` | 10.353 | 0 |
| `lake build --wfail` | 7.104 | 0 |
| `bash scripts/audit-foundation.sh` | 6.873 | 0 |
| `bash scripts/audit-geometry.sh` | 9.505 | 0 |
| `bash scripts/audit-analysis.sh` | 44.823 | 0 |
| `git diff --check` | 0.012 | 0 |

37 raízes de biblioteca (33 teoremas e quatro definições), fechamento de tipos/corpos com **5269** declarações. Oito raízes de pesquisa (oito teoremas nativos), fechamento com **6162** declarações. Os fechamentos se sobrepõem; seus tamanhos não são somados. Todas as 45 raízes imprimem somente `propext`, `Classical.choice`, `Quot.sound` e passam o guard transitivo.

O teste `reference_test.py` é uma cópia íntegra do arquivo fornecido. Foi executado no desktop local com SymPy já instalado; todas as comparações simbólicas passaram. O Python padrão do servidor não tem SymPy e não recebeu novas dependências. Versões, comando, SHA256 e log estão em `evidence/reference-local.*`.

`verify_evidence.py` e `check_sources.py` passaram também após a campanha: fontes novas/reutilizadas, pins, arquivos preservados do operador e logs correspondem aos hashes registrados.

A lei de escala é genérica e não demonstra positividade canônica all-order. A dilatação física da síntese completada permanece aberta. A ausência de novos sinais upstream é distinta do PASS destas identidades algébricas.
