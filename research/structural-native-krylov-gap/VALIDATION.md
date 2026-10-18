# Validação final

| Comando | Saída | Log |
| --- | --- | --- |
| `/usr/bin/python3 /home/thlinux/geometry-of-numbers/research/structural-native-krylov-gap/check_sources.py` | 0 | `evidence/source.log.gz` |
| `lake build --wfail GeometryOfNumbers.Analysis.MaterialClockKrylovGap GeometryOfNumbers.Analysis.MaterialClockKrylovGapAudit` | 0 | `evidence/focused.log.gz` |
| `bash /home/thlinux/geometry-of-numbers/research/structural-native-krylov-gap/compile_module.sh CanonicalClockGap` | 0 | `evidence/canonical.log.gz` |
| `bash /home/thlinux/geometry-of-numbers/research/structural-native-krylov-gap/compile_module.sh Regression` | 0 | `evidence/regression.log.gz` |
| `bash /home/thlinux/geometry-of-numbers/research/structural-native-krylov-gap/compile_module.sh Audit` | 0 | `evidence/axioms.log.gz` |
| `lake build --wfail` | 0 | `evidence/root.log.gz` |
| `bash scripts/audit-foundation.sh` | 0 | `evidence/foundation.log.gz` |
| `bash scripts/audit-geometry.sh` | 0 | `evidence/geometry.log.gz` |
| `bash scripts/audit-analysis.sh` | 0 | `evidence/analysis.log.gz` |
| `git diff --check` | 0 | `evidence/diff.log.gz` |

Auditoria nova: 9 raízes de biblioteca / 4649 declarações transitivas; 13 raízes de pesquisa / 5719 declarações transitivas. Todos os 22 teoremas passaram o guard e `#print axioms`; apenas os três axiomas padrão permitidos.

Os jobs Lake incluem replay de dependências já compiladas. A compilação cruzada explícita usa o ambiente original e caches das pesquisas certificadas. Não foram alterados pins. Para reconstruir caches históricos ausentes, usar os validadores preexistentes de `research/sixth-odd-twelve-sources/` e seus pré-requisitos antes do `validate.py` desta rodada.

O CSV de preflight é apenas diagnóstico de decimais armazenados; os teoremas Lean usam caixas dos integrais theta já certificados. Hashes das fontes e logs estão nos manifestos, e `verify_evidence.py` os confere.
