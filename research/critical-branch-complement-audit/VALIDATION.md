# Validação final

| Comando | Saída | Log |
| --- | --- | --- |
| `/usr/bin/python3 /home/thlinux/geometry-of-numbers/research/critical-branch-complement-audit/check_sources.py` | 0 | `evidence/source-check.log.gz` |
| `lake build --wfail GeometryOfNumbers.Analysis.CriticalBranchComplementTransport GeometryOfNumbers.Analysis.CriticalBranchComplementAudit` | 0 | `evidence/focused.log.gz` |
| `lake build --wfail` | 0 | `evidence/root.log.gz` |
| `bash scripts/audit-foundation.sh` | 0 | `evidence/foundation.log.gz` |
| `bash scripts/audit-analysis.sh` | 0 | `evidence/analysis.log.gz` |
| `bash scripts/audit-geometry.sh` | 0 | `evidence/geometry.log.gz` |
| `git diff --check` | 0 | `evidence/diff-check.log.gz` |

Auditoria dedicada: **20 raízes**, fechamento de **5221 declarações** por tipos/corpos. Apenas `propext`, `Classical.choice`, `Quot.sound`. Foundation conservou footprint vazio; Geometry permite `propext` e `Quot.sound`; Analysis foi auditada separadamente.

Os totais de jobs Lake incluem dependências e replay de cache; não significam compilação limpa integral de cada dependência. Não foi usado um resultado numérico como premissa. `verify_evidence.py` confere os códigos de saída e hashes dos logs.
