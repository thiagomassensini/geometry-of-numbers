# Evidências da direção crítica física

`validation.json` registra o resultado e os hashes dos logs. `source-manifest.json` fixa a base, o checkout consultado do operador, a toolchain e os hashes dos sete módulos Lean.

`Audit.log` contém `#print axioms` das 57 declarações públicas, com guards transitivos que visitam tipos e corpos. Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos.

Os logs comprimidos registram o build raiz `--wfail` e as auditorias Foundation, Geometry e Analysis. Logs de módulos vazios representam compilações silenciosas bem-sucedidas.

Os módulos novos são recompilados. Dependências históricas vêm de caches anteriormente compilados, com fontes, commits e pins conferidos. Não se anuncia recompilação fresca de todas essas dependências.

Reprodução:

    bash research/critical-source-return/audit-critical-source-return.sh

A realização da direção crítica, seu limite e a margem do quinto teste par estão provados. A desigualdade integral do quinto teste ímpar é um alvo equivalente, ainda sem certificado de sinal.
