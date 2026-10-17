# Evidências

`source-manifest.json` fixa a base, o operador consultado, a toolchain e os hashes dos oito módulos Lean. `validation.json` registra os resultados e os hashes dos logs.

`Audit.log` reúne os axiomas das 75 declarações públicas. Todas passaram pelo guard transitivo que visita tipos e corpos; somente `propext`, `Classical.choice` e `Quot.sound` são permitidos. As verificações fechadas de intervalos usam `decide +kernel`; não há certificado de sinal baseado apenas em avaliação nativa.

Os logs comprimidos contêm o build raiz `--wfail` e as auditorias Foundation, Geometry e Analysis. Logs individuais vazios indicam compilações silenciosas bem-sucedidas.

As dependências históricas usam seus caches compilados, com fontes, commits e pins conferidos. Todos os módulos novos são recompilados. Não se anuncia compilação fresca de todas as dependências anteriores.

Reprodução:

    bash research/theta-fifth-odd-pattern/audit-theta-fifth-odd-pattern.sh

O certificado positivo alcança dez fontes. A escolha comum crescente de modos e as estimativas de cauda valem em ordem arbitrária; a positividade da diferença completa de Schur em toda ordem permanece aberta.
