# Evidências

`validation.log` registra as etapas concluídas e `validation.json` os hashes
dos logs. `source-manifest.json` fixa os commits consultados, toolchain e hashes
das oito fontes Lean verificadas.

`Audit.log` contém `#print axioms` dos 66 nomes públicos novos, submetidos
também ao guard transitivo que visita tipos e corpos. A política Analysis
permite somente `propext`, `Classical.choice`, `Quot.sound`. O teste fechado
`eighthDiscriminant_rectangle_check` é uma redução inteira pelo kernel.

Build raiz e auditorias de zona são preservados com gzip determinístico.
Logs individuais vazios indicam compilações silenciosas bem-sucedidas; seus
hashes constam no JSON. Reprodução:

    bash research/return-block-compatibility/audit-return-block-compatibility.sh

Os módulos novos são recompilados. Dependências inalteradas dos PRs #23–25
e `CanonicalComparison.olean` vêm dos caches anteriormente compilados, com
fontes e pins conferidos. Não se anuncia recompilação fresca dessas dependências.

O novo limite incondicional é de oito fontes; a torre de ordem arbitrária
preserva expressamente a hipótese de estimativas do retorno em cada ordem.
