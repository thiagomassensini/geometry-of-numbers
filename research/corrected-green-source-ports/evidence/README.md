# Evidências

`validation.log` registra o resultado de cada etapa; `validation.json` inclui
hashes dos logs. `source-manifest.json` fixa os commits de proveniência, o
toolchain e os hashes das sete fontes Lean verificadas.

`Audit.log` registra `#print axioms` dos 50 nomes públicos novos. Cada root
também é submetido ao guard transitivo que visita tipos e corpos. O footprint
permitido em Analysis é `propext`, `Classical.choice`, `Quot.sound`.

Os logs completos do build raiz e das três auditorias de zona são publicados
com compressão gzip determinística. Logs individuais vazios dos módulos
correspondem a compilações bem-sucedidas e silenciosas; os seus hashes constam
do JSON. A rodada completa é reproduzida por:

    bash research/corrected-green-source-ports/audit-corrected-green-source-ports.sh

As fontes desta rodada são recompiladas. Os imports inalterados
`CanonicalComparison.olean` e os módulos do PR #24 vêm de caches anteriormente
compilados. O script confere suas fontes e os pins compartilhados; não se
anuncia recompilação fresca dessas dependências.

Os resultados são finitos: realização física exata de jets 0..6. A extensão
geral retém a estimativa de retorno como hipótese, sem tratá-la como provada.
