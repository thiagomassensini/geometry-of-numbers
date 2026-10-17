# Evidências

`validation.log` registra a execução completa do script dedicado. `validation.json`
identifica os nove módulos e hashes dos logs; `Audit.log` contém as guardas
transitivas de tipos/corpos e `#print axioms` dos 88 roots novos.

Os logs completos de `lake build --wfail` e das três auditorias de zona são
preservados em gzip determinístico. Os logs de módulos sem mensagens são
artefatos locais, com seus hashes registrados no JSON.

`source-manifest.json` identifica os commits dos checkouts, a versão do Lean e
os hashes exatos dos arquivos Lean novos. O HEAD de geometry registrado pode
anteceder o commit da tarefa; os hashes vinculam os fontes efetivamente
compilados. Os pins compartilhados e o HEAD fixo do operador são conferidos
pelo script. A dependência preexistente `CanonicalComparison.olean` é reutilizada
após verificar que seu fonte não mudou contra `21115c7`.

Empacotamento após término com sucesso:

    python3 research/prime-camera-schur/package_evidence.py --validation-log /tmp/carry-prime-camera-validation.log

O build padrão não inclui estes módulos de `research/`: a compilação dedicada,
com avisos como erros, é indispensável. Analysis usa somente `propext`,
`Classical.choice` e `Quot.sound`; não se anuncia ausência de todos os axiomas.
