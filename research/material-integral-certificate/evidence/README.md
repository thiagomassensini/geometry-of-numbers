# Evidências do certificado integral

- `validation.log`: saída da execução completa do script dedicado, copiada somente após seu término bem-sucedido.
- `build-results.json`: módulos aprovados, comando efetivo e hashes dos logs individuais. Os logs vazios correspondem a compilações sem mensagens.
- `Audit.log`: guardas transitivas e `#print axioms` das 221 declarações públicas, seguidos dos tipos dos principais teoremas incondicionais.
- `root-build.log`: `lake build --wfail`; o build padrão não inclui automaticamente estes módulos de `research/`.
- `foundation-audit.log`, `geometry-audit.log`, `analysis-audit.log`: políticas de axiomas das três zonas.
- `source-manifest.json`: hashes SHA-256 dos arquivos Lean efetivamente validados, versão do Lean e commits dos dois checkouts consultados.

O HEAD de `geometry-of-numbers` registrado no manifesto é o commit existente no momento de consolidação da validação. Os hashes individuais identificam exatamente as fontes Lean compiladas. O checkout do operador foi somente consultado, com seu HEAD fixado e pins comuns idênticos.

A execução registrada reutiliza os artefatos já conferidos das dependências dos PRs #21/#22 e verifica que suas fontes estão inalteradas contra `0ec56d5`. Recompila todos os módulos novos. Para reconstruir também essas dependências, executar o script sem `CARRY_INTEGRAL_REUSE_PR22=1`.

Os arquivos `witness-*.json` e `regenerated-*.lean` produzidos pela reprodução são artefatos locais ignorados: o script exige igualdade literal com as tabelas publicadas. Essas tabelas são testemunhas não confiadas; os teoremas de verificação calculam todas as entradas no kernel. Não se usa `native_decide` para estabelecer as inclusões ou o sinal do pivô.

Depois da execução, o pacote de evidências pode ser refeito com:

```bash
python3 research/material-integral-certificate/package_evidence.py \
  --validation-log /tmp/carry-integral-full-validation.log --reuse-pr22
```

A análise permite os axiomas usuais `propext`, `Classical.choice` e `Quot.sound`; não se afirma ausência de todos os axiomas.
