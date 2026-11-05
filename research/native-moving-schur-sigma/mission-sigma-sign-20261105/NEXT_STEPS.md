# Próximos passos para retomada

1. Revisar a mudança C1B em `SigmaPersistentNegativeDirection.lean`, o script de compilação, os documentos e as evidências; confirmar `git diff --check`.
2. O commit local `8cc4a31` já contém somente esses arquivos. Publicar a branch `agent/sigma-c1b-persistent-negative-20261105` e abrir PR contra `main`.
3. Aguardar e conferir a CI hospedada da PR C1B. Integrar quando os gates passarem e registrar o merge SHA e o run.
4. Iniciar C2 em branch separada sobre a `main` integrada: compor a decomposição exata do resto, o limite Padé e o isolamento certificado de altura 50 para provar a negatividade eventual dos menores originais em `d=1/5`.
5. Após C2, concluir C3 para `s=0` e `s=1`, com índices explícitos `k=2i` e `k=2i+1`; usar C1B para prolongar as direções em dimensões maiores.
6. Investigar C4 por último, mantendo explícito o fator 2 da fonte deslocada e os canais da costura Bézout.

Build focado reproduzível para C1+C1B:

```bash
SIGMA_OUTPUT_DIR=/tmp/sigma-c1b-persistent-20261105 \
  research/native-moving-schur-sigma/compile_c1.sh
```

O script compila em Lean 4.32.0, confere os pins e recompila as fontes locais relevantes, os módulos portados e o fechamento mínimo do certificado do primeiro zero. Dependências Lean/Mathlib/Carry externas são lidas de checkouts e caches versionados; este build focado não é uma reconstrução limpa de toda a árvore externa. A auditoria de 1.278 módulos não-Mathlib está registrada em `evidence/c1-source-pin-audit.txt`.
