# Próximos passos para retomada

1. Conferir `SESSION_STATE.md`, `git status --short --branch` e a ponta remota da branch `agent/sigma-c1-certified-20261105`.
2. Revisar o diff C1, rodar `git diff --check`, adicionar somente fontes, script, proveniência, licenças e evidências desta missão.
3. Commitar e publicar C1; registrar o SHA remoto e abrir PR contra `main`.
4. Verificar os checks da PR. O build local completo e focado passou; não declarar CI hospedado aprovado se nenhum workflow/check for apresentado. Integrar quando as condições da missão estiverem satisfeitas e confirmar o SHA remoto da `main`.
5. Criar uma branch nova a partir da `main` integrada para C1B. Demonstrar primeiro a identidade de bloco prefixo principal da `sigmaMatrix`; depois prolongar por zeros o vetor negativo de C1 e provar não-positividade semidefinida para toda dimensão maior.
6. Após publicar e integrar C1B, começar C2. Reusar o isolamento de altura 50 e a decomposição do resto para concluir negatividade eventual nos jets originais em `d=1/5`.
7. Após C2, transportar aos setores par e ímpar em C3. Deixar C4 por último.

Comandos focados reproduzíveis:

```bash
SIGMA_OUTPUT_DIR=/tmp/sigma-c1-certified-20261105 \
  research/native-moving-schur-sigma/compile_c1.sh
python3 research/native-moving-schur-sigma/check_c1_pins.py
lake build --wfail
```

O script C1 usa a toolchain fixada pela worktree, compila as fontes locais e portadas em saída temporária e lê artefatos externos de caches com versões/pins explícitos. A auditoria de 1.278 fontes não-Mathlib alcançáveis está registrada em `evidence/c1-source-pin-audit.txt`; o build focado não deve ser descrito como uma recompilação limpa de todas as dependências externas.

Antes de voltar a fontes das branches de pesquisa antigas, preservar seus caches e conferir a proveniência. Para uma futura exploração R2/TFVD, ler `docs/R2_TFVD_GREEN_VALVE_ROUTE.md` e manter C4 depois de C1–C3.
