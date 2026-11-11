# Checkpoint — TFVD/Bézout order compensation

- Fase atual: Checkpoint 0 concluído; iniciando a lei universal dos coeficientes.
- Commit-base (`origin/main`, 2026-11-10): `8f5631a7808ad7c73491b558a894566e1d39899c`.
- Branch isolada: `agent/tfvd-bezout-order-compensation-20261110` (worktree dedicado).
- Árvore original preservada: havia itens não rastreados `GeometryOfNumbers/Analysis/IntegerMomentGramPositivity.lean` e `research/entrywise-moment-square/`; nenhum foi alterado.
- Pins: Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- PRs #41, #69, #70, #143, #144 e #145 confirmadas integradas; arquivos e relatórios de pesquisa estão no `main`.
- Reuso principal: `research/tfvd-bezout-schur-residual/SourceBezout.lean`, `KernelBudget.lean`, `SourceMap.lean`, `SourceBlocks.lean`, `SourceSchur.lean`, `LiteralTfvd.lean`, `Repartition.lean`, `NativeRepartition64.lean`.
- Fórmula inicial: `CarrySourceBezout.mixed_kernel_coefficient`, especializada à mesma sequência; evitar reconstruir o kernel ou importar os gates de sinal C3.
- Comandos de reconhecimento: `git status --short`, `git branch --show-current`, `git remote -v`, `git fetch origin`, `git rev-parse origin/main`; PRs consultadas no GitHub.
- Teoremas novos: nenhum ainda.
- Validações: reconhecimento concluído; ainda sem compilação de arquivos novos.
- Falhas/dificuldades: o worktree novo não contém `.lake` nem caches privados; validação deverá apontar ao cache Lean já usado pelas pesquisas sem modificar a árvore preexistente.
- Próximo passo exato: formalizar as duas fórmulas explícitas do coeficiente de `sourceKernel` e extrair o update em `c_(2n+s+1)`.
- Obrigações matemáticas abertas: dependência triangular, atualização de posto um, determinante bordeado sem inversa, limiar de Schur e transporte TFVD.
- Sinal: nenhum resultado de positividade nova alegado; os sinais theta da PR #144 não serão premissas dos gates C3 geométricos.
