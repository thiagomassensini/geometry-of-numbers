# Checkpoints

## C0 — recuperação, inventário e ambiente (2026-11-05)

**Estado:** documentação do inventário publicada no commit `5ad667a06007ac3d56a5b208473e01dcabcb5c64`; PR #153 aberta contra `main`. Nenhum status check/workflow foi retornado pelo GitHub; CI não declarado aprovado.

- A worktree original `agent/native-moving-schur-sigma` foi localizada em `/home/thlinux/geometry-of-numbers-native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, remoto coincidente. Não há mudanças rastreadas, mas há caches e logs de validação não rastreados; todos foram preservados.
- A integração Lean 4.32 de altura 50 está em `/home/thlinux/worktrees/geometry-of-numbers-native-sigma-isolated-pole-radius`, HEAD/remoto `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, com apenas `.cache/` não rastreado. A worktree Padé está em `/home/thlinux/worktrees/geometry-of-numbers-native-sigma-pade-signed-pencil`, HEAD/remoto `b7a7ca1f2a06faea539ee848bc5bdfa58507cb9c`, também com apenas cache não rastreado.
- O SHA remoto atual de `main` é `21b3dacefbfcbd6c5d648bc2bada32c67d46145c`. A branch sugerida pela missão não existia; foi criada uma worktree limpa sobre essa base: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`, branch `agent/sigma-allorder-negative-certified-20261105`.
- Todos os quatro repositórios e suas worktrees foram inventariados. Modificações e arquivos não rastreados preexistentes em geometry, carry e primos estão descritos em `MERGE_INVENTORY.md`; nenhum foi alterado.
- Geometry, carry e primos usam Lean 4.32.0 e Mathlib `81a5d257…`; a toolchain 4.32 está instalada. O shell fora da worktree escolhe Lean 4.35 por padrão; a compilação deve respeitar o pin de cada projeto.
- C0 não executa Lean, pois não altera prova. A evidência do inventário e os estados de PR estão em `evidence/c0-inventory.md`.

## C1 — direção negativa finita para todo deslocamento pequeno

**Aberto.** Há um teorema condicional existente em `SigmaZeroObstruction.lean`; falta compor um zero positivo certificado com a ponte exata para `completedNativeOperatorCharacteristic` sem ampliar desnecessariamente a dependência de altura 50.

## C1B — persistência em dimensões maiores

**Aberto.** Falta formalizar a incorporação por bloco principal/prefixo e prolongar por zeros a direção negativa, na matriz `sigmaMatrix` original.

## C2 — menores Padé originais eventualmente negativos em `d = 1/5`

**Aberto.** Há lemas gerais de convergência dos menores normalizados e de sinal eventual na branch Padé; o insumo de isolamento formal está na integração de altura 50 não mesclada. Compor esses lemas sem substituir `completedSigmaLogJet` por `twoPoleMoment`.

## C3 — setores par e ímpar

**Aberto.** Transportar a negatividade eventual de `D_k(1/5)` às janelas `k=2i` e `k=2i+1`, então prolongar a direção negativa para dimensões maiores de cada torre.

## C4 — fonte deslocada e Bézout

**Não iniciado; exploratório.** Verificar o fator 2 na recorrência da série do produto deslocado e manter separados os canais físicos/TFVD. Não atrasar C1–C3.
