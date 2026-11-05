# Evidência do C0 — consulta de estado em 2026-11-05

## Cabeças e toolchain

```text
geometry-of-numbers origin/main: 21b3dacefbfcbd6c5d648bc2bada32c67d46145c
carry-self-adjoint-operator origin/main: 045369f6dedcb2e75e9aefed1d12c9f73b9a2532
primos origin/main: e2a723b4ec3e645539de0b9ca881951d93259cda
momentos origin/main: 05c9314d59306383baa55ed3be80ab950e799e97
Lean usado pela worktree nova: 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
GreenFrame: cd2d838bee67ad23f869a02f8ed9f0a0feb926fa
MemAvailable após reinício: 54,386,116 kB
```

## Worktrees relevantes do geometry-of-numbers

```text
/home/thlinux/geometry-of-numbers
  branch agent/tfvd-bezout-schur-residual @ 4103131555dd4b17042a3502aca4e2d78ec62627
  preexistentes: GeometryOfNumbers/Analysis/IntegerMomentGramPositivity.lean não rastreado;
  research/entrywise-moment-square/ não rastreado.

/home/thlinux/geometry-of-numbers-native-moving-schur-sigma
  branch agent/native-moving-schur-sigma @ 9392ebac9930f5d11c56f595556080e8ab1de809
  sem mudanças rastreadas; caches e logs de validação não rastreados.

/home/thlinux/worktrees/geometry-of-numbers-native-sigma-isolated-pole-radius
  branch codex/native-sigma-height50-lean432-integrated @ b9ce1955c1e8830afad2323afe5266ed3f5f35d9
  somente research/native-moving-schur-sigma/.cache/ não rastreado.

/home/thlinux/worktrees/geometry-of-numbers-native-sigma-pade-signed-pencil
  branch agent/native-sigma-pade-signed-pencil @ b7a7ca1f2a06faea539ee848bc5bdfa58507cb9c
  somente research/native-moving-schur-sigma/.cache/ não rastreado.

/tmp/geometry-of-numbers-native-sigma-4.35
  branch local codex/native-sigma-height50-lean435 @ 353a7db22ca3b886ff111d0e61827784a4eb6053
  lean-toolchain, lakefile.toml e lake-manifest.json modificados localmente; preservados.

/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
  branch agent/sigma-allorder-negative-certified-20261105 @ 21b3dacefbfcbd6c5d648bc2bada32c67d46145c
  limpa na criação; base remota origin/main.
```

Também foram listadas as worktrees restantes dos quatro repositórios. Elas contêm caches/logs não rastreados e, em alguns casos, fontes/documentos locais não publicados; nenhum desses arquivos foi modificado por este C0. Ver `MERGE_INVENTORY.md` para os estados materiais de geometry, carry e primos.

## GitHub

- PR da missão #153 aberta: head `5ad667a06007ac3d56a5b208473e01dcabcb5c64`, base `main@21b3dace…`; contém apenas os sete documentos C0. O endpoint de status retornou `statuses: []` e o endpoint de workflow retornou `workflow_runs: []`; não há CI aprovado reportado.
- Geometry PRs #139, #140, #141 e #142: fechadas e mescladas; merge SHAs verificados como ancestrais da `origin/main` atual.
- Geometry PR #146: fechada/mesclada; a branch atual `agent/c3-critical-tilt-prime` tem 8 commits após a base integrada e diverge da `main`.
- Carry PR #107: aberta; #108: aberta em draft; #62: aberta em draft e empilhada em base que não é `main`.
- Momentos PR #2: aberta, dados de validação numérica.
- Primos PR #53: aberta, documentação histórica.
- Não foram encontradas PRs para as branches de integração de altura 50, isolamento de polo e pencil Padé.

## Comparações de branches geométricas com `origin/main`

```text
agent/native-moving-schur-sigma: 42 exclusivos / main 18 exclusivos; MB 8e0f88ca489a85a32fe15725de62f9840de95a75
agent/native-sigma-isolated-pole-radius: 66 / 18; MB 8e0f88ca489a85a32fe15725de62f9840de95a75
agent/native-sigma-pade-signed-pencil: 59 / 18; MB 8e0f88ca489a85a32fe15725de62f9840de95a75
agent/c3-critical-tilt-prime: 8 / 24; MB 7578f935ab95a515fa2355de88a57204bb460cc2
codex/native-sigma-height50-checkpoint: 71 / 18; MB 8e0f88ca489a85a32fe15725de62f9840de95a75
codex/native-sigma-height50-lean432-integrated: 72 / 18; MB 8e0f88ca489a85a32fe15725de62f9840de95a75
agent/native-sixth-explicit-sigma: 0 / 17; branch-tip ab9959be3e103ca8dfc487e1512ce5ae8df18cda é ancestral da main.
```

## Observação sobre a toolchain

O `lean` global do shell resolve para Lean 4.35.0, mas `elan run leanprover/lean4:v4.32.0 lean --version` confirma a toolchain 4.32.0 instalada. Build da missão deve chamar a versão pinada e compilar a partir de fontes/cache 4.32; nenhum `.olean` 4.35 será usado.
