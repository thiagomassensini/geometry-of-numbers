# Inventário de branches, worktrees e PRs

Inventário consultado em 2026-11-05. SHAs abaixo são remotos quando marcados `origin/*`; árvores locais sujas são apenas registradas e permanecem intocadas.

## geometry-of-numbers

- `origin/main` after C0: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`; Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

| Branch/PR | SHA remoto | Base / merge-base com `main` | Exclusivos da branch / main | Estado e resultado ainda fora de `main` |
|---|---|---|---:|---|
| `agent/native-moving-schur-sigma` | `9392ebac9930f5d11c56f595556080e8ab1de809` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 42 / 18 | PR #140 foi mesclada; 42 commits posteriores são divergentes e não têm PR aberta. Contém `SigmaZeroObstruction`, a recorrência/PDE e o resultado condicional ao zero. `SigmaZeroObstruction.lean` está ausente da `main`. Não integrar a branch inteira. |
| `agent/native-sigma-isolated-pole-radius` | `6194ca9ec646a506b5170010748b71e8fa62efef` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 66 / 18 | Nenhuma PR encontrada. Tem fatorização/isolation e módulos da rota Padé; arquivos de `SigmaZeroObstruction` também estão fora da `main`. Preservar a proveniência e selecionar somente dependências auditadas. |
| `agent/native-sigma-pade-signed-pencil` | `b7a7ca1f2a06faea539ee848bc5bdfa58507cb9c` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 59 / 18 | Nenhuma PR encontrada. Contém convergência Padé, decomposição de resto, pencil e modelo auxiliar. Resultados C2 ainda fora da `main`. |
| `agent/c3-critical-tilt-prime` | `7ff6e4b875dc1e9f4e9cddb4223bb31a7ea8044a` | MB `7578f935ab95a515fa2355de88a57204bb460cc2` | 8 / 24 | PR #146 foi mesclada; a ponta atual tem 8 commits adicionais sem PR aberta. Esses commits adicionam `CameraCoherence`, `HankelBilinearForm`, `HankelLimitObject`, `NativeBilinearForm`, `NativeLimitObject` e módulos de escala; ainda não estão na `main`. Usar só se necessário e auditar. |
| `agent/native-sixth-explicit-sigma` | `ab9959be3e103ca8dfc487e1512ce5ae8df18cda` | Base-tip/MB `ab9959be3e103ca8dfc487e1512ce5ae8df18cda` | 0 / 17 | PR #139 mesclada e ponta contida em `main`; resultado de curvatura/cauda já integrado. |
| `agent/native-critical-euler-balance`, `agent/native-local-sigma-positivity` | PR heads #141 `12caf30c310c25ca3459eafe27b9a477e71fd3ce`; #142 `00902b835841b622a37e643360930d32009ce57c` | PRs encadeadas após #140/#141 | verificadas por ancestralidade | PRs #141 e #142 mescladas; commits relevantes constam em `main`. Positividade all-order continua explicitamente aberta. |
| `codex/native-sigma-height50-checkpoint` | `353a7db22ca3b886ff111d0e61827784a4eb6053` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 71 / 18 | Nenhuma PR encontrada; a branch remota fixa Lean 4.32.0. O handoff Lean 4.35 só aparece na worktree local `/tmp/geometry-of-numbers-native-sigma-4.35`, na mesma base, com `lean-toolchain`, `lakefile.toml` e `lake-manifest.json` modificados; preservar e não confundir com a ponta remota. |
| `codex/native-sigma-height50-lean432-integrated` | `b9ce1955c1e8830afad2323afe5266ed3f5f35d9` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 72 / 18 | Nenhuma PR encontrada. Integração de altura 50 em Lean 4.32, útil como certificado para C2; não está na `main`. Ponta verificada no GitHub. |

As PRs #139, #140, #141 e #142 constam fechadas/mescladas, e seus SHAs de merge foram confirmados ancestrais de `origin/main`. PR #146 também está mesclada; o estado de sua ponta antiga não torna os 8 commits posteriores da branch atual parte da `main`.

O checkpoint C0 da branch `agent/sigma-allorder-negative-certified-20261105` foi integrado pela PR #153; o merge commit é `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`. A branch antiga permanece preservada.

A worktree C1 foi criada sobre `main@2a3e899…`; a prova C1 está no commit `c2706339b15db390bf8f5f50535016bd1aca8cb8`, integrado pela PR #154 no merge `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`. A CI hospedada `42101466137` passou.

C1B foi integrado pela PR #155 no merge `0586e238441096ecd2248e3f14bdac3a832af427`. O commit local de prova foi `8cc4a31`; não há publicação pendente desse checkpoint.

## carry-self-adjoint-operator

- `origin/main`: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; Lean 4.32.0; Mathlib `81a5d257…`.
- PR #107 `agent/material-boundary-source-sewing`: head `dc3a5cdb64a0c4dfccdfa2507bb1761bf520fe8e`, base `main@045369f6…`, 1 commit à frente, merge-base `045369f6…`; **aberta**, não mesclada.
- PR #108 `agent/critical-branch-native-audit`: head `bfeb10fd2425400fa38139903d12bf0599f02e53`, base `main@045369f6…`, 1 commit à frente, merge-base `045369f6…`; **aberta em rascunho**, não mesclada.
- PR #62 `agent/prime-depth-allorder-moment-bridge-2026-09-18`: head `90f4914b600e03db197db105c8acd4ef3ae0f417`, base `agent/publish-all-local-work-2026-09-18@8928a197b12a7627975d3b3a16295c4f88c6d3e3`, 39 commits exclusivos do head e 1 do base após MB `3cf2366910c75f950acc0ba492a67285c1e9c69d`; **aberta em rascunho**, não mesclada à `main`.
- `agent/native-jet-polynomial-pencil-20261103`: remoto `8f15ec76e5a95eb0c61da3a114729363a1d6a477`; worktree `/home/thlinux/native-jet-polynomial-pencil` está 2 commits atrás e contém dois Lean files não rastreados. Nenhuma PR identificada. Preservar; não usar como premissa de C4.
- Worktree raiz `/home/thlinux/carry-self-adjoint-operator`, branch `research/boundary-energy-e8-theta16` (`8f15ec76…`, 2 commits à frente), tem arquivos Theta16/TFVD modificados e não rastreados. Worktrees `carry-c2-source-raw-green` e `carry-finite-clock-jet-height` também estão sujas. Nenhuma foi tocada.
- O `lake-manifest.json` de `origin/main` fixa geometry em `d7cc54f5c485320f1fada33118e9e6101488819a` e CPFormal/primos em `65d50f6db1208708e109982ba97e1d51d3039956`, não nas `main`s atuais. Reconciliar pins antes de usar imports dessa cadeia.

## momentos

- `origin/main`: `05c9314d59306383baa55ed3be80ab950e799e97`; árvore limpa; repositório é usado aqui como validação numérica.
- PR #2 `research/sigma-pade-dimension-depth-20261104`: head `a2448545f98475f945abf2b02d81b078594697d7`, base `main@05c9314d…`, 12 commits à frente, merge-base `05c9314d…`; **aberta**, não mesclada. Resultados numéricos não são premissas do Lean.

## primos

- `origin/main`: `e2a723b4ec3e645539de0b9ca881951d93259cda`; Lean 4.32.0; Mathlib `81a5d257…`.
- PR #53 `docs/chat-2026-09-19-prime-depth-structural-record`: head `edda25d282d3432bfeeb827d29cd0dece07cef58`, base `main@e2a723b4…`, 2 commits à frente, merge-base `e2a723b4…`; **aberta**, documentação histórica.
- Worktree local `/home/thlinux/primos` está em `agent/release-v0.63.0-c3-carrier-gate`, 5 commits à frente de sua remota, com `CPFormal.lean` modificado e `CpCarryCriticalDressingCrosswalk.lean` não rastreado. Preservados; não representam `origin/main` nem foram usados.

## Regra de integração

Não fazer merges em massa. Para C1/C1B/C2/C3, integrar à `main` somente o código autocontido que passar build e auditoria, e registrar qualquer dependência de PR encadeada. C4 é secundário. Branches antigas permanecem para proveniência.
