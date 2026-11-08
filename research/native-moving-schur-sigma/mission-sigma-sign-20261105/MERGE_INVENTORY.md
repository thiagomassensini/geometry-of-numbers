# Inventário de branches, worktrees e PRs

Inventário consultado em 2026-11-05. SHAs abaixo são remotos quando marcados `origin/*`; árvores locais sujas são apenas registradas e permanecem intocadas. A tabela retrata o inventário anterior aos merges C0–C3; os checkpoints integrados mais recentes estão registrados após ela.

## geometry-of-numbers

- `origin/main` after C0: `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`; Lean 4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

| Branch/PR | SHA remoto | Base / merge-base com `main` | Exclusivos da branch / main | Estado e resultado ainda fora de `main` |
|---|---|---|---:|---|
| `agent/native-moving-schur-sigma` | `9392ebac9930f5d11c56f595556080e8ab1de809` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 42 / 18 | PR #140 foi mesclada; 42 commits posteriores são divergentes e não têm PR aberta. Contém `SigmaZeroObstruction`, a recorrência/PDE e o resultado condicional ao zero. `SigmaZeroObstruction.lean` está ausente da `main`. Não integrar a branch inteira. |
| `agent/native-sigma-isolated-pole-radius` | `6194ca9ec646a506b5170010748b71e8fa62efef` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 66 / 18 | Nenhuma PR encontrada. Tem fatorização/isolation e módulos da rota Padé; arquivos de `SigmaZeroObstruction` também estão fora da `main`. Preservar a proveniência e selecionar somente dependências auditadas. |
| `agent/native-sigma-pade-signed-pencil` | `b7a7ca1f2a06faea539ee848bc5bdfa58507cb9c` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 59 / 18 | No snapshot de 2026-11-05, nenhuma PR havia sido encontrada; a tabela registrava os resultados C2 ainda fora da `main`. A closure selecionada foi integrada depois pela PR #157; a branch inteira permanece sem merge. |
| `agent/c3-critical-tilt-prime` | `7ff6e4b875dc1e9f4e9cddb4223bb31a7ea8044a` | MB `7578f935ab95a515fa2355de88a57204bb460cc2` | 8 / 24 | PR #146 foi mesclada; a ponta atual tem 8 commits adicionais sem PR aberta. Esses commits adicionam `CameraCoherence`, `HankelBilinearForm`, `HankelLimitObject`, `NativeBilinearForm`, `NativeLimitObject` e módulos de escala; ainda não estão na `main`. Usar só se necessário e auditar. |
| `agent/native-sixth-explicit-sigma` | `ab9959be3e103ca8dfc487e1512ce5ae8df18cda` | Base-tip/MB `ab9959be3e103ca8dfc487e1512ce5ae8df18cda` | 0 / 17 | PR #139 mesclada e ponta contida em `main`; resultado de curvatura/cauda já integrado. |
| `agent/native-critical-euler-balance`, `agent/native-local-sigma-positivity` | PR heads #141 `12caf30c310c25ca3459eafe27b9a477e71fd3ce`; #142 `00902b835841b622a37e643360930d32009ce57c` | PRs encadeadas após #140/#141 | verificadas por ancestralidade | PRs #141 e #142 mescladas; commits relevantes constam em `main`. Positividade all-order continua explicitamente aberta. |
| `codex/native-sigma-height50-checkpoint` | `353a7db22ca3b886ff111d0e61827784a4eb6053` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 71 / 18 | Nenhuma PR encontrada; a branch remota fixa Lean 4.32.0. O handoff Lean 4.35 só aparece na worktree local `/tmp/geometry-of-numbers-native-sigma-4.35`, na mesma base, com `lean-toolchain`, `lakefile.toml` e `lake-manifest.json` modificados; preservar e não confundir com a ponta remota. |
| `codex/native-sigma-height50-lean432-integrated` | `b9ce1955c1e8830afad2323afe5266ed3f5f35d9` | MB `8e0f88ca489a85a32fe15725de62f9840de95a75` | 72 / 18 | No snapshot de 2026-11-05, nenhuma PR havia sido encontrada e a ponta não estava na `main`. A integração 4.32 serviu de referência para C2; os módulos necessários foram selecionados e integrados depois pela PR #157. A branch inteira não foi mesclada. |

As PRs #139, #140, #141 e #142 constam fechadas/mescladas, e seus SHAs de merge foram confirmados ancestrais de `origin/main`. PR #146 também está mesclada; o estado de sua ponta antiga não torna os 8 commits posteriores da branch atual parte da `main`.

O checkpoint C0 da branch `agent/sigma-allorder-negative-certified-20261105` foi integrado pela PR #153; o merge commit é `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`. A branch antiga permanece preservada.

A worktree C1 foi criada sobre `main@2a3e899…`; a prova C1 está no commit `c2706339b15db390bf8f5f50535016bd1aca8cb8`, integrado pela PR #154 no merge `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`. A CI hospedada `42101466137` passou.

C1B foi integrado pela PR #155 no merge `0586e238441096ecd2248e3f14bdac3a832af427`. O commit local de prova foi `8cc4a31`; não há publicação pendente desse checkpoint.

C2 foi integrado pela PR #157, com commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9` e merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. A PR não retornou status checks hospedados; compilação Lean 4.32 e auditorias de axiomas locais estão registradas em `evidence/c2-eventual-negativity/`.

C3 foi integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. A closure 4.32, as torres par/ímpar e as evidências estão em `evidence/c3-parity/`. O GitHub não retornou status checks; C2/C3 estão concluídos.

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

Não fazer merges em massa. Para C1/C1B/C2/C3/C4, integrar à `main` somente o código autocontido que passar build e auditoria, e registrar qualquer dependência de PR encadeada. Branches antigas permanecem para proveniência.

## Atualização após C4 (2026-11-06)

O inventário acima é o snapshot anterior aos merges C0–C3; esta atualização registra as mudanças posteriores sem reescrever os estados históricos das worktrees alheias.

- `origin/main` contém C4 pela PR #162: branch `codex/sigma-c4-source-bezout-20261106`, commit de prova `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge `799a0e06af5469e9fe0665943adbb1cb29d0b6f8`.
- A observação da tabela histórica de que `SigmaZeroObstruction.lean` estava ausente da `main` descrevia o snapshot de 2026-11-05. O módulo e a closure C1/C2 necessários foram incorporados pelas PRs #154 e #157; não está ausente da `main` atual.
- O estado pós-C4 foi integrado pela PR #163, merge `13f4b6f509c090344d7dc41213f83018f3bdcc69`. A ponta de `origin/main` observada nesse snapshot é esse commit.
- Na observação pós-PR #163, a worktree `/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main` estava no branch local `codex/c4-state-merged-20261106`, commit `9138be9e110354878487719696a697e65a74463a`, head da PR #163. Os únicos itens não rastreados então observados eram o symlink local `.lake` e caches de compilação sob `research/native-moving-schur-sigma/.cache/`; foram preservados e não incluídos nos commits.
- As duas worktrees de tentativa 4.35 em `/tmp` aparecem agora como `prunable` porque seus gitdirs temporários não existem. O conteúdo necessário à retomada segue versionado em `evidence/lean435-validation-incomplete/` (overlays/patches, pins, manifests, logs e README com o último erro e comandos). Nenhuma tentativa foi recriada nem os checkpoints removidos.
- PRs #153–#163 relevantes à missão foram consultadas no GitHub e estão mescladas: C0 #153, C1 #154, C1B #155, checkpoint 4.35 #156, C2 #157, C3 #159, atualizações de estado #160/#161/#163 e C4 #162. Os SHAs de merge correspondentes constam em `SESSION_STATE.md`, `CHECKPOINTS.md` e nos registros de validação.
- A tabela inicial registra o estado anterior aos merges C0–C3. Em particular, suas observações de que a fonte de altura 50 e os resultados C2 estavam fora da `main` descrevem aquele snapshot, não o estado atual após a PR #157. O commit de referência `b9ce1955c1e8830afad2323afe5266ed3f5f35d9` continua preservado para proveniência, enquanto a closure C2 necessária está na `main`.

## Atualização após PR #202 e revalidação C2/C3 (2026-11-06)

- A base de origin/main conferida foi 935911bce2c253ee508a4990face113ea63c87ee. As integrações C1B (#155), C2 (#157) e C3 (#159) continuam presentes e sem publicação pendente.
- C2 e C3 foram recompilados focadamente em Lean 4.32; a auditoria transitiva atual percorreu 133 roots e 70.861 dependências. Os detalhes e logs estão em evidence/c2-c3-post-reboot-20261106/.
- As worktrees 4.35 em /tmp realmente não sobreviveram ao reinício. O checkpoint publicado preserva os overlays, patches, pins, manifests e logs. O README foi atualizado com reconstrução a partir da base 353a7db22ca3b886ff111d0e61827784a4eb6053; o scheduler agora recebe os caminhos Geometry, Carry, saída e Lean por variáveis de ambiente.

## Atualização após PR #220 e revalidação C2/C3 (2026-11-07)

- `origin/main` foi conferida em `08a413f34dd5588ed3d021351af27f3f55e0c072`. C1B (#155, merge `0586e238441096ecd2248e3f14bdac3a832af427`), C2 (#157) e C3 (#159) continuam presentes; não existe publicação pendente dessas entregas.
- C2/C3 recompilaram em Lean 4.32 nessa revisão. A auditoria transitiva repetida percorreu 133 raízes e 70.861 dependências, somente com axiomas padrão. A evidência desta execução está em `evidence/c2-c3-priority-20261107/`.
- O checkpoint 4.35 segue durável na `main`, com overlays, patches, pins, manifests, logs/erro e comandos de reconstrução em `evidence/lean435-validation-incomplete/`. Ele permanece explicitamente incompleto. A rota 4.32 publicada continua sendo a referência para C2; não se iniciou migração geral de Geometry/Carry.

## Atualização após PR #235 e reinício da VM (2026-11-07)

- `origin/main` foi conferida em `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1`. As integrações C1B (#155, merge `0586e238441096ecd2248e3f14bdac3a832af427`), C2 (#157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`) e C3 (#159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`) continuam ancestrais da `main`.
- O checkpoint de overlays/logs/pins 4.35 foi publicado e mesclado pela PR #221, merge `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`. Ele conserva a tentativa como incompleta; a rota C2 4.32 não tem bloqueio identificado.
- Após a ampliação de memória, C2/C3 recompilaram e passaram pelos verificadores Lean 4.32. A auditoria transitiva encontrou 133 raízes e 70.861 dependências, apenas com axiomas padrão. Fontes, logs e comandos estão em `evidence/c2-c3-current-main-20261107/`; os hashes das fontes coincidem com `origin/main` em `b604c06`.

## Atualização pós-PR #241 (2026-11-07)

- `origin/main@24f61b01732f44599869350c4bf675c3f3a3dcb6` contém as integrações C1B (#155, merge `0586e238441096ecd2248e3f14bdac3a832af427`), C2 (#157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`), C3 (#159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`) e o checkpoint explicitamente incompleto 4.35 (#221, merge `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`). A reconciliação anterior dos registros foi integrada pela PR #241, merge `24f61b01732f44599869350c4bf675c3f3a3dcb6`.
- A revalidação C2/C3 arquivada em Lean 4.32 continua aplicável: os cinco módulos auditados não mudaram entre seu snapshot compilado (`b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1`) e a revisão atual. A rota C2 usa a integração publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`; não há bloqueio que justifique retomar a migração geral 4.35.


## Estado integrado conferido após a PR #288 — 2026-11-07

A ponta consultada é origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8. C1B (#155, merge 0586e238441096ecd2248e3f14bdac3a832af427), C2 (#157, merge f4f5cf5ecc60ea3747cbaf21389fab52832d3949), C3 (#159, merge b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8) e o checkpoint Lean 4.35 incompleto (#221, merge c67b2f72e0ad2f331c0966fb3ed82e98655e3df8) já estão publicados na main. Nenhuma entrega C1B/C2/C3 está pendente.

Os cinco módulos C2/C3 foram recompilados diretamente a partir dessa ponta em Lean 4.32 com warningAsError. Os verificadores C2/C3 aceitaram o corolário e os quatro relatórios públicos usando somente propext, Classical.choice e Quot.sound; SigmaPadeAudit refez a auditoria de 133 raízes públicas e 70.861 dependências. Os logs atuais estão em evidence/c2-c3-live-main-20261107/build-logs/; os logs pós-reinício anteriores permanecem preservados em evidence/c2-c3-current-main-20261107/.

A integração Lean 4.32 no commit b9ce1955c1e8830afad2323afe5266ed3f5f35d9 continua sendo a primeira referência C2 e não mostrou impedimento. A prova conserva o resto e as definições originais, sem hipótese de sinal adicional. A tentativa 4.35 continua somente como checkpoint incompleto; patches, logs, pins, erro mais recente e comandos de retomada estão preservados no checkpoint publicado #221.

## Reconciliação após retomada — 2026-11-08

O inventário de PRs e integrações C1B/C2/C3 permanece válido no snapshot de código `ebd6c57c33edcf8596f09889c7bf956e7d9b284f`; a reconciliação documental foi integrada depois pela PR #307, merge `898e1ca03b8f1121cb3d699c3dfb7bcfc8ef3a5a`. A validação 4.32 de `78a10e8af611a5c690b248f8889b9e87674fd5c8` continua aplicável: nenhuma fonte Lean preexistente da closure C2/C3 mudou entre aquelas revisões; a auditoria registrou 133 raízes e 70.861 dependências. O checkpoint incompleto 4.35 da PR #221 continua versionado. Checksums e evidência da conferência estão em `evidence/c2-c3-priority-resume-20261108/VALIDATION.md`.
