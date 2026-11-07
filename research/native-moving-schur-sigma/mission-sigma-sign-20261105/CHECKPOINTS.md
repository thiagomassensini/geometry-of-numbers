# Checkpoints

## C0 — recuperação, inventário e ambiente (2026-11-05)

**Estado:** concluído e integrado pela PR #153. O merge commit da `main` é `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`. O checkpoint C0 tratou apenas documentação; nenhum build Lean foi requisito para aquela entrega.

- A worktree original `agent/native-moving-schur-sigma` foi localizada e preservada, assim como os checkouts separados de altura 50 e Padé.
- O inventário de branches e PRs dos quatro repositórios está em `MERGE_INVENTORY.md`; as alterações locais existentes foram registradas e não foram alteradas.
- A PR #153 foi mesclada depois de ficar limpa e mergeable; nenhum status check foi retornado para o commit de documentação.

## C1 — direção negativa finita para todo deslocamento pequeno

**Estado:** integrado pela PR #154; CI hospedado concluído com sucesso.

Teorema concluído:

```lean
CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0
```

- Parte do certificado `HardyFirstZero.first_zero_on_line`, transporta o zero da zeta para `completedNativeCharacteristicContinuation` pela equivalência no strip, usa `completedNativeCharacteristicContinuation_eq_native` somente dentro do strip e aplica o teorema condicional existente `exists_sigmaMatrix_negative_direction_of_zero`.
- A conclusão usa a `sigmaMatrix` original e mantém a quantificação sobre todo `0 < |d| < 1/4`.
- Não conclui persistência para todos os tamanhos maiores; isso pertence a C1B.
- Build raiz: um build completo em worktree sem cache terminou com sucesso em 8.857/8.857 jobs. O log versionado registra também uma execução posterior com cache aquecido: `evidence/c1-root-build.log`.
- Build focado Lean 4.32, warnings-as-errors: `evidence/c1-focused-build.log`.
- Axiomas do corolário e do primeiro zero: somente `propext`, `Classical.choice`, `Quot.sound`. O checker aceitou 106 relatórios; nenhuma ocorrência de `sorryAx`, `sorry`, `admit`, `native_decide` ou axioma customizado foi encontrada nos fontes C1.
- Auditoria recursiva de proveniência: 1.278 módulos-fonte não-Mathlib alcançáveis conferem com os pins registrados em `evidence/c1-source-pin-audit.txt`.
- Proveniência completa: `evidence/c1-source-provenance.md`; hashes: `evidence/c1-source-sha256.txt`.
- Commit da prova: `c2706339b15db390bf8f5f50535016bd1aca8cb8`; PR #154; merge commit `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`.
- A execução hospedada `42101466137` passou pelo build padrão com warnings-as-errors e pelos alvos de auditoria formal.

## C1B — persistência em dimensões maiores

**Integrado pela PR #155**, merge `0586e238441096ecd2248e3f14bdac3a832af427`.

- `sigmaMatrix_prefix_submatrix` prova que a seção de tamanho `N` é exatamente a submatriz principal prefixo da seção de tamanho `M≥N`.
- `Matrix.PosSemidef.submatrix` mostra que a semidefinição positiva da seção maior implicaria a da seção menor, contradizendo a direção negativa de C1.
- `certified_sigma_negative_directions_persist` conclui uma direção negativa em cada dimensão suficientemente grande; `certified_sigma_not_posSemidef_persist` registra diretamente a não semidefinição positiva eventual.
- A prova usa `sigma_matrix_symm` para converter a falha de `PosSemidef` em um vetor real com forma quadrática estritamente negativa. Não afirma crescimento do índice negativo nem que todos os pivôs sejam negativos.
- O build focado C1/C1B recompilou a cadeia Lean 4.32 e aceitou 109 relatórios de axiomas padrão. Ver `evidence/c1b-focused-build.log`, `evidence/c1b-source-sha256.txt` e `evidence/c1b-validation.md`.

Não há publicação pendente de C1B. Sua persistência é a ferramenta de transporte reutilizada por C3.

## C2 — menores originais eventualmente negativos em `d = 1/5`

**Integrado pela PR #157**, commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
`exists_eventually_negative_sigmaPadeD_from_height50_certificate` prova
`∃ P, ∀ p ≥ P, sigmaPadeD (1/5) p < 0` pelos quatro lemas de composição documentados em
`SESSION_STATE.md`. A decomposição do resto permanece na prova e os jets originais são mantidos.
Build Lean 4.32 e auditorias externa, de integração e transitiva passaram localmente; a PR não
recebeu status checks hospedados. Evidências em `evidence/c2-eventual-negativity/`.

## C3 — setores par e ímpar

**Integrado pela PR #159**, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. Em `SigmaParityNegativeDirection.lean`, `exists_even_sigma_negative_directions_from_pade` usa `p=2i` e a janela `sigmaMatrix (1/5) 0 (i+2)`; `exists_odd_sigma_negative_directions_from_pade` usa `p=2i+1` e `sigmaMatrix (1/5) 1 (i+2)`. Em ambos os casos, `sigmaMatrix_negative_directions_of_window` aplica a persistência integrada de C1B e entrega um vetor negativo para toda dimensão `M≥i+2`.

- Build completo da closure externa/C2/C3 e auditoria de axiomas: `evidence/c3-parity/VALIDATION.md` e logs adjacentes.
- Auditoria transitiva C2/C3 preserva `completedSigmaLogJet` e a característica originais; somente axiomas padrão.
- O certificado C3 não alega crescimento do índice negativo nem negatividade de todos os pivôs.
- O GitHub não retornou status checks para a PR #159.

## C4 — fonte deslocada e Bézout

**Integrado pela PR #162**, commit `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge `799a0e06af5469e9fe0665943adbb1cb29d0b6f8`. `SigmaSourceBezout.lean` define a fonte pelos coeficientes pares da densidade original e prova que sua soma em `t²` recompõe localmente `completedSigmaDensity d t`; `displacedProductC_ofReal_eq_density` então mantém o produto `F(t-id)F(t+id)` original.

- A recorrência exata é `C_d · H_d = -C_d′`, onde `H_d(n)=2*completedSigmaLogJet d n`. Como `C_d(0)>0`, o lema de derivada logarítmica formal conclui `-C_d′/C_d=H_d` sem alterar os jets.
- `completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix` identifica a matriz de Hankel como `2 • sigmaMatrix`. A congruência usa os coeficientes reais da fonte; o termo constante positivo torna a convolução invertível. A semidefinição positiva do bloco de Bézout equivale à da matriz sigma original.
- `CarrySourceBezout.sourceKernel_head_tail` mantém os quatro termos ordenados da decomposição genérica. Nenhum termo recebe sinal ou é identificado artificialmente com o bracket material.
- Compilação limpa, warnings-as-errors e auditoria transitiva de dez raízes (57.386 declarações alcançáveis), somente axiomas padrão: `evidence/c4-source-bezout/VALIDATION.md` e logs associados. O GitHub não apresentou status checks para a PR.

## Revalidação focada C2/C3 após reinício (2026-11-06)

Sobre as fontes de origin/main@935911bce2c253ee508a4990face113ea63c87ee, os módulos finais C2 e C3 foram recompilados em Lean 4.32 com warnings tratados como erros. O checker C2 aceitou seu corolário; o checker C3 aceitou os quatro roots par/ímpar; ambos usam apenas propext, Classical.choice e Quot.sound. A auditoria transitiva recompilada contou 133 roots públicos e 70.861 dependências, mantendo a característica e os jets sigma originais.

Logs, checker do root C2, hashes e pins estão em evidence/c2-c3-post-reboot-20261106/. Esta foi uma recompilação focada com caches das dependências já compilados no pin 4.32; a reconstrução limpa da closure continua documentada em evidence/c3-parity/VALIDATION.md.

## Prioridade C2/C3 confirmada na main atual (2026-11-07)

Sobre `origin/main@08a413f34dd5588ed3d021351af27f3f55e0c072`, C2 e C3 foram recompilados em Lean 4.32 a partir dos fontes integrados. O verificador C2 aceitou o corolário `exists_eventually_negative_sigmaPadeD_from_height50_certificate`; o verificador C3 aceitou os quatro resultados públicos de janela/direção. A auditoria transitiva aceitou 133 raízes e 70.861 dependências de tipo/corpo com apenas axiomas padrão e confirmou a proveniência de `completedSigmaLogJet`, da característica original e de `sigmaMatrix`. A única definição de `CarrySigmaObstruction.sigmaLineZero` continua em `SigmaCertifiedNegativeDirection.lean`.

Os logs de compilação, auditoria, pins e hashes estão em `evidence/c2-c3-priority-20261107/`. A integração de referência 4.32 permanece a publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`. A validação 4.35 permanece apenas como checkpoint incompleto em `evidence/lean435-validation-incomplete/`; não foi iniciada migração geral de Geometry/Carry.

## Revalidação após reinício e PR #235 (2026-11-07)

`origin/main` foi conferida em `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1`. Os módulos C2/C3 recompilaram em Lean 4.32 a partir de fontes com hashes idênticos aos da `main` atual; os verificadores C2/C3 aceitaram somente `propext`, `Classical.choice` e `Quot.sound`. A auditoria transitiva repetida contou 133 raízes públicas e 70.861 dependências. Evidências e comandos estão em `evidence/c2-c3-current-main-20261107/`. C2 (#157), C3 (#159), C1B (#155) e o checkpoint durável dos overlays 4.35 (#221) já estão mesclados; não há prova nem publicação C2/C3 pendente.

## Reconfirmação após PR #240 (2026-11-07)

- A ponta atual consultada é `origin/main@89710ecaf940f1a7887cd133451916edd76bddcb`. C1B (#155), C2 (#157), C3 (#159), o checkpoint incompleto 4.35 (#221) e a revalidação pós-reinício (#236) estão integrados.
- Os cinco módulos C2/C3 cobertos pelos hashes da execução de 2026-11-07 não mudaram entre `b604c06` e `89710ec`; os builds e a auditoria transitiva arquivados continuam válidos para a base atual. A comparação está documentada em `evidence/c2-c3-current-main-20261107/VALIDATION.md` e `source-pins-and-hashes.txt`.
- Os patches de overlay, pins, manifests, logs com o último erro e comandos de retomada 4.35 permanecem em `evidence/lean435-validation-incomplete/`, publicados pela PR #221. A validação continua incompleta e não foi retomada; para C2 usa-se a integração Lean 4.32 publicada.

## Reconfirmação após PR #241 (2026-11-07)

`origin/main@24f61b01732f44599869350c4bf675c3f3a3dcb6` mantém C1B (#155), C2 (#157), C3 (#159) e o checkpoint 4.35 incompleto (#221) integrados. Reexecutei a comparação dos cinco módulos C2/C3 entre o snapshot de compilação `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1` e essa revisão; não há diferenças. Permanecem válidos os builds Lean 4.32, os verificadores C2/C3 e a auditoria transitiva arquivados em `evidence/c2-c3-current-main-20261107/` (133 raízes públicas; 70.861 dependências; axiomas padrão). C1B foi integrado pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`. O checkpoint 4.35 continua identificado como incompleto; os overlays, patches, pins, manifests, logs, último erro e comandos de retomada estão versionados em `evidence/lean435-validation-incomplete/`.
