# Checkpoints

## C0 — recuperação, inventário e ambiente (2026-11-05)

**Estado:** concluído e integrado pela PR #153. O merge commit da `main` é `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`. O checkpoint C0 tratou apenas documentação; nenhum build Lean foi requisito para aquela entrega.

- A worktree original `agent/native-moving-schur-sigma` foi localizada e preservada, assim como os checkouts separados de altura 50 e Padé.
- O inventário de branches e PRs dos quatro repositórios está em `MERGE_INVENTORY.md`; as alterações locais existentes foram registradas e não foram alteradas.
- A PR #153 foi mesclada depois de ficar limpa e mergeable; nenhum status check foi retornado para o commit de documentação.

## C1 — direção negativa finita para todo deslocamento pequeno

**Estado:** prova Lean concluída e auditada localmente; commit, push e PR desta branch são a próxima ação operacional.

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

## C1B — persistência em dimensões maiores

**Aberto.** Provar a identidade de bloco prefixo principal entre `sigmaMatrix d 0 N` e `sigmaMatrix d 0 M`, estender a direção negativa com zeros e concluir não-positividade semidefinida para todo `M ≥ N`. A próxima branch deve partir da `main` depois da integração de C1.

## C2 — menores originais eventualmente negativos em `d = 1/5`

**Aberto.** Compor a decomposição exata da sequência original `completedSigmaLogJet`, o controle do resto e o certificado de altura 50 para provar `∃ K, ∀ k ≥ K, sigmaPadeD (1/5) k < 0`. Não substituir os jets originais por `twoPoleMoment`.

## C3 — setores par e ímpar

**Aberto.** Usar a negatividade eventual dos menores para janelas `k=2i` e `k=2i+1`, obter direções em cada torre e prolongá-las para dimensões maiores. Não afirmar crescimento do índice negativo sem prova própria.

## C4 — fonte deslocada e Bézout

**Não iniciado; exploratório.** Verificar a recorrência em `u=t²` com o fator 2, avaliar a costura com `source_bezout_to_hankel_congruence` e manter explícitos os canais físicos e compensadores. Não atrasar C1–C3.
