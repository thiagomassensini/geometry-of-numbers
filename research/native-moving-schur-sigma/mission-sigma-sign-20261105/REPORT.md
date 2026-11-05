# Relatório consolidado — missão de negatividade transversal sigma

**Atualizado em 2026-11-05.** C0, C1, C1B e C2 estão integrados. C3 é a prioridade ativa.

## Resultados formais

C1 prova, para todo `0 < |d| < 1/4`, a existência de uma direção negativa finita para a matriz sigma original:

```lean
CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0
```

A prova compõe o certificado formal `HardyFirstZero.first_zero_on_line`, as pontes de coordenadas e a equivalência no strip entre a zeta, a continuação e a característica nativa. Em seguida aplica a obstrução condicional já provada para `sigmaMatrix`. O certificado final usa apenas `propext`, `Classical.choice` e `Quot.sound`.

C1B prova a persistência dessa negatividade para todas as dimensões maiores que algum limiar:

```lean
CarrySigmaObstruction.certified_sigma_negative_directions_persist
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      ∃ v : Fin M → ℝ, v ≠ 0 ∧
        v ⬝ᵥ (sigmaMatrix d 0 M *ᵥ v) < 0
```

O lema `sigmaMatrix_prefix_submatrix` identifica exatamente a seção antiga como submatriz principal prefixo da nova. Se a matriz maior fosse semidefinida positiva, a submatriz também seria; isso contradiz a forma quadrática negativa de C1. A simetria de `sigmaMatrix` converte a falha de semidefinição positiva em uma direção negativa em cada tamanho maior. O teorema `certified_sigma_not_posSemidef_persist` registra também essa conclusão diretamente.

## Estado dos checkpoints

| Checkpoint | Estado | Resultado/evidência |
|---|---|---|
| C0 — inventário e recuperação | Integrado | PR #153; merge `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa` |
| C1 — direção negativa finita | Integrado, CI passou | PR #154; commit de prova `c2706339b15db390bf8f5f50535016bd1aca8cb8`; merge `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`; run `42101466137` success |
| C1B — persistência em dimensões maiores | Integrado pela PR #155; merge `0586e238441096ecd2248e3f14bdac3a832af427` | `evidence/c1b-focused-build.log`; 109 relatórios de axiomas padrão |
| C2 — menores originais eventualmente negativos em `d=1/5` | Integrado pela PR #157; merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949` | `evidence/c2-eventual-negativity/`; 72 relatórios externos, 17 de integração e auditoria transitiva de 124 raízes |
| C3 — torres par e ímpar | Prioridade ativa | C2 cobre `p=2i` e `p=2i+1`; C1B transporta as direções às dimensões maiores |
| C4 — fonte deslocada e Bézout | Não iniciado | Explorar depois de C1–C3, preservando o fator 2 |

## Compilação, auditoria e proveniência

- Build raiz Lean 4.32 de C1 passou em 8.857/8.857 jobs; a execução capturada após aquecer o cache está em `evidence/c1-root-build.log`.
- O build focado C1/C1B recompilou as fontes locais relevantes, os módulos sigma portados, a ponte e os dez módulos Lean do certificado mínimo do primeiro zero. O log final está em `evidence/c1b-focused-build.log`.
- O checker aceitou 109 relatórios; todos usam somente `propext`, `Classical.choice` e `Quot.sound`. A varredura não encontrou `sorry`, `admit`, `native_decide`, `sorryAx` nem declaração `axiom` nos fontes verificados.
- A auditoria recursiva anterior confirmou 1.278 módulos-fonte não-Mathlib contra os pins em `evidence/c1-source-pin-audit.txt`. Proveniência e licenças do certificado estão em `evidence/c1-source-provenance.md`; hashes C1 e C1B estão nos manifests correspondentes.
- C1B já está publicado pela PR #155. O checkpoint da validação incompleta 4.35 e os registros atualizados foram publicados pela PR #156, merge `301c36c710c87dc5fc43db9c26aa90c005e9e5a6`.
- C2 foi integrado pela PR #157; o GitHub não retornou status checks para essa PR. O estado consolidado da missão foi atualizado após o merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
- A compilação local respeitou o gate do script de 30 GiB; após o aumento da VM havia cerca de 60 GiB disponíveis.

## Limites

Não se provam positividade central all-order, RH, negatividade de todos os pivôs ou crescimento do índice negativo. C3 deve cobrir explicitamente as duas torres.
