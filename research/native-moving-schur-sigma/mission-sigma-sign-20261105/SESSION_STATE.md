# Estado da missão — negatividade transversal all-order

**Atualizado:** 2026-11-05
**Objetivo ativo:** concluir C2 e C3 e integrar ambos à `main`. C0, C1 e C1B não serão refeitos. A lei quantitativa distância × profundidade e os novos cadernos ficam adiados até depois de C2/C3.

## Base integrada

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Base atual: `main` em `0586e238441096ecd2248e3f14bdac3a832af427`.
- C0 foi integrado pela PR #153, merge `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- C1 foi integrado pela PR #154, merge `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`; a CI hospedada passou.
- **C1B está integrado** pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`. Não há publicação pendente desse checkpoint.

## Prioridade: C2

Provar, nos momentos originais e sem hipótese adicional de sinal,

```text
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0.
```

A primeira referência é a integração Lean 4.32 publicada no commit
`b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, em especial
`SigmaHeight50Integration.lean`, `SigmaRemainderDescent.lean` e
`SigmaPadeConvergence.lean`. Reutilizar e compor:

- `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`;
- `completedNative_sigmaRemainder_square_decomposition_of_isolation`;
- `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder`;
- `sigmaPadeD_eventually_neg_of_normalized_limit`.

Manter `completedSigmaLogJet` e `sigmaPadeD` originais, conservando o resto. Não inserir premissas de sinal para fechar o corolário. Ao reunir módulos, verificar e eliminar qualquer definição duplicada de `CarrySigmaObstruction.sigmaLineZero`.

## Depois: C3

Usar explicitamente as janelas `p = 2i` e `p = 2i + 1` para cobrir os setores par e ímpar. Transportar cada direção negativa às dimensões maiores usando o resultado integrado de persistência de C1B. Fechar C2 antes de iniciar essa integração.

## Checkpoint da tentativa Lean 4.35

O checkpoint `evidence/lean435-validation-incomplete/` preserva overlays temporários, pins, logs, manifests de módulos e comandos de retomada. A validação 4.35 está **incompleta** e não é a rota prioritária: o build externo zeta-lab passou, mas a compilação focada da cadeia Geometry/Carry parou em incompatibilidades concretas de `LinearPMap`, a começar por `CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock`. Não iniciar uma migração geral de Geometry ou Carry. Só voltar a esse overlay se o caminho 4.32 apresentar um impedimento concreto para C2.

## Rotina de entrega

Para cada checkpoint pequeno: prova → compilação → auditoria de axiomas → checkpoint durável → push → PR → merge na `main` → atualização deste estado. C4 e as tarefas quantitativas permanecem depois de C2/C3.
