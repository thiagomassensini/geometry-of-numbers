# Registro de C2/C3 após a integração de C1B

**Data:** 2026-11-05
**Base:** `main` em `0586e238441096ecd2248e3f14bdac3a832af427`.

- C0, C1 e C1B estão integrados; PR #155 fechou C1B nesse merge.
- C2 continua aberto. A integração de altura 50 em Lean 4.32 está no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`; ela fecha a entrada de isolamento e a recuperação de raiz Padé, mas o corolário de negatividade eventual ainda precisa ser composto e validado na `main`.
- A meta exata é `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`, para os momentos originais. Devem permanecer no enunciado as definições originais e a decomposição completa do resto.
- Os pontos de composição previstos são `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`.
- Antes da composição, conferir a duplicação de `CarrySigmaObstruction.sigmaLineZero` entre o bridge e a integração de altura 50.
- C3 continua aberto até C2 estar integrado. A cobertura deve ser explícita para `p = 2i` e `p = 2i + 1`, com transporte das direções negativas às dimensões maiores usando C1B.
- A rota Lean 4.35 está pausada e preservada apenas como checkpoint incompleto; não há plano de migração geral. A lei quantitativa distância × profundidade, novos cadernos e C4 estão adiados.
