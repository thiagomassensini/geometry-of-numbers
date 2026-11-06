# Registro de C2/C3 após a integração de C2

**Data:** 2026-11-05
**Base:** `main` em `d9fe8117ad69108f89a558961e19ab2bdf4386bf` (após PR #158).

- C0, C1 e C1B estão integrados; PR #155 fechou C1B nesse merge.
- C1B foi integrado pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2 foi integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. A primeira referência foi a integração de altura 50 no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
- A meta exata é `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`, para os momentos originais. Devem permanecer no enunciado as definições originais e a decomposição completa do resto.
- Os pontos de composição previstos são `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`.
- A bridge agora reutiliza a definição única `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas as duplicações de `sigmaNativeCompletionFactor_ne_zero_of_strip` e `completedNativeCharacteristicContinuation_zero_iff_zeta`.
- C3: a prova explícita das janelas par (`p = 2i`) e ímpar (`p = 2i + 1`) e o transporte por C1B estão implementados em `SigmaParityNegativeDirection.lean`. Os teoremas `exists_even_sigma_negative_directions_from_pade` e `exists_odd_sigma_negative_directions_from_pade` fornecem uma direção negativa para toda dimensão a partir de `i₀ + 2`. Build/auditoria e checkpoint em `evidence/c3-parity/`; PR e merge pendentes.
- A rota Lean 4.35 está pausada e preservada apenas como checkpoint incompleto; não há plano de migração geral. A lei quantitativa distância × profundidade, novos cadernos e C4 estão adiados.
