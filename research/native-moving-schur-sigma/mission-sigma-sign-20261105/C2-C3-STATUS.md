# Registro de C2/C3 após a integração de C3

**Data:** 2026-11-05
**Base:** `main` em `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8` (após PR #159).

- C0, C1 e C1B estão integrados; PR #155 fechou C1B nesse merge.
- C1B foi integrado pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2 foi integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. A primeira referência foi a integração de altura 50 no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
- A meta exata é `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`, para os momentos originais. Devem permanecer no enunciado as definições originais e a decomposição completa do resto.
- Os pontos de composição previstos são `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`.
- A bridge agora reutiliza a definição única `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas as duplicações de `sigmaNativeCompletionFactor_ne_zero_of_strip` e `completedNativeCharacteristicContinuation_zero_iff_zeta`.
- C3 foi integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. As janelas par (`p=2i`) e ímpar (`p=2i+1`) geram direções negativas em toda dimensão a partir de `i₀+2`, via persistência C1B. O GitHub não retornou status checks; evidências em `evidence/c3-parity/`.
- A rota Lean 4.35 está preservada como checkpoint incompleto; não há plano de migração geral. C2/C3 estão concluídos. A lei quantitativa distância × profundidade, novos cadernos e C4 ficam no backlog posterior.

## Adendo 2026-11-06 — C4

C2/C3 permanecem concluídos e integrados. A etapa seguinte, C4, agora tem prova e auditoria locais em Lean 4.32: `D_d(t)=C_d(t²)`, `C_d·H_d=-C_d′` com `H_d(n)=2*completedSigmaLogJet d n`, e congruência de Bézout à `2 • sigmaMatrix` original. A publicação e integração desse checkpoint estão pendentes. Evidências em `evidence/c4-source-bezout/`.
