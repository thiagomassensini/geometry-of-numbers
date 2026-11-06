# Estado da missão — negatividade transversal all-order

**Atualizado:** 2026-11-05
**Estado:** C0, C1, C1B, C2 e C3 estão concluídos e integrados à `main`. A lei quantitativa distância × profundidade, os novos cadernos e C4 ficam no backlog posterior; não fizeram parte desta entrega.

## Base integrada

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Base atual: `main` em `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`; a PR #159 integrou C3 após o estado documental da PR #158.
- C0 foi integrado pela PR #153, merge `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa`.
- C1 foi integrado pela PR #154, merge `b7a8a0eda7230c02f80dc63b41ab4cc9f9cf1d1e`; a CI hospedada passou.
- **C1B está integrado** pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`. Não há publicação pendente desse checkpoint.

## C2 — concluído

**Concluído e integrado pela PR #157**, commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. O corolário
`exists_eventually_negative_sigmaPadeD_from_height50_certificate` foi acrescentado em
`SigmaPadeEventualNegativity.lean` e prova o alvo abaixo sem hipóteses de sinal adicionais. A
integração recompila os módulos compartilhados de C1 para reutilizar a definição única
`sigmaLineZero`; a duplicação de dois lemas strip-local da bridge também foi removida.
Build Lean 4.32 e auditorias externa, de integração e transitiva passaram localmente. O GitHub
não retornou status checks para a PR.
Evidências: `evidence/c2-eventual-negativity/VALIDATION.md` e os logs no mesmo diretório.

Resultado provado, nos momentos originais e sem hipótese adicional de sinal:

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

## C3 — concluído e integrado

Integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. `exists_even_sigma_negative_directions_from_pade` usa `p=2i`; `exists_odd_sigma_negative_directions_from_pade` usa `p=2i+1`. Cada torre fornece um vetor negativo em todas as dimensões `M≥i₀+2`, transportado pela persistência de C1B. Build, auditorias e checkpoint estão em `evidence/c3-parity/`. O GitHub não retornou status checks para a PR.

## Checkpoint da tentativa Lean 4.35

O checkpoint `evidence/lean435-validation-incomplete/` preserva overlays temporários, pins, logs, manifests de módulos e comandos de retomada. A validação 4.35 continua **incompleta**: o build externo zeta-lab passou, mas a closure focada Geometry/Carry parou em incompatibilidades de `LinearPMap`, a começar por `CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock`. C2/C3 foram concluídos em Lean 4.32; não há migração geral de Geometry ou Carry em andamento.

## Rotina de entrega

Para cada checkpoint: prova → compilação → auditoria de axiomas → checkpoint durável → push → PR → merge na `main` → atualização deste estado. C2/C3 estão encerrados; lei quantitativa distância × profundidade, novos cadernos e C4 permanecem como backlog posterior.
