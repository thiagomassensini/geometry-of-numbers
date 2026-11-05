# Mapa dos teoremas e obrigações

## Objetos que não devem ser confundidos

`completedNativeOperatorCharacteristic` é a característica completada original; `completedSigmaLogJet d n` são os momentos sigma originais; `sigmaMatrix d s N` é a Hankel real original. `twoPoleMoment` e o operador de alturas são objetos distintos e não substituem esses termos.

## Rota A — zero positivo certificado para direção negativa finita

### Implicação condicional reutilizada

- `CarrySigmaObstruction.exists_sigmaMatrix_negative_direction_of_zero`
- Fonte: `research/native-moving-schur-sigma/SigmaZeroObstruction.lean`, commit `671bd23b5ec3a486668f74ebbf756ad1dce269f6` e descendentes de `origin/agent/native-moving-schur-sigma`.
- Entrada: `d, γ`, `γ>0`, `0<|d|<1/4`, e `completedNativeOperatorCharacteristic (γ : ℂ)=0`.
- Saída: `∃ N v`, `v≠0` e `v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v)<0`.
- Fonte portada por byte da branch `agent/native-moving-schur-sigma` em `9392ebac9930f5d11c56f595556080e8ab1de809`; compilada de novo no build focado Lean 4.32 desta missão.
- `#print axioms` confirma somente `propext`, `Classical.choice`, `Quot.sound` para a implicação e para os resultados-base auditados.

### C1 — concluído e compilado nesta worktree

Arquivos adicionados: `SigmaNativeZeroBridge.lean` e `SigmaCertifiedNegativeDirection.lean`. A ponte usa as declarações e seus tipos exatos:

- `HardyFirstZero.first_zero_on_line` fornece `γ > 0` e `riemannZeta (sigmaLineZero γ)=0`.
- `operatorHeightParameter (γ : ℂ) = sigmaLineZero γ` identifica a coordenada.
- `completedNativeCharacteristicContinuation_zero_iff_zeta` transfere o zero da zeta dentro de `genuineCriticalStrip`.
- `completedNativeCharacteristicContinuation_eq_native` retorna à característica nativa original, também só dentro do strip.
- `exists_sigmaMatrix_negative_direction_of_zero` conclui a direção quadrática negativa da matriz original.

O teorema final está compilado e auditado com somente os axiomas padrão. O certificado Lean do primeiro zero foi copiado em fonte para `height50-certified/`; os dez módulos da cadeia mínima foram compilados de novo em Lean 4.32. Veja logs e pins em `evidence/c1-*`.

Teorema C1 concluído:

```lean
theorem certified_sigma_negative_direction_of_nonzero_small_shift
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0
```

## Rota de persistência — C1B/C3

Precisam de uma identidade exata entre `sigmaMatrix d s N` e o bloco principal prefixo de `sigmaMatrix d s M` quando `N≤M`. Dada uma direção negativa no tamanho `N`, estendê-la por zeros deve preservar a forma quadrática e a não nulidade. Isso implica `¬ PosSemidef` em todo tamanho maior. Não implica que todos os pivôs sejam negativos, nem crescimento linear do índice negativo.

Possíveis módulos reutilizáveis: `CameraCoherence.lean` e `HankelLimitObject.lean` em `origin/agent/c3-critical-tilt-prime`; são posteriores ao PR #146, não estão na `main` e não devem ser importados em bloco sem auditoria.

## Rota B — menores Padé, C2

- Originais: `hₙ(d) = completedSigmaLogJet d n` e `Dₖ(d)=hₖhₖ₊₂−hₖ₊₁²`.
- Disponível fora da `main`: `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder`, `sigmaPadeD_eventually_neg_of_normalized_limit` e a decomposição de resto `completedNative_sigmaRemainder_square_decomposition_of_isolation` em `origin/agent/native-sigma-pade-signed-pencil`.
- Fonte de isolamento fora da `main`: `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate` na branch `codex/native-sigma-height50-lean432-integrated`; origem externa `teal-sea/zeta-lab@b09fa4dd…`, portada integralmente para Lean 4.32.
- Resultado pedido: `∃ K, ∀ k≥K, Dₖ(1/5)<0`, com limite normalizado `−y²<0`, `a=1/(γ²+1/25)` e `y=Im((γ+i/5)⁻²/a)≠0`.
- O modelo `twoPoleMoment` serve só para o termo dominante; a conclusão deve permanecer nos jets originais.

## C3 — as duas torres

Para `s∈{0,1}`, as janelas consecutivas das torres `H_{s,N}` têm menores `D_{s+2i}`. A paridade deve ser explicitada: `k=2i` no setor par e `k=2i+1` no ímpar. A negatividade eventual em todo `k≥K` cobre as duas. Prolongar a direção do bloco `2×2` preserva negatividade para toda matriz maior.

## C4 — série de fonte deslocada

Investigar, sem impor identificação artificial com o bracket material:

```text
D_d(t) = F(t-id) F(t+id) = C_d(t²)
-C'_d(u)/C_d(u) = 2 * ∑ n, completedSigmaLogJet d n * u^n
```

O fator 2 vem da derivada anterior `−D'_d(t)/(4tD_d(t))`. Primeiro lema faltante, recorrência exata, escala positiva e canais compensadores devem ser nomeados se a costura Bézout não fechar.

## Limites

Não há prova de positividade central all-order, de RH, de todos os pivôs negativos em toda ordem ou de crescimento da inércia. A quantificação esperada é `∀ d, ∃ N(d)` onde apropriado, não uma lei uniforme em `d` sem prova.
