# Reconciliação C2/C3 e checkpoint 4.35 — 2026-11-08

## Estado conferido

- `origin/main`: `ebd6c57c33edcf8596f09889c7bf956e7d9b284f`.
- C1B: PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2: PR #157, prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
- C3: PR #159, prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
- Checkpoint da validação 4.35 incompleta: PR #221, merge `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`.

Não existe prova ou integração C1B/C2/C3 pendente. A integração 4.32 de altura 50 em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, especialmente `SigmaHeight50Integration.lean`, foi a referência usada para C2.

## C2 e C3 já demonstrados

C2 prova, nos momentos originais,

```lean
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0
```

O corolário `exists_eventually_negative_sigmaPadeD_from_height50_certificate` compõe:

- `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`;
- `completedNative_sigmaRemainder_square_decomposition_of_isolation`;
- `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder`;
- `sigmaPadeD_eventually_neg_of_normalized_limit`.

O resultado preserva `completedSigmaLogJet`, `sigmaPadeD` e a decomposição exponencial completa do resto; nenhuma hipótese adicional de sinal foi introduzida.

C3 usa `p=2i` para o setor par e `p=2i+1` para o ímpar. `sigmaMatrix_negative_directions_of_window` transporta a direção negativa de cada janela para todas as dimensões `M≥i₀+2`, usando a persistência C1B. A definição de `CarrySigmaObstruction.sigmaLineZero` ocorre uma única vez, em `SigmaCertifiedNegativeDirection.lean`.

## Aplicabilidade da compilação e auditoria Lean 4.32

A compilação limpa e auditoria transitiva mais recentes estão arquivadas em `../c2-c3-live-main-20261107/`. A revisão compilada foi `origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8`, com Lean `4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`, Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` e certificado altura 50 `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`.

A comparação entre `78a10e8` e a ponta atual `ebd6c57` não encontrou alterações em nenhum fonte Lean preexistente da closure C2/C3; o delta da pasta contém novos módulos C5 e atualizações documentais. Os cinco logs de build e os logs dos verificadores continuam identificando exatamente o código atual. Os verificadores aceitam somente `propext`, `Classical.choice` e `Quot.sound`; `SigmaPadeAudit` percorre 133 raízes públicas e 70.861 dependências de tipo/corpo. Como as fontes correspondem ao snapshot validado, não foi necessário recompilar nem criar uma segunda integração das mesmas provas.

Comandos de conferência usados na retomada:

```bash
git diff --name-status 78a10e8af611a5c690b248f8889b9e87674fd5c8..ebd6c57c33edcf8596f09889c7bf956e7d9b284f -- research/native-moving-schur-sigma
sha256sum -c research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/c2-c3-live-main-20261107/checkpoint-sha256sums.txt
gzip -t research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete/geometry-pins-4.35.patch.gz research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete/tracked-source-overrides.patch.gz research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete/logs-lean435.tar.gz
tar -tzf research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete/logs-lean435.tar.gz
```

O diff mostrou somente módulos C5 novos/alterados e documentos da missão; nenhum módulo Lean preexistente da closure C2/C3 aparece como alterado. `sha256sum -c` imprimiu `OK` para os dois patches compactados e para o arquivo de logs; `gzip -t` terminou sem erro.

## Integridade do checkpoint Lean 4.35

O checkpoint incompleto está em `../lean435-validation-incomplete/`. Os três objetos abaixo passaram `sha256sum -c` com `OK`:

- `geometry-pins-4.35.patch.gz`: `5b8343873eee8c28ba765920df868f8b0e589616b5e3de180e24145dcf7c9920`;
- `tracked-source-overrides.patch.gz`: `54b286b2dc52235b021d706ad691a9bcb5183a2980bb85b92f20e0b3fcaae0fb`;
- `logs-lean435.tar.gz`: `c2efdb2ec33e648fda36c7451ad791230baa9bc57549cc0241671ca61c8578cb`.

`gzip -t` também passou nos três arquivos. O tar contém `logs/direct-latest-error.log`, `logs/integration-build435/status.log`, `logs/integration-build435/status-attempt1.log`, `logs/integration-build435/direct-latest-error.log`, `logs/zeta-lab-lean435-full-build.log` e `root-build.log`. O README do checkpoint mantém os pins, overlays, manifests, scheduler e comandos de retomada. A validação segue explicitamente incompleta.

## Decisão de rota

Não há impedimento na rota 4.32 para C2/C3. A falha 4.35 registrada em `CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock`, declaração `realAdjoint_ker_eq_bot_of_denseRange`, é um bloqueio de portabilidade separado e não motivou migração geral de Geometry/Carry.

A lei quantitativa distância × profundidade e os novos cadernos seguem adiados. A primeira profundidade de falha não foi calculada, pois não é necessária para a negatividade eventual.
