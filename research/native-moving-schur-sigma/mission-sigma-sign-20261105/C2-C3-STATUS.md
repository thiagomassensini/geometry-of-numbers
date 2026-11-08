# Registro de C2/C3 após a integração de C3

## Retomada e reconciliação da prioridade — 2026-11-08

`origin/main@ebd6c57c33edcf8596f09889c7bf956e7d9b284f` já contém as provas e integrações solicitadas: C1B pela PR #155 (merge `0586e238441096ecd2248e3f14bdac3a832af427`), C2 pela PR #157 (merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`) e C3 pela PR #159 (merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`). Portanto, não há código C2/C3 pendente de integração.

A validação Lean 4.32 de 2026-11-07 foi compilada sobre `origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8`. A comparação de toda a árvore `research/native-moving-schur-sigma/` até `ebd6c57` encontrou apenas arquivos C5 novos/alterados e registros; nenhum módulo Lean preexistente da closure C2/C3 foi alterado. Os hashes e logs que identificam a execução estão em `evidence/c2-c3-live-main-20261107/`; por identidade de fontes, essa compilação e auditoria continuam aplicáveis à `main` atual. Os verificadores aceitaram apenas `propext`, `Classical.choice` e `Quot.sound`, e `SigmaPadeAudit` conferiu 133 raízes públicas e 70.861 dependências.

A referência inicial de C2 é `SigmaHeight50Integration.lean` na revisão Lean 4.32 `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`. Ela não apresenta bloqueio. O corolário publicado mantém `completedSigmaLogJet` e `sigmaPadeD` originais, a decomposição exponencial completa do resto e nenhuma hipótese de sinal adicional. C3 usa `p=2i` e `p=2i+1` e transporta as duas direções negativas para `M≥i₀+2` pela persistência C1B. `CarrySigmaObstruction.sigmaLineZero` tem uma única definição em `SigmaCertifiedNegativeDirection.lean`.

O checkpoint 4.35 foi publicado pela PR #221 e permanece explicitamente incompleto. Os checksums dos patches Geometry/Carry e do arquivo de logs foram verificados nesta retomada; o tar contém o erro direto mais recente, os dois estados do scheduler e o build Geometry. O primeiro impedimento daquela rota continua sendo `CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock`, na declaração `realAdjoint_ker_eq_bot_of_denseRange`: a API 4.35 espera `T.ker = ⊥`, enquanto a prova-base entrega `LinearMap.ker T.toFun = ⊥`; após a adaptação inicial, `Subtype.ext` deixa pendente o objetivo de injetividade no domínio subtype. Isso não é um bloqueio na rota C2 4.32 e não justifica uma migração geral de Geometry/Carry.

Não foi necessário calcular a primeira profundidade de falha. A lei quantitativa distância × profundidade e os novos cadernos seguem adiados. Registro reproduzível desta conferência: `evidence/c2-c3-priority-resume-20261108/VALIDATION.md`.

**Revalidação final:** os módulos C2/C3 foram recompilados e auditados em Lean 4.32 sobre as fontes de origin/main@9951fcb7315c25b6d878befc42b2d02c26a96ec7. A auditoria transitiva aceitou 133 roots públicos e 70.861 dependências com apenas axiomas padrão. Os logs, pins e hashes desta execução estão em evidence/c2-c3-final-validation-20261106/; a revalidação imediatamente após o reboot permanece em evidence/c2-c3-post-reboot-20261106/.

**Registro original:** 2026-11-05, `main` em `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8` (após PR #159).
**Estado reconciliado após reinício:** 2026-11-07. C0–C4 estão concluídos e integrados à `main`; C1B, C2 e C3 não têm prova nem publicação pendente. C2/C3 recompilaram e passaram pela auditoria transitiva em Lean 4.32 com fontes idênticas ao snapshot `origin/main@b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1`. A comparação direta até `origin/main@24f61b01732f44599869350c4bf675c3f3a3dcb6` e, agora, até `origin/main@71721874eb01071a07c83e4f71117b7d662e1b53` não encontra diferenças nos módulos auditados. Os logs da compilação estão em `evidence/c2-c3-current-main-20261107/`; esta ponta foi registrada ao final do arquivo. A revisão dos marcos e próximos passos está em `SESSION_STATE.md` e `NEXT_STEPS.md`.

- C0, C1 e C1B estão integrados; PR #155 fechou C1B nesse merge.
- C1B foi integrado pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2 foi integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. A primeira referência foi a integração de altura 50 no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.
- A meta exata é `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`, para os momentos originais. Devem permanecer no enunciado as definições originais e a decomposição completa do resto.
- A prova integrada compõe `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`.
- A bridge agora reutiliza a definição única `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas as duplicações de `sigmaNativeCompletionFactor_ne_zero_of_strip` e `completedNativeCharacteristicContinuation_zero_iff_zeta`.
- C3 foi integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. As janelas par (`p=2i`) e ímpar (`p=2i+1`) geram direções negativas em toda dimensão a partir de `i₀+2`, via persistência C1B. O GitHub não retornou status checks; evidências em `evidence/c3-parity/`.
- A rota Lean 4.35 está preservada como checkpoint incompleto; não há plano de migração geral. C2/C3 estão concluídos. A lei quantitativa distância × profundidade e os novos cadernos ficam no backlog posterior. C4 foi concluído e integrado pela PR #162, conforme o adendo abaixo.

## Reconfirmação da prioridade e da base atual (2026-11-07)

`origin/main@24f61b01732f44599869350c4bf675c3f3a3dcb6` contém C1B (#155), C2 (#157), C3 (#159), o checkpoint Lean 4.35 incompleto (#221) e a reconciliação de estado da PR #241. A validação pós-reinício em Lean 4.32 está registrada em `evidence/c2-c3-current-main-20261107/`; uma comparação direta entre o snapshot compilado `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1` e esta ponta não encontra mudanças nos cinco módulos C2/C3 auditados. Portanto, a validação permanece aplicável à base atual. C1B foi integrado no merge `0586e238441096ecd2248e3f14bdac3a832af427`; nenhuma publicação C2/C3 está pendente. A rota 4.32 não apresenta bloqueio para C2, então não se retomou a migração geral 4.35.

## Reconfirmação após a PR #283 (2026-11-07)

`origin/main@71721874eb01071a07c83e4f71117b7d662e1b53` mantém C1B (#155, merge `0586e238441096ecd2248e3f14bdac3a832af427`), C2 (#157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`), C3 (#159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`) e o checkpoint incompleto 4.35 (#221, merge `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`). A comparação dos módulos C2/C3 entre a revisão anterior `24f61b01732f44599869350c4bf675c3f3a3dcb6` e esta ponta não encontra mudanças; assim, a compilação e auditoria Lean 4.32 já arquivadas (133 raízes, 70.861 dependências, apenas axiomas padrão) continuam cobrindo o código integrado. C2 usa a integração publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`; não há impedimento na rota 4.32 nem trabalho C2/C3 por publicar. Os overlays, patches, pins, manifests, logs, erro e comandos de retomada 4.35 continuam versionados como validação incompleta.

## Adendo 2026-11-06 — C4

C2/C3 permanecem concluídos e integrados. C4 foi integrado pela PR #162, commit `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge `799a0e06af5469e9fe0665943adbb1cb29d0b6f8`. A prova e auditoria Lean 4.32 estabelecem `D_d(t)=C_d(t²)`, `C_d·H_d=-C_d′` com `H_d(n)=2*completedSigmaLogJet d n`, e congruência de Bézout à `2 • sigmaMatrix` original. Evidências em `evidence/c4-source-bezout/`; não houve status checks hospedados.


## Conferência após a PR #288 — 2026-11-07

A ponta consultada é origin/main@78a10e8af611a5c690b248f8889b9e87674fd5c8. C1B (#155, merge 0586e238441096ecd2248e3f14bdac3a832af427), C2 (#157, merge f4f5cf5ecc60ea3747cbaf21389fab52832d3949), C3 (#159, merge b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8) e o checkpoint Lean 4.35 incompleto (#221, merge c67b2f72e0ad2f331c0966fb3ed82e98655e3df8) já estão publicados na main. Nenhuma entrega C1B/C2/C3 está pendente.

Os cinco módulos C2/C3 foram recompilados diretamente a partir dessa ponta em Lean 4.32 com warningAsError. Os verificadores C2/C3 aceitaram o corolário e os quatro relatórios públicos usando somente propext, Classical.choice e Quot.sound; SigmaPadeAudit refez a auditoria de 133 raízes públicas e 70.861 dependências. Os logs atuais estão em evidence/c2-c3-live-main-20261107/build-logs/; os logs pós-reinício anteriores permanecem preservados em evidence/c2-c3-current-main-20261107/.

A integração Lean 4.32 no commit b9ce1955c1e8830afad2323afe5266ed3f5f35d9 continua sendo a primeira referência C2 e não mostrou impedimento. A prova conserva o resto e as definições originais, sem hipótese de sinal adicional. A tentativa 4.35 continua somente como checkpoint incompleto; patches, logs, pins, erro mais recente e comandos de retomada estão preservados no checkpoint publicado #221.
