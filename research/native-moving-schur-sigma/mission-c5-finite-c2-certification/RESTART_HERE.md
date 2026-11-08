# Retomar primeiro — missão C5

## Estado atual — prefixo Bernoulli de 160 entradas em compilação (2026-11-08)

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
CURRENT PHASE: certificado formal dos dados da tabela usada pela avaliação de zeta.
CURRENT SUBTASK: compile and audit c5BernoulliPrimeTable_160_eq_data from the integrated prefix 128.
LAST VERIFIED THEOREM: CarrySigmaObstruction.c5BernoulliPrimeTable_128_eq_data.
LAST COMPILED FILE: SigmaC5BernoulliDataCertificate128Audit.lean (Lean 4.32.0, warningAsError=true).
LAST SUCCESSFUL INTEGRATED PROOF: c5BernoulliPrimeTable_128_eq_data, proof commit b6f26114502116c65fe2482ebda3464e4b1fc645, PR #309, merge c7782c54b78f97b1ea3f5a61f6e0ceefe75f2f11.
CURRENT BRANCH: codex/c5-zeta-bernoulli-prefix160-20261108, latest checkpoint dc5ee8b.
MAIN SHA: 9156f7e7363e7129a7a9c132a5f9a2276e4352cd.
OPEN PR: none; the prefix160 proof is not validated.
ACTIVE BUILD: tmux session c5-bernoulli-prefix160-20261108, pane PID 16470. State: evidence/rational-boxes/c5-bernoulli-data-prefix160-20261108/runner-status.txt.
WHAT IS PROVED: indices 0–127 equal the first 128 rational data literals; clean build, exact 601-value table check, and isolated standard-axiom audit pass for prefix128.
WHAT IS CONDITIONAL: the final finite signs still depend on the unproved source-box inclusions sigmaC00495SourceBoxes and sigmaC01SourceBoxes.
WHAT IS BLOCKED: no mathematical/compiler error has been established for prefix160. Two earlier execution attempts were interrupted and are preserved under this step's attempts/ directory; 473 equalities and the CSV–Lean zeta-box bridge remain open.
EXACT NEXT COMMAND: cat research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix160-20261108/runner-status.txt; tmux has-session -t c5-bernoulli-prefix160-20261108
EXACT NEXT MATHEMATICAL OBLIGATION: finish the current compile, audit #print axioms, and validate c5BernoulliPrimeTable_160_eq_data; then prove the next cumulative prefix and continue toward 601.
DO NOT REPEAT: C1B/C2/C3/C4; prefixes 32/64/96/128; the missing-prefix64 import failure; the invalid default-100000 simp attempt; either interrupted prefix160 execution. Do not restart while runner-status is RUNNING.
```

The 128-entry run passed in Lean 4.32.0 with `warningAsError=true`; the audit
accepts only `propext`, `Classical.choice` and `Quot.sound`. Build logs,
verification output, errors from the earlier invalid attempts and hashes are
in `evidence/rational-boxes/c5-bernoulli-data-prefix128-20261108/README.md`.
This is still a partial data checkpoint: the other 473 equalities, zeta-box
bridge, source inclusions and final signs remain open. Do not reopen C1B/C2/C3/C4.

## Histórico — tabela de Bernoulli certificada até 64 entradas (2026-11-08)

A PR #300 certificou 64/601 entradas e deixou o prefixo 0–95 como próximo alvo; esse prefixo foi integrado pela PR #302. Evidência anterior: `evidence/rational-boxes/c5-bernoulli-data-prefix64-20261108/README.md`.

## Histórico — primeiro bloco da tabela de Bernoulli certificado (2026-11-08)

- A PR #298 está integrada na `main`: commit de prova `1ed4a00`, merge `171c19681482312bf71bffdcd23b24a728edf04b`.
- `c5BernoulliPrimeTable_32_eq_data` prova a igualdade entre a recorrência e o primeiro bloco literal de 32 coeficientes. A reprodução compara exatamente, como racionais, os 601 valores emitidos pela sonda Lean com a tabela literal (`DATA_TABLE_CHECK=PASS`); a igualdade formal dos 569 valores restantes continua pendente.
- Sonda, tabela, certificado, auditoria isolada e logs estão em `SigmaC5BernoulliData*.lean` e `evidence/rational-boxes/c5-bernoulli-data-prefix32-20261108/`. Build limpo Lean 4.32.0 com `warningAsError=true`; axiomas do teorema: `propext`, `Classical.choice`, `Quot.sound`; `CLEAN_BUILD=PASS`, `AXIOM_AUDIT=PASS`.
- Próximo passo: provar o bloco 32–64 usando o prefixo certificado como base e avançar em blocos até 601. Depois, retomar a ponte formal de uma caixa de zeta exportada para a caixa Lean correspondente.
- Este avanço não certifica caixas exportadas de zeta, inclusões da fonte ou sinais C5. C5 continua incompleta; C1B/C2/C3/C4 permanecem concluídas.

## Histórico — quatro nós complexos de Gamma integrados (2026-11-08)

- C5 segue ativa; C1B/C2/C3/C4 permanecem concluídas. Não reiniciar essas fases nem a migração geral para Lean 4.35.
- A PR #296 integrou `CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexBox_contains`, que contém `Complex.Gamma (3/10 + (3/20) * Complex.I)`. Isso fecha o par complexo de `d=1/10`, junto de `Γ(1/5 + 3i/20)` da PR #294.
- Para a cota de potência de raio 8, `SigmaC5GammaDOneUpperLogBounds.lean` prova `|Interval.logQ 384 8 240| ≤ 10`; a composição inclui `240^z`, 16 blocos × 64 termos do núcleo racional e `gamma_finite_1024_240_error ≤ 10⁻⁹⁹`.
- Seis módulos passaram em Lean 4.32.0 com `warningAsError=true`; 16 relatórios usam somente `propext`, `Classical.choice`, `Quot.sound`, sem `sorryAx`, axiomas próprios ou `native_decide`. Pico de RSS: 8.4 GiB. A reprodução limpa também passou; a primeira falha de composição foi preservada.
- Evidência, reprodução, pins, hashes e logs: `evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108/README.md`. PR #296 integrou o commit `e986390937265fc1bb759140ed7fb6d80d23eadf` no merge `113ed1517fff040f4fc619cf7d5086c57f137427`.
- Também estão integrados `Γ(901/4000 + 3i/20)` e `Γ(1099/4000 + 3i/20)` para `d=99/2000` (PRs #290 e #292), e os pontos reais `Γ(1/5)` e `Γ(901/4000)`.
- Próxima obrigação: formalizar em Lean a ligação das 516 caixas de zeta exportadas (129 nós × quatro coordenadas) às caixas usadas na avaliação nodal. A exportação CSV/`#eval` confirma os dados e a cobertura, mas não prova essa ligação; a expansão Euler–Maclaurin de ordem 600 já está integrada.
- Depois, certificar os demais nós necessários e compor zeta, Gamma, fator nativo e quadraturas da fonte original para provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 e os sinais finais de `sigmaPadeD` continuam incompletos.

## Checkpoint anterior — caixa `Γ(1/5)` (PR #285 integrada)

`CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains` está integrada pelo merge `832b201b6907c6682aa9657c3e4ff9da6dd40254`; evidência em `evidence/rational-boxes/c5-gamma-first-node-20261107/README.md`.

## Histórico — checkpoint do núcleo Gamma racional por blocos (PR #282)

- Base de `main`: merge da PR #281, `ec5c5e8998b62726ada6f942cf4c2410048a2a23`; branch de trabalho `codex/c5-o4-after-stage19-20261107`. Geometry de referência está em `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Integração: PR #282, commit de prova `131d5f57da009a830c0a967bb5cf4713412c3473`, merge `7c301a2bb0b975369c8f8889ec2940372d2266c2` em 2026-11-07. Retome a partir da `main` nesse merge; o branch citado acima é a origem do checkpoint.
- Para `gammaFiniteRationalCore 1024 240 (1/5) 0`, 16 blocos de 64 termos têm seus pisos certificados em Lean. A recomposição dá a caixa exata do núcleo racional `[S/2^1024,(S+16)/2^1024] × {0}`; a inclusão está em `c5GammaCoreNodePilotChunkBox_contains`. Auditoria isolada: 20 raízes, somente `propext`, `Classical.choice`, `Quot.sound`, sem `sorryAx` nem `native_decide`; Lean 4.32 com warnings como erros.
- Escopo: um ponto e só o núcleo racional. A caixa ainda não inclui `240^z`, `gammaFinite`, Gamma completa, zeta, os demais nós nem os coeficientes da fonte C2. `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` seguem sem prova; C5 permanece incompleta.
- Fontes, comandos, logs de tentativas falhas, checker e hashes estão em `evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/README.md`. Não repetir a prova monolítica nem usar o caminho `native_decide`.
- Próximo: compor esta caixa com a inclusão formal da potência e o erro `gamma_finite_1024_240_error`, fechar uma caixa Gamma para o ponto e só então expandir para os nós de interpolação.


## Snapshot anterior — estado após PR #280 (2026-11-07)

- A última integração de prova na `main` é a PR #280: commit `8a8fcde3682f804a2e3cdb03dae2be5d71d54654`, merge `de09a348a9e2b0f0c6bd700eeed63d92726a56c5`. Esta atualização de estado foi preparada na branch `codex/c5-stage19-state-20261107` sobre essa base.
- C1B já entrou pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`; C2 pela PR #157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`; C3 pela PR #159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. C4 e a recorrência dos momentos também estão integradas. Não reabrir essas fases nem a migração geral para Lean 4.35.
- C5 O2 (`SigmaFiniteCoefficientSignTransport`) está provada em Lean 4.32: recorrência polinomial sem divisão e transporte do sinal para `sigmaPadeD` original. O3 também está provada e auditada, mas **condicionada** às inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
- Reproduzi as três configurações de `certify_finite_c2.py`; o verificador racional exato confirmou `+++++++++++-`, `+++++++++++-` e `+++++++++-`. Logs, JSONs e hashes: `evidence/rational-boxes/reproduction-20261107/`. A execução precisou do patch local `gmpy2.mpz`→`int`, já preservado em `evidence/interval-certificate/momentos-gmpy2-compat.patch`; o checkout Momentos foi restaurado limpo. Esses resultados continuam condicionais e não provam a inclusão formal da fonte.
- A PR #213 já exportou 516 caixas racionais de zeta nos 129 nós e quatro coordenadas. `#eval`/CSV confirma a exportação e a cobertura, mas ainda não há prova Lean de que cada valor exportado seja igual à caixa usada na composição. A tentativa monolítica para uma caixa está documentada como falha; não a repetir.
- Último resultado formal para a recorrência nodal: `c5RoundedExpStateC_stage18_correct` já está integrado pela PR #275; `c5RoundedExpStateC_stage19_correct` também compilou e passou pela auditoria Lean 4.32, integrado pela PR #280 (commit `8a8fcde3682f804a2e3cdb03dae2be5d71d54654`). Evidência completa em `evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107/`.
- A PR #279 integrou `c5CenteredDirichletTermBox_one_eq_generic` e `c5CenteredDirichletTermBox_one_fixed` (commit `aa542db5f40bc8d1cb5cf76c3ef8d46358702cb0`, merge `b06200968bc004694ee8d7acc3af88463d40ebf2`). O primeiro termo da cabeça, `m=1`, é exatamente `c5GenericBox 11 15`; build Lean 4.32 e auditoria padrão passaram. Isso não cobre os outros 98 termos nem a inclusão da fonte. Evidência em `evidence/rational-boxes/c5-centered-first-term-20261107/`.
- **Próxima obrigação:** fechar uma caixa Gamma completa no primeiro ponto usando a caixa certificada do núcleo racional, a inclusão formal de `240^z` e `gamma_finite_1024_240_error`; depois estender a composição aos nós da interpolação e provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. Não repetir a prova monolítica nem ampliar Taylor sem dependência concreta.
- Alvo final: provar incondicionalmente os sinais de `sigmaPadeD` original em `d=99/2000` e `d=1/10`. A missão permanece incompleta até as inclusões da fonte e a composição final passarem build e auditoria.


## Checkpoint — recorrência nodal `m=2`, `n=18→19` (PR #280 integrada)

`SigmaC5M2TaylorStateStage19Certificate.lean` prova
`c5RoundedExpStateC_stage19_correct` para `(a,j)=(2/5,0)`, usando o estado
`n=18` da PR #275. Lean 4.32.0 compilou com `warningAsError=true`; as cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O probe exportou seis limites racionais; o estado
`n=19` tem potência negativa, termo de Taylor positivo e soma acumulada positiva.
Builds, falha inicial preservada, pins, comandos e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107/`. A compilação
observou 60.45 GiB de `MemAvailable` sob o limite de 30 GiB.

O alcance é apenas uma transição em um nó. Não prova a caixa C2 completa, as
inclusões da fonte nem os sinais finais. A PR #280 integrou o commit de prova `8a8fcde3682f804a2e3cdb03dae2be5d71d54654` na `main` pelo merge
`de09a348a9e2b0f0c6bd700eeed63d92726a56c5`. O GitHub não reportou checks
hospedados. Este checkpoint segue parcial.

## Snapshot anterior — checkpoint auxiliar do nó m=2, n=17→18 (PR #275)

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #275, commit de prova eb7209321914de6733de0bd160e1c64633924dba, merge df23788957cb17b16832d5f4c9e47fd8aa12d68f.
PROOF BASE MAIN: 0807c1052a9e5ac4464139e1593958a495a80103 (PR #274 integrada).
MAIN AT THAT CHECKPOINT: df23788957cb17b16832d5f4c9e47fd8aa12d68f.
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage18_correct (auxiliar).
LAST COMPILED FILE: SigmaC5M2TaylorStateStage18Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=18.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage18-20261107/README.md.
NEXT AT THAT CHECKPOINT: n=19. After the m=1 theorem on the active branch, this is again the next transition for the m=2 term.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Consulte o README de estágio 18 para reprodução, pins, logs e checksums.

## Checkpoint anterior integrado — transição Taylor n=16→17 pela PR #273

`c5RoundedExpStateC_stage17_correct` foi integrado no merge `41164de6cf0042594833bae02cdab2ce4cd11aae`.
Evidência: `evidence/rational-boxes/c5-m2-dirichlet-term-stage17-20261107/`.

## Checkpoint anterior integrado — transição Taylor n=15→16 pela PR #271

`c5RoundedExpStateC_stage16_correct` foi integrado no merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`.
Evidência: `evidence/rational-boxes/c5-m2-dirichlet-term-stage16-20261107/`.

## Checkpoint anterior integrado — transição Taylor n=14→15 pela PR #269

`c5RoundedExpStateC_stage15_correct` foi integrado no merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`.
Evidência: `evidence/rational-boxes/c5-m2-dirichlet-term-stage15-20261107/`.

## Checkpoint anterior integrado — transição Taylor n=13→14 pela PR #267

`c5RoundedExpStateC_stage14_correct` foi integrado no merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`.
Evidência: `evidence/rational-boxes/c5-m2-dirichlet-term-stage14-20261107/`.

## Checkpoint anterior integrado — transição Taylor n=12→13 pela PR #265

`c5RoundedExpStateC_stage13_correct` foi integrado no merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`.
Evidência: `evidence/rational-boxes/c5-m2-dirichlet-term-stage13-20261107/`.

## Checkpoint anterior integrado — transição Taylor n=11→12 pela PR #263

O estágio `c5RoundedExpStateC_stage12_correct` foi integrado no merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`. A prova e a evidência estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage12-20261107/`.

## Retomada mais recente — nó m=2, transição Taylor n=9→10 integrada pela PR #259

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #259, commit de prova 5dd4f4874a192e83af26640f412f81f42239487b, merge d68eec91118e2cdcb89fced66a14062ef6170cf9.
BASE MAIN: 72d91196e14289f1818e33b539776f6fa80f8413 (PR #258 integrada).
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage10_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage10Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=10.
OPEN: n=11…192, outros nós, quadraturas, caixa completa, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/README.md.
PINS: Geometry bf76ce8f5bb753b377a12ba6dbd5c397e4fb3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
EXPORT: probe #eval fornece dados; a igualdade está demonstrada no certificado Lean.
NEXT: continuar a recorrência do nó m=2 em n=11.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Consulte o README de estágio 10 para comando, pins, logs e hashes.

## Retomada mais recente — nó m=2, transição Taylor n=8→9 integrada pela PR #257

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #257, commit de prova 62c9fbd7b04034f21ccf0336abf0d83d8c6a6592, merge 9655308b17dbf565d272f7578545bb68b7b0b867.
BASE MAIN: 27c5496a55dd3bbf2fbca5b7fe92371f7ab44662 (PR #256 integrada).
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage9_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage9Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=9.
OPEN: n=10…192, outros nós, quadraturas, caixa completa, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/README.md.
PINS: Geometry bf76ce8f5bb753b377a12ba6dbd5c397e4fb3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
EXPORT: probe #eval gera os racionais; o certificado Lean prova as igualdades.
NEXT: continuar a recorrência do nó m=2 em n=10.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Consulte o README de estágio 9 para comando, pins, logs e checksums.

## Retomada mais recente — nó m=2, transição Taylor n=7→8 integrada pela PR #255

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #255, commit de prova 96f5f5709829282756bc8c8a2b52a80290c96735, merge 29d363068d52c62c37afc3896f6b3d46f734f16b.
BASE MAIN: e6a05bb60a866502400d163923d5ae749db48d9c (PR #254 integrada).
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage8_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage8Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=8.
OPEN: n=9…192, outros nós, quadraturas, nó completo, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/README.md.
PINS: Geometry bf76ce8f5bb753b377a12ba6dbd5c397e4fb3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
EXPORT: probe #eval fornece os racionais usados; o certificado prova as igualdades.
NEXT: continuar a recorrência do nó m=2 em n=9.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Consulte o README da evidência para o probe, build, pins e hashes.

## Retomada mais recente — nó m=2, transição Taylor n=6→7 integrada pela PR #253

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #253, commit de prova a08a5c9c5a1d02fc33b3207ef2be3d362d526de8, merge 952fcd76093681f3feacc540bb0db9c49bfc6034.
BASE MAIN: c0d2b4799ce81a5428ee84b68a886bd656441779 (PR #252 integrada).
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage7_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage7Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=7.
OPEN: n=8…192, outros nós, quadraturas, nó completo, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/README.md.
PINS: Geometry bf76ce8f5bb753b377a12ba6dbd5c397e4fb3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
EXPORT: probe #eval auxilia a obter os racionais; o certificado prova as igualdades em Lean.
NEXT: continuar a recorrência do nó m=2 em n=8.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Use o README da evidência para reproduzir o probe e o build. O `#eval` fornece
dados de construção e não substitui o teorema certificado.

## Retomada mais recente — nó m=2, transição Taylor n=5→6 integrada pela PR #251

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF PR: #251, commit de prova e6c9ef307c69c59a8e665232b4b0271c481d8fcd, merge 7b61a5ceb0d8567c33fe27a5810d493f4640ed69.
BASE MAIN: 850582ec76a9819149df2cbad4eba49f3e666e40 (PR #250 integrada).
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage6_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage6Certificate.lean (Lean 4.32.0, warnings como erros).
BUILD: BUILD_EXIT=0; cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=6.
OPEN: n=7…192, outros nós, quadraturas, nó completo, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/README.md.
PINS: Geometry bf76ce8f5bb753b377a12ba6dbd5c397e4fb3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
LAST ENVIRONMENT ERROR: tentativa isolada sem o diretório compartilhado de saída não encontrou SigmaC5M2TaylorStateStage5Certificate; log preservado, build final corrigido passou.
NEXT: continuar a recorrência do nó m=2 em n=7.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

Consulte o README da evidência para variáveis de ambiente, pins e comandos de
retomada. A primeira execução sem código de saída registrado e a falha de
configuração do caminho de imports também estão preservadas nessa evidência.

## Retomada mais recente — nó m=2, transição Taylor n=4→5 integrada pela PR #249

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF MERGE: PR #249, commit de prova 1782048f05c43fc31e491fa7192105235b34a14e, merge 58b9a61532f79f6aa51ebfb48edaacf728be3738.
ESTADO: checkpoint integrado; consultar origin/main antes da próxima alteração.
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage5_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage5Certificate.lean (Lean 4.32.0, warnings como erros).
AXIOM AUDIT: cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2, argumento (a,j)=(2/5,0), recorrência até n=5.
OPEN: n=6…192, quadraturas, nó completo, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/README.md.
PINS: Geometry de referência bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

O estágio `n=4` foi integrado pela PR #247 e o registro pós-merge pela PR #248.
Para este passo, siga as dependências e o ambiente no README da evidência.


## Retomada mais recente — nó m=2, transição Taylor n=3→4 integrada pela PR #247

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF MERGE: PR #247, commit de prova 7b355ce2349a242c133caf8d71b777c2a186c0a0, merge ab6d5f1923770d4db830ba9ebf2fbc17c9626149.
ESTADO: checkpoint integrado; consultar origin/main antes da próxima alteração.
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage4_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage4Certificate.lean (Lean 4.32.0, warnings como erros).
AXIOM AUDIT: cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: nó m=2 em (a,j)=(2/5,0), recorrência Taylor n=0…4.
OPEN: n=5…192, quadraturas, nó completo, ponte CSV–Lean, inclusões da fonte e sinais C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/README.md.
PINS: Geometry de referência bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

O estado `n=3` está integrado pela PR #245 e seu registro pós-merge pela PR
#246. Para este estágio, use a sequência de dependências e as configurações de
ambiente descritas no README da evidência indicada acima.


## Retomada mais recente — nó m=2, transição Taylor n=2→3 integrada pela PR #245

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF MERGE: PR #245, commit de prova e264aea05ac6036dea612c5e9ca97c8c7cc81495, merge 727b3920d12e0979c5f722a04732fb346fc880d8.
ESTADO: checkpoint integrado; consultar origin/main antes da próxima alteração.
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage3_correct.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage3Certificate.lean (Lean 4.32.0, warnings como erros).
AXIOM AUDIT: cinco raízes com propext, Classical.choice, Quot.sound; sem sorryAx.
SCOPE: termo nodal m=2 em (a,j)=(2/5,0), recorrência Taylor n=0…3.
OPEN: n=4…192, quadraturas da exponencial, nó completo, ponte CSV–Lean e inclusões C5.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/README.md.
PINS: Geometry de referência bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica dos 192 passos.
```

O estágio 2 já está integrado pela PR #243 e os documentos pós-merge pela PR
#244. Para reproduzir este passo, siga o ambiente e as dependências no README
do estágio 2 e compile o módulo indicado na evidência do estágio 3.


## Retomada anterior — piloto do nó m=2 até o estado n=2

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
PROOF MERGE: PR #243, commit de prova 86d42067db230b661321190ca397bb496e855186, merge 20c30cec4b3964fc063d8eb3c93e09a41d319cfc.
ESTADO: checkpoint integrado; consultar origin/main antes da próxima alteração.
LAST VERIFIED THEOREM: c5RoundedExpStateC_stage2_correct_refined.
LAST COMPILED FILE: SigmaC5M2TaylorStateStage2Refined.lean (Lean 4.32.0, warnings como erros).
AXIOM AUDIT: propext, Classical.choice, Quot.sound nas quatro declarações auditadas; sem sorryAx.
SCOPE: nó (a,j)=(2/5,0), estados Taylor n=0,1,2. Não é a caixa completa m=2 nem a inclusão da fonte.
OPEN: estado n=3; depois n=192 e composição da avaliação completa; ponte das 516 caixas e inclusões C5.
LAST PROOF PR: #243; sem checks hospedados.
EVIDENCE: evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md.
PINS: Geometry de referência bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3; Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; Lean 4.32.0.
DO NOT REPEAT: C1B/C2/C3/C4; migração geral para Lean 4.35; prova monolítica que expande os 192 passos de uma vez.
```

O passo imediato é estender a prova em um passo, usando os registros e comandos
em `evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.
A exportação de estados `n=0…192` é saída de `#eval`, não uma prova. O arquivo que contém a recuperação `sorryAx` está arquivado em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/attempts/` e não
deve ser tratado como compilação válida.


## Retomada anterior — recorrência genérica integrada pela PR #239

```text
MISSION: C5 — certificar as janelas negativas da fonte C2 original.
CURRENT PHASE: ponte CSV–Lean e composição da fonte C2.
CURRENT BASE: main em 8c3691e59f9280864b93c4868eb465dbdad6da2c.
LAST VERIFIED THEOREM: c5RoundedExpC_zero_stage_2_to_192_closed_form.
LAST COMPILED FILE: SigmaC5ZeroExpGenericRecurrenceAudit.lean (Lean 4.32.0, warnings como erros).
LAST PROOF PR: #239, commit de prova be04221f5eb4a174804fb96c9011d0b58bfc2642, merge 8c3691e59f9280864b93c4868eb465dbdad6da2c; sem checks hospedados.
OPEN PR: nenhuma para a recorrência genérica.
WHAT IS PROVED: fórmula fechada da exponencial arredondada na entrada zero, para cada 2≤k≤192; resto original preservado; auditoria com somente axiomas padrão.
WHAT REMAINS: ponte CSV–Lean, composição da fonte C2, inclusões sigmaC00495SourceBoxes/sigmaC01SourceBoxes e sinais finais C5.
EVIDENCE: evidence/rational-boxes/c5-generic-exp-recurrence-20261107/.
RESOURCES: Lean 4.32.0; Carry pin 045369f6dedcb2e75e9aefed1d12c9f73b9a2532; 60.5 GiB disponíveis no build.
DO NOT REPEAT: C1B/C2/C3, migração geral para Lean 4.35 ou estágios C5 já integrados.
```

O build e a auditoria passaram e estão integrados. A reconstrução do módulo-base e as
tentativas de cache que falharam estão registradas junto da reprodução; use
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/reproduce.sh`.

## Retomada anterior — replay intervalar registrado; estágio 6 integrado

Em 2026-11-07, as três gerações experimentais das caixas foram repetidas a
partir do checkout Momentos pinado. A primeira tentativa sem patch reproduziu
e preservou o erro de compatibilidade `gmpy2.mpz` → `Decimal`; com o patch
local apenas de conversão para `int`, as três gerações terminaram e passaram
no verificador racional exato. Os resultados coincidem campo a campo com os
JSONs já arquivados. Isto segue condicional às caixas e não prova as inclusões
dos coeficientes C2 em Lean. Logs, patch, hashes, pins e comandos estão em
`evidence/interval-certificate/reproduction-2026-11-07.md`.

O checkpoint foi integrado pela PR #237, merge
`5fe7837e0f9509950aeb95777bdd220d68835ad8`; o GitHub não reportou checks
hospedados. A branch partiu de `origin/main` em
`9fafe0d7db30e8a8391be863fe8d56dd3ca7ebfb`, após a PR #236. A prova Lean mais
recente continua sendo a igualdade do estágio 6 abaixo; a próxima prova é a
recorrência exata para `2 ≤ k ≤ 192`.

C1B/C2/C3 já estão integradas pelas PRs #155/#157/#159; não as refazer. A
prioridade vigente é C5. O núcleo `m = 1` foi integrado pela PR #222, e as
igualdades dos estágios 1 e 2 pelas PRs #224 e #226.
`SigmaC5ZeroExpStage3Certificate.lean`
importa o estágio 2 integrado e prova que a caixa exponencial arredondada de
estágio 3 coincide com os extremos exportados. Build e auditoria dos nove
teoremas novos passaram em Lean 4.32. A PR #228 integrou a prova, commit
`682eae99f4b05abd70ee8068aada7bc2af3e0ebb`, merge
`0d312c654015bf10384969e64f352b0313e2dd39`. C5 continua incompleta; faltam a
ponte CSV–Lean e as inclusões dos coeficientes da fonte C2 nas caixas.

`SigmaC5ZeroExpStage4Certificate.lean` importa o estágio 3 integrado e prova
`c5ZeroExpStage4_eq`. O build e a auditoria das nove declarações passaram em
Lean 4.32, somente com axiomas padrão. O estágio 4 foi integrado pela PR #230,
commit de prova `fe2df2cd361d0d5096d6c4503468833e364b4481`, merge
`f89cb99d6790bb2c84985c67022b8045a7fb181f`. O erro inicial de import, os
comandos e os logs estão preservados na evidência.

`SigmaC5ZeroExpStage5Certificate.lean` importa o estágio 4 integrado, define a
caixa seguinte em função de `2^896` e prova `c5ZeroExpStage5_eq`. O build e a
auditoria das nove declarações passaram em Lean 4.32, somente com axiomas
padrão. O estágio 5 foi integrado pela PR #232, commit de prova
`821b119d4f0d506e685a585d7f3a52c00a6a95d5`, merge
`75bacc9c2b7ca8113ee906c61a411922e01bb978`.

`SigmaC5ZeroExpStage6Certificate.lean` importa o estágio 5 integrado, define a
caixa seguinte em função de `2^896` e prova `c5ZeroExpStage6_eq`. O build e a
auditoria das nove declarações passaram em Lean 4.32, somente com axiomas
padrão. O estágio 6 foi integrado pela PR #234, commit de prova
`a9be0be89794465fefa44bf66c3b50d5702cc0f5`, merge
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`.

**Base atual:** Geometry `main` após a PR #237, commit
`5fe7837e0f9509950aeb95777bdd220d68835ad8`. A branch formal C5 contém o
estágio 6 integrado pela PR #234; o checkpoint de reprodução da PR #237
partiu do commit `9fafe0d7db30e8a8391be863fe8d56dd3ca7ebfb`.

Retomar provando a recorrência exata das caixas para `2 ≤ k ≤ 192`. Builds,
auditorias, pins, hashes, tentativas e sondas estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. Depois, retomar a
ponte CSV–Lean, compor a fonte C2 original e provar as inclusões O3. Os merges
atuais fecham somente as igualdades dos estágios 1–6, não C5.

## Retomada anterior — 2026-11-07 UTC, componente `log 2` certificado

```text
MISSION: C5 — certificar as primeiras janelas negativas da fonte C2 original.
CURRENT PHASE: continuar a decomposição da caixa CSV–Lean e compor a fonte C2; C5 permanece aberta.
CURRENT BASE: `main` após PR #219, `d6ed8ad249ef69c33920164fe43821cc83f138a8`.
LAST INTEGRATED PROOF PR: #219, commit `bd84a673b3c5c1c82168a6655c59ad6a28bbf127`, merge `d6ed8ad249ef69c33920164fe43821cc83f138a8`. O GitHub não reportou checks hospedados.
FAILED PILOT STILL OPEN: `(a,j)=(2/5,0)` não fecha: `decide` para em `Rat.num`, `rfl` falha por não conversibilidade e `norm_num` excedeu 1M passos após ~28 minutos. A tentativa direta de igualdade para `log 2` foi superada pela prova em blocos.
WHAT IS PROVED: cobertura adaptativa formal de zeta nos 129 nós; exportação de 516 caixas por `#eval`; somas `Interval.logSum 512 (±1/3)` certificadas em 16 blocos de 32 termos; igualdade formal `c5CenteredLog2I 512 = c5ExportedLogTwo512`.
WHAT REMAINS: ligar formalmente as linhas CSV às caixas Lean; avaliar os demais componentes da caixa; compor com Gamma/π/fonte C2 e provar as inclusões em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
EVIDENCE: `evidence/rational-boxes/c5-log2-component-validation/README.md`, mais o histórico das tentativas em `c5-exported-box-proof-attempt/` e `c5-log2-component-attempt/`.
RESOURCES: Lean 4.32; Carry pin `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; não há necessidade de mais memória.
DO NOT REPEAT: C1B/C2/C3/C4; as adaptações Lean 4.35 preservadas; os módulos C5 já integrados.
```

## Retomada anterior — 2026-11-07 UTC, cobertura zeta adaptativa local

```text
MISSION: C5 — certificar as primeiras janelas negativas da fonte C2 original.
CURRENT PHASE: composição das caixas nodais com a fonte original e inclusão O3.
CURRENT SUBTASK: escolher `nExp`/`p`, exportar retângulos racionais, compor zeta/Gamma/fator de π com a cabeça C2 e sua cauda exata.
LAST VERIFIED THEOREM: `CarrySigmaObstruction.c5RationalZetaAdaptiveNodeConjugateBox_contains_at`.
LAST COMPILED FILE: `SigmaC5RationalNodeInstantiateAudit.lean` (Lean 4.32.0, warnings como erros).
LAST PROOF PR: #209, commit `05dae531d4ec10c916c340f58255f35977a3abdd`, merge `386b654eabe4c942d6b0db46754120ab79b52fb5`.
CURRENT MAIN SHA: `386b654eabe4c942d6b0db46754120ab79b52fb5`.
OPEN PR: nenhuma para o checkpoint de cobertura zeta.
WHAT IS PROVED: condições adaptativas de log/exp construídas para todos os `1≤m≤100`; caixas de `riemannZeta` nos 129 nós `b=j/100000` para todo `a∈[2/5,3/5]`, mais os nós conjugados. Cauda Euler–Maclaurin preservada e inflação `<10^-250`. Auditoria de 21 raízes, somente axiomas padrão.
WHAT REMAINS: achatamento de extremos numéricos, composição com Gamma, π e fonte C2, e inclusões dos coeficientes em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 está incompleta.
EVIDENCE: `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`; logs limpos em `evidence/rational-boxes/c5-node-instantiation-clean-20261107/`.
EXACT NEXT MATHEMATICAL OBLIGATION: escolher precisão suficiente para os sinais O3, produzir os extremos racionais de cada nó e compor a fonte C2 original mantendo a cabeça e a cauda exata.
DO NOT REPEAT: C1B/C2/C3/C4; transporte polinomial C4; domínio/cota analítica; faixa de π e fator exponencial; limites dos pesos 0–14; erro Gamma `10^-259`; EM ordem 300; ponte Gamma racional genérica; caixa racional genérica e cobertura adaptativa dos 129 nós já compiladas.
```

A reprodução experimental mais recente e o ajuste de compatibilidade aplicado
somente numa cópia temporária estão documentados em
`evidence/interval-certificate/reproduction-2026-11-06.md`. Use esses logs como
checagem condicional, não como inclusão formal dos coeficientes.

Logs e hashes do subpasso Gamma: `evidence/rational-boxes/c5-gamma-rational-core-validation.md`.
Ele ainda não fornece extremos numéricos para qualquer nó nem prova a inclusão nas caixas O3.

O avaliador genérico foi integrado pela PR #207 como checkpoint explicitamente
incompleto; aquela etapa ainda não instanciava os nós. A cobertura adaptativa
formal foi construída depois e está registrada no checkpoint integrado acima.
Hipóteses, logs, pins e hashes do avaliador genérico original permanecem em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

## Estado mais recente — 2026-11-06

A PR #195 integrou `SigmaC5PiInterval.lean` e `SigmaC5PiExp.lean`, com commit
de prova `321ae94` e merge `0032b10295bfeaadb29d0387f9b99dde9b160ac3`. O build
limpo e a auditoria Lean 4.32 passaram; os detalhes e comandos estão em
`evidence/rational-boxes/c5-pi-completion-factor-validation.md`. O fator
exponencial original dependente de `log π` está incluído em uma caixa, sob as
hipóteses declaradas sobre a caixa de `s`. A avaliação da Gamma, da cauda C2 e
dos 129 nós permanece aberta.

Na retomada da avaliação dos nós, preserve a rota exata via
`nativeScalar_eq_riemannZeta` e a ponte da cabeça C2 mais cauda exata. O
parágrafo anterior sobre `zeta_em4_error` é histórico: a Euler–Maclaurin de
ordem alta foi integrada pela PR #205, e as inclusões e exportações zeta pelas
PRs #211 e #213. O novo gargalo imediato é compor a caixa racional do núcleo
Gamma-piloto com a potência `240^z`; ver
`evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/README.md`.

A PR #191 integrou a cota `10^100` no merge
`88a52ba3a6bda7a78b8317d892b6f7bc640c863f`; a PR #192 integrou a cota mais
forte `10^13`, merge `654dbb0bd7bb7d400cf0c4cab61bea1873995db4`. O contorno de
Cauchy usa raio `38/100`, e a análise racional exata com esse majorante dá
erro `<10^-501`. Detalhes, hashes e logs estão em
`evidence/rational-boxes/analytic-bounds-10pow13-validation.md`.

`SigmaC5PiBounds.lean` foi integrada pela PR #193, commit de prova `45bc923`,
merge `2567ab0204c46c4ce04fca601c99e47e810e18b9`. Build limpo e auditoria
Lean 4.32 passaram para a faixa racional exata de π derivada da série de
`arctan` e da identidade de Machin. A trilha reproduzível está em
`evidence/rational-boxes/c5-pi-bounds-validation.md`.

`SigmaC5PiInterval.lean` e `SigmaC5PiExp.lean` já estão integradas pela PR
#195; consulte `evidence/rational-boxes/c5-pi-completion-factor-validation.md`
para reproduzir o build e a auditoria.

O4/C5 continua incompleta: certificar a avaliação da fonte original nos 129
nós e provar a inclusão dos coeficientes nas caixas O3. Não refazer C1B, C2,
C3, C4, O3, o domínio analítico, a ponte Gamma, os limites de pesos ou a faixa
racional de π já provada.

### Retomar o build da cota analítica

Da raiz da worktree C5, com os checkouts fixados disponíveis:

Se `C5_SOURCE_ANALYTIC_OUTPUT` ainda não existir, compile primeiro
`SigmaC5SourceAnalytic` com o comando de domínio registrado mais abaixo neste
arquivo.

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_SOURCE_ANALYTIC_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-source-analytic-clean-retry1-20261106
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-analytic-bounds-10pow13-repro-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_SOURCE_ANALYTIC_OUTPUT:$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5AnalyticBounds \
    > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log"
  exit "$C5_STATUS"
fi
python3 "$C5_SOURCE_ROOT/check_c5_analytic_bounds_axioms.py" \
  "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-build.log" \
  > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-axiom-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaC5AnalyticBounds.lean" \
  "$C5_SOURCE_ROOT/check_c5_analytic_bounds_axioms.py" \
  "$C5_OUTPUT/SigmaC5AnalyticBounds.olean" \
  > "$C5_EVIDENCE/c5-analytic-bounds-10pow13-repro-source-olean-sha256.txt"
```

O comando `compile_sigma_pade.sh` verifica a revisão limpa do Carry
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, usa Lean 4.32 e exige pelo menos
30 GiB de memória disponível durante a compilação.

**MISSÃO:** certificar as primeiras janelas negativas da fonte C2 original,
para `d=99/2000` e `d=1/10`. A validação segue incompleta até que as caixas
racionais contenham os coeficientes originais.

## Snapshot histórico — início do trabalho C5, antes das PRs #189–#192

- A `origin/main` consultada está em `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- A prova do domínio analítico foi integrada pela PR #189: commit de prova
  `e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge
  `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- Branch de estado pós-merge: `codex/c5-state-after-pr189-20261106`.
- A prova local `SigmaC5SourceAnalytic.lean` fecha o domínio analítico no disco
  aberto de raio `2/5` para `|d|≤1/10`; Lean 4.32 compilou o arquivo com
  `warningAsError=true`, e os quatro `#print axioms` passaram com axiomas padrão.
- Registro daquele checkpoint: a ponte estabelecia apenas o domínio e ainda
  não havia cota do módulo. A cota foi provada depois; as inclusões nas caixas
  continuam pendentes.

- C1–C4 e O3 estão integradas. O3 prova os sinais finais apenas sob as
  hipóteses explícitas de inclusão nas caixas.
- Em Lean 4.32 estão provados os limites dos pesos escalados de graus `0..14`:
  grau zero `=1`, grau um `<10^11`, e todo `2≤n≤14` tem soma `<10^145`.
- `c5InterpolationWeightSum_lt_ten_145` é a última declaração validada.
- A PR #187 integrou essa prova: commit `6424f4334edd5c776997116403043635fa0c8f83`, merge na `main` `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Build limpo com `warningAsError=true`: `evidence/rational-boxes/c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`.
- Auditoria transitiva de 23 teoremas: somente `propext`, `Classical.choice` e
  `Quot.sound`. O checker fail-closed passou; logs e hashes estão ao lado.
- O estado atual foi retomado em `codex/c5-state-after-pr187-20261106`, sobre
  `origin/main` no merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Pins: Lean `leanprover/lean4:v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- C1B/C2/C3/C4 e provas C5 anteriores não devem ser refeitas. A PR #185
  integrou o limite de grau um no merge
  `c840ba35711ac8f938fa24c191f2af60f505480d`; #184 integrou o checkpoint
  explicitamente incompleto em `5528ddc8093a22682c87f3f9c6575e30e90a7011`.

## O que continua aberto — snapshot anterior ao avanço da cota

Naquele snapshot faltava provar uma cota numérica uniforme, além de certificar
a avaliação racional da fonte nos 129 nós e provar a inclusão dos coeficientes
originais nas caixas O3. A cota numérica já foi provada, conforme o estado mais
recente acima; as avaliações e inclusões continuam pendentes. A saída
`mpmath.iv` continua sendo evidência computacional, não prova de inclusão.

Preservar a fonte C2 original, a cabeça e a cauda exponencial exata. A ponte
Euler-Gamma de erro `10⁻²⁵⁹` está provada. A cota dos pesos `<10^145` é uniforme
e suficiente para a margem estimada; não é necessário recuperar o limite
exploratório `10^124`.

## Próximo passo histórico — cota já provada

O passo seguinte naquele checkpoint era provar a cota do módulo. Ela agora está
provada localmente na bola aberta de raio `39/100`; o passo corrente é
certificar as avaliações nos 129 nós e a inclusão nas caixas. Consulte
`evidence/rational-boxes/analytic-bounds-validation.md`.

## Retomada histórica do subpasso de domínio

- Último teorema validado: `CarrySigmaObstruction.displacedProductC_analyticOnNhd_ball`.
- Arquivo compilado: `research/native-moving-schur-sigma/SigmaC5SourceAnalytic.lean`.
- Prova integrada à `main` pela PR #189.
- Branch de estado: `codex/c5-state-after-pr189-20261106`, baseada no merge
  `3513a3b3854b105419d4f2cef245efac7ce88ba0`.
- PR aberta: nenhuma. A próxima PR deve atacar a cota explícita do módulo.
- Não refazer C1B, C2, C3, C4, a recorrência de transporte, O3, a ponte Gamma
  ou os limites dos pesos 0–14.
- Obrigação matemática exata: derivar uma cota explícita do módulo usando a
  expressão original C2 completada, com as remoções de singularidade em
  `s=0` e `s=1` justificadas. O domínio analítico sozinho não basta para
  limitar o resto da interpolação.

Comando de inventário para começar a obrigação seguinte:

```bash
rg -n 'nativeXiCompletionFactor|completedNativeOperatorCharacteristic|nativeScalarDomain|finiteHead_add_exactTail' \\
  /home/thlinux/worktrees/carry-sigma-c2-pinned-045369/CarrySelfAdjointOperator \\
  research/native-moving-schur-sigma
```

Build e auditoria do módulo de domínio:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-source-analytic-repro-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
export SIGMA_HEIGHT50_BUILD="$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5SourceAnalytic \\
    > "$C5_EVIDENCE/c5-source-analytic-repro-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\\n' >> "$C5_EVIDENCE/c5-source-analytic-repro-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-source-analytic-repro-build.log"
  exit "$C5_STATUS"
fi
python3 "$C5_SOURCE_ROOT/check_c5_source_analytic_axioms.py" \\
  "$C5_EVIDENCE/c5-source-analytic-repro-build.log" \\
  > "$C5_EVIDENCE/c5-source-analytic-repro-axiom-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaC5SourceAnalytic.lean" \\
  "$C5_OUTPUT/SigmaC5SourceAnalytic.olean" \\
  > "$C5_EVIDENCE/c5-source-analytic-repro-source-olean-sha256.txt"
```

## Comando de build e auditoria

Da raiz da worktree C5:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree2-14-final-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
    > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
  exit "$C5_STATUS"
fi
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaRationalInterpolation.lean" \
  "$C5_OUTPUT/SigmaRationalInterpolation.olean" \
  "$C5_OUTPUT/interpolation-audit.olean" \
  > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt"
```

The checker report and hashes already committed with the validation record are
`interpolation-audit-degree2-14-final-clean-check.log` and
`c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt`.
