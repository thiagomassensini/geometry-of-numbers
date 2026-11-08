# C5 — validação

## Prefixo 224 — primeira compilação falhou; auditoria não executada (2026-11-08)

- `c5BernoulliPrimeTable_224_eq_data` não compilou em Lean 4.32.0 na primeira tentativa. `BUILD_EXIT=1`, tempo 1h56m46s, pico RSS 9,869,328 KiB.
- Erro: a inclusão do prefixo 160 faltou nas listas de simplificação, deixando aberto `c5BernoulliPrimeDataPrefix160.size = 160` e dependências de `getD` nos índices 192–223. A lista completa de mensagens está preservada em `attempts/first-build-failure-20261108/SigmaC5BernoulliDataCertificate224-clean-build.log`.
- A auditoria isolada não foi rodada; `sorryAx` aparece no log do módulo incompleto em consequência das metas em aberto e não é aceito como resultado.
- Estado validado segue 192/601 pela PR #313. A correção já inclui `c5BernoulliPrimeDataPrefix160` nas quatro listas de simplificação; ela ainda aguarda checkpoint e nova compilação.

## Prefixo 192 — validado e integrado pela PR #313 (2026-11-08)

- `c5BernoulliPrimeTable_192_eq_data` passou em reprodução limpa Lean 4.32.0 com `warningAsError=true`: `BUILD_EXIT=0`, `CLEAN_BUILD=PASS`.
- Auditoria isolada: `AXIOM_AUDIT=PASS`; apenas `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx` ou axiomas próprios.
- Build: 3h07m38s, pico RSS 16,632,976 KiB (aprox. 15.87 GiB). Auditoria: 4.40s, pico RSS 3,236,712 KiB.
- PR #313, commit de prova `636ea8d7ceea1af08adafcdb4d373e8e9b9895b4`, merge `f0bd4ec675a3dc483f55373d3a58092042fac67d`.
- Resultado integrado: prefixo 192/601; 409 valores, a ponte das caixas de zeta, as inclusões da fonte e os sinais finais continuam abertos. Logs, pins, reprodutor e hashes: `evidence/rational-boxes/c5-bernoulli-data-prefix192-20261108/README.md`.

## Prefixo 160 — validação concluída e integrada (2026-11-08)

- `c5BernoulliPrimeTable_160_eq_data` passou em reprodução limpa com Lean 4.32.0 e `warningAsError=true`: `BUILD_EXIT=0`, `CLEAN_BUILD=PASS`.
- A auditoria isolada também passou: `AXIOM_AUDIT=PASS`; dependências axiomáticas somente `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx` ou axiomas próprios.
- Tempo de compilação: 1h56m34s; pico RSS: 12,572,772 KiB (11.99 GiB). Auditoria: 4.23s, pico RSS 3,236,680 KiB. `sha256sum -c SHA256SUMS.txt` passou para todos os artefatos listados.
- Duas execuções anteriores interrompidas continuam preservadas em `evidence/rational-boxes/c5-bernoulli-data-prefix160-20261108/attempts/`; não são falhas da prova. O auditor corrigido está no commit `3cea0c3`.
- Resultado parcial integrado: 160/601 entradas formalmente certificadas pela PR #312, merge `cb829d98d799df72f07c9aff03e9d93871da6f77`; a ponte CSV–Lean, inclusões da fonte, 441 entradas e sinais finais continuam abertas.

## Validação recente — prefixo Bernoulli de 128 entradas (PR #309, 2026-11-08)

- `c5BernoulliPrimeTable_128_eq_data` prova formalmente os índices 0–127 a partir do certificado integrado de 96 entradas.
- Reprodução limpa Lean 4.32.0 com `warningAsError=true`: sonda, tabela, certificado 128 e auditoria compilaram; todos os logs registram `BUILD_EXIT=0` (`CLEAN_BUILD=PASS`).
- Comparação racional exata da sonda com os literais: `DATA_TABLE_CHECK=PASS`, `COEFFICIENTS=601`. Auditoria isolada: `AXIOM_AUDIT=PASS`, apenas `propext`, `Classical.choice` e `Quot.sound`.
- O teorema compilou em 1h15m45s, pico RSS de 9,450,592 KiB (aprox. 9.01 GiB). A tentativa anterior com limite padrão de simplificação falhou e continua preservada, não contabilizada como prova.
- O certificado aumenta o prefixo formal para 128/601; 473 valores, a ponte CSV–Lean, as inclusões da fonte e os sinais finais continuam abertos. Evidência, pins, reprodução, logs e hashes: `evidence/rational-boxes/c5-bernoulli-data-prefix128-20261108/README.md`.
- Integrado à `main` pela PR #309, commit de prova `b6f2611`, merge `c7782c54b78f97b1ea3f5a61f6e0ceefe75f2f11`.

## Validação recente — prefixo Bernoulli de 96 entradas (PR #302)

- `c5BernoulliPrimeTable_96_eq_data` prova as entradas 0–95, apoiando-se no certificado integrado de 64 entradas.
- Reprodução limpa Lean 4.32.0 com `warningAsError=true`: sonda, tabela, teorema 96 e auditoria compilaram. `CLEAN_BUILD=PASS`.
- Comparação racional exata da sonda com os 601 literais: `DATA_TABLE_CHECK=PASS`. Auditoria isolada: `AXIOM_AUDIT=PASS`; apenas `propext`, `Classical.choice` e `Quot.sound`.
- O teorema compilou em 38m42s, pico RSS de 6.45 GiB. PR #302, commit `4fc4c8d`, merge `b72149bf5727f2440c676f4f414664788fa010ba`.
- Limite: 96/601 entradas estão formalmente provadas; as outras 505, a ponte CSV–Lean das caixas de zeta e as inclusões da fonte continuam abertas. Evidências: `evidence/rational-boxes/c5-bernoulli-data-prefix96-20261108/README.md`.

## Histórico — prefixo Bernoulli de 64 entradas (PR #300)

O certificado anterior provou 64/601 entradas em 14m09s, com pico RSS de aproximadamente 4.8 GiB. A PR #302 estendeu o prefixo até 96. Evidência: `evidence/rational-boxes/c5-bernoulli-data-prefix64-20261108/README.md`.

## Histórico — primeiro bloco da tabela de Bernoulli (PR #298)

- `c5BernoulliPrimeTable_32_eq_data` prova formalmente que o prefixo de 32 valores coincide com a recorrência `c5BernoulliPrimeTable`.
- Reprodução limpa em Lean 4.32.0 e `warningAsError=true`: sonda, tabela, certificado e auditoria compilaram; `CLEAN_BUILD=PASS`.
- Comparação racional exata entre os 601 valores emitidos pela sonda Lean e os literais: `DATA_TABLE_CHECK=PASS`, `COEFFICIENTS=601`.
- Auditoria isolada: `AXIOM_AUDIT=PASS`, somente `propext`, `Classical.choice`, `Quot.sound`. Certificado ~2:34 e 3.7 GiB RSS; sonda ~1:42 e 2.7 GiB RSS.
- PR #298, commit `1ed4a00`, merge `171c19681482312bf71bffdcd23b24a728edf04b`. Fontes, pins, reprodução, logs, tentativas e hashes: `evidence/rational-boxes/c5-bernoulli-data-prefix32-20261108/README.md`.
- Limite: apenas os primeiros 32 valores têm igualdade formal certificada. A verificação dos 601 literais contra a saída da sonda é uma comparação reprodutível, ainda não substitui as provas formais dos blocos restantes nem liga as caixas exportadas de zeta a definições Lean.

## Histórico — nó complementar de Gamma para `d=1/10` (PR #296)

- Fonte: `SigmaC5GammaComplexNodeDOneUpperComplexGammaCertificate.lean`; teorema `CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexBox_contains`.
- `SigmaC5GammaDOneUpperLogBounds.lean` prova `|Interval.logQ 384 8 240| ≤ 10`, o limite que faz caber o argumento de potência no raio 8.
- Seis módulos compilaram em Lean 4.32.0 com `warningAsError=true`; 16 relatórios contêm apenas `propext`, `Classical.choice`, `Quot.sound`. Sem `sorryAx`, axiomas próprios ou `native_decide`.
- A caixa contém `Complex.Gamma (3/10 + (3/20) * Complex.I)`, compondo `240^z`, 16 blocos × 64 termos e erro `10⁻⁹⁹`. Pico RSS: 8.4 GiB; reprodução limpa passou.
- Commit `e986390937265fc1bb759140ed7fb6d80d23eadf`, PR #296, merge `113ed1517fff040f4fc619cf7d5086c57f137427`. Evidência, pins, hashes, logs e falha corrigida: `evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108/README.md`.

## Histórico — primeiro nó complexo de Gamma para `d=1/10`

- Fonte principal: `SigmaC5GammaComplexNodeDOneComplexGammaCertificate.lean`; declaração `CarrySigmaObstruction.c5GammaComplexNodeDOneComplexBox_contains`.
- Build limpo dos cinco módulos em Lean 4.32.0 com `warningAsError=true`, saída zero em cada etapa; reprodução executada de novo com sucesso. Pico RSS: 8.4 GiB.
- Os 14 relatórios usam somente `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx`, axiomas próprios ou `native_decide`.
- A caixa contém `Complex.Gamma (1/5 + (3/20) * Complex.I)`, usando `240^z`, 16 blocos × 64 termos do núcleo racional e erro `10⁻⁹⁹`.
- PR #294 integrou o commit `752e6d1` no merge `5175969e6e11ccb1a7460389e78efe7c8f78ee60`. Builds, checker, reprodução, pins e hashes: `evidence/rational-boxes/c5-gamma-d1-complex-node-20261108/README.md`.

## Histórico — segundo nó complexo de Gamma

- Fonte principal: `SigmaC5GammaComplexNodeUpperGammaCertificate.lean`; declaração `CarrySigmaObstruction.c5GammaComplexNodeUpperBox_contains`.
- Build limpo dos cinco módulos em Lean 4.32.0 com `warningAsError=true`, saída 0 em cada etapa; pico RSS de 11.5 GiB.
- Os 14 relatórios cobrem 11 declarações novas e três auxiliares recompiladas. Só dependem de `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx`, axiomas próprios ou `native_decide`.
- A caixa contém `Complex.Gamma (1099/4000 + (3/20) * Complex.I)`, usando `240^z`, 16 blocos × 64 termos do núcleo racional e erro `10⁻⁹⁹`.
- PR #292 integrou o commit `5a859f7` no merge `18784869bd942422cfc2ace1b70e7e2ba8623b0f`. Build, logs, pins, hashes e tentativas: `evidence/rational-boxes/c5-gamma-complex-upper-node-20261107/README.md`.

## Histórico — primeiro nó complexo de Gamma

- Fonte principal: `SigmaC5GammaComplexNodeGammaCertificate.lean`; declaração `CarrySigmaObstruction.c5GammaComplexNodeBox_contains`.
- O build limpo recompilou os cinco módulos em Lean 4.32.0 com `warningAsError=true`; cada etapa terminou com saída 0.
- Auditoria das raízes: somente `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx`, axiomas próprios ou `native_decide`.
- A caixa composta contém `Complex.Gamma (901/4000 + (3/20) * Complex.I)` e usa a inflação `10⁻⁹⁹`.
- PR #290 integrou o commit `482110b10c9173f6a8c9b231c7f3ed07c0935933` no merge `06001aaae85c19d01dca48a802fecbb06ffb381d`. Build, logs, pins, hashes e tentativas: `evidence/rational-boxes/c5-gamma-complex-node-20261107/README.md`.

## Validação anterior — caixa `Γ(901/4000)`

- Fonte principal: `SigmaC5GammaSecondRealPointGammaCertificate.lean`, SHA-256 `931ca3014a0443fe40bd213c5f9f0dc2cae4a864b986b49a86f46e34cf005411`.
- Os módulos Probe, Certificate, Combine e Gamma foram compilados em Lean 4.32.0 via `compile_sigma_pade.sh`; `warningAsError=true`, saída 0 em cada log.
- Auditoria das raízes públicas: apenas `propext`, `Classical.choice`, `Quot.sound`; sem `sorryAx`, axiomas próprios ou `native_decide`.
- A caixa composta contém `Complex.Gamma (901/4000 : ℂ)` e usa a inflação `10⁻⁹⁹`.
- PR #287 integrou o resultado no merge `742eb6fd03311adbb80507867c47e726fd648a21` (commit `7f3d880e73f5383718cf2442b915e8cd866139cf`). Evidência: `evidence/rational-boxes/c5-gamma-second-real-point-20261107/README.md`.

## Histórico — caixa `Γ(1/5)` integrada pela PR #285

- `CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains` contém `Complex.Gamma (1/5 : ℂ)`.
- PR #285 integrou o commit `742dd764df81ee75bd487d1bf21e5a9afa5519c5`; merge `832b201b6907c6682aa9657c3e4ff9da6dd40254`.
- Fonte, comando, hashes e logs: `evidence/rational-boxes/c5-gamma-first-node-20261107/README.md`.

## Histórico — checkpoint do núcleo Gamma racional por blocos (PR #282)

- Base de `main`: merge da PR #281, `ec5c5e8998b62726ada6f942cf4c2410048a2a23`; branch de trabalho `codex/c5-o4-after-stage19-20261107`. Geometry de referência está em `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Integração: PR #282, commit de prova `131d5f57da009a830c0a967bb5cf4713412c3473`, merge `7c301a2bb0b975369c8f8889ec2940372d2266c2` em 2026-11-07. O checkpoint já está na `main`.
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

## Primeiro termo da cabeça centrada — compilado e auditado nesta branch

`SigmaC5CenteredFirstTerm.lean` compila em Lean 4.32.0 com `warningAsError=true` (`BUILD_EXIT=0`). O checker fail-closed aceitou as duas raízes; somente `propext`, `Classical.choice` e `Quot.sound` aparecem. O resultado identifica `m=1` com `c5GenericBox 11 15`, mas não implica as inclusões C5. Reproduza por `evidence/rational-boxes/c5-centered-first-term-20261107/reproduce.sh`; build, hashes e pin estão no README local.

## Checkpoint auxiliar: transição do nó m=2 para n=18 — integrada pela PR #275; C5 parcial

`SigmaC5M2TaylorStateStage18Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`; o build terminou com `BUILD_EXIT=0`. As cinco raízes
auditadas usam somente `propext`, `Classical.choice` e `Quot.sound`, sem
`sorryAx`. Pins, logs e comando estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage18-20261107/`.

A prova cobre `c5RoundedExpStateC` somente até `n=18` no nó `(2/5,0)`.
Estados seguintes, quadraturas, caixa completa, composição com a fonte C2 e
sinais finais continuam abertos. A PR #275 integrou o commit `eb7209321914de6733de0bd160e1c64633924dba` pelo
merge `df23788957cb17b16832d5f4c9e47fd8aa12d68f`; o GitHub não reportou checks hospedados. C5 permanece
incompleta.

## Transição do nó m=2 para n=17 — integrada pela PR #273

`c5RoundedExpStateC_stage17_correct` compilou e passou pela auditoria Lean.
A integração ocorreu no merge `41164de6cf0042594833bae02cdab2ce4cd11aae`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage17-20261107/`.

## Transição do nó m=2 para n=16 — integrada pela PR #271

`c5RoundedExpStateC_stage16_correct` compilou e passou pela auditoria Lean.
A integração ocorreu no merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage16-20261107/`.

## Transição do nó m=2 para n=15 — integrada pela PR #269

`c5RoundedExpStateC_stage15_correct` compilou e passou pela auditoria Lean.
A integração ocorreu no merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage15-20261107/`.

## Transição do nó m=2 para n=14 — integrada pela PR #267

`c5RoundedExpStateC_stage14_correct` compilou e passou pela auditoria Lean.
A integração ocorreu no merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage14-20261107/`.

## Transição do nó m=2 para n=13 — integrada pela PR #265

`c5RoundedExpStateC_stage13_correct` compilou e passou pela auditoria Lean.
A integração ocorreu no merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage13-20261107/`.

## Transição do nó m=2 para n=12 — integrada pela PR #263

`c5RoundedExpStateC_stage12_correct` compilou e passou pela auditoria em Lean
4.32.0. A PR #263 integrou o commit de prova
`b7c442c318de488cb928fc8e456110b4b27a81f4` no merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage12-20261107/`.

## Transição do nó m=2 para n=10 — passou e foi integrada pela PR #259; C5 parcial

`SigmaC5M2TaylorStateStage10Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`; os pins e o comando estão no README da evidência. O
build terminou em `BUILD_EXIT=0`; as cinco raízes auditadas dependem somente de
`propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/`.

A prova valida `c5RoundedExpStateC` apenas até `n=10` no nó `(2/5,0)`. Os
estados restantes, quadraturas, caixa completa, inclusão da fonte C2 e sinais
finais continuam abertos. A PR #259 integrou o commit de prova
`5dd4f4874a192e83af26640f412f81f42239487b` no merge
`d68eec91118e2cdcb89fced66a14062ef6170cf9`; o GitHub não reportou checks
hospedados. C5 permanece incompleta.

## Transição do nó m=2 para n=9 — passou e foi integrada pela PR #257; C5 parcial

`SigmaC5M2TaylorStateStage9Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`, Geometry e Carry nos pins indicados no README. O build
terminou com `BUILD_EXIT=0`; as cinco raízes auditadas dependem somente de
`propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`. Evidência e
comando em `evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/`.

A prova valida somente `c5RoundedExpStateC` até `n=9` no nó `(2/5,0)`. Estados
seguintes, quadraturas, caixa completa, ponte CSV–Lean, inclusão da fonte C2 e
sinais finais continuam abertos. A PR #257 integrou o commit de prova
`62c9fbd7b04034f21ccf0336abf0d83d8c6a6592` no merge
`9655308b17dbf565d272f7578545bb68b7b0b867`; o GitHub não reportou checks
hospedados. C5 permanece incompleta.

## Transição do nó m=2 para n=8 — passou e foi integrada pela PR #255; C5 parcial

`SigmaC5M2TaylorStateStage8Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`, usando Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O build terminou com
`BUILD_EXIT=0`; as cinco raízes auditadas usam somente `propext`,
`Classical.choice` e `Quot.sound`, sem `sorryAx`. Fonte, logs e comando em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/README.md`.

A prova valida apenas `c5RoundedExpStateC` até `n=8` no nó `(2/5,0)`. Os
estados seguintes, quadraturas, caixa completa, composição com a fonte C2 e
sinais finais permanecem abertos. A PR #255 integrou o commit de prova
`96f5f5709829282756bc8c8a2b52a80290c96735` no merge
`29d363068d52c62c37afc3896f6b3d46f734f16b`; o GitHub não reportou checks
hospedados. C5 segue incompleta.

## Transição do nó m=2 para n=7 — passou e foi integrada pela PR #253; C5 parcial

`SigmaC5M2TaylorStateStage7Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`, usando Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O build terminou com
`BUILD_EXIT=0`; as cinco declarações auditadas reportam somente `propext`,
`Classical.choice` e `Quot.sound`, sem `sorryAx`. Fonte, logs e comando em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/README.md`.

A prova cobre somente `c5RoundedExpStateC` até `n=7` no nó `(2/5,0)`. Os
estados seguintes, quadraturas, caixa completa e a inclusão dos coeficientes
da fonte C2 continuam abertos. A PR #253 integrou o commit de prova
`a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` no merge
`952fcd76093681f3feacc540bb0db9c49bfc6034`; o GitHub não reportou checks
hospedados. C5 segue incompleta.

## Transição do nó m=2 para n=6 — passou e foi integrada pela PR #251; C5 parcial

`SigmaC5M2TaylorStateStage6Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`, contra Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O build terminou com
`BUILD_EXIT=0`; as cinco raízes auditadas mostram somente `propext`,
`Classical.choice` e `Quot.sound`, sem `sorryAx`. Log e comando em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/README.md`.

A prova cobre apenas `c5RoundedExpStateC` até `n=6` no nó `(2/5,0)`. Ela não
fecha os outros termos, as quadraturas, a caixa nodal completa ou a ligação
entre as caixas e os coeficientes da fonte C2. A PR #251 integrou o commit de
prova `e6c9ef307c69c59a8e665232b4b0271c481d8fcd` no merge
`7b61a5ceb0d8567c33fe27a5810d493f4640ed69`; o GitHub não reportou checks
hospedados. C5 permanece incompleta.

## Transição do nó m=2 para n=5 — PASSOU e foi integrada pela PR #249; C5 parcial

`SigmaC5M2TaylorStateStage5Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`. As cinco raízes auditadas reportam somente
`propext`, `Classical.choice` e `Quot.sound`; o build aprovado não contém
`sorryAx`. Não houve tentativa de prova Lean que falhasse.

A validação cobre somente `c5RoundedExpStateC` até `n=5` para `(a,j)=(2/5,0)`.
Os estados restantes, as quadraturas, a caixa completa, a ponte CSV–Lean e as
inclusões da fonte C2 permanecem abertas. Evidência e comando em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/README.md`.
C5 segue incompleta. A PR #249 integrou a prova na `main`, merge
`58b9a61532f79f6aa51ebfb48edaacf728be3738`; o GitHub não reportou checks.


## Transição do nó m=2 para n=4 — PASSOU e foi integrada pela PR #247; C5 parcial

`SigmaC5M2TaylorStateStage4Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`. As cinco raízes auditadas mostram somente
`propext`, `Classical.choice` e `Quot.sound`; o build aceito não tem
`sorryAx`. Nesta etapa não houve tentativa de prova Lean que falhasse.

A prova certifica somente `c5RoundedExpStateC` até `n=4` no nó `(2/5,0)`. Não
prova os outros termos, as quadraturas da exponencial, a caixa nodal completa
ou as inclusões dos coeficientes C2. Fonte, log e reprodução estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/README.md`.
C5 permanece incompleta. A PR #247 integrou a prova na `main`, merge
`ab6d5f1923770d4db830ba9ebf2fbc17c9626149`; o GitHub não reportou checks.


## Transição do nó m=2 para n=3 — PASSOU e foi integrada pela PR #245; C5 parcial

`SigmaC5M2TaylorStateStage3Certificate.lean` compilou em Lean 4.32.0 com
`warningAsError=true`. As cinco declarações auditadas reportam somente
`propext`, `Classical.choice` e `Quot.sound`. O build aprovado não contém
`sorryAx`. A primeira tentativa ficou aberta por uma variável não usada e por
falta de desdobramento da caixa da soma; o log foi preservado separadamente.

A prova valida apenas `c5RoundedExpStateC` em `n=3` para o nó `(2/5,0)`. Ela
não certifica os demais estados, as quadraturas da exponencial, a caixa nodal
completa ou a inclusão dos coeficientes originais. Evidências e comando em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/README.md`.
C5 permanece incompleta. A PR #245 integrou a prova na `main`, merge
`727b3920d12e0979c5f722a04732fb346fc880d8`; o GitHub não reportou checks.


## Piloto do nó m=2 até n=2 — PASSOU e foi integrado pela PR #243; C5 parcial

`SigmaC5M2TaylorStateStage2Refined.lean` compilou em Lean 4.32.0 com
`warningAsError=true`. A auditoria das quatro raízes
`c5M2Stage2PowerCoarsenExport`, `c5M2Stage2PowerCorrect`,
`c5M2Stage2SumCorrect` e `c5RoundedExpStateC_stage2_correct_refined` mostrou
somente `propext`, `Classical.choice` e `Quot.sound`. O último log mostra código
zero e não contém `sorryAx`.

A prova valida a transição de `c5RoundedExpStateC` de `n=1` para `n=2` para o
argumento do nó `(2/5,0)`, derivado do log `2` e quatro metades. Não valida a
série de 192 termos nem a caixa nodal completa. A tentativa monolítica e as
iterações falhas foram mantidas como evidência negativa, separadas do build
aceito. Fontes, logs, hashes, pins e comandos de reprodução estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.
A ponte CSV–Lean e as inclusões da fonte C2 continuam abertas. A PR #243
incluiu o checkpoint na `main`, merge
`20c30cec4b3964fc063d8eb3c93e09a41d319cfc`; o GitHub não reportou checks.


## Recorrência genérica da exponencial nos estágios 2–192 — PASSOU e FOI INTEGRADA; C5 parcial

`SigmaC5ZeroExpGenericRecurrence.lean` prova a igualdade fechada entre
`c5RoundedExpC 192 896 k (ComplexInterval.exact 0 0)` e a caixa definida por
`3*2^(k-2)-1` e `4*2^(k-2)-1`, para cada `2 ≤ k ≤ 192`. O passo genérico
certifica os quatro extremos da caixa quadrada, os pisos e tetos em 896 bits e
o limite de erro que torna a recorrência uniforme. A prova mantém o resto
racional original.

O build limpo em Lean 4.32.0 passou com `warningAsError=true`; a auditoria
separada mostrou apenas `propext`, `Classical.choice` e `Quot.sound` nas quatro
raízes. Os logs, fontes, pins, hashes e comando estão em
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`. PR #239 integrou
o checkpoint: commit de prova `be04221f5eb4a174804fb96c9011d0b58bfc2642`, merge
na `main` `8c3691e59f9280864b93c4868eb465dbdad6da2c`; o GitHub não reportou
checks. C5 continua parcial: sem ponte CSV–Lean, inclusão da fonte C2 ou sinais
finais.

## Nó trivial `m = 1` e igualdades dos estágios 1–6 — PASSARAM; C5 parcial

Em Lean 4.32.0, com `warningAsError=true`, passaram os builds de
`SigmaC5RationalNodePreciseLogBounds.lean`,
`SigmaC5RoundedComplexExp.lean` e
`SigmaC5RationalNodeCenteredBoxes.lean`. As auditorias cobrem sete teoremas:
o estado do log em zero, `log 1`, a conversão do log centrado, o argumento e o
termo de Dirichlet em `m = 1`, e o estado/caixa da exponencial na entrada zero.
Todas reportam somente `propext`, `Classical.choice` e `Quot.sound`.

A prova preserva a inflação racional que limita o resto de Taylor.
`SigmaC5ZeroExpStagesCertificate.lean` prova que a caixa de estágio 1 na
entrada zero coincide exatamente com `c5ZeroExpStage1Export`; quatro lemas
provam os pisos e tetos por desigualdades racionais exatas. O build Lean 4.32
com `warningAsError=true` passou, e a auditoria por import das seis raízes
reporta somente `propext`, `Classical.choice` e `Quot.sound`. As falhas antigas
continuam preservadas como histórico, sem serem tratadas como validação. Logs,
fontes, pins, hashes e comandos estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

C5 segue incompleta; não há ponte CSV–Lean, composição completa da fonte C2,
inclusões O3 ou prova dos sinais finais. O núcleo inicial do nó trivial foi
integrado pela PR #222, commit `67e6cf9fdf86ac735b6ade80d2f4a64982968363`, merge
`e55858690e296d00c88692b8f30902987e853137`; o GitHub não reportou checks
hospedados. A atualização do estágio 1 foi integrada pela PR #224, commit de
prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`; o GitHub não reportou checks.

O estágio 2 agora também passou: `c5ZeroExpStage2_eq` coincide com
`c5ZeroExpStage2Export`; quatro novos lemas certificam os pisos/tetos por
desigualdades racionais exatas. Build limpo e auditoria das onze raízes
passaram em Lean 4.32.0, somente com axiomas padrão. Evidências e hashes estão
no mesmo diretório. A PR #226 integrou o subpasso, commit de prova
`ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`, merge
`96579150be6700793970bf8cd84f91dd2cccb102`; o GitHub não reportou checks.

O estágio 3 também passou localmente. `SigmaC5ZeroExpStage3Certificate.lean`
importa a prova integrada do estágio 2 e mostra que
`c5RoundedExpC 192 896 3` na entrada zero coincide com
`c5ZeroExpStage3Export`. Quatro lemas provam os extremos exatos da caixa
quadrada e quatro certificam pisos/tetos. Build limpo e auditoria das nove
raízes passaram em Lean 4.32.0, somente com axiomas padrão. Os logs, pins,
hashes e histórico das tentativas interrompidas estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. Este resultado
foi integrado pela PR #228, commit de prova
`682eae99f4b05abd70ee8068aada7bc2af3e0ebb`, merge na `main`
`0d312c654015bf10384969e64f352b0313e2dd39`; o GitHub não reportou checks.
Não fecha a ponte CSV–Lean nem as inclusões O3.

O estágio 4 também passou localmente. `SigmaC5ZeroExpStage4Certificate.lean`
importa a prova integrada do estágio 3 e mostra que
`c5RoundedExpC 192 896 4` na entrada zero coincide com
`c5ZeroExpStage4Export`. Quatro lemas provam os extremos racionais do quadrado
do estágio 3 e quatro certificam os pisos/tetos `2^896 - 11`, `2^896 + 15`,
`-15` e `15`. Build e auditoria das nove raízes passaram em Lean 4.32.0,
somente com axiomas padrão. Pins, hashes, logs e o erro inicial de import estão
em `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. O estágio 4 foi
integrado pela PR #230, commit de prova
`fe2df2cd361d0d5096d6c4503468833e364b4481`, merge na `main`
`f89cb99d6790bb2c84985c67022b8045a7fb181f`; o GitHub não reportou checks.
C5 continua incompleta.

O estágio 6 também passou localmente. `SigmaC5ZeroExpStage6Certificate.lean`
importa a prova integrada do estágio 5, define `c5ZeroExpStage6Export` e prova
que `c5RoundedExpC 192 896 6` na entrada zero coincide com essa caixa. Os
extremos racionais do quadrado do estágio 5 dão pisos/tetos `2^896 - 47`,
`2^896 + 63`, `-63` e `63`. Build e auditoria das nove raízes passaram em
Lean 4.32.0, somente com axiomas padrão. Pins, hashes e logs estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. O estágio 6 foi
integrado pela PR #234, commit de prova
`a9be0be89794465fefa44bf66c3b50d5702cc0f5`, merge na `main`
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`; o GitHub não reportou checks.
C5 continua incompleta.

O estágio 5 também passou localmente. `SigmaC5ZeroExpStage5Certificate.lean`
importa a prova integrada do estágio 4, define `c5ZeroExpStage5Export` e prova
que `c5RoundedExpC 192 896 5` na entrada zero coincide com essa caixa. Os
extremos racionais do quadrado do estágio 4 dão pisos/tetos `2^896 - 23`,
`2^896 + 31`, `-31` e `31`. Build e auditoria das nove raízes passaram em
Lean 4.32.0, somente com axiomas padrão. Pins, hashes e logs estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. O estágio 5 foi
integrado pela PR #232, commit de prova
`821b119d4f0d506e685a585d7f3a52c00a6a95d5`, merge na `main`
`75bacc9c2b7ca8113ee906c61a411922e01bb978`; o GitHub não reportou checks.
C5 continua incompleta.

## Componente `log 2` em blocos — PASSOU; C5 permanece parcial

`SigmaC5Log2Certified.lean` prova as somas racionais
`Interval.logSum 512 (1/3)` e `Interval.logSum 512 (-1/3)` por decomposição em
16 blocos de 32 termos. A soma dos blocos é recomposta formalmente, e
`c5CenteredLog2I 512 = c5ExportedLogTwo512` certifica exatamente os extremos
exportados desse componente.

O build Lean 4.32.0 passou com warnings como erros. O checker fail-closed
aceitou exatamente as três declarações auditadas; só aparecem `propext`,
`Classical.choice` e `Quot.sound`. A varredura da fonte não encontrou
`sorry`, `sorryAx`, `admit` ou `native_decide`. Fonte, checker, build/auditoria,
saída `#eval`, pins, hashes e comando reprodutor estão em
`evidence/rational-boxes/c5-log2-component-validation/README.md`.
O commit de prova `bd84a673b3c5c1c82168a6655c59ad6a28bbf127` foi integrado
pela PR #219, merge na `main` `d6ed8ad249ef69c33920164fe43821cc83f138a8`;
não houve checks hospedados.

**Limite:** isso fecha só o componente central `log 2`. O CSV de 516 extremos
continua sem igualdade formal com as caixas Lean; a cabeça e demais correções
não foram compostas com Gamma, fator de π e fonte C2. As inclusões
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` seguem abertas, então os sinais
C5 permanecem condicionais.

## Tentativa de igualdade CSV–Lean — FALHOU; C5 segue parcial

A primeira linha do CSV foi testada contra `c5RationalZetaCenteredNodeBox`.
`decide` não reduziu `Rat.num`, `rfl` não foi conversível, e `norm_num` com
`maxSteps=1000000` excedeu o limite após ~28 minutos. Não foi produzido
`.olean` válido nem auditoria do teorema; a saída `sorryAx` após erro é
inválida. O pico foi ~7,6 GiB com ~58 GiB disponíveis, apontando custo de
redução e não falta de RAM. A exportação CSV permanece não ligada formalmente
às definições Lean e não foi usada para provar as inclusões dos coeficientes.
Comandos, pins, fontes e logs estão em
`evidence/rational-boxes/c5-exported-box-proof-attempt/`. O checkpoint foi
integrado pela PR #215, commit `baa5e3e`, merge `6bfb4b14606ec1896a2d01d60be4ca54117bd128`.

## Primeira abordagem direta de `log 2` — FALHOU; substituída pela prova em blocos

A tentativa inicial exportou `c5CenteredLog2I 512`, mas as provas diretas por
`norm_num` deixaram metas abertas mesmo após separar os campos e elevar
`maxSteps` a 1M. Essa abordagem não gerou teorema auditável; o histórico foi
integrado pela PR #217, commit `e34733a`, merge
`30a615cafa3b27de40427a73cc64988c77e236d3`. O resultado foi depois superado
pela prova certificada em blocos documentada acima. As fontes e logs antigos
permanecem em `evidence/rational-boxes/c5-log2-component-attempt/`.

## Cobertura zeta adaptativa dos 129 nós — PASSOU; C5 parcial

`SigmaC5RationalNodeLogBounds.lean` e `SigmaC5RationalNodeInstantiate.lean`
constroem as condições do avaliador de log/exp para `1≤m≤100` e provam
`c5RationalZetaAdaptiveNodeBox_contains_at` para cada `j≤128`, com
`b=j/100000` e `a∈[2/5,3/5]`. O teorema conjugado cobre parte imaginária
negativa. A caixa conserva a cauda Euler–Maclaurin exata, limitada por
`<10^-250`.

A compilação limpa em Lean 4.32, com warnings como erros, terminou com
`BUILD_EXIT=0` para os nove módulos da cadeia. O checker fail-closed aceitou 21
raízes; aparecem somente `propext`, `Classical.choice` e `Quot.sound`. Logs,
hashes, pins, comando de reprodução e tentativas anteriores estão no registro
`evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.

Este checkpoint foi integrado pela PR #209, commit de prova
`05dae531d4ec10c916c340f58255f35977a3abdd`, merge
`386b654eabe4c942d6b0db46754120ab79b52fb5`. Ainda não exporta extremos
numéricos achatados nem compõe Gamma, o fator dependente de π e a fonte C2;
não prova as inclusões O3 e não fecha C5. A branch de prova partiu do merge
da PR #208 `296e899e70bee78c54a3278e73e9bd89eaafaa58`.

## Avaliador racional genérico de zeta — PROVADO CONDICIONALMENTE

O build limpo de `SigmaC5RationalNodeEval.lean` e
`SigmaC5RationalNodeEvalAudit.lean` passou em Lean 4.32, com warnings como
erros. A auditoria de dez teoremas encontrou somente `propext`,
`Classical.choice` e `Quot.sound`; o checker fail-closed passou. A fatorização
de `emZetaHighRHS 100 300` mantém a soma de cauda explícita, e
`c5RationalZetaNodeBox_contains` inclui zeta sob condições explícitas do
avaliador `logQ`/`expCr`, inflando pela cota `<10^-250`.

Checkpoint integrado pela PR #207: commit de prova
`fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df`, merge na `main`
`27a61e6bebcce178b81b961f507400ed77b96d3b`. Essa integração não altera os
limites de validação abaixo.

As condições de intervalo continuam sem instanciação concreta nos 129 nós.
Este checkpoint não calcula caixas para Gamma ou para a fonte C2 e não prova
as inclusões dos coeficientes nas caixas O3. Logs, pins, hashes e falha do
primeiro comando de reprodução estão em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

## Reprodução das três caixas intervalares — PASSOU, condicional

As três configurações prescritas foram executadas novamente em uma cópia
temporária do checkout Momentos; o checkout compartilhado permaneceu sem
alterações. A cópia usou o patch preservado `momentos-gmpy2-compat.patch`, que
normaliza `gmpy2.mpz` para `int` antes de passar numeradores e denominadores a
`Decimal`. Todas as gerações terminaram com `REPRO_EXIT=0`. O verificador
independente por frações racionais exatas também passou nas três saídas, com
`+++++++++++-` nas duas configurações `d=0.0495` e `+++++++++-` em `d=0.1`.

Logs de geração: `sign1024_stirling-reproduced.log`,
`sign512_stirling_L12-reproduced.log` e `sign512_d01_L12-reproduced.log`.
Logs da checagem exata: os arquivos `*.exact-check.log` com os mesmos prefixos.
JSONs gerados e resultados exatos estão na mesma pasta. A falha anterior de
compatibilidade ficou registrada em `sign1024_stirling-initial-gmpy2-failure.log`;
as três tentativas iniciais sem patch nesta retomada encontraram a mesma falha
antes de escrever JSON. O registro completo, comandos e checksums estão em
`evidence/interval-certificate/reproduction-2026-11-06.md` e
`evidence/interval-certificate/reproduction-2026-11-06-sha256.txt`.

**Limite:** isso confirma sinais racionais condicionais aos intervalos
produzidos pela biblioteca experimental `mpmath.iv`. Não é uma prova formal de
que os coeficientes da fonte C2 original pertençam às caixas, portanto não
fecha O4 nem C5.

## Ponte Gamma de núcleo racional — build, auditoria e merge da PR #198

`SigmaC5GammaRationalCore.lean` define uma soma finita exata em `ℚ+iℚ` e prova
que `gammaFinite N T (a+bi)` é seu produto por `T^(a+bi)`. A caixa racional
exata contém esse núcleo; `gammaFiniteInterval_contains` combina-a com
`ZetaLean.ComplexInterval.dirichletTermBox2` para o fator de potência. Para
`N=3072`, `T=620`, `gamma3072Interval_contains` infla a caixa da Gamma finita
pelo erro rigoroso `10^-259` e inclui `Complex.Gamma (a+bi)`, sob as hipóteses
de intervalo e limite exponencial declaradas no teorema.

O build focado usa Lean `4.32.0`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` e Carry
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; os módulos de apoio são
`SigmaGammaEulerIntegral` (erro `10^-259`, PR #175) e
`ZetaLean.IntervalCExp` (infraestrutura O4, PR #169). Ambos os módulos-alvo
foram compilados em diretório de saída limpo, com warnings como erros. O
checker fail-closed aceitou seis raízes, totalizando 11 relatórios dos dois
builds, e somente `propext`, `Classical.choice` e `Quot.sound`.

O commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a` foi integrado
pela PR #198; o merge na `main` é `36cba9d805bc3274538cdc93bd0a3702154edcb2`.
O GitHub não reportou checks hospedados. Este merge não fecha O4/C5.

Logs: `c5-gamma-rational-core-try5-build.log`,
`c5-gamma-rational-core-audit-try6-build.log` e
`c5-gamma-rational-core-final-axiom-check.log`. Hashes de fonte, checker e
olean em `c5-gamma-rational-core-source-olean-sha256.txt`. O comando reprodutor
está nesta validação; o runner impõe `MemAvailable≥30 GiB`.

```bash
C5_SOURCE_ROOT="$PWD/research/native-moving-schur-sigma"
C5_EVIDENCE="$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes"
C5_OUTPUT="$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-rational-core-final-clean-20261106"
C5_EULER_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-3072-clean"
C5_INTERVAL_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean"
export SIGMA_REFERENCE_ROOT="/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105"
export CARRY_LEAN_ROOT="/home/thlinux/worktrees/carry-sigma-c2-pinned-045369"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export SIGMA_HEIGHT50_BUILD="$C5_EULER_CACHE:$C5_INTERVAL_CACHE"
export LEAN_BIN="$(elan which lean)"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCore
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCoreAudit
python3 "$C5_SOURCE_ROOT/check_c5_gamma_rational_core_axioms.py" \
  "$C5_EVIDENCE/c5-gamma-rational-core-try5-build.log" \
  "$C5_EVIDENCE/c5-gamma-rational-core-audit-try6-build.log"
```

**Limite desta etapa:** o teorema é genérico; não foram obtidos ainda valores
racionais efetivos para qualquer um dos 129 nós, nem a caixa completa da fonte
C2 nos pontos. A inclusão dos coeficientes nas caixas O3 continua não provada,
e C5 não está concluída.

## Avaliação da fonte C2 nos nós — ainda sem validação

A auditoria original da rota zeta permanece como histórico, mas sua limitação
de ordem 4 foi superada pela Euler–Maclaurin de alta ordem integrada pela PR
#205; as caixas e exportação zeta seguem nas PRs #211 e #213. Nenhuma dessas
etapas, nem o novo piloto do núcleo racional Gamma, prova por si só a inclusão
da fonte C2 nas caixas O3. A caixa Gamma ainda precisa da potência `240^z`, do
erro analítico, e da composição nos nós. O diagnóstico original está em
`evidence/rational-boxes/c5-original-source-zeta-route-audit.md`; o piloto
atual, em `evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/README.md`.

## Faixa racional exata de π — PASSOU e integrada pela PR #193

`SigmaC5PiBounds.lean` prova o erro da série alternada de `Real.arctan` para
argumentos racionais entre zero e um. Com truncações `N=170` e `N=55`, a
identidade de Machin dá `c5_pi_rational_enclosure`, que limita
`|Real.pi - c5PiCenter|` pelo racional exato `c5PiError`. O resultado não
depende da tentativa auxiliar de reduzir esse erro a uma potência decimal.

Build Lean 4.32 limpo com warnings como erros passou; a auditoria transitiva de
`c5_arctan_partial_enclosure` e `c5_pi_rational_enclosure` encontrou somente
`propext`, `Classical.choice` e `Quot.sound`. Logs, pins, hashes e comando estão
em `evidence/rational-boxes/c5-pi-bounds-validation.md`.

Merge na `main`: `2567ab0204c46c4ce04fca601c99e47e810e18b9`.

Esse incremento não certifica a avaliação da fonte nos nós e não prova
inclusão C2 nas caixas; C5 segue incompleta.

## `log π` e fator exponencial da completação — PASSOU e integrado pela PR #195

`SigmaC5PiInterval.lean` usa a faixa de π integrada pela PR #193 para provar
uma caixa racional de `Real.log Real.pi` por meio de `ZetaLean.Interval.log1`.
`SigmaC5PiExp.lean` transporta essa caixa pelo fator `-s/2` e aplica o
`ComplexInterval.expCr` já certificado para incluir o exponencial usado pela
definição original da completação.

Build limpo Lean 4.32 e auditoria das cinco raízes passaram; somente
`propext`, `Classical.choice` e `Quot.sound` aparecem. PR #195, commit de prova
`321ae94`, merge na `main` `0032b10295bfeaadb29d0387f9b99dde9b160ac3`.
Evidência reproduzível, pins e hashes em
`evidence/rational-boxes/c5-pi-completion-factor-validation.md`. O incremento
não avalia Gamma, a cauda C2 nem os 129 nós.

## Cota do módulo da fonte original — PASSOU e integrada; O4 parcial

`SigmaC5AnalyticBounds.lean` prova a cota uniforme
`CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39` para o
produto deslocado original, com `|d|≤1/10` e `z∈ball(0,39/100)`. A prova
mantém a característica nativa completada e seus fatores originais. Ela usa
uma cota da característica de `2·10^6` em cada fator; o produto fica abaixo
de `10^13`. Para a estimativa de Cauchy, usamos o contorno exterior de raio
`38/100`; seu disco fechado está estritamente dentro da bola aberta de raio
`39/100` na qual o lema da cota vale, e dentro do disco analítico aberto de
raio `2/5` integrado pela PR #189.

O build limpo em Lean 4.32 terminou com `BUILD_EXIT=0` e a cota `10^13` foi
integrada pela PR #192, merge `654dbb0bd7bb7d400cf0c4cab61bea1873995db4`. A auditoria
fail-closed das duas cotas Gamma, da cota `10^13` e do wrapper `10^100`
aceitou apenas `propext`, `Classical.choice` e `Quot.sound`. Logs, hashes e
detalhes estão em `evidence/rational-boxes/analytic-bounds-10pow13-validation.md`.

A análise de interpolação refeita em frações exatas com majorante `10^13` e
raio externo `38/100` confirma cauda `<10^-501` e erro Gamma amplificado
`<10^-135`. Isso ainda não certifica avaliações nos nós: O4 permanece aberta
até incluir os valores originais nos 129 pontos e provar as caixas dos
coeficientes C2.

## Limite de peso de grau um — PASSOU em build limpo e auditoria

`SigmaRationalInterpolation.lean` compila integralmente em Lean 4.32, em
diretório de saída limpo. Os teoremas
`c5LagrangeBasisProductCoeffOne_bound`,
`c5InterpolationCoeffOneAbsSum_le_six` e
`c5InterpolationWeightSum_one_lt_ten_eleven` concluem o limite escalado
`<10^11` do coeficiente de grau um.

A auditoria fail-closed percorreu 21 raízes, incluindo os três resultados
novos, e aceitou somente `propext`, `Classical.choice` e `Quot.sound`.
O checker não encontrou placeholder, axioma próprio ou `native_decide`.
Logs, hashes, pins e comandos:
`evidence/rational-boxes/degree1-weight-bound-validation.md`.

Este resultado é parcial: os graus `2..14`, a cota da fonte, as avaliações
racionais nos pontos e a inclusão dos coeficientes C2 nas caixas seguem
pendentes.

## Histórico de tentativas incompletas de grau um — 2026-11-06

Essas falhas são históricas e foram sucedidas pelo build limpo e pela auditoria
aprovada acima; permanecem para preservar a trilha de diagnóstico.

As tentativas abaixo foram **superadas pela validação limpa acima**. O módulo de produção havia sido estendido com
uma tentativa simbólica de `c5LagrangeBasisProductCoeffOne_bound` e corolários,
mas nenhuma compilação integral produziu `SigmaRationalInterpolation.olean`.
As tentativas, os perfis e os traces estão registrados em
`evidence/rational-boxes/c5-interpolation-degree1-*.log*`.

O lema auxiliar `c5_inv_sq_sum_range_le_isolated` compilou isoladamente em
Lean 4.32 (`c5-sum-bound-isolated-build.log`); isso não prova o limite do peso.
O último perfil integral elaborou o lema da soma, mas os lemas de produto
seguintes continuam sem conclusão. A saída rejeitada que encontrou axiomas
próprios gerados por `native_decide` está em
`interpolation-audit-degree1-native-decide-rejected.log`. O relatório
`interpolation-audit.log` restaurado é o histórico aprovado das 14 raízes da
versão anterior e não audita as raízes novas do checker atualizado.

A revisão WIP está na branch `codex/c5-degree1-weight-bound-20261106`, sobre
`origin/main` `c736dc073091e6184dbb673b622b6b91759accac`. O comando de retomada e
os pins estão em `RESTART_HERE.md` e
`evidence/rational-boxes/degree1-retry-checkpoint.md`.

**Estado das fases anteriores:** Fase 1 de transporte algébrico integrada pela PR #165. O3 foi integrada pela PR #167. A infraestrutura O4 e as pontes Euler-Gamma estão registradas nas PRs #169–#175; a interpolação, o peso constante e a estrutura derivativa de grau um nas PRs #177–#181. A prova `gamma_finite_3072_620_error` tem erro `≤10⁻²⁵⁹`, build Lean 4.32 e auditoria de doze raízes. A O4 continua aberta: faltam limites para graus `2..14`, a cota analítica da fonte e as inclusões C2.
**Toolchain:** `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
**Base geometry da PR #165:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776`; `main` após o merge: `75691edf0e74cc643f098213f60b684476132175`.
**Fonte C4 compilada:** source hashes de `SigmaSourceBezout.lean`, `SourceBezout.lean`, `SigmaPadeCorrespondence.lean` e `SigmaZeroObstruction.lean` conferem com `origin/main`; pins completos em `evidence/pins-and-sha256.txt`.

**O4, auditoria de 2026-11-06:** os módulos de intervalo elementar foram recompilados e auditados; também foi localizada a identidade formal de Weierstrass `Zeta23.DigammaSeries.inv_gamma_eq_prod`. Nenhuma caixa numérica para `Complex.Gamma` foi ainda derivada dessa identidade, e a aproximação Stirling usada pelo avaliador segue sem ponte Lean. O4 e a inclusão incondicional das caixas continuam abertas.

**Estado histórico após PR #181/#182:** a estrutura derivativa estava integrada, enquanto o limite numérico ainda aguardava prova.

**O4, prova Euler-Gamma de precisão alta integrada pela PR #173:** `gamma_finite_1024_240_error` aproxima a Gamma original por `gammaFinite 1024 240 z` com erro `≤10⁻⁹⁹` para `1495/20000≤Re(z)≤1`. Build Lean 4.32 e auditoria de dez raízes passaram; a caixa racional estreita da expressão finita continua pendente. Prova, logs e hashes estão em `evidence/rational-boxes/`.

## Estado após PR #185 — peso de grau um integrado

A PR #184 preservou o checkpoint incompleto (`5528ddc8093a22682c87f3f9c6575e30e90a7011`); a prova de grau um foi depois integrada pela PR #185, merge `c840ba35711ac8f938fa24c191f2af60f505480d`. A prova Lean 4.32 e a auditoria de 21 raízes estão registradas em `evidence/rational-boxes/degree1-weight-bound-validation.md` e nos logs associados. C5 continua parcial: os graus `2..14`, a cota analítica, as avaliações da fonte e a inclusão nas caixas seguem abertos.

## 1. Transporte algébrico Lean — PASSOU

Arquivos novos:

- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean`
- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransportAudit.lean`

A prova começa em `completedSigmaDisplacedSource_coefficient_recurrence` de C4 e mantém `completedSigmaDisplacedMoment = 2*completedSigmaLogJet`. O módulo prova a recorrência polinomial sem divisão, a identidade do menor escalado com `CarrySigmaPade.sigmaPadeD` original e os dois lemas de transferência de sinal usando `completedSigmaDisplacedSourceCoefficient_zero_pos`.

O build final foi feito para diretório de saída novo, com warnings tratados como erros, usando o script `compile_sigma_pade.sh`. Os logs e o comando exato estão em `build-transport-clean.log` e `transport-build-record.md`.

`#print axioms` para os quatro teoremas auditados lista apenas `propext`, `Classical.choice` e `Quot.sound`. Saída em `axiom-audit-transport-clean.log`. Nenhum axioma próprio, `sorryAx` ou `admit` foi introduzido.

PR #165 foi integrada à `main`; o GitHub não retornou status checks hospedados. A validação local registrada acima é o resultado de build/auditoria desta fase.

## 2. Genealogia da fonte — conferida, preservada

A revisão carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, em `CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean`, prova
`canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar`:

```text
finiteBracketCharacteristic 2 cutoff s
  + ∑' index, centerBracketTerm 2 s (index + cutoff)
  = factor 2 s * nativeScalar s
```

O gerador numérico C5 avalia a mesma cabeça C2 mais cauda exata. Hurwitz é usado somente para avaliar a soma exata omitida; depois o fator nativo C2 e a completação original são aplicados. C4 liga os coeficientes resultantes aos jets originais. Hash da ponte carry e demais fontes em `pins-and-sha256.txt`.

## 3. Verificação racional condicional — PASSOU

O verificador `verify_signs_exact.py` usa `fractions.Fraction`; não usa Float para decidir sinal. Resultados nos JSONs rastreados:

| Deslocamento | Sinais condicionais | Log |
|---|---|---|
| `99/2000` | `+++++++++++-` | `interval-certificate/verify-d00495.log` |
| `1/10` | `+++++++++-` | `interval-certificate/verify-d01.log` |

Esses cálculos provam os sinais supondo as inclusões de todos os coeficientes nas caixas.

## 4. Geração intervalar — REPRODUZIDA, não é ainda prova formal

As três configurações pedidas passaram após uma correção apenas de compatibilidade de backend, registrada como patch:

1. `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`; sinais `+++++++++++-`.
2. `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`; sinais `+++++++++++-`.
3. `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`; sinais `+++++++++-`.

Cada saída foi conferida pelo verificador exato em um segundo passo. JSONs e logs de geração e verificação estão em `interval-certificate/`.

A primeira execução falhou antes de produzir JSON porque esta instalação do `mpmath 1.3.0` seleciona `gmpy2.mpz`, que `Decimal` não aceita. A falha foi preservada em `sign1024_stirling-initial-gmpy2-failure.log`. No checkout Momentos isolado foi testada uma conversão explícita `int(mpz)`; o patch correspondente está versionado ao lado. A branch remota da PR #2 não foi alterada.

O avaliador permanece experimental: as funções elementares `mpmath.iv` e sua garantia de arredondamento externo não foram provadas em Lean. Portanto, as caixas ainda não são inclusões formais dos coeficientes verdadeiros.

## 5. Sinais condicionais — provados em Lean

O3 compõe as caixas racionais com a recorrência polinomial sem divisão e prova
em Lean os sinais condicionais dos menores. Os teoremas
`sigmaPadeD_signs_at_99_2000_of_source_boxes` e
`sigmaPadeD_signs_at_1_10_of_source_boxes` concluem sobre o `sigmaPadeD`
original, assumindo respectivamente `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`. Todos os índices requeridos foram cobertos: `D₀..D₁₀>0,
D₁₁<0` em `d=99/2000` e `D₀..D₈>0, D₉<0` em `d=1/10`.

O build limpo dos seis módulos e a auditoria das 13 raízes passaram; apenas
`propext`, `Classical.choice` e `Quot.sound` aparecem. Consulte
`evidence/rational-boxes/VALIDATION.md` para comandos, logs e hashes.

## 6. Resultado incondicional — ainda aberto

Os dois teoremas finais de primeira janela negativa ainda não são
incondicionais, pois O4 não prova que os coeficientes reais da fonte C2 original
estão dentro das caixas. A fonte permanece a cabeça C2, a cauda exponencial
exata e a completação original; os resultados condicionais não substituem essa
prova. A primeira obrigação aberta está em `OPEN_OBLIGATIONS.md`.
