# C5 — checkpoints

## 2026-11-07 — caixa exponencial de estágio 2 provada (publicação pendente)

- `c5ZeroExpStage2_eq` prova que `c5RoundedExpC 192 896 2` na entrada zero é
  exatamente `c5ZeroExpStage2Export`; quatro lemas verificam os pisos/tetos da
  caixa quadrada do estágio 1 por desigualdades racionais exatas.
- Build Lean 4.32 com `warningAsError=true` e auditoria das onze raízes
  passaram; somente `propext`, `Classical.choice` e `Quot.sound` aparecem.
- Logs, pins, hashes e comandos estão em
  `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.
- O checkpoint ainda não foi publicado. A igualdade do estágio 2 não fecha a
  ponte CSV–Lean ou as inclusões O3; C5 permanece incompleta.

## 2026-11-07 — caixa exponencial de estágio 1 provada e integrada (PR #224)

- `c5ZeroExpStage1_eq` prova a igualdade entre
  `c5RoundedExpC 192 896 1 (ComplexInterval.exact 0 0)` e os extremos racionais
  exportados em `c5ZeroExpStage1Export`.
- Quatro lemas certificam os pisos/tetos por desigualdades racionais exatas.
  Lean 4.32, `warningAsError=true`, compilou os corpos dos teoremas; uma
  auditoria por import passou com somente `propext`, `Classical.choice` e
  `Quot.sound` nas seis declarações auditadas.
- Logs, fontes, hashes, pins, falhas históricas e comando de retomada estão em
  `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.
- PR #224 integrou o checkpoint: commit de prova
  `a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge
  `d667abfc42020e442c62ec1b49b82f5bcf1971ad`. O GitHub não reportou checks
  hospedados.
- A igualdade do estágio 1 não liga o CSV às caixas Lean e não prova a inclusão
  dos coeficientes C2 nas caixas O3; C5 permanece incompleta.

## 2026-11-07 — identidades exatas do nó `m = 1` (checkpoint parcial integrado)

- O log centrado em `1` é exatamente zero, para qualquer intervalo `logTwo`.
  Assim, o argumento exponencial e o termo de Dirichlet `m = 1` reduzem ao
  avaliador arredondado na entrada complexa zero.
- A recorrência em zero mantém a potência exatamente nula e a soma de Taylor
  exatamente unitária em todo estágio positivo; `c5RoundedExpSmall_zero`
  mantém explícita a inflação racional do resto de Taylor.
- Os módulos alterados compilaram com Lean 4.32.0 e
  `warningAsError=true`. As auditorias dos sete teoremas retornaram somente
  `propext`, `Classical.choice` e `Quot.sound`.
- Evidência reproduzível, pins, hashes, fontes de auditoria e último erro em
  `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.
- Naquele momento a tentativa de identificar os extremos exatos do estágio 1
  ainda falhava; essa lacuna foi fechada no checkpoint mais recente acima. A
  saída `sorryAx` antiga continua sendo recuperação do elaborador e é inválida.
- PR #222, commit de prova `67e6cf9fdf86ac735b6ade80d2f4a64982968363`, integrou
  o checkpoint à `main` no merge `e55858690e296d00c88692b8f30902987e853137`.
  O GitHub não reportou checks hospedados.
- C5 permanece aberta: sem avaliação completa da fonte, sem inclusões O3 e
  sem fechamento dos sinais.

## 2026-11-07 — `log 2` em blocos certificado (C5 ainda incompleta)

- `SigmaC5Log2Certified.lean` divide cada `Interval.logSum 512 (±1/3)` em 16
  blocos de 32 termos, certifica cada bloco com aritmética racional e recompõe
  as somas completas. O teorema final prova
  `c5CenteredLog2I 512 = c5ExportedLogTwo512`.
- Build limpo Lean 4.32.0 com `warningAsError=true` passou. A auditoria
  fail-closed passou nas três raízes; só aparecem `propext`, `Classical.choice`
  e `Quot.sound`. A fonte não contém placeholders.
- PR #219, commit `bd84a673b3c5c1c82168a6655c59ad6a28bbf127`, integrada na
  `main` pelo merge `d6ed8ad249ef69c33920164fe43821cc83f138a8`. O GitHub não
  reportou checks hospedados.
- Fonte, checker, logs, pins, comando de retomada e hashes estão em
  `evidence/rational-boxes/c5-log2-component-validation/README.md`.
- Escopo: a prova cobre apenas o componente `log 2`; não liga as 516 linhas do
  CSV às caixas Lean e não prova as inclusões
  `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 continua aberta. A linha
  piloto `(a,j)=(2/5,0)` ainda falha com `decide` em `Rat.num`, `rfl` por não
  conversibilidade, e `norm_num` após ~28 minutos/1M passos. O próximo passo é
  formalizar os componentes restantes e a ligação CSV–Lean.

## 2026-11-07 — exportação Lean das caixas zeta em quatro coordenadas (parcial)

- Quatro sondas Lean exportaram 129 caixas racionais exatas cada, para
  `a=2/5`, `901/2000`, `1099/2000` e `3/5`; os índices cobrem `j=0…128`.
- Os logs registram tempos de 30:25–32:00, código 0 e pico RSS abaixo de
  6,56 GiB. O CSV tem 516 linhas de caixas e foi gerado por um exportador que
  confere a cobertura dos índices e a forma racional dos quatro extremos.
- Isso conclui apenas a exportação de zeta. A composição com Gamma, o fator
  dependente de π, a interpolação e as duas inclusões dos coeficientes C2
  continuam abertas; também falta provar em Lean que os extremos do CSV
  coincidem com as definições das caixas. Veja
  `evidence/rational-boxes/c5-centered-all-a-zeta-export-validation.md`.
- Publicado pela PR #213, commit de prova
  `f51db20fa6fd21e08bbc2080cdd4bcb2265e2ea1`, merge na `main`
  `5fe8a7b330d6a106e2b2c44781b8d0677c7ea7f3`.

## 2026-11-07 — estado integrado da negatividade e checkpoint C5 parcial

- C1B foi integrada pela PR #155, merge
  `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2 foi integrada pela PR #157, merge
  `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
- C3 foi integrada pela PR #159, merge
  `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
- O checkpoint de tabela Bernoulli compartilhada foi integrado pela PR #211,
  commit `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`, merge
  `c6dd548bcb030a21bb90c1aee08023c2ca2d485f`.
- C5 segue explicitamente incompleta. A tabela Bernoulli compartilhada e as
  caixas de nó estão provadas e auditadas, mas as inclusões
  `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` continuam abertas.
- Pins, fontes da sobreposição temporária, logs, último estado de falha e
  comandos de retomada estão em
  `evidence/rational-boxes/c5-fast-bernoulli-table-validation.md`.

## 2026-11-07 UTC — cobertura zeta adaptativa dos 129 nós (PR #209 integrada)

- `SigmaC5RationalNodeLogBounds.lean` prova por aritmética racional os limites
  de log necessários para `1≤m≤100`; a escala adaptativa mantém `m/2^k` entre
  `1/2` e `1`.
- `SigmaC5RationalNodeInstantiate.lean` constrói as condições da cabeça e da
  potência-base, inclui zeta em todos os nós `j=0,…,128` para
  `a∈[2/5,3/5]`, e transporta a inclusão aos nós conjugados. A cauda exata
  Euler–Maclaurin permanece na caixa, com inflação `<10^-250`.
- Build limpo Lean 4.32 (`warningAsError=true`) passou e checker fail-closed
  aceitou 21 raízes, somente com axiomas padrão. Logs, pins, hashes, comandos
  e falhas anteriores em
  `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
- PR #209, commit de prova `05dae531d4ec10c916c340f58255f35977a3abdd`, merge
  na `main` `386b654eabe4c942d6b0db46754120ab79b52fb5`; base anterior: merge
  da PR #208 `296e899e70bee78c54a3278e73e9bd89eaafaa58`.
- Limite: não há extremos racionais achatados nem composição com Gamma, fator
  de π e fonte C2; as inclusões O3 e C5 continuam abertas. A publicação deste
  checkpoint pela PR #209 o identificou explicitamente como incompleto.

## 2026-11-06 — reprodução das três caixas experimentais

- As configurações `d=0.0495, L=0, N=1024, r/R=0.3/0.4`, `d=0.0495,
  L=12, N=512, r/R=0.2/0.4` e `d=0.1, L=12, N=512, r/R=0.15/0.3` foram
  executadas em uma cópia temporária do checkout Momentos, aplicando apenas o
  patch de conversão `gmpy2.mpz`→`int` já guardado nesta missão.
- Todas as gerações e as verificações independentes por frações racionais
  exatas terminaram com código zero. Os sinais são `+++++++++++-`,
  `+++++++++++-` e `+++++++++-`, respectivamente.
- O checkpoint é experimental e condicional às caixas. A inclusão dos
  coeficientes verdadeiros da fonte C2 não foi provada por Lean; O4/C5 segue
  aberta. Os logs, JSONs, comandos e a falha anterior de compatibilidade estão
  em `evidence/interval-certificate/reproduction-2026-11-06.md`.

## 2026-11-06 — ponte Gamma de núcleo racional (PR #198 integrada)

- `SigmaC5GammaRationalCore.lean` expressa exatamente `gammaFinite` como o
  produto de `T^z` por uma soma finita racional-complexa; não aproxima nem
  arredonda essa soma sensível a cancelamento.
- O avaliador `dirichletTermBox2` enxerra o fator exponencial sob hipóteses
  explícitas. `gamma3072Interval_contains` usa o erro analítico
  `gamma_finite_3072_620_error≤10^-259` para incluir a Gamma verdadeira.
- Build Lean 4.32 com warnings como erros e auditoria fail-closed de seis
  raízes passaram; somente `propext`, `Classical.choice` e `Quot.sound`.
  Logs, hashes e comandos em
  `evidence/rational-boxes/c5-gamma-rational-core-validation.md`.
- Commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a`; merge na `main`
  `36cba9d805bc3274538cdc93bd0a3702154edcb2`. Não houve checks hospedados.
- Escopo: lema genérico, sem avaliação efetiva dos 129 nós. Ainda falta
  formalizar zeta/Hurwitz de ordem alta, calcular caixas nodais completas e
  provar as inclusões dos coeficientes C2 nas caixas O3. C5 continua aberta.

## 2026-11-06 — auditoria da rota zeta para a fonte original C5

- Confirmada a rota Lean 4.32 sem trocar a fonte: o escalar nativo é
  `riemannZeta` no domínio provado, e a ponte C2 conserva cabeça finita mais
  cauda exata.
- Primeiro limite disponível localizado: `HardyFirstZero.zeta_em4_error`, de
  ordem 4. Em `N=100`, seu resto no contorno é aproximadamente `1.351·10⁻⁸`,
  insuficiente para provar inclusão nas caixas O3.
- Falta um lema Lean de ordem alta para zeta/Hurwitz, a avaliação intervalar
  correspondente e a avaliação racional intervalar de `gammaFinite 3072 620`.
  O limite analítico da Gamma `10⁻²⁵⁹` já está provado, mas não avalia a soma.
- Registro do diagnóstico: `evidence/rational-boxes/c5-original-source-zeta-route-audit.md`.
  Este checkpoint é investigação, não fechamento de O4/C5.

## 2026-11-06 — PR #195 integrada: fator exponencial com `log π`

- `SigmaC5PiInterval.lean` certifica a faixa racional de `log π` e
  `SigmaC5PiExp.lean` leva essa faixa ao fator original da completação usando
  `expCr`, sob as hipóteses de caixa de entrada registradas na validação.
- Build limpo Lean 4.32 e auditoria de cinco raízes passaram; somente axiomas
  padrão foram encontrados. Logs, hashes, pins e comandos estão em
  `evidence/rational-boxes/c5-pi-completion-factor-validation.md`.
- PR #195, commit de prova `321ae94`, merge na `main`
  `0032b10295bfeaadb29d0387f9b99dde9b160ac3`.
- C5 permanece incompleta: avaliação da fonte original nos 129 nós e inclusão
  dos coeficientes C2 nas caixas O3 ainda estão pendentes.

## 2026-11-06 — cota analítica explícita integrada

- `SigmaC5AnalyticBounds.lean` prova que a fonte deslocada original satisfaz
  `‖displacedProductC d z‖≤10^100` para `|d|≤1/10` e `z∈ball(0,39/100)`.
  A derivação limita Gamma pela integral de Euler e recorrência, os fatores
  nativos pela série C3 exata e a completação original; não substitui a fonte
  por modelo clássico.
- Build limpo em Lean 4.32 terminou com `BUILD_EXIT=0`. A auditoria fail-closed
  das três declarações (duas cotas Gamma e a cota da fonte) aceitou somente
  `propext`, `Classical.choice` e `Quot.sound`.
- Hashes de fonte, checker e `.olean`, logs e comando de retomada estão em
  `evidence/rational-boxes/analytic-bounds-validation.md` e nos arquivos
  `c5-analytic-bounds-final-clean-*`.
- A análise exata de interpolação foi recalculada com raio externo `38/100`,
  estritamente dentro do disco aberto onde o lema da fonte fornece a cota; o
  erro de cauda continua `<10^-410`, e o erro Gamma amplificado continua
  `<10^-135`. Log em `rational-interpolation-analysis-radius-38.log`.
- A cota mais forte `10^13` foi integrada pela PR #192, commit de prova
  `b122eafd10ed9b75f7e3c4c5f04c22b93697ffcc`, merge na `main`
  `654dbb0bd7bb7d400cf0c4cab61bea1873995db4`; a cota `10^100` permanece como
  wrapper.
- C5 segue incompleta: falta certificar os valores nos 129 nós e provar que os
  coeficientes C2 originais pertencem às caixas O3. Nenhum sinal incondicional
  novo foi declarado.

## 2026-11-06 — majorante apertado para a fonte, validado localmente

- A PR #191 integrou `displacedProductC_norm_le_10pow100_on_ball_39`, merge
  `88a52ba3a6bda7a78b8317d892b6f7bc640c863f`.
- O mesmo argumento dá a cota mais forte
  `displacedProductC_norm_le_10pow13_on_ball_39`, pois cada fator tem norma
  `≤2,000,000` e o produto é `≤4·10^12≤10^13`. O teorema `10^100` é mantido
  como wrapper. Build limpo e auditoria fail-closed de quatro raízes passaram.
- A análise racional exata com limite `10^13` e raio exterior `38/100` dá erro
  de cauda `<10^-501`; hashes e logs estão em
  `evidence/rational-boxes/analytic-bounds-10pow13-validation.md`.
- Ainda faltam as avaliações nos 129 nós e as inclusões O3; o checkpoint C5
  segue incompleto.

## 2026-11-06 — faixa racional exata de π integrada

- `SigmaC5PiBounds.lean` prova o limite da série alternada para `arctan` e
  deriva de Machin uma faixa racional exata para `Real.pi`, com truncações
  `N=170` em `1/5` e `N=55` em `1/239`.
- Build limpo Lean 4.32 com warnings como erros e auditoria de duas raízes
  passaram. O footprint contém somente `propext`, `Classical.choice` e
  `Quot.sound`.
- Comandos, pins, logs, hashes, definição racional do centro/erro e uma
  tentativa decimal auxiliar não fechada estão preservados em
  `evidence/rational-boxes/c5-pi-bounds-validation.md` e arquivos relacionados.
- PR #193 integrou este incremento; commit de prova `45bc923`, merge na `main`
  `2567ab0204c46c4ce04fca601c99e47e810e18b9`.
- A entrega é preparatória: a avaliação da fonte original nos 129 nós e a
  inclusão nas caixas C2/O3 continuam abertas.

## 2026-11-06 — `log π` e fator exponencial da completação, validado localmente

- `SigmaC5PiInterval.lean` prova `c5_pi_log_interval_contains`, construindo a
  faixa de `log π` com `log1` e a âncora formal de `log 2`.
- `SigmaC5PiExp.lean` prova a inclusão do fator original
  `Complex.exp (-(s/2) * log π)` em `expCr`, para qualquer retângulo complexo
  `s` cujo limite de norma exigido seja fornecido.
- Builds limpos Lean 4.32 e auditoria de cinco raízes passaram; apenas
  `propext`, `Classical.choice` e `Quot.sound` aparecem. Logs, pins, hashes e
  comando estão em `evidence/rational-boxes/c5-pi-completion-factor-validation.md`.
- Ainda não integrado. Não avalia Gamma, a cauda Hurwitz da fonte C2 nem os
  valores da característica nos 129 nós.

## 2026-11-06 — limite dos pesos de graus 2–14 validado localmente

- `c5InterpolationCoeffAbsSum_le_four_mul_two_pow` prova que, para todo
  `n≥1`, a soma absoluta dos coeficientes das bases de Lagrange é no máximo
  `4·2^n`. `c5InterpolationWeightSum_lt_ten_145` conclui a cota escalada
  `<10^145` para cada `2≤n≤14`.
- `SigmaRationalInterpolation.lean` passou build limpo em Lean 4.32 com
  `warningAsError=true`; a auditoria fail-closed de 23 raízes passou usando
  somente `propext`, `Classical.choice` e `Quot.sound`.
- Logs, pins, hashes e comando para retomar estão em
  `evidence/rational-boxes/degree2-14-weight-bound-validation.md` e nos
  arquivos `c5-interpolation-degree2-14-final-clean-*`.
- A PR #187 integrou a prova: commit `6424f4334edd5c776997116403043635fa0c8f83`,
  merge na `main` `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- O checkpoint permanece incompleto: a cota analítica da fonte C2, a avaliação
  nos 129 nós e a inclusão dos coeficientes originais nas caixas continuam
  abertas.

## 2026-11-06 — inventário inicial (pré-prova)

- Criada worktree isolada `codex/c5-finite-c2-certification-20261106` sobre geometry `origin/main` em `91a1af2f9663d6761a3320e2f06504fe8aaa6776`.
- A branch de pesquisa original geometry `agent/native-moving-schur-sigma` em `9392ebac9930f5d11c56f595556080e8ab1de809` tem logs/caches não rastreados, preservados sem alteração.
- C4 e a missão C0–C4 estão documentadas na main e integradas.
- A branch de pesquisa Momentos `origin/research/sigma-pade-dimension-depth-20261104` está em `68c9b5f`; PR #2 está aberta. Ela contém as duas caixas racionais, código para gerar caixas e relatório condicional. Não foi feito merge.
- O build alvo é Lean 4.32.0, conforme `lean-toolchain` da main.
- Estado matemático inicial e comandos de retomada: `RESTART_HERE.md` e `SESSION_STATE.md`.

## Próximo checkpoint

Certificar a fonte original nos 129 nós e provar a inclusão dos coeficientes
C2 nas caixas O3. A inclusão permanece aberta; consulte `RESTART_HERE.md` e não
misture caches/logs das outras worktrees.

## 2026-11-06 — transporte algébrico provado, antes do PR

- `SigmaFiniteCoefficientSignTransport.lean` e seu audit Lean 4.32 compilaram em diretório de saída limpo; `#print axioms` mostrou somente `propext`, `Classical.choice` e `Quot.sound` para os quatro teoremas.
- A recorrência mantém `completedSigmaDisplacedMoment = 2*completedSigmaLogJet` e o menor final usa `CarrySigmaPade.sigmaPadeD` original.
- As verificações exatas dos JSONs e três gerações intervalares foram reproduzidas; os sinais são condicionais às caixas. O erro local `gmpy2.mpz`/`Decimal`, sua correção de compatibilidade e os logs foram preservados em `evidence/interval-certificate/`.
- A inclusão dos coeficientes verdadeiros nas caixas não foi provada. Nenhum teorema de primeira janela final foi declarado.
- Commit de prova/evidência `1250a9989e596fa250304d8ec8fd3ae45897e589`; PR #165 e merge ainda pendentes no checkpoint original.
- Pins, hashes, comandos de build e SHA dos `.olean` estão em `evidence/pins-and-sha256.txt` e `evidence/transport-build-record.md`.

## 2026-11-06 — Fase 1 integrada

- PR #165 integrou o transporte algébrico, a auditoria e as evidências. Commit de prova: `1250a9989e596fa250304d8ec8fd3ae45897e589`; merge na `main`: `75691edf0e74cc643f098213f60b684476132175`.
- A revisão foi compilada em Lean 4.32 com warnings como erros; os quatro footprints de axiomas contêm somente `propext`, `Classical.choice` e `Quot.sound`. O GitHub não apresentou status checks hospedados.
- A PR mantém explícito que os padrões de sinais numéricos continuam condicionais às caixas. A integração não declara os teoremas finais de C5.
- `origin/main` após o merge: `75691edf0e74cc643f098213f60b684476132175`. A próxima obrigação é O3, propagação intervalar racional formal em Lean.

## 2026-11-06 — O3 formalizada, antes da publicação

- Adicionados seis módulos Lean que representam os dados das duas caixas como bolas racionais exatas, propagam a recorrência escalada de C4, encerram os sinais de cada menor e transferem os resultados ao `sigmaPadeD` original sob hipóteses explícitas de inclusão.
- Em `99/2000`, os menores são positivos para `s<11` e negativo em `s=11`; em `1/10`, positivos para `s<9` e negativo em `s=9`. Os resultados permanecem condicionais a `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
- Os seis módulos compilaram em Lean 4.32, com warnings como erros, em saída limpa. A auditoria transitiva cobre 13 teoremas; o checker fail-closed passou e encontrou apenas `propext`, `Classical.choice`, `Quot.sound`.
- Logs, comandos de reprodução, hashes de fontes e `.olean`, e limitação O4 estão em `evidence/rational-boxes/`. A inclusão analítica da fonte não foi provada; nenhum teorema incondicional de janela negativa foi declarado.
- A publicar em uma PR própria. Próxima obrigação após integração: O4, provar a inclusão dos coeficientes originais nas caixas.

## 2026-11-06 — O3 integrada

- PR #167 integrou os seis módulos de aritmética intervalar racional, os sinais condicionais, o checker de axiomas e suas evidências.
- Merge na `main`: `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. O conteúdo de O3 foi validado em Lean 4.32 localmente; não houve status checks hospedados.
- O3 prova as janelas somente sob `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. A próxima obrigação é O4, inclusão analítica dos coeficientes da fonte C2 original.

## 2026-11-06 — auditoria de infraestrutura intervalar para O4

- A busca encontrou a infraestrutura já existente `ZetaLean.Rigor`, `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp`. Os três módulos recompilaram em Lean 4.32 com warnings como erros em saída limpa.
- `contains_logQ`, `contains_expI`, `contains_expC` e `contains_dirichletTerm` foram auditados; todos usam apenas `propext`, `Classical.choice`, `Quot.sound`. Comandos, logs e hashes estão em `evidence/rational-boxes/`.
- Isso fornece `log`, `exp` e potências Dirichlet com inclusão kernel-checked, mas ainda não fecha os coeficientes C2.
- A busca também encontrou `Zeta23.DigammaSeries.inv_gamma_eq_prod` em `height50-certified/lean/vendor/zeta23/Zeta23/GammaFacts/Series.lean`, uma identidade formal exata pelo produto de Weierstrass para `1/Γ`.
- Primeiro subproblema analítico pendente: obter uma caixa racional quantitativa para `Complex.Gamma (w/2)` no domínio `0.1495 ≤ Re(w) ≤ 0.9495`, `|Im(w)|≤0.4`. A rota Python usa Stirling deslocado por 80 com 75 correções; a identidade de Weierstrass oferece uma rota formal alternativa, mas sua cauda ainda precisa de um limite numérico eficiente.
- O4 segue aberta. Depois de Gamma, será necessário certificar a cauda Hurwitz e a composição de Cauchy, mantendo a fonte C2 exata.

## 2026-11-06 — ponte Euler-Gamma provada em Lean

- `SigmaGammaEulerIntegral.lean` aproxima a Gamma original pela integral de Euler truncada, prova a fórmula fechada `gammaFinite 512 81 z` e limita explicitamente tanto o resto Taylor compacto quanto a cauda infinita.
- Para `1495/20000 ≤ Re(z) ≤ 1`, `gamma_finite_512_error` prova erro absoluto `≤ 10⁻³²`. As oito raízes públicas auditadas usam somente `propext`, `Classical.choice` e `Quot.sound`.
- Build limpo em Lean 4.32, `warningAsError=true`; comandos, log de build, auditoria e hashes em `evidence/rational-boxes/`.
- A main na base desta prova contém o update de estado pós-PR #169: PR #170, merge `46f5c52037cecd01b6fee43005db57539a3e1af0`.
- A ponte é um subpasso: ainda falta uma caixa racional estreita para `gammaFinite` em cada caixa do contorno, seguida da composição Hurwitz/Cauchy. Nenhuma hipótese `sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes` foi provada nesta etapa.
- PR #171 integrou a prova e a evidência; merge na `main`: `a585de1d4df0b093ef4221cf576a9a87a057652a`.

## 2026-11-06 — ponte Euler-Gamma a precisão alta

- `gamma_finite_1024_240_error` prova, para `1495/20000 ≤ Re(z) ≤ 1`, que `Complex.Gamma z` difere de `gammaFinite 1024 240 z` por no máximo `10⁻⁹⁹`.
- O limite usa a mesma integral de Euler: resto da exponencial truncada `≤10⁻¹²⁰` e cauda `exp(-240)≤10⁻¹⁰⁰`.
- Build Lean 4.32 com warnings como erros passou; auditoria de dez raízes usa só `propext`, `Classical.choice` e `Quot.sound`.
- PR #173 integrou a prova e a evidência; merge na `main`: `72586b6223579ee1b37a6077ad6f2a0eceaf919c`.
- Ainda faltam caixas racionais para `gammaFinite 1024 240` e a inclusão C2.

## 2026-11-06 — ponte Euler-Gamma para interpolação racional

- `gamma_finite_3072_620_error` prova erro absoluto `≤10⁻²⁵⁹` para `gammaFinite 3072 620` em `1495/20000 ≤ Re(z) ≤ 1`.
- Os dois componentes são limitados separadamente: resto Taylor `≤10⁻³⁰⁰`, cauda `exp(-620)≤10⁻²⁶⁰`.
- Build Lean 4.32 com warnings como erros e auditoria de doze raízes passaram; todos os axiomas são os três padrão.
- PR #175 integrou a prova e a evidência; merge na `main`: `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`.
- A análise exata racional `analyze_rational_interpolation.py` encontra uma rota em 129 pontos racionais `t_j=j/100000`; sob a cota analítica ainda a provar `|D(t)|≤10^100` no disco de raio `2/5`, o erro de interpolação para `c₀..c₁₄` fica abaixo de `10⁻⁴¹⁰`. O erro `10⁻²⁵⁹` da Gamma é amplificado por no máximo `10^124`, permanecendo abaixo de `10⁻¹³⁵` antes dos demais fatores da fonte.
- Esta estimativa de pesos foi calculada com frações exatas em Python, mas ainda não formalizada em Lean; a cota analítica e a avaliação dos 129 valores da fonte também estão abertas. Código e log em `analyze_rational_interpolation.py` e `evidence/rational-boxes/`.

## 2026-11-06 — checkpoint O4 publicado

- PR #169 publicou os comandos reproduzíveis, logs vazios de compilação, auditoria de quatro raízes e hashes do motor intervalar reutilizado.
- Merge na `main`: `75782fb8b7fb00bd273bd99f78c337f98439e934`.
- Esse checkpoint continua explicitamente incompleto: nenhuma inclusão de `Complex.Gamma` ou das caixas C2 foi provada; O4 segue aberta.

## 2026-11-06 — identidade algébrica dos 129 nós de interpolação

- `SigmaRationalInterpolation.lean` prova que os nós racionais `j²`, para `0≤j≤128`, são distintos e que a interpolação de Lagrange recupera qualquer polinômio racional de grau menor que 129 exatamente.
- O módulo também prova a identidade coeficiente a coeficiente: cada coeficiente interpolado é a soma dos valores nodais multiplicados pelos coeficientes correspondentes das bases de Lagrange. Os pesos escalados usados na rota numérica estão definidos, mas seus limites ainda não foram provados.
- Build Lean 4.32.0 com `warningAsError=true` passou em saída limpa. A auditoria cobre quatro raízes e encontrou apenas `propext`, `Classical.choice` e `Quot.sound`; o checker fail-closed passou.
- Logs, comandos e hashes estão em `evidence/rational-boxes/VALIDATION.md`, `interpolation-audit*.log` e `source-and-olean-sha256.txt`.
- O4 continua incompleta: faltam os limites Lean dos pesos, a cota analítica da densidade e a avaliação rigorosa da fonte nos pontos.
- A prova foi publicada pela PR #177; commit `67ff0b7ef32de922dda7cd0fcea890bc3afbf738`, merge na `main` `0702371cff0c6016eae9eaa0aa9331ae95483456`.
- O checkpoint permanece parcial: nenhuma inclusão de `sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes` foi provada.

## 2026-11-06 — soma exata do peso constante

- `c5BasisDivisor_coeff_zero`, `c5LagrangeBasis_coeff_zero` e seus casos `j=0`/`j≠0` provam que somente a base indexada por zero contribui para o coeficiente constante.
- `c5InterpolationWeightSum_zero_eq_one` fecha a soma absoluta dos pesos escalados de grau zero como exatamente `1`. Os pesos dos graus `1..14` ainda não têm limites Lean.
- Build Lean 4.32.0 em diretório limpo passou com `warningAsError=true`. A auditoria de nove raízes encontrou somente `propext`, `Classical.choice` e `Quot.sound`; o checker fail-closed passou.
- Base geometry: PR #178, merge `7ad7e29195790eedda01645e71e5c52edf1b4e6b`.
- O4 continua incompleta: a cota analítica da fonte, as avaliações nos pontos e as inclusões em caixas não foram provadas.
- A prova foi publicada pela PR #179; commit `963dbdb035714ddf6d61f5ad329769de48c77354`, merge na `main` `f6a2298b92cbfddad77abe512d73387efea4e870`. Não houve status checks hospedados.
- O checkpoint é parcial: ele não prova os limites de pesos para graus positivos nem as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`.

## 2026-11-06 — fórmula derivativa para o coeficiente linear

- `c5Coeff_one_eq_derivative_eval_zero` prova que o coeficiente linear de um polinômio é a derivada avaliada em zero.
- `c5LagrangeBasis_derivative_eval_zero` expressa a derivada de cada base como soma finita de produtos. Isso fornece uma forma estrutural para tentar limitar o peso de grau um.
- A tentativa de provar diretamente `c5InterpolationWeightSum 1 < 10^11` por expansão racional atingiu `simp failed: maximum number of steps exceeded`, mesmo com `maxSteps=500000`. Erro e comando exatos estão preservados em `evidence/rational-boxes/interpolation-weight-degree1-prototype.log`.
- Depois de remover o lema numérico não fechado, o módulo recompilou limpo em Lean 4.32. A auditoria de 14 raízes passou; somente `propext`, `Classical.choice` e `Quot.sound` aparecem.
- Base geometry: PR #180, merge `de95637d38d5e6d5488342cd5141b88233be6eb7`. Naquele checkpoint, a fórmula derivativa e o registro da tentativa ainda não haviam sido publicados.
- O limite numérico para grau um e todos os graus superiores continuam abertos; O4 não está concluída.

## 2026-11-06 — PR #181 integrada: fórmula derivativa para grau um

- A prova `c5Coeff_one_eq_derivative_eval_zero` e a expansão `c5LagrangeBasis_derivative_eval_zero`, mais a evidência do build/auditoria e a tentativa numérica malsucedida, foram publicadas pela PR #181.
- Commit de prova `0a188c9d71a1a54bdf446ec753609fdde8326bc8`; merge na `main` `7460497307e7ed0ffb47ef1ac96b096e9b410472`.
- O limite numérico dos pesos para grau um permanece aberto; os graus `2..14`, a cota da fonte e as inclusões O4 também permanecem abertos. A validação continua incompleta.

## 2026-11-06 — PR #182: estado pós-PR #181

- Atualizados `SESSION_STATE.md`, `RESTART_HERE.md`, `OPEN_OBLIGATIONS.md`, `VALIDATION.md`, `pins-and-sha256.txt` e este histórico para registrar o merge da prova estrutural.
- Merge do checkpoint de estado na `main`: `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.
- Nenhuma prova numérica nova foi incluída; O4 permanece aberta.

## 2026-11-06 — tentativa intermediária de grau um, validação incompleta (histórico)

- Base confirmada: geometry `origin/main` em `c736dc073091e6184dbb673b622b6b91759accac` (PR #183); branch local `codex/c5-degree1-weight-bound-20261106`.
- A tentativa simbólica do limite de grau um substitui `native_decide` por identidades de produtos fatoriais e uma cota de série. O build integral de `SigmaRationalInterpolation.lean` não concluiu; não há `.olean` novo nem auditoria aprovada das raízes novas.
- `c5-sum-bound-isolated.lean` compilou isoladamente, mas só valida o lema auxiliar. A saída antiga com axiomas `_native.native_decide` foi separada em `interpolation-audit-degree1-native-decide-rejected.log`; o log aprovado anterior de 14 raízes foi restaurado.
- Tentativas, traces comprimidos, pins, hashes e comando de retomada estão em `evidence/rational-boxes/degree1-retry-checkpoint.md` e nos logs associados.
- Não abrir PR desta prova até build integral, auditoria transitiva das raízes novas e hashes de source/olean passarem. O4 permanece aberta.

## 2026-11-06 — limite simbólico de grau um validado

- A continuação da mesma branch substituiu as tentativas anteriores por identidades simbólicas de produtos fatoriais e compilou `SigmaRationalInterpolation.lean` integralmente em uma saída limpa Lean 4.32.
- Foram provados `c5LagrangeBasisProductCoeffOne_bound`, `c5InterpolationCoeffOneAbsSum_le_six` e `c5InterpolationWeightSum_one_lt_ten_eleven`. A soma absoluta escalada do coeficiente de grau um é estritamente menor que `10^11`.
- A auditoria transitiva compilada de forma limpa aceitou 21 raízes; somente `propext`, `Classical.choice` e `Quot.sound` aparecem. O checker fail-closed passou.
- Evidência, comandos e hashes: `evidence/rational-boxes/degree1-weight-bound-validation.md` e os arquivos `c5-interpolation-degree1-final-clean-*`.
- No registro feito antes da PR #185, o checkpoint estava parcial e pronto para publicação. Permanecem abertos os pesos `2..14`, a cota analítica da fonte e as inclusões das caixas de coeficientes C2.

## 2026-11-06 — checkpoint C5 incompleto integrado pela PR #184

- A PR #184 publicou a tentativa e seus diagnósticos como checkpoint explicitamente incompleto; merge na `main`: `5528ddc8093a22682c87f3f9c6575e30e90a7011`.
- Logs, pins, comandos de retomada e o estado da tentativa foram preservados. Esse merge não certificou as caixas nem os sinais finais.

## 2026-11-06 — limite de grau um integrado pela PR #185

- Commit de prova `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`; merge na `main`: `c840ba35711ac8f938fa24c191f2af60f505480d`.
- `c5LagrangeBasisProductCoeffOne_bound`, `c5InterpolationCoeffOneAbsSum_le_six` e `c5InterpolationWeightSum_one_lt_ten_eleven` foram compilados em saída limpa Lean 4.32 e auditados entre 21 raízes; somente os três axiomas padrão aparecem.
- A entrega fecha apenas o limite do peso escalado de grau um. Os pesos `2..14`, a cota analítica, as avaliações da fonte e as inclusões em caixas permanecem abertos; os teoremas finais continuam condicionais.

## 2026-11-07 — avaliador racional genérico dos nós zeta (checkpoint parcial integrado)

- `SigmaC5RationalNodeEval.lean` prova a fatorização racional exata da
  correção de Bernoulli em `emZetaHighRHS 100 300`, mantém a cauda exata e
  prova `c5RationalZetaNodeBox_contains` sob hipóteses explícitas de log/exp.
- Build Lean 4.32 com warnings como erros passou para o módulo e sua auditoria;
  o checker fail-closed aceitou dez relatórios, somente com `propext`,
  `Classical.choice` e `Quot.sound`.
- Os verificadores racionais dos JSONs de Momentos passaram: `+++++++++++-`
  para `d=99/2000` e `+++++++++-` para `d=1/10`; os resultados são
  condicionais às caixas. Logs e hashes estão em
  `evidence/rational-boxes/`.
- **Limite:** nenhuma condição foi instanciada nos 129 nós; não há retângulos
  nodais, composição com Gamma/fonte C2, nem inclusão O4. C5 permanece
  incompleta. A falha de build causada por caminho relativo e a recompilação
  com caminho absoluto também foram preservadas.
- PR #207: commit de prova `fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df`, merge
  na `main` `27a61e6bebcce178b81b961f507400ed77b96d3b`. A validação segue
  explicitamente incompleta.
- Validação detalhada: `evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

## 2026-11-07 — tabela Bernoulli incremental e caixa zeta com tabela compartilhada (checkpoint local)

- `c5BernoulliPrimeTable` constrói `bernoulli'` em um array; o tamanho e cada
  entrada foram provados. A recorrência de escala consome coeficientes dessa
  tabela e mantém a potência inversa como racional exato.
- Os módulos da tabela, da escala e da caixa centrada com tabela foram
  compilados em Lean 4.32 com warnings como erros. As raízes auditadas incluem
  apenas `propext`, `Classical.choice` e `Quot.sound`.
- Uma tabela compartilhada calculou três caixas nodais em 2:20. O lote de 129
  alturas não terminou dentro de 15:57 e não produziu largura agregada; a
  medição é preservada, sem alegação de conclusão.
- A VM disponibilizou 64 GiB totais e o pico medido foi ~6,5 GiB. Não é
  necessário aumentar a memória.
- C5 continua parcial: nenhuma inclusão `sigmaC00495SourceBoxes` ou
  `sigmaC01SourceBoxes` foi provada. Ver
  `evidence/rational-boxes/c5-fast-bernoulli-table-validation.md` para pins,
  logs e retomada.


## 2026-11-07 — ponte CSV–Lean para caixa zeta: tentativa incompleta

- A caixa `(a,j)=(2/5,0)` foi comparada com a linha correspondente do CSV
  contra `c5RationalZetaCenteredNodeBox 512 192 896 (2/5) 0`.
- `decide` falhou ao reduzir `Rat.num`; `rfl` falhou por não-conversibilidade;
  `norm_num` com `maxSteps=1000000` excedeu o limite após aproximadamente 28
  minutos. O pico observado foi ~7,6 GiB, com ~58 GiB disponíveis.
- Nenhum teorema foi compilado; a listagem `#print axioms` posterior aos erros
  contém `sorryAx` da recuperação do elaborador e não é auditoria válida.
- Os arquivos e logs foram preservados em
  `evidence/rational-boxes/c5-exported-box-proof-attempt/`. O CSV permanece
  não certificado como igualdade das caixas Lean, e nenhuma inclusão `sigmaC00495SourceBoxes` ou
  `sigmaC01SourceBoxes` foi provada.
- Próxima etapa: compartilhar a avaliação dos componentes numéricos em lemas
  certificados antes de ampliar a prova a qualquer lote de nós. C5 continua
  explicitamente incompleta.


## 2026-11-07 — PR #215 integrada: checkpoint da ponte CSV–Lean incompleta

- A linha piloto `(a,j)=(2/5,0)` não obteve prova de igualdade com a definição
  Lean. `decide` parou em `Rat.num`, `rfl` não fechou por conversibilidade e
  `norm_num` com 1M passos excedeu o limite em ~28 minutos.
- Os fontes das três rotas, logs, pins, comando e hashes foram publicados. O
  CSV segue sem ligação formal às definições; não houve inclusão C5 nem auditoria
  válida do teorema da tentativa.
- PR #215, commit `baa5e3e`; merge na `main`
  `6bfb4b14606ec1896a2d01d60be4ca54117bd128`.
- C5 continua explicitamente incompleta. Próximo passo: compartilhar lemas de
  cálculo numérico, validar uma caixa-piloto e só então ampliar a avaliação.


## 2026-11-07 — tentativa de prova isolada de `c5CenteredLog2I 512`

- `#eval` exportou os dois extremos racionais em ~40 s.
- `norm_num` não provou a igualdade aos literais; separar os campos, elevar
  `maxSteps` a 1M e aplicar `norm_num1` também deixou metas abertas. Não há
  teorema compilado nem auditoria válida; `sorryAx` nos logs é recuperação de
  erro do elaborador.
- Fontes e logs estão em
  `evidence/rational-boxes/c5-log2-component-attempt/`. A redução em Lean
  continua necessária antes de tratar a saída exportada como formal.
- Próximo passo: dividir a soma em blocos e provar cada parcela intermediária
  com aritmética racional certificada. C5 e as inclusões de fonte permanecem
  incompletas.


## 2026-11-07 — PR #217 integrada: tentativa isolada de `log 2`

- O registro `#eval` dos extremos foi preservado junto às tentativas de prova;
  a igualdade racional não fechou e não há raiz auditável nova.
- PR #217, commit `e34733a`; merge na `main`
  `30a615cafa3b27de40427a73cc64988c77e236d3`.
- C5 permanece incompleta; próximo passo é somar em blocos com certificados
  reutilizáveis antes de ampliar a prova às caixas de zeta.
