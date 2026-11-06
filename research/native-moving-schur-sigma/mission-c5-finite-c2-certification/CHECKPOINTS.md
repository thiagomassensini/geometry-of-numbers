# C5 — checkpoints

## 2026-11-06 — inventário inicial (pré-prova)

- Criada worktree isolada `codex/c5-finite-c2-certification-20261106` sobre geometry `origin/main` em `91a1af2f9663d6761a3320e2f06504fe8aaa6776`.
- A branch de pesquisa original geometry `agent/native-moving-schur-sigma` em `9392ebac9930f5d11c56f595556080e8ab1de809` tem logs/caches não rastreados, preservados sem alteração.
- C4 e a missão C0–C4 estão documentadas na main e integradas.
- A branch de pesquisa Momentos `origin/research/sigma-pade-dimension-depth-20261104` está em `68c9b5f`; PR #2 está aberta. Ela contém as duas caixas racionais, código para gerar caixas e relatório condicional. Não foi feito merge.
- O build alvo é Lean 4.32.0, conforme `lean-toolchain` da main.
- Estado matemático inicial e comandos de retomada: `RESTART_HERE.md` e `SESSION_STATE.md`.

## Próximo checkpoint

O checkpoint de build e auditoria da O3 está em `evidence/rational-boxes/`. Após integrar essa etapa, o próximo checkpoint deve registrar a investigação/prova de O4; não misturar os caches/logs das outras worktrees.

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

## 2026-11-06 — checkpoint O4 publicado

- PR #169 publicou os comandos reproduzíveis, logs vazios de compilação, auditoria de quatro raízes e hashes do motor intervalar reutilizado.
- Merge na `main`: `75782fb8b7fb00bd273bd99f78c337f98439e934`.
- Esse checkpoint continua explicitamente incompleto: nenhuma inclusão de `Complex.Gamma` ou das caixas C2 foi provada; O4 segue aberta.
