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
