# Avaliador racional de nós zeta — ponte genérica, C5 ainda parcial

**Data:** 2026-11-06
**Base:** `origin/main` `c3d8d0fc106134bdfa9c62c6d529489b20e157c3` (PR #206).
**Branch:** `codex/c5-rational-zeta-node-eval-20261106`.
**Classificação:** PROVADO — ponte genérica condicional; nenhuma avaliação nodal concreta ou inclusão O4 foi concluída.

## Resultado Lean desta etapa

`SigmaC5RationalNodeEval.lean` fatoriza exatamente, para argumentos racionais,
a correção de Bernoulli de `emZetaHighRHS 100 300` como `100⁻ˢ` vezes uma
soma em `ℚ+iℚ`. A identidade deixa explícita a soma finita de Dirichlet e
preserva a cauda exata `∑' k, emZetaHighBlock ...`; não a remove nem a substitui
por um modelo espectral.

O teorema `CarrySigmaObstruction.c5RationalZetaNodeBox_contains` prova que a
caixa racional definida por `c5RationalZetaNodeBox` contém a
`riemannZeta (a+bi)` quando:

- `2/5 ≤ a ≤ 3/5` e `0 ≤ b ≤ 128/100000`;
- as 99 condições de logaritmo/exponencial para a cabeça finita são fornecidas;
- as condições correspondentes para a potência de base 100 são fornecidas.

O teorema usa a identidade Euler–Maclaurin original e infla a caixa finita
pela cota da cauda `<10^-250`. As condições dos intervalos são hipóteses
explícitas, não números já instanciados. Em particular, este resultado ainda
não avalia os 129 nós `j/100000`, não fornece retângulos concretos de zeta, não
compõe a Gamma ou o fator de completação, e não prova
`sigmaC00495SourceBoxes` nem `sigmaC01SourceBoxes`.

A genealogia da fonte C2 continua nos módulos originais: cabeça material,
cauda geométrica exata, fator da câmera e escalar nativo. Este módulo é apenas
uma ponte para avaliar `riemannZeta` nos argumentos racionais usados adiante;
não redefine a fonte C2 nem `completedSigmaLogJet`.

## Build e auditoria

Rebuild do avaliador e da auditoria passou em Lean 4.32.0 com
`warningAsError=true`. O checker fail-closed aceitou os dez relatórios de
`SigmaC5RationalNodeEvalAudit.lean`; todos usam somente `propext`,
`Classical.choice` e `Quot.sound`. Logs novos:

- `c5-node-clean-11-eval-rebuild.log`;
- `c5-node-clean-12-audit-rebuild.log`;
- `c5-node-clean-13-axiom-check.log`.

O primeiro comando de reprodução, registrado em
`c5-node-clean-08-eval-rebuild.log`, falhou porque passou um diretório de
saída relativo; o script muda para o checkout Carry antes de compilar. A
reexecução com caminho absoluto passou. Essa falha de configuração não é erro
do Lean nem da prova e foi mantida como evidência.

Dependências/pins usados:

- Geometry e toolchain: `c3d8d0fc106134bdfa9c62c6d529489b20e157c3`, Lean
  `leanprover/lean4:v4.32.0`;
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`;
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`;
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

O build limpo completo dos seis módulos está registrado em
`c5-node-clean-01-bernoulli.log` até `c5-node-clean-06-audit.log`. Os `.olean`
ficaram em `.cache/c5-rational-node-clean-20261106/` e não são necessários
para recuperar o fonte; hashes de fontes, logs e `.olean` estão em
`c5-rational-node-evaluator-source-olean-sha256.txt`.

## Checagem das caixas publicadas

Os JSONs em `thiagomassensini/momentos`, branch
`research/sigma-pade-dimension-depth-20261104` no commit
`68c9b5f0a196289e28a8e5586146707d27df6b75`, passaram novamente por
`verify_signs_exact.py`, que usa frações exatas:

- `d=99/2000`: `+++++++++++-`;
- `d=1/10`: `+++++++++-`.

Os hashes dos JSONs e saídas estão em `c5-node-phase0-coefficient-boxes.sha256`
e nos dois logs `c5-node-phase0-verify-*.log`. Isso verifica os sinais
condicionados à inclusão dos coeficientes nas caixas; não demonstra essa
inclusão. A PR #2 de Momentos continua aberta e não foi alterada.

## Próxima obrigação exata

Instanciar as condições `hhead` e `hbase` do avaliador para `j=0,…,128`,
`b=j/100000` e cada parte real necessária (`2/5`, `901/2000`, `1099/2000` e
`3/5`). Para argumentos com parte imaginária negativa, provar e usar a
simetria de conjugação da zeta. Produzir e auditar os retângulos racionais
efetivos dos valores zeta; em seguida compor Gamma, o fator de π e a expressão
da fonte C2 original. Somente a inclusão formal dos coeficientes nas caixas
O3 permitirá retirar as hipóteses condicionais dos teoremas de sinais.

## Comando de reprodução do build

Da raiz da worktree Geometry, o encadeamento de dependências e auditoria é:

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
SIGMA_SOURCE_ROOT="$GEOM/research/native-moving-schur-sigma"
EVIDENCE="$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes"
RUN_EVIDENCE="$EVIDENCE/c5-rational-node-rebuild-20261106"
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
SIGMA_OUTPUT_DIR="$SIGMA_SOURCE_ROOT/.cache/c5-rational-node-clean-20261106"
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_HEIGHT50_BUILD SIGMA_OUTPUT_DIR LEAN_BIN
mkdir -p "$RUN_EVIDENCE"

for MODULE in \
  SigmaC5ZetaBernoulliBounds \
  SigmaC5EulerMaclaurin \
  SigmaGammaEulerIntegral \
  SigmaC5GammaRationalCore \
  SigmaC5RationalNodeEval \
  SigmaC5RationalNodeEvalAudit; do
  if bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" "$MODULE" \
      > "$RUN_EVIDENCE/$MODULE.log" 2>&1; then
    printf 'BUILD_EXIT=0\n' >> "$RUN_EVIDENCE/$MODULE.log"
  else
    STATUS=$?
    printf 'BUILD_EXIT=%s\n' "$STATUS" >> "$RUN_EVIDENCE/$MODULE.log"
    exit "$STATUS"
  fi
done

python3 "$SIGMA_SOURCE_ROOT/check_c5_rational_node_eval_axioms.py" \
  "$RUN_EVIDENCE/SigmaC5RationalNodeEvalAudit.log" \
  > "$RUN_EVIDENCE/axiom-check.log"
sha256sum "$SIGMA_SOURCE_ROOT/SigmaC5RationalNodeEval.lean" \
  "$SIGMA_SOURCE_ROOT/SigmaC5RationalNodeEvalAudit.lean" \
  "$SIGMA_OUTPUT_DIR/SigmaC5RationalNodeEval.olean" \
  "$SIGMA_OUTPUT_DIR/SigmaC5RationalNodeEvalAudit.olean" \
  > "$RUN_EVIDENCE/source-olean-sha256.txt"
```

`compile_sigma_pade.sh` verifica `MemAvailable≥30 GiB`, exige o pin Lean 4.32
e compila com `warningAsError=true`. A tentativa validada usou a saída limpa
acima; hashes ficam no arquivo listado nesta validação.
