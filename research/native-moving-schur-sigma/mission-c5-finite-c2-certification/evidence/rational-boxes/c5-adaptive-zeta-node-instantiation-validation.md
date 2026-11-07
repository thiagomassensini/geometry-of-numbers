# C5 — cobertura zeta adaptativa dos 129 nós

**Data:** 2026-11-07
**Base:** `main` após PR #208, merge `296e899e70bee78c54a3278e73e9bd89eaafaa58`.
**Branch local:** `codex/c5-node-instantiation-20261107`.
**Classificação:** PROVADO — inclusão de zeta em caixas racionais para todos os nós; C5 ainda parcial.

## Resultado formal

`SigmaC5RationalNodeLogBounds.lean` escolhe a redução binária de `log` por termo de Dirichlet, com `m/2^k` entre `1/2` e `1` para `1≤m≤100`. A tabela de escalas evita a redução fixa `k=6`, que para `m=1` produz o argumento `1−m/2^k=63/64` e um limite geométrico do resto muito largo. O erro dessa primeira tentativa está preservado em `c5-node-instantiate-logQ-01.log`.

Com 128 termos, o módulo prova por aritmética racional que os extremos de `logQ` ficam em `[-5,5]` para todos os 100 índices. Para `2/5≤a≤3/5` e `0≤b≤128/100000`, isso dá `normBound≤4` no argumento complexo de cada potência de Dirichlet; `kE=2` cobre o domínio de `expCr`. Assim, as condições `hhead` e `hbase` deixam de ser hipóteses: `c5RationalZetaAdaptiveHeadBox_contains` e `c5RationalZetaAdaptiveBasePowerBox_contains` as constroem.

`c5RationalZetaAdaptiveNodeBox_contains_at` prova a inclusão para todo `j≤128`, `b=j/100000` e todo `a` racional em `[2/5,3/5]`. Isso cobre, em particular, as quatro partes reais `2/5`, `901/2000`, `1099/2000` e `3/5` usadas pelos dois deslocamentos C2. `c5RationalZetaAdaptiveNodeConjugateBox_contains_at` cobre os argumentos com parte imaginária negativa por conjugação e pelo teorema Mathlib `riemannZeta_conj`.

A caixa mantém a representação Euler–Maclaurin original de `riemannZeta`, a correção Bernoulli racional e a cauda exata; a cauda continua limitada por `<10^-250` e é absorvida somente pela inflação da caixa. As provas foram auditadas com 21 relatórios; aparecem apenas `propext`, `Classical.choice` e `Quot.sound`.

## Limites desta etapa

O teorema fornece funções Lean de caixas racionais com parâmetros de precisão `nExp` e `p`; ainda não foram exportados os extremos numéricos achatados dos 129 pontos. Gamma, o fator dependente de π e a expressão da fonte C2 original ainda não foram compostos com as caixas. Não há prova de `sigmaC00495SourceBoxes` nem `sigmaC01SourceBoxes`; os sinais O3 continuam condicionais e C5 permanece aberta.

## Build e auditoria limpos

Cadeia limpa Lean 4.32, com `warningAsError=true`, em `c5-node-instantiation-clean-20261107/`:

1. `SigmaC5ZetaBernoulliBounds`
2. `SigmaC5EulerMaclaurin`
3. `SigmaGammaEulerIntegral`
4. `SigmaC5GammaRationalCore`
5. `SigmaC5RationalNodeEval`
6. `SigmaC5RationalNodeLogBounds`
7. `SigmaC5RationalNodeInstantiate`
8. `SigmaC5RationalNodeEvalAudit`
9. `SigmaC5RationalNodeInstantiateAudit`

Todos terminaram com `BUILD_EXIT=0`. O checker fail-closed aceitou 21 relatórios; não há axiomas fora do conjunto padrão. A primeira tentativa do encadeamento limpo omitiu `SigmaC5RationalNodeEvalAudit` e falhou ao importar o módulo. A cadeia foi corrigida incluindo essa dependência e a auditoria repetiu com sucesso. Esse problema foi de comando/ordem de compilação; não altera as provas.

Reprodução, da raiz desta worktree, com os pins abaixo disponíveis:

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
SIGMA_SOURCE_ROOT="$GEOM/research/native-moving-schur-sigma"
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
SIGMA_OUTPUT_DIR="$SIGMA_SOURCE_ROOT/.cache/c5-node-instantiation-clean-20261107"
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_HEIGHT50_BUILD SIGMA_OUTPUT_DIR LEAN_BIN
for MODULE in SigmaC5ZetaBernoulliBounds SigmaC5EulerMaclaurin SigmaGammaEulerIntegral SigmaC5GammaRationalCore SigmaC5RationalNodeEval SigmaC5RationalNodeLogBounds SigmaC5RationalNodeInstantiate SigmaC5RationalNodeEvalAudit SigmaC5RationalNodeInstantiateAudit; do
  bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" "$MODULE"
done
python3 "$SIGMA_SOURCE_ROOT/check_c5_rational_node_eval_axioms.py" \
  "$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-node-instantiation-clean-20261107/SigmaC5RationalNodeInstantiateAudit.log"
```

`compile_sigma_pade.sh` verifica `MemAvailable≥30 GiB`, exige Lean 4.32 e usa `warningAsError=true`. Os logs individuais, checker e hashes estão em `c5-node-instantiation-clean-20261107/`; os logs das tentativas e erros anteriores estão na pasta `evidence/rational-boxes/`.

Pins: Lean `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`; Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

## Próxima obrigação

Escolher e registrar `nExp`/`p` para a precisão exigida pelas caixas O3, produzir os retângulos numéricos dos nós e compô-los com `gamma3072Interval_contains`, o fator de completação dependente de π e a ponte exata da fonte C2. Em seguida, provar as duas inclusões de coeficientes e auditar os teoremas de sinais finais.
