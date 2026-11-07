# C5 — exportação exata das caixas zeta nos quatro lados

**Data:** 2026-11-07. **Estado:** checkpoint parcial; a validação C5 segue
incompleta. Nenhuma das inclusões `sigmaC00495SourceBoxes` ou
`sigmaC01SourceBoxes` foi concluída nesta etapa.

## Resultado exportado

As quatro coordenadas reais usadas pelos dois deslocamentos foram avaliadas
nos 129 pontos `b=j/100000`, `0≤j≤128`:

- `a=2/5` e `a=3/5`, para `d=1/10`;
- `a=901/2000` e `a=1099/2000`, para `d=99/2000`.

Cada execução compartilhou uma tabela `c5BernoulliPrimeTable 601` entre seus
129 pontos e imprimiu os quatro extremos racionais de cada
`ComplexInterval`. Os quatro logs contêm, portanto, 516 caixas com extremos
exatos. `c5-centered-all-a-zeta-boxes.csv` reúne os mesmos valores com colunas
`a,j,re_lo,re_hi,im_lo,im_hi,source_log`; o exportador
`export_c5_centered_node_boxes.py` verifica os índices `0…128`, quatro limites
racionais por linha e o total de 516 linhas.

As caixas são avaliações de `c5RationalZetaCenteredNodeBoxWithTable`. A
inclusão formal geral para `riemannZeta` vem de
`c5RationalZetaCenteredNodeBoxWithTable_contains`, integrado pela PR #211;
a tabela de Bernoulli é certificada pelos lemas de tamanho e igualdade de
entrada do checkpoint anterior. O inflamento preserva o resto Euler–Maclaurin
com raio `10^-250`. O CSV registra as saídas exatas de `#eval` e a cobertura
dos índices foi checada pelo exportador. Ainda falta refletir esses extremos
como constantes Lean e provar sua igualdade com cada caixa avaliada antes de
usar o CSV numa composição formal.

## Compilação e auditoria

Os quatro módulos `SigmaC5CenteredAllA*Probe.lean` foram compilados com Lean
4.32.0 e `warningAsError=true`. Os teoremas de inclusão importados e seus
footprints de axiomas foram auditados no checkpoint integrado pela PR #211;
as sondas novas não declaram teoremas, apenas avaliam as funções de caixa e
escrevem seus extremos racionais. Cada log registra 129 índices, o tempo,
o pico de memória e `Exit status: 0`:

| Coordenada `a` | Índices | Tempo | Pico RSS |
|---|---:|---:|---:|
| `2/5` | 129 (`0…128`) | 30:25.72 | 6,550,180 KiB |
| `901/2000` | 129 (`0…128`) | 32:00.14 | 6,527,540 KiB |
| `1099/2000` | 129 (`0…128`) | 31:33.08 | 6,548,940 KiB |
| `3/5` | 129 (`0…128`) | 31:33.96 | 6,532,928 KiB |

As quatro execuções foram paralelas numa VM de 64 GiB; durante a execução,
`MemAvailable` permaneceu perto de 58 GiB. Não é preciso aumentar RAM.

### Pins

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Referência Sigma: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`,
  HEAD `caa07002306b555fea5624cc11ab2ea5811a4324`.
- Base geometry: merge da PR #212,
  `09339ba2374e28ddcdb7ed9982f968c86fea0acc`.

### Comando reproduzível

A raiz do fonte é a worktree do checkpoint atual. A ordem dos diretórios de
cache importa: o cache centrado com o módulo de Bernoulli deve preceder o
cache mais antigo de instanciação, que contém versões anteriores dos mesmos
nomes de módulos.

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-c5-source-box-inclusions-20261107
SIGMA_SOURCE_ROOT="$GEOM/research/native-moving-schur-sigma"
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
SIGMA_OUTPUT_DIR="$SIGMA_SOURCE_ROOT/.cache/c5-centered-all-a-20261107"
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_HEIGHT50_BUILD SIGMA_OUTPUT_DIR LEAN_BIN

for LABEL in 0400 4505 5495 0600; do
  /usr/bin/time -v bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" \
    "SigmaC5CenteredAllA${LABEL}Probe" \
    > "$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-centered-all-a-${LABEL}-probe-retry2.log" 2>&1
done
python3 "$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/export_c5_centered_node_boxes.py"
```

Para repetir em paralelo, inicie as quatro invocações do loop como processos
independentes. Os logs atuais preservam também as tentativas de importação que
usaram uma ordem de cache incorreta (`c5-centered-all-a-*-probe.log` e
`c5-centered-all-a-0400-probe-retry1.log`); o cache centrado mais novo deve vir
primeiro, como no comando acima.

## Próxima obrigação

Esta etapa só exporta os extremos racionais das caixas de `riemannZeta` nos
pontos. Ainda falta provar em Lean que os extremos exportados coincidem com as
definições das caixas, compor cada caixa com `gamma3072Interval_contains`, o fator de completação
original dependente de `π` e a expressão C2 original, interpolar os 129 pontos
e provar que os coeficientes verdadeiros pertencem às bolas de O3. Até essa
prova e auditoria, os sinais finitos C5 permanecem condicionais.
