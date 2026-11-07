# C5 — tabela incremental de Bernoulli e caixas zeta com tabela compartilhada

**Data:** 2026-11-07. **Branch:** `codex/c5-flatten-zeta-boxes-20261107`.
**Classificação:** checkpoint parcial, ainda não integrado. As inclusões em
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` continuam sem prova.

## O que foi provado e compilado

- `SigmaC5FastBernoulliTable.lean` constrói a sequência `bernoulli'` uma vez
  em um `Array ℚ`. `c5BernoulliPrimeTable_size` e
  `c5BernoulliPrimeTable_getD` provam o tamanho e a igualdade de cada entrada
  com a definição recursiva do Mathlib.
- `SigmaC5RoundedRationalScale.lean` carrega os coeficientes dessa tabela na
  recorrência intervalar. As potências inversas ficam como racionais exatos;
  `c5RatCorrectionSumIntervalWithTable_contains` e
  `c5RatScaleIntervalWithTable_contains` provam as inclusões para qualquer
  tabela suficientemente longa cujas entradas estejam corretas.
- `SigmaC5RationalNodeCenteredInstantiate.lean` acrescenta
  `c5RationalZetaCenteredNodeBoxWithTable_contains`, que transporta uma tabela
  compartilhada para a caixa completa de zeta. Os wrappers antigos continuam
  provados usando a tabela canônica.
- Os três módulos foram compilados com Lean 4.32 e `warningAsError=true`.
  Os `#print axioms` de tabela, escala e caixa de nó listam somente
  `propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx`.

## Medições

| Ensaio | Resultado | Tempo / pico de memória |
|---|---|---|
| Tabela incremental até `B₆₀₀` | `(3141, 54)` bits para numerador e denominador | 2:07 / 2,68 GiB |
| Correção Euler–Maclaurin, `P=300`, `N=100` | larguras real e imaginária `(8,896)` | 2:13 / 6,55 GiB |
| Caixa completa em `a=3/5`, `b=128/100000` | larguras `(1568,2371)` e `(1561,2371)` | 2:05 / 6,55 GiB |
| Três alturas com uma tabela compartilhada | larguras gravadas no log | 2:20 / 6,55 GiB |
| Grade de 129 alturas | interrompida sem largura final | 11:01 e 15:57 / ~6,54 GiB |

Os ensaios anteriores sem a tabela incremental foram interrompidos após
12–13 minutos sem largura; a sonda isolada de `bernoulli 600` foi interrompida
após 5:19. Isso identifica a recomputação recursiva de Bernoulli como um
gargalo real. A versão compartilhada reduziu o ensaio de três nós para pouco
mais que o custo de um nó, mas o lote de 129 ainda exige otimização ou execução
mais longa. A VM tem 64 GiB totais e cerca de 59 GiB disponíveis; mais memória
não é necessária para esses ensaios.

## Logs reproduzíveis

Os logs de build, auditoria e medição permanecem nesta pasta:

- `c5-fast-bernoulli-table-build-retry5.log`
- `c5-fast-bernoulli-scale-with-table-build-retry1.log`
- `c5-centered-node-shared-table-build.log`
- `c5-fast-bernoulli-600-probe.log`
- `c5-rounded-scale-fast-bernoulli-probe.log`
- `c5-centered-zeta-node-fast-bernoulli-probe.log`
- `c5-centered-shared-table-three-node-probe-retry3.log`
- `c5-centered-129-shared-table-probe.log`
- `c5-centered-129-stream-probe-retry1.log`
- falhas e tentativas anteriores `c5-bernoulli-600-probe.log`,
  `c5-rounded-scale-exact-inverse-probe.log` e
  `c5-rounded-scale-real-inverse-probe.log`.

## Retomada

Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106`.
Pins: Lean `v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`;
Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

Compile, em ordem, `SigmaC5FastBernoulliTable`, `SigmaC5RoundedRationalScale`
e `SigmaC5RationalNodeCenteredInstantiate` usando
`research/native-moving-schur-sigma/compile_sigma_pade.sh` e o ambiente Lean
registrado em `c5-adaptive-zeta-node-instantiation-validation.md`. Para testar
compartilhamento, compile `SigmaC5CenteredSharedTableProbe`; para repetir o
lote interrompido, use `SigmaC5Centered129SharedTableProbe` ou
`SigmaC5Centered129StreamProbe`. Todos os fontes e logs de diagnóstico estão
fora de `.cache`; o cache de build não deve ser publicado.

## Ainda aberto

O checkpoint não contém retângulos achatados dos 129 nós, composição com
Gamma, fator dependente de `π` e fonte C2, nem prova de qualquer inclusão de
coeficientes. Os sinais C5 continuam condicionais. A lei distância ×
profundidade e os novos cadernos seguem adiados.

## Snapshot para retomada e publicação (2026-11-07)

Este é um checkpoint **parcial; a validação C5 está incompleta**. Os fontes
Lean das adaptações de tabela/escala/caixa, sondas, logs de tentativas e os
registros da missão ficam versionados junto com este documento. A sobreposição
temporária está preservada nos fontes `SigmaC5FastBernoulliTable.lean`,
`SigmaC5RoundedRationalScale.lean` e
`SigmaC5RationalNodeCenteredInstantiate.lean`; as sondas estão nos demais
`SigmaC5*Probe.lean`. O diff reaplicável dessas fontes está em
`c5-bernoulli-shared-table-overlay.patch`; nenhum patch adicional do C5 foi
localizado em `/tmp`. O patch de compatibilidade de outro subpasso,
`evidence/interval-certificate/momentos-gmpy2-compat.patch`, também permanece
no checkpoint. O diretório `.cache` contém apenas artefatos locais de build e
não faz parte da publicação.

### Pins e raízes usadas

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Referência Sigma: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`,
  HEAD `caa07002306b555fea5624cc11ab2ea5811a4324`.
- Raiz de pesquisa deste checkpoint: branch
  `codex/c5-flatten-zeta-boxes-20261107`, baseada no merge PR #210
  `82ceb1825b2c7546883d80c58b6549b5fd0390de`.
- Checkout Carry usado pelo script:
  `/home/thlinux/worktrees/carry-sigma-c2-pinned-045369`.
- Build height-50 usado pelo script:
  `/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean`.

### Comandos de retomada

Na raiz da worktree acima, configure as mesmas raízes e compile a cadeia em
ordem (o cache indicado é local e deve ser recriado se necessário):

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
SIGMA_SOURCE_ROOT="$GEOM/research/native-moving-schur-sigma"
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean
SIGMA_OUTPUT_DIR="$SIGMA_SOURCE_ROOT/.cache/c5-bernoulli-shared-table-20261107"
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_HEIGHT50_BUILD SIGMA_OUTPUT_DIR LEAN_BIN

for MODULE in SigmaC5FastBernoulliTable SigmaC5RoundedRationalScale \
  SigmaC5RationalNodeCenteredInstantiate SigmaC5CenteredSharedTableProbe; do
  bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" "$MODULE"
done
```

Para repetir as duas tentativas do lote de 129 nós e manter os códigos de saída
nos logs, rode separadamente:

```bash
/usr/bin/time -v bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" \
  SigmaC5Centered129SharedTableProbe \
  > "$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-centered-129-shared-table-probe-retry2.log" 2>&1
/usr/bin/time -v bash "$SIGMA_SOURCE_ROOT/compile_sigma_pade.sh" \
  SigmaC5Centered129StreamProbe \
  > "$SIGMA_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-centered-129-stream-probe-retry2.log" 2>&1
```

O script `compile_sigma_pade.sh` exige Carry no pin acima, Lean 4.32.0,
`warningAsError=true` e `MemAvailable≥30 GiB`. Os comandos são apenas para
retomar as medições; não substituem a obrigação pendente de produzir as duas
inclusões de coeficientes e seus teoremas finais.

### Última falha observada

A compilação e a auditoria Lean dos módulos de tabela, escala e caixa de nó
passaram. A última falha foi operacional no lote de 129 nós:
`SigmaC5Centered129StreamProbe` foi interrompida por `SIGINT` (signal 2) após
15:57.63, 99% de CPU e pico de 6,542,308 KiB; não houve erro de elaborador Lean
nem saída parcial por nó. A tentativa agregada anterior de
`SigmaC5Centered129SharedTableProbe` também foi interrompida por `SIGINT` após
11:01.07, 99% de CPU e pico de 6,539,792 KiB, sem largura agregada. Portanto,
o gargalo medido é tempo de CPU/exatidão racional, não memória. A VM tinha 64
GiB totais e aproximadamente 59 GiB disponíveis.

Os registros completos dessas execuções e das tentativas anteriores estão em
`c5-centered-129-shared-table-probe.log`,
`c5-centered-129-stream-probe-retry1.log` e no restante de
`evidence/rational-boxes/`. O checkpoint não alega que a grade foi calculada.
