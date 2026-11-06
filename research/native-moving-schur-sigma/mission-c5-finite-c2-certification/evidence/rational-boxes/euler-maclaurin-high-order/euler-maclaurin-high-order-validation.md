# C5 — Euler–Maclaurin de ordem alta (checkpoint parcial)

**Status:** a identidade analítica e a cota explícita da cauda foram provadas
localmente em Lean 4.32. O4/C5 segue incompleta: este checkpoint ainda não
avalia nenhum dos 129 nós e não prova a inclusão dos coeficientes da fonte C2
nas caixas racionais.

## Resultado formal

`SigmaC5EulerMaclaurin.lean` constrói uma identidade de Euler–Maclaurin para a
`riemannZeta` original com número arbitrário de correções de Bernoulli. A
identidade é provada primeiro em `Re(s)>2`, estendida ao quadrante superior em
`Re(s)>0, Im(s)>0` por continuação analítica e aos pontos reais positivos,
`s ≠ 1`, por continuidade.

Para os nós usados em C5, `2/5 ≤ Re(s) ≤ 3/5` e
`|Im(s)| ≤ 128/100000`. Com `N=100` e `P=300` (ordem total `2P=600`),
`emZetaHighTail_norm_le_node` prova que a norma da cauda exponencial completa
é `< 10^-250`. A cauda fica preservada como termo matemático; a cota permite
inflar uma futura caixa intervalar da parte finita. A identidade usa a cabeça
finita de Dirichlet e os termos de borda de Bernoulli sem trocar a função
`riemannZeta` nem omitir a cauda.

O limite `<10^-250` é mais forte que o orçamento `<10^-170` necessário para
que a amplificação de interpolação abaixo de `10^145` continue pequena. Ainda
falta compor caixas racionais da parte finita em cada nó com a ponte Gamma e a
fonte C2 original. Nenhum sinal C5 incondicional foi concluído neste passo.

## Build e pins

- Lean: `leanprover/lean4:v4.32.0`, binário Lean 4.32.0,
  commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Referência Geometry/C2: `caa07002306b555fea5624cc11ab2ea5811a4324`.
- Base da branch no momento do build: `282adac6abe82584de6d6b8fe2010d8976b87203`.
- O helper usa `warningAsError=true`; os dois módulos foram compilados em
  ordem numa saída limpa `/tmp/c5-em-final-clean-20261106`.

Comandos de compilação, executados nessa ordem:

```bash
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105 \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
SIGMA_OUTPUT_DIR=/tmp/c5-em-final-clean-20261106 \
./compile_sigma_pade.sh SigmaC5ZetaBernoulliBounds

SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105 \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
SIGMA_OUTPUT_DIR=/tmp/c5-em-final-clean-20261106 \
./compile_sigma_pade.sh SigmaC5EulerMaclaurin
```

O primeiro build terminou com status 0; o segundo registra `BUILD_EXIT=0`.
`check_c5_em_axioms.py` validou exatamente oito raízes — os dois lemas de
Bernoulli e os seis resultados Euler–Maclaurin — sem axiomas além de
`propext`, `Classical.choice` e `Quot.sound`. Logs e checker estão no mesmo
diretório deste arquivo:

- `01-bernoulli-build.log`
- `02-em-build-and-axioms.log`
- `03-axiom-audit-check.log`

Hashes de fontes, binários `.olean`, helper e checker estão em
`source-olean-sha256.txt`.

## Próxima obrigação

Avaliar intervalarmente, nos 129 nós racionais, a parte finita de
`emZetaHighRHS 100 300`, inflando-a pela cauda `<10^-250`. Usar
`ZetaLean.ComplexInterval.dirichletTermBox2` para os termos `m^-s`, conservar
as correções de Bernoulli e tratar separadamente o nó real `j=0`. Em seguida,
compor esses valores com a completação Gamma e a fonte C2 original e provar as
inclusões racionais que hoje permanecem condicionais.
