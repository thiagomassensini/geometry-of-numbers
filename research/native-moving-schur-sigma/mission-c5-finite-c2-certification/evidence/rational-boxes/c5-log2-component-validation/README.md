# C5 — componente `log 2` certificado por blocos

**Estado:** componente formal validado; a missão C5 continua incompleta.

## Resultado

[`SigmaC5Log2Certified.lean`](SigmaC5Log2Certified.lean) divide as somas
`Interval.logSum 512 (1/3)` e `Interval.logSum 512 (-1/3)` em 16 blocos
racionais de 32 termos. Cada um dos 32 blocos foi certificado por aritmética
racional, as somas parciais foram recompostas em Lean e o teorema
`c5CenteredLog2I_512_eq_export` prova a igualdade exata
`c5CenteredLog2I 512 = c5ExportedLogTwo512`.

A prova cobre somente esse componente central. Ela **não** estabelece a
igualdade formal dos 516 extremos CSV às caixas Lean, não avalia a cabeça e os
demais componentes da caixa, e não prova as inclusões
`sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes`. Os sinais C5 continuam
condicionais.

## Build e auditoria

- Lean `4.32.0`; `warningAsError=true`.
- Geometry de referência: `caa07002306b555fea5624cc11ab2ea5811a4324`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- O wrapper verifica o pin Carry e espera por `MemAvailable ≥ 30 GiB`.
- Build: [`build.log`](build.log). Auditoria: [`axiom-audit.log`](axiom-audit.log).
- `#print axioms` reportou exatamente três raízes: `c5LogSum512_pos_eq`,
  `c5LogSum512_neg_eq` e `c5CenteredLog2I_512_eq_export`. Todas dependem
  somente de `propext`, `Classical.choice` e `Quot.sound`; o checker
  fail-closed aceitou os três relatórios.
- A fonte foi varrida por `sorry`, `sorryAx`, `admit` e `native_decide`; não
  houve correspondências.
- O `.olean` recompilado no diretório local `.cache` teve SHA-256
  `60115f6927ca2fa5c541138be42f2b759961d9f50dc63328a66121b9a43c1783`.
  O binário não é versionado; reproduza-o com o comando abaixo.

## Reprodução

Da raiz do worktree C5:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-log2-export"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5Log2Certified \
  > "$SIGMA_OUTPUT_DIR/log2-blocks-and-interval-build-final.log" 2>&1
python3 research/native-moving-schur-sigma/check_c5_log2_axioms.py \
  "$SIGMA_OUTPUT_DIR/log2-blocks-and-interval-build-final.log"
```

The module itself contains the three `#print axioms` commands, so the wrapper
log is also the audit input. `build.log` and `axiom-audit.log` preserve the
successful run used for this checkpoint. [`log2-eval-output.log`](log2-eval-output.log)
keeps the original exported rational endpoints.

## Erro piloto ainda aberto e retomada

A primeira igualdade do CSV,
`(a,j)=(2/5,0)` contra
`c5RationalZetaCenteredNodeBox 512 192 896 (2/5) 0`, segue sem prova formal:

- `decide` não reduz `Rat.num`;
- `rfl` falha por a igualdade não ser definicional;
- `norm_num` com `maxSteps=1000000` excedeu o limite depois de cerca de 28
  minutos (pico observado de ~7,6 GiB, com ~58 GiB disponíveis).

O `.olean`/relatório posterior ao erro tinha `sorryAx` por recuperação do
elaborador e foi rejeitado; não é uma prova válida. Fontes, logs, pins e esse
último erro estão preservados em
`../c5-exported-box-proof-attempt/`. A abordagem direta anterior de `log 2`,
também superada por esta prova, permanece em
`../c5-log2-component-attempt/`.

Retome fatorando os componentes da caixa que ainda faltam (cabeça, correções
Bernoulli e exponencial), compile e audite cada lema, e só então volte à
igualdade piloto CSV–Lean. Preserve a cabeça e a cauda exata da fonte C2.
Depois da ponte, componha Gamma e o fator de π e prove as duas inclusões de
fonte; até lá, C5 permanece explicitamente incompleta.

## Checksum dos arquivos versionados deste checkpoint

`SHA256SUMS` cobre a fonte Lean, o checker, os logs e este README. O hash do
`.olean` local está registrado acima, mas o artefato compilado é reproduzível
e não faz parte do manifesto de arquivos versionados.
