# C5 — termo Dirichlet `m=2`, estado de Taylor até `n=2` (parcial)

## Resultado validado

Para o nó racional `(a,j)=(2/5,0)`, o logaritmo `log 2` exportado e
arredondado em 896 bits, e quatro metades do argumento, foram ligados por
provas Lean aos extremos racionais usados na recorrência. A igualdade
formalizada é somente

```lean
c5RoundedExpStateC 896 c5M2TaylorArgExport 2 = c5M2Stage2
```

Ela certifica os estados `n=0,1,2` da recorrência que acumula os primeiros
termos da série de Taylor. Ainda não certifica os 192 termos nem a caixa
completa `c5CenteredDirichletTermBox 512 192 896 4 2 ...`; também não liga as
516 caixas CSV aos coeficientes da fonte C2. Portanto, este é um piloto local
de uma parcela da ponte CSV–Lean, e C5 segue incompleta.

O estágio 2 foi dividido em três resultados auditáveis: produto de intervalos
reais com sinais conhecidos, coarsening exato dos extremos racionais e
atualização da soma. A compilação Lean 4.32.0 com `warningAsError=true` passou.
`#print axioms` para `c5M2Stage2PowerCoarsenExport`,
`c5M2Stage2PowerCorrect`, `c5M2Stage2SumCorrect` e
`c5RoundedExpStateC_stage2_correct_refined` reportou somente
`propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx` na compilação
validada. O log completo está em `state-stage2-refined-build3.log`.

## Pins e ambiente

- Base da `main`: `e96caa7b1850a0d2775c5f801ccfe598e4a2ee0d` (PR #242).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0`.
- `MemAvailable` observado: `63376328 kB`; o wrapper requer pelo menos
  30 GiB.
- O wrapper usa `warningAsError=true` e valida o pin do Carry antes de compilar.
- SHA-256 do `.olean` validado: `dd158e1b6bc94dc757f07e0dc86950e0aceb5f48d643b38150622a2d77800fa9`.

## Reprodução

Da raiz da worktree C5, com os dois checkouts de referência disponíveis:

```bash
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_OUTPUT_DIR SIGMA_HEIGHT50_BUILD LEAN_BIN
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage2Refined
```

Para reconstruir os módulos importados no cache vazio, execute antes, na ordem:

```bash
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2LogCoarsenCertificate
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorArgCertificate
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateCertificate
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage2Refined
```

Os módulos-base já integrados (`SigmaC5Log2Certified` e os módulos Height50)
precisam estar nos diretórios de build indicados em `SIGMA_HEIGHT50_BUILD`.
Para regenerar a tabela dos estados `0…192`, compile também
`SigmaC5M2TaylorStateExportProbe` e capture sua saída; para repetir apenas a
sonda do termo nodal, compile `SigmaC5M2CenteredTermProbe`.

O build validado foi copiado integralmente para `state-stage2-refined-build3.log`.
Os estados racionais `0…192` exportados por `#eval` estão em
`state-export.log`; esse arquivo é dado de trabalho para construir novos
certificados, não é por si só uma prova Lean.

## Tentativas que não validaram o estágio 2

- `attempts/Stage2Monolithic.lean` e `attempts/state-stage2-build.log` registram
  uma tentativa em bloco. Ela deixou metas de piso/teto abertas porque o
  elaborador expandiu ao mesmo tempo os quatro cantos do produto complexo e as
  operações de arredondamento. A saída `sorryAx` emitida durante recuperação
  do elaborador é inválida e não foi aceita.
- `attempts/state-stage2-refined-build.log` e `...build2.log` registram
  iterações intermediárias com erros de projeção, sinais e simplificação de
  intervalos. A correção validada é a fonte
  `SigmaC5M2TaylorStateStage2Refined.lean` e o build `...build3.log`.
- `attempts/CenteredTermMonolithic.lean` registra a prova monolítica do termo
  completo. O log `attempts/certificate-build.log` é o resumo da tentativa;
  a implementação permaneceu impraticável quando `norm_num` expandiu a
  recorrência inteira. Não repetir essa estratégia.

Os arquivos Lean deste diretório e os logs listados em `SHA256SUMS.txt`
preservam as fontes e a evidência da retomada. Para continuar, prove o estado
`n=3` com multiplicação intervalar de sinais mistos e some os estados em ordem,
antes de tentar fechar `n=192` ou compor a caixa do nó.
