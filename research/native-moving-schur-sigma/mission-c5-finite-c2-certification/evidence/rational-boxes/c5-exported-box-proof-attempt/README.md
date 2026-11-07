# Tentativa de prova da caixa zeta exportada — validação incompleta

**Data:** 2026-11-07 UTC
**Base geometry:** `dcca7d1cdef7c2f13685540a7768c3d8c9899aa8` (PR #214)
**Lean:** `leanprover/lean4:v4.32.0`
**Carry pin:** `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`
**Sigma reference pin:** `caa07002306b555fea5624cc11ab2ea5811a4324`

## Objetivo e resultado

Testar se a primeira linha do CSV (`a=2/5`, `j=0`) pode ser importada como
constante racional Lean e ligada por um teorema à definição
`c5RationalZetaCenteredNodeBox 512 192 896 (2/5) 0`.

**Resultado:** nenhuma prova de igualdade foi obtida. O CSV continua sendo uma
exportação de `#eval`, e não um fato formal sobre os limites da definição Lean.
Nenhuma inclusão `sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes` foi provada;
C5 segue incompleta. Nenhum `.olean` válido para o teorema foi produzido e não
houve auditoria de axiomas aprovada.

## Tentativas e erros observados

1. `norm_num` expandindo as definições excedeu o limite padrão de passos de
   simplificação após cerca de 1:50. O primeiro rascunho também esqueceu o
   campo de ordem `le` em cada intervalo; os dois campos foram corrigidos nos
   rascunhos preservados.
2. `decide` falhou ao tentar reduzir a igualdade de `ℚ`; a redução parou na
   decisão sobre `Rat.num` do primeiro extremo real (`re.lo`). Log:
   `compile-decide.log`.
3. `norm_num (config := { maxSteps := 1000000 })` com a expansão completa das
   funções rodou por cerca de 28 minutos e terminou com
   ``simp failed: maximum number of steps exceeded``. O pico observado foi
   aproximadamente 7,6 GiB RSS; a VM tinha cerca de 58 GiB disponíveis. Assim,
   mais memória não é o gargalo desta rota. Log:
   `compile-norm-num-1m-steps.log`.
4. `rfl` falhou em cerca de 13 segundos porque o cálculo não é
   definicionalmente igual aos literais exportados. Log:
   `compile-rfl.log`.

Os `#print axioms` capturados depois de um erro de tática mostram `sorryAx` por
causa da recuperação de erro do elaborador. Essa saída é inválida como prova e
não deve ser usada como auditoria.

## Próxima rota técnica

Decompor o cálculo em lemas reutilizáveis que evitem reexpandir em cada nó a
série de `log 2`, as 99 parcelas da cabeça, as 300 correções de Bernoulli e as
avaliações de `exp`. Validar o custo de cada componente antes de gerar as 516
igualdades. Manter a cauda `<10^-250` e os teoremas genéricos de inclusão já
provados. Até haver uma ponte formal, não tratar o CSV como entrada certificada.

## Reprodução

A partir de uma worktree geometry com a integração C5 atual, execute
`research/native-moving-schur-sigma/compile_sigma_pade.sh` com:

```bash
cd /home/thlinux/worktrees/geometry-of-numbers-c5-formalize-zeta-boxes-20261107
cp research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-exported-box-proof-attempt/c5-exported-box-2_5-0-rfl.lean research/native-moving-schur-sigma/SigmaC5FormalizeOneZetaBox.lean
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105 \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/worktrees/geometry-of-numbers-c5-formalize-zeta-boxes-20261107/research/native-moving-schur-sigma/.cache/c5-formalize-zeta-boxes \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals \
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5FormalizeOneZetaBox
```

O comando aplica `warningAsError=true`, verifica o pin Carry, usa Lean 4.32 e
exige pelo menos 30 GiB de `MemAvailable`. As fontes de prova que falharam e os
quatro logs estão nesta pasta; as caixas CSV e as sondas originais permanecem
em `../c5-centered-all-a-zeta-export-validation.md` e seus arquivos associados.
