# Tentativa de certificação isolada de `c5CenteredLog2I 512`

**Data:** 2026-11-07 UTC
**Base:** `792a5864e1fe0d5568f64d7865c71c316b420863` (main após PR #216)
**Lean:** `leanprover/lean4:v4.32.0`
**Carry pin:** `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`

## Resultado

`#eval` exportou os dois extremos racionais de `c5CenteredLog2I 512` em cerca
de 40 segundos. Foram então tentadas provas de igualdade com os extremos como
literais. `norm_num` deixou metas aritméticas abertas, mesmo separando os campos
`lo`/`hi`, aumentando `maxSteps` para 1 milhão e aplicando `norm_num1` às metas
residuais. A última tentativa ficou ativa por cerca de cinco minutos. Não há
teorema compilado nem auditoria de axiomas válida; o `sorryAx` nos logs vem da
recuperação do elaborador após o erro e não constitui prova.

Isso mostra que até o componente `log 2` compartilhado exige decomposição da
soma finita em blocos ou uma prova recursiva com certificados aritméticos
intermediários. Não foi feita uma inclusão C5 e os extremos continuam apenas
saída de avaliação. Nenhum código C5 de produção foi alterado.

## Arquivos e reprodução

- `SigmaC5Log2ExportProbe.lean`: exporta os extremos por `#eval`.
- `SigmaC5Log2Certified.lean`: rascunhos de igualdade e tentativas com
  `norm_num`; não compila como teorema final.
- `log2-export.log`: saída exata da avaliação.
- `log2-certify*.log`: saídas dos quatro testes de prova que falharam.
- `SHA256SUMS`: hashes dos arquivos desta tentativa e da definição importada.

A partir da worktree geometry C5 e com as worktrees de dependência abaixo
presentes, use o wrapper de compilação (warnings como erros, Lean 4.32, pin do
Carry e limiar de 30 GiB `MemAvailable`):

```bash
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
SIGMA_OUTPUT_DIR=/home/thlinux/worktrees/geometry-of-numbers-c5-formalize-zeta-boxes-20261107/research/native-moving-schur-sigma/.cache/c5-log2-export
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_REFERENCE_ROOT CARRY_LEAN_ROOT SIGMA_OUTPUT_DIR SIGMA_HEIGHT50_BUILD LEAN_BIN
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5Log2ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5Log2Certified
```

O próximo passo é provar uma soma parcial em blocos usando lemas reutilizáveis;
não repetir a expansão completa com limites de passos maiores. O registro maior
da ponte CSV–Lean incompleta está em
`../c5-exported-box-proof-attempt/README.md`.
