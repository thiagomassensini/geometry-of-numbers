# C5 O4 — núcleo racional Gamma, primeiro nó (checkpoint parcial)

**Status: validação incompleta.** Este checkpoint certifica somente o núcleo
racional de `gammaFinite 1024 240` no ponto `a=1/5, b=0`. Ele ainda não
certifica a potência `240^z`, a caixa de `gammaFinite`, Gamma completa, zeta,
nem as inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 continua
incompleta.

## Resultado provado

`SigmaC5GammaCoreNodePilot.lean` define

```lean
gammaFiniteRationalCore 1024 240 (1 / 5) 0
```

como um racional complexo exato. O primeiro `#eval` exporta os limites do
componente real escalado por `2^1024`, com extremos inteiros adjacentes, e
componente imaginário zero. A prova monolítica do piso da soma toda não foi
prática; a rota validada divide os 1.024 termos em 16 blocos de 64.

`SigmaC5GammaCoreChunk64Certificate.lean` prova cada um dos 16 pisos por
`Int.floor_eq_iff` e `norm_num`; `SigmaC5GammaCoreChunk64Combine.lean` prova a
identidade de decomposição, soma os limites e prova a inclusão da parte real do
núcleo na caixa racional:

```text
[ S / 2^1024, (S+16) / 2^1024 ] × {0}
S = 275781938341656998247498279059590815312276036036255216214882872600995774029861836058896937160041575903320151944800026402972432844284228092678807476044282215424584268737143184859696367110367053499844618346501765028880499401777805926442826222879058356397163086588169838861545660142942420951717265122285587424398
```

A largura do intervalo real é `16/2^1024`. A declaração
`c5GammaCoreNodePilotChunkBox_contains` prova que o núcleo racional está
nessa caixa. O lema auxiliar `2^1024` usa `decide` com redução pelo kernel;
nenhuma prova usa `native_decide`.

O build final foi feito com Lean 4.32.0 e `warningAsError=true`. A auditoria
isolada lista 20 raízes: os 16 pisos, a recomposição dos blocos, os limites da
soma, a soma dos pisos e a inclusão na caixa. Todas dependem somente de
`propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx` nem axiomas de
avaliação nativa. O log é `chunk64-axiom-audit.log`.

## Arquivos e histórico

Este checkpoint parcial foi publicado pela PR #282, com commit de prova
`131d5f57da009a830c0a967bb5cf4713412c3473`, integrada à `main` no merge
`7c301a2bb0b975369c8f8889ec2940372d2266c2` em 2026-11-07.

Fontes compiladas: `SigmaC5GammaCoreNodePilot.lean`,
`SigmaC5GammaCoreChunk64Probe.lean`, `SigmaC5GammaCoreChunk64Certificate.lean`,
`SigmaC5GammaCoreChunk64Combine.lean` e `SigmaC5GammaCoreChunk64Audit.lean`.
O log `chunk64-probe.log` preserva os 16 inteiros exportados. Falhas anteriores
não foram apagadas: estão nos logs `chunk64-cert-probe*.log`,
`chunk64-cert-decide-probe.log` e `chunk64-axiom-audit-env-fail.log`; a tentativa de prova monolítica de 3.072
termos, a tentativa que acionou `native_decide` e o erro de caminho também
permanecem neste diretório. As fontes que produziram essas falhas foram
preservadas com o sufixo `Failed` ou `RootAttempt`.

O resultado de 3.072/620 fica como histórico separado (`*3072*`). Esta prova
nova usa 1.024/240 porque o erro analítico disponível para esses parâmetros é
`gamma_finite_1024_240_error`, com erro `≤10^-99`.

## Ambiente e reprodução

- Base da branch: commit `ec5c5e8998b62726ada6f942cf4c2410048a2a23` (merge da
  PR #281).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Memória disponível durante os builds: `63,383,072 kB`; o script de build
  exige pelo menos 30 GiB.

Da raiz deste checkout:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-gamma-core-node-pilot"
export SIGMA_HEIGHT50_BUILD="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-rational-node-clean-20261106"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaCoreNodePilot
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaCoreChunk64Probe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaCoreChunk64Certificate
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaCoreChunk64Combine
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5GammaCoreChunk64Audit
python3 research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/check_chunk64_axioms.py research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/chunk64-axiom-audit.log
```

The detailed attempts, outputs, and sources are retained here
for resumption. `.cache/` contains only local compiled artifacts and is not
part of this checkpoint.
