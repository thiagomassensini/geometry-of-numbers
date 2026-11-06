# C4 — fonte deslocada e Bézout

**Estado:** integrado pela PR #162, commit `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge
`799a0e06af5469e9fe0665943adbb1cb29d0b6f8`. A compilação foi feita sobre a base
`ed85c42272798604c54454325e138b8c0680c7ca`, que já continha C0–C3.

## Resultado formalizado

Para `c_d(n)` igual ao coeficiente de Taylor `2n` da densidade original, o módulo prova:

```text
D_d(t) = F(t-id) F(t+id) = C_d(t²)                         localmente no eixo real
C_d · H_d = -C_d′
H_d(n) = 2 * completedSigmaLogJet d n
-C_d′ / C_d = H_d,                                           em séries formais
```

O primeiro resultado recompõe a densidade pelos coeficientes pares e usa
`displacedProductC_ofReal_eq_density` para manter a característica e o produto deslocado
originais. A recorrência vem da identidade local entre a derivada da densidade e a derivada de
seu logaritmo; os coeficientes ímpares da densidade anulam-se pela paridade exata. O fator dois
é explícito, positivo e não é absorvido nos jets originais.

`completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix` identifica o Hankel dos momentos
com `2 • sigmaMatrix`. A congruência de Bézout usa a matriz triangular de convolução dos próprios
coeficientes `c_d`; como `c_d(0)>0`, essa matriz é invertível em dimensão finita. Assim,
`completedSigmaDisplacedSource_bezout_posSemidef_iff_sigmaMatrix` prova a equivalência exata
entre positividade semidefinida do bloco de Bézout original e da `sigmaMatrix` original, em
ambos os setores deslocados.

O lema genérico `CarrySourceBezout.sourceKernel_head_tail` mantém os quatro termos ordenados
`head/head`, `head/tail`, `tail/head` e `tail/tail`. C4 não os identifica com um bracket material
nem lhes atribui sinais.

## Validação

- `focused-build.log`: `SourceBezout.lean` e `SigmaSourceBezout.lean` compilados em diretório
  de saída limpo, com warnings tratados como erros. A resolução de módulos Geometry usa a
  cache local C1 (`.cache/c3-validation/c1`); `SigmaZeroObstruction.lean` confere com o hash no
  manifesto C1 e as demais fontes diretas importadas foram hashadas em `pins-and-sha256.txt`.
- `axiom-audit.log`: dez raízes; 57.386 declarações de tipo/corpo alcançáveis; somente
  `propext`, `Classical.choice` e `Quot.sound`. O auditor exige proveniência da `sigmaMatrix`,
  dos jets e do produto deslocado originais. A auditoria rejeitaria `sorryAx` ou axioma próprio.
- A execução ocorreu com aproximadamente 60 GiB disponíveis; o limite de 30 GiB do script foi
  mantido.
- O GitHub não apresentou status checks hospedados para a PR #162.
- Sem pressupostos de sinal para os jets, sem redefinição de `completedSigmaLogJet` e sem
  alteração do produto deslocado original.

Reprodução, a partir da raiz deste checkout:

```bash
SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c4-main-clean" \
SIGMA_REFERENCE_ROOT="$PWD" \
SIGMA_HEIGHT50_BUILD="$PWD/research/native-moving-schur-sigma/.cache/c3-validation/c1" \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
LEAN_BIN="$HOME/.elan/bin/lean" \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SourceBezout

SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c4-main-clean" \
SIGMA_REFERENCE_ROOT="$PWD" \
SIGMA_HEIGHT50_BUILD="$PWD/research/native-moving-schur-sigma/.cache/c3-validation/c1" \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
LEAN_BIN="$HOME/.elan/bin/lean" \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaSourceBezout

SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c4-main-clean" \
SIGMA_REFERENCE_ROOT="$PWD" \
SIGMA_HEIGHT50_BUILD="$PWD/research/native-moving-schur-sigma/.cache/c3-validation/c1" \
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
LEAN_BIN="$HOME/.elan/bin/lean" \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaSourceBezoutAudit
```

Pins and SHA-256 digests of the new proof, audit, and direct source dependencies are in
`pins-and-sha256.txt`.
