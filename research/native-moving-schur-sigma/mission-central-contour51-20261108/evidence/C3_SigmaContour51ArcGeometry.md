# C3 — caixas geométricas formais para os arcos 4096

`SigmaContour51ArcGeometry.lean` reutiliza a caixa racional C5 de `π/4`, escalada
para uma caixa que contém `π`. Para cada `k < 4096`, a prova inclui o arco fechado
`u ∈ [k/4096,(k+1)/4096]` na caixa angular, verifica `normBound ≤ 8`, aplica
`ComplexInterval.expCr 32 80 3` e escala a exponencial por 51. O resultado é
`contour51Arc4096ZBox_contains`; a identidade afim de `s` dá
`contour51Arc4096SBox_contains`.

## Teoremas compilados e hipóteses

- `contour51C5PiBox_contains`: incondicional; reutiliza
  `c5_pi_quarter_interval_contains` de C5.
- `contour51Arc4096UBox_contains`: assume apenas que `u` pertence ao arco racional
  fechado correspondente.
- `contour51Arc4096AngleBox_normBound_le_eight`: assume `k < 4096`.
- `contour51Arc4096AngleBox_contains`: assume apenas que `u` pertence ao arco.
- `contour51Arc4096ZBox_contains` e `contour51Arc4096SBox_contains`: assumem
  `k < 4096` e `u` no arco fechado; não recebem amostras pontuais.

Todos os `#print axioms` retornam `[propext, Classical.choice, Quot.sound]`.
Compilação Lean 4.32.0 com `-DwarningAsError=true`, saída isolada
`/home/thlinux/tmp/c2-contour51-20261108-lean432`; não há `sorry`, `admit` ou
axiomas declarados no fonte.

## Relação com o certificado externo

As caixas para `z(u)` e `s(u)` agora são teoremas Lean contínuos em cada arco.
Elas podem preencher os campos geométricos `parameterContains` e `sContains` de
`Contour51Arb4096N0ArcComponentBoxes`. Elas não foram comparadas ainda com caixas
de componentes exportadas pelo Arb; o JSON C3 atual guarda faixas finais dos
integrandos, não as caixas de `ζ`, `ζ′`, digamma e os intermediários da avaliação.
Assim, não prova nenhum `composedLowerEndpoint`/`composedUpperEndpoint` nem a
inclusão ponto a ponto do avaliador. A tabela 4096 continua sendo certificado Arb
externo com 160 bits e Taylor de ordem 32.

A identidade de resíduos da fonte C2 não mudou: ela liga `e_n=H_n-P_n` à
integral normalizada do kernel meromorfo original. O resto Taylor/Cauchy limita
somente a avaliação por arco; só após inclusão ponto a ponto e integração ele
transporta um limite a `e_n`. A cauda material C2 continua distinta. Os cinco
termos cruzados do determinante continuam todos explícitos; nenhuma hipótese de
sinal do resto foi adicionada.

## Ainda não descarregado

1. Caixas racionais de coeficientes Taylor exatos de ζ até ordem 32 nos centros
   efetivamente usados e a ligação dessas caixas às derivadas verdadeiras.
2. Para cada disco: `DiffContOnCl` de ζ, diferenciabilidade da derivada,
   majorante de fronteira, razão `q<1`, limite de deslocamento e limites racionais
   dos restos de Cauchy.
3. Caixas contínuas para digamma nos arcos. As caixas C5 de Gamma em nós fixos
   não cobrem digamma variando no contorno. A caixa de `log π` já é reutilizável
   pelo teorema `contour51C5LogPiBox_contains`.
4. Inclusões para ζ e ζ′, positividade Lean das caixas de norma quadrada de
   `s-1`, ζ e potências do parâmetro, e as comparações da caixa composta com
   cada extremo Arb.
5. A inclusão contínua dos 4096 integrandos residuais para `n=0,…,5`, e a
   inclusão separada dos 512 arcos para `‖R‖≤4/5`.

Para o primeiro avanço determinantal, bastam as inclusões residuais de
`n=0,1,2`; o adaptador compilado entrega então o intervalo dos três resíduos e a
margem absoluta `1/1000000000 < sigmaPadeD 0 0`. Esse adaptador ainda está
condicional à inclusão por arco. Para todas as janelas centrais, continuam
necessários os seis intervalos residuais e a cota uniforme no círculo.

As caixas C5 em `d=0.0495` e `d=0.1` não foram transportadas para o centro. Não
foi refeita a tabela Bernoulli nem a lista de nós zeta/Gamma de C5.

## Build e hashes

Comando, usando o checkout Carry fixado e isolado já previsto para esta missão:

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51ArcGeometry
```

- Fonte SHA-256: `8fa865179e62d4ca6d1e83eded8f20e329e535ef5234c7ebe48c279232e151d1`
- OLean SHA-256: `d92eb400e09dbdecb4d69e0fe7401f07711eb527500b7b174bd34ae99eaf6deb`
- Log de sucesso SHA-256: `8f3dc8369237ee2643d8adae41e5fe627bfd8988b37fed21f4c4bd7f12d426b8`
- Log completo: `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArcGeometry-attempt7.log`
