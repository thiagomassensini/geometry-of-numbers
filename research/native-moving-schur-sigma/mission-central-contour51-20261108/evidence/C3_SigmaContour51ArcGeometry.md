# C3 — caixas geométricas formais para os arcos 4096

`SigmaContour51ArcGeometry.lean` reutiliza a caixa racional C5 de `π/4`, escalada
para uma caixa que contém `π`. A construção agora vale para qualquer partição uniforme
positiva de `[0,1]`: para `N>0`, `k<N`, e `u∈[k/N,(k+1)/N]`, inclui o arco fechado na caixa
angular, verifica `normBound≤8`, aplica `ComplexInterval.expCr 32 80 3` e escala a exponencial por
51. As especializações fornecem `z(u)` e `s(u)` para as partições de 4096 e 512 arcos.

## Teoremas compilados e hipóteses

- `contour51C5PiBox_contains`: incondicional; reutiliza
  `c5_pi_quarter_interval_contains` de C5.
- `contour51ArcPartitionUBox_contains` e `contour51ArcPartitionAngleBox_contains`:
  assumem apenas que `u` pertence ao arco fechado correspondente.
- `contour51ArcPartitionUBox_bounds` e `contour51ArcPartitionAngleBox_normBound_le_eight`:
  assumem `0<N` e `k<N`.
- `contour51ArcPartitionZBox_contains` e `contour51ArcPartitionSBox_contains`:
  assumem `0<N`, `k<N` e `u` no arco fechado; não recebem amostras pontuais.
- As especializações `contour51Arc4096ZBox_contains`, `contour51Arc4096SBox_contains`,
  `contour51Arc512ZBox_contains` e `contour51Arc512SBox_contains` assumem somente `k<N` e `u`
  no arco, com o valor positivo fixado de `N`.

Todos os sete `#print axioms` retornam `[propext, Classical.choice, Quot.sound]`.
Compilação Lean 4.32.0 com `-DwarningAsError=true`, saída isolada
`/home/thlinux/tmp/c2-contour51-20261108-lean432`; não há `sorry`, `admit` ou
axiomas declarados no fonte.

## Relação com o certificado externo

As caixas para `z(u)` e `s(u)` agora são teoremas Lean contínuos em cada arco de 4096 ou 512
partições. As de 4096 podem preencher os campos geométricos `parameterContains` e `sContains` de
`Contour51Arb4096N0ArcComponentBoxes`; as de 512 estão disponíveis para compor a inclusão da
resposta na cota de círculo. Elas ainda não foram comparadas com caixas
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
   `s`, `s-1`, ζ e potências do parâmetro, e as comparações da caixa composta com
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

- Fonte SHA-256: `43499cc8f04929535203f03035c448507d0d2a2646722c95c90b836c900a2302`
- OLean SHA-256: `b17874f8ff593038c7ca833fb856cffed241a8958313644e07aeaacf6d59c981`
- Log de sucesso SHA-256: `aceade4bfb3fd16ecd6813394c8f4992bfcacd9844a4cb4c77f02ceb68856ae9`
- Log completo: `/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArcGeometry-attempt8.log`

## Tentativas de compilação preservadas

As tentativas 2–6 são mantidas em `C3_SigmaContour51ArcGeometry-attemptN-failed.log`. Elas
identificaram, respectivamente, a redução incompleta de `Interval.contains`, camadas extras de
cast racional/real, a forma do cast em `k+1`, e dois argumentos de arco não usados. A tentativa 7
compilou a primeira versão especializada em 4096 arcos; a versão final generalizou a partição e
foi recompilada na tentativa 8, incluindo as especializações para 512 e 4096.
