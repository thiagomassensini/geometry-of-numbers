# Checkpoint — controle físico C2 radial: N=2 e determinante N=3

Data: 2026-11-17
Branch: task/gon-physical-pick-radial-two-20261117
Base: GoN PR #335, commit 5dfdc56 (empilhada sobre GoN #334).
Comparação externa: CSA pelo LEAN_PATH existente; nenhuma dependência Lake nova.

## Proveniência

A fonte continua a segunda diferença C2 com pernas materiais, centro,
seed, gradientes L1/L2, retorno físico, câmera, completamento, derivada
vetorial do companheiro, duas quiralidades e o kernel Cauchy–Pick.

Nenhum vetor é definido a partir da Hankel alvo. A identificação
F_C2 = F_native no germ complexo foi provada anteriormente na GoN #335.

## Novos teoremas no comparador GoN–CSA

Arquivo: research/material-central-calibration/CanonicalComparison.lean

- physicalC2RadialDefectMatrix: matriz de defeito da fonte original
  amostrada nas alturas canonicalCompletedC3RadialTiltPoint k i.

- physicalC2RadialDefectMatrix_eventually_eq_native:
  PARA TODO tamanho finito N, o defeito da fonte C2 coincide
  EVENTUALMENTE em k com a matriz de Pick quiral nativa de N pontos,
  em todas as entradas. A prova usa a identidade complexa do quociente
  físico e a convergência de cada amostra para o centro.

- physicalC2RadialDefectMatrix_two_eventually_posSemidef:
  certificado INCONDICIONAL de PSD na fonte C2 para N=2.
  Reaproveita a positividade já demonstrada no CSA, oriunda de
  desigualdades de momentos xi-cosseno de baixa ordem. Não é
  uma prova nova da contração geral a partir da fonte.

- physicalC2Radial_eventually_regular:
  não anulação do valor completado e da coordenada HB+ da fonte
  nas amostras finitas, usando seu germ complexo e os fatos canônicos.

- physicalC2RadialPick_two_eventually_posSemidef:
  a PRÓPRIA matriz Pick física C2 de duas amostras é PSD
  EVENTUALMENTE, sem hipótese adicional de sinal. A conclusão
  usa a equivalência de gauge invertível da GoN #335.

- physicalC2RadialPickMatrix_eventually_eq_native_dslope:
  PARA TODO N fixo, a matriz Pick física C2 coincide eventualmente
  com a matriz nativa dslope de todos os N pontos radiais. A prova
  uniformiza as hipóteses sobre a família finita ANTES de usar
  os dois cruzamentos por entrada.

- physicalC2RadialPickMatrix_three_det_eventually_re_pos:
  o determinante da matriz Pick física C2 de tamanho 3 tem parte
  real ESTRITAMENTE positiva para k suficientemente grande.
  Usa a cauda analítica do stencil confluent e o certificado
  incondicional do CSA de h0*h2-h1^2>0 e h1>0.

Todos estes novos teoremas foram compilados no Lean 4.32
com -DwarningAsError=true, sem sorry, sem axiomas extras
(além dos padrões propext, Classical.choice, Quot.sound).

## Por que NÃO é o fechamento all-order?

PSD do bloco 2x2 e det(3x3)>0 são fatos diferentes.
Ainda não foi formalizado o critério hermitiano completo para
deduzir o sinal 3x3 de todos os menores principais.
Também não se demonstrou que as matrizes do defeito físico
são PSD em QUALQUER tamanho N. Esse é o gate geral.

O CSA já contém um no-go contra identificar o retorno quiral com
um shift TFVD FINITO de borda truncada. Esse teste impede uma
solução ingênua, mas não descarta um transporte conservativo diferente.

## Próximo alvo exato

Formalizar no Lean um critério 3x3 de Schur/Sylvester para a matriz
radial física, com certificado de 1x1 e 2x2 estritos, Hermiticidade
e o determinante positivo; depois procurar um mecanismo de energia
para o complemento Schur na quarta direção e acima.

Sem merge, sem alegação de RH ou positividade dos Hankels all-order.
