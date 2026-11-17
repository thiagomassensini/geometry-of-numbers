# Checkpoint — terceiro bloco radial físico C2: positividade definida em Lean

Data: 2026-11-17
Branch: task/gon-c2-pick-three-schur-20261117
Base: GoN PR #336, commit f83ce36; depende da #335 (germ) e #334 (fonte).
Estado: draft, sem merge.
Comparador externo GoN+CSA sem novas dependências Lake.

## Resultado

TEOREMA INCONDICIONAL, QUALIFICADO PELO REGIME RADIAL:

  physicalC2RadialPickMatrix_three_eventually_posDef :
      ∀ᶠ k in atTop, (physicalC2RadialPickMatrix k 3).PosDef

para as três alturas canônicas

  z_j = i*(j+1)/(k+1), j=0,1,2,

porém APENAS eventualmente para k suficientemente grande.
Este teorema envolve o kernel Cauchy–Pick obtido do vetor MATERIAL C2
com pernas, seed, retorno, câmera, completamento e companheiro.
Não troca a fonte pelo objeto-alvo.

Mais forte, usando congruência HB invertível:

  physicalC2RadialDefectMatrix_three_eventually_posDef :
      ∀ᶠ k in atTop, (physicalC2RadialDefectMatrix k 3).PosDef.

Logo, para as três amostras radiais canônicas e todos os coeficientes
complexos não nulos, a desigualdade da contração quiral é ESTRITA,
nas escalas suficientemente finas.

**Esta é uma afirmação para um tamanho fixo (N=3) e uma grade específica,
não uma alegação de Schur global ou positividade all-order.**

## Como a prova fecha, sem circularidade

### Peça A: estriteza do bloco 2×2 via diferenças confluentes

Novo arquivo externo:
research/material-central-calibration/PhysicalPickTwoStrictNative.lean

- Define a transformação inversível de duas colunas
  T₂(h) = [[1, −1/h],[0,1/h]] e a demonstra por congruência
  com a matriz dslope nativa nas mesmas duas alturas.
- O transformado pelo stencil das segundas diferenças centradas
  converge à matriz de coeficientes
      [[h₀,0],[0,h₁]]
  (o símbolo h_j designa os momentos canônicos readout, não pernas).
- O determinante transformado converge a h₀ h₁>0;
  não pode se anular para todas as escalas suficientemente finas.
- Pela identidade de determinantes sob congruência, a matriz 2×2
  nativa original também tem determinante não nulo.
- O comparador usa a costura C2 física com a dslope nativa (#336)
  e a PSD física C2 2×2 anterior. Pela equivalência do Mathlib
  PosSemidef.posDef_iff_det_ne_zero, deriva
      physicalC2RadialPickMatrix_two_eventually_posDef.

As premissas h₀>0 e h₁>0 já foram certificadas no CSA
(sinais de baixa ordem). Elas não são hipóteses novas nem
foram obtidas da positividade 3×3 que se quer demonstrar.

### Peça B: critério Schur–Sylvester genérico, sem usar momentos

Novo módulo GoN:
GeometryOfNumbers/Analysis/CarryMaterialPickThreeSchurCriterion.lean

- hermitian_two_plus_one_posDef_of_corner_posDef_det_pos
- hermitian_sum_two_one_posDef_of_corner_posDef_det_pos
- hermitian_fin_three_posDef_of_leading_posDef_det_pos

Para uma matriz hermitiana finita 3×3:
  bloco PRINCIPAL 2×2 estritamente PosDef
    + det 3×3 estritamente positivo
  => matriz inteira PosDef.

A prova tipada usa Matrix.PosDef.fromBlocks₁₁
(complemento de Schur) e Matrix.det_fromBlocks₁₁;
a dimensão do complemento é Fin 1. Reindexa de
Fin 2 ⊕ Fin 1 para Fin 3 e preserva o determinante.
Sem hipótese de PSD/PD da matriz 3×3 como entrada.

### Peça C: a hermiticidade da própria fonte, não postulada

- carryMaterialComplexSourcePickMatrix_isHermitian:
  prova para QUALQUER seção finita na parte superior do plano,
  desde que F_C2 não tenha zeros nos pontos; decorre apenas da
  simetria conjugada da diferença dividida
  (R(w)−conj(R(z)))/(w−conj(z)).

### Peça D: terceira direção física

No comparador externo
research/material-central-calibration/CanonicalComparison.lean:

- physicalC2RadialPickMatrix_three_leading_two_eventually_posDef:
  o menor principal do Pick físico 3×3 é literalmente a matriz
  física 2×2 já estritamente positiva.
- physicalC2RadialPickMatrix_three_det_eventually_re_pos (#336):
  det radial 3×3 tem parte REAL positiva, apoiado no
  certificado h₁*(h₀h₂-h₁²)>0 + cauda confluent.
- A hermiticidade física implica que o determinante é real;
  portanto a positividade da parte real é a positividade
  do determinante em ℂ.
- hermitian_fin_three_posDef_of_leading_posDef_det_pos fecha
  physicalC2RadialPickMatrix_three_eventually_posDef.
- O gauge Hermite–Biehler da fonte é inversível: novo
  carryMaterialComplexSourcePickMatrix_posDef_iff_sourceDefect
  transporta PD ao defeito de multiplicador, fechando
  physicalC2RadialDefectMatrix_three_eventually_posDef.

## Origem e limites

A sucessão permanece:
segundas diferenças centradas C2 → fonte material L1/L2
→ seed e retorno → câmera → dressing → companheiro vetorial
→ Green → Pick/HB → diferenças confluentes e Schur.

Os certificados analíticos de h₀, h₁ e h₀h₂−h₁² são
resultados CANÔNICOS independentes de baixa ordem do CSA,
transportados pela IDENTIDADE COMPLEXA da fonte C2 (#335).
Logo não é demonstração autônoma desses sinais a partir de
uma Gram positiva da fonte original, e não é prova de
positividade de todas as ordens.

PRs:
- GoN #334: fonte material física no complexo.
- GoN #335: identificação de germ e matriz de defeito HB/Pick.
- GoN #336: 2×2 PSD e det 3×3 >0 no físico.
- Esta PR: 2×2 PD => 3×3 PD e defeito 3×3 PD.

## Próxima obrigação

Passar da terceira para a quarta direção exigirá um
novo Schur/complemento ou certificado da margem 4×4:
em geral o determinante ou o 3×3 isolados não fornecem
a positividade de ordem arbitrária. A grade radial é
suficientemente fina, para cada N fixo, mas nenhum
controle uniforme em N foi demonstrado.
