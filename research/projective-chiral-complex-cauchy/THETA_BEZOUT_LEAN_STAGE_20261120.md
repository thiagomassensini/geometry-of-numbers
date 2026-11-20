# C2 Mellin → theta → Bézout: Lean staging (20/11/2026)

## Proveniência preservada

Este estágio parte da cadeia **pernas materiais C2 e profundidade vertical** (`2^k m ± 1`, peso `2^-k`) → **pushforward ímpar e seu defeito conectado** → **bracket com semente** → **carta/Genuine dividida pelo fator da câmera C2** → **característica completada `F=A*N` e resposta logarítmica** → **densidade theta e Hankels/Bézout**. O pushforward de massas e a fonte Mellin bracketada não são identificados como a mesma medida: seus canais possuem construções e normalizações próprias.

Este checkpoint **não** contém uma demonstração de positividade em toda ordem nem uma prova da identidade integral analítica completa com `F`.

## Oito arquivos resgatados do Work

Preservados sem alteração no commit `86cb6e5`, na branch `research/radial-cauchy-schur-all-orders-20261118`. Incluem `C2_MELLIN_POLARIZED_CANCELLATION.md`, `MELLIN_CAMERA_MATCHED_SCHUR.md`, `THETA_CAMERA_FREE_SCHUR.md`, `TfvdFirstEdgeGreenSign.lean` e os certificados Python, mantendo todas as identidades, ressalvas e limites dos autores.

## Novo módulo `GeometryOfNumbers/Analysis/C2ThetaBezoutAlgebra.lean`

Provas com índices `Fin n` para **todo `n`**, sem presumir sinal:

- `c2ThetaBezoutConvolution_eq_congruence`: coeficientes da convolução dupla de `W(U)W(V)` com o kernel de momentos equivalem a `T_n H_{e,n} T_nᵀ`, incluindo todos os termos cruzados.
- `c2ThetaToeplitz_det`: `det T_n = w_0^n` (o portador é triangular de diagonal constante).
- `c2ThetaBezoutConvolution_det`: `det C_{e,n} = w_0^(2n) det H_{e,n}` sem divisão nem inversas.
- `c2ThetaBezoutConvolution_posDef_iff`: se `w_0 ≠ 0`, `C_{e,n}` é PosDef **se e somente se** `H_{e,n}` é PosDef. Esta equivalência **não** fornece positividade nova.
- `c2ThetaBezoutConvolution_adjacent_det_ratio`: razão de determinantes adjacentes escala por `w_0²`, quando o determinante anterior é não nulo. Logo a escala de pivôs Schur é preservada.
- `c2ThetaBezout_even_numerator`, `c2ThetaBezout_odd_numerator`: identidade polinomial **sem denominadores** sob `W' = -WH` em dois argumentos. Os coeficientes iniciais também estão demonstrados.

**Limite exato:** foi formalizada a convolução coeficiente a coeficiente e os numeradores algébricos. Ainda falta provar em Lean que **os coeficientes do quociente bivariado analítico de Bézout** coincidem, para todos os índices, com a convolução `c2ThetaBezoutConvolution`. Não tratar essa identificação como já concluída.

## Novo módulo `GeometryOfNumbers/Analysis/C2ThetaDensityBridge.lean`

- Define literalmente cada parcela da densidade teta de `THETA_CAMERA_FREE_SCHUR.md`:
  `2π(n+1)² exp(5y/2) [2π(n+1)² exp(2y)-3] exp(-π(n+1)² exp(2y))`.
- `c2ThetaDensityTerm_pos` e `c2ThetaDensityHead_pos` provam **positividade estrita de cada termo e de todo prefixo não vazio para `y≥0`**.
- Define a série `c2ThetaDensity`, seus momentos pares e `c2ThetaRawW(j)=(-1)^j 2/(2j)! · ∫₀∞ y^(2j) Φ(y)dy`, como **objetos-alvo**. Ainda não se provou a somabilidade da série, a integrabilidade dos momentos, nem a identidade dessas definições com `F`.
- `c2ThetaRawBezout_congruence` instancia a álgebra geral nos coeficientes definidos pela integral.
- `c2ThetaRawBezout_odd_origin` demonstra, **assumindo a recorrência `W'=-WH` nos dois primeiros coeficientes**, a identidade exata
  `C_{1,1}(0,0)= μ₂² - μ₀ μ₄/3`, onde `μ_{2j}=∫₀∞ y^(2j) Φ(y)dy`.
  O sinal exige `3μ₂² > μ₀μ₄`. Positividade da densidade sozinha não basta.

## Validação e confiança

Os dois módulos passaram com Lean 4.32, `-DwarningAsError=true`. Os novos `#print axioms` mostraram apenas `propext`, `Classical.choice`, `Quot.sound`. Nenhum `sorryAx`. O ambiente de verificação focal utilizou as `.olean` já compiladas e a mesma revisão `81a5d257c8` da mathlib da GoN; uma reconstrução limpa do root ainda não foi executada.

## Três obrigações restantes

1. **Análise:** a série teta converge e tem a reflexão/paridade requerida; seus momentos existem e `F(1/2+u)=∫ℝ exp(uy) Φ(y)dy`, derivado a partir do bracket e da câmera original. Transportar a semente, pushforward e fator arquimediano sem saltos de proveniência.
2. **Coeficientes:** `W'=-WH` e a identidade bivariada dos numeradores implicam que *cada* coeficiente do Bézout analítico é a convolução formal já provada, para todo `i,j`; sem identificar por decreto.
3. **Sinal:** encontrar uma desigualdade específica da densidade `Φ` que torne os dois blocos PosDef em toda ordem. Os 40 pivôs intervalares de cada setor continuam sendo evidência finita, não a prova universal.

A rota Green/TFVD permanece uma segunda interface a ser conectada a esse Bézout por um pareamento **polarizado de dois argumentos**, não por uma compressão escalar do bordo.
