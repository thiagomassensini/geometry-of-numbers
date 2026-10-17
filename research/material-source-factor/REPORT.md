# Carry — fator triangular derivado dos observáveis materiais

## Resultado

Foi construída uma recorrência triangular a partir dos jets ordenados do
**residual material efetivo**, depois da síntese completa. A construção não
recebe `PosDef` e não define uma nova fonte ou um novo produto interno.

O Lean verifica duas conclusões distintas:

1. Para qualquer ordem finita, a recorrência fornece uma identidade polarizada
   assinada, com residual explícito e uma fórmula exata para o defeito do fator
   real candidato. Não há conclusão geral de positividade.
2. Para as ordens de Taylor **2, 4, 6**, os certificados theta anteriores provam
   os três pivôs positivos. O fator real desse bloco satisfaz `C * Cᵀ = K` e
   tem determinante positivo, sem hipótese `PosDef`. A recomposição do canal
   central fornece também um fator real invertível do Hankel nativo **4 × 4**.

O novo resultado é a ligação exata entre a extração material, o fator e os
certificados já existentes. A positividade de sete fontes já estava provada;
esta rodada não cria um certificado de sinal em uma nova ordem da fonte.

## Proveniência e objetos

- Repositório alterado: `thiagomassensini/geometry-of-numbers`.
- Base: `aee21826a385ebd3a2ac16bcf8f50d9435a48209`, merge do PR #19.
- Operador consultado, sem modificações: `carry-self-adjoint-operator`,
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `momentos` consultado anteriormente para a cadeia computacional:
  `a54f267365d5d8c965376734b17b10ae89ed3f74`; nenhum arquivo alterado.
- Os pins de Lean, Mathlib e GreenFrame permanecem iguais aos da base.

O ponto de entrada é `carryMaterialRealResidual`, não uma matriz escolhida.
O PR #19 já demonstrou, a partir da fonte completada, a identidade dos seus
jets com os momentos canônicos. Nesta rodada usamos literalmente:

\[
K(i,j)=\operatorname{carryMaterialResidualJet}(2(i+1),2(j+1))
=h_{i+j+2}-\frac{h_{i+1}h_{j+1}}{h_0}.
\]

`carryMaterialEvenPairing` usa o lado esquerdo como definição. O lado direito
é um teorema de comparação, não a definição de um novo estado físico.
`carryMaterialOddPairing(i,j)` permanece separado e satisfaz
`carryMaterialResidualJet(2i+1,2j+1) = h_(i+j+1)`.

As ordens aqui são ordens confluentes de Taylor. Não são profundidades,
câmeras, índices materiais ou coordenadas de um estado de Hilbert global.

## Recorrência sem positividade

Para o pareamento real simétrico já sintetizado, definimos:

\[
R_0(i,j)=K(i,j),\qquad p_r=R_r(r,r),\qquad
\ell_r(i)=\frac{R_r(i,r)}{p_r},
\]

\[
R_{r+1}(i,j)=R_r(i,j)-\frac{R_r(i,r)R_r(r,j)}{p_r}.
\]

São funções totais do Lean. Se um pivô for zero, a divisão totalizada vale
zero; isso **não** elimina sua linha. Nenhuma invertibilidade é deduzida dessa
convenção. A identidade que continua válida, inclusive nesse caso, é:

\[
\boxed{K(i,j)=\sum_{r<n}p_r\ell_r(i)\ell_r(j)+R_n(i,j).}
\]

Os argumentos `i,j` são independentes. O teorema bilinear também conserva
todos os cruzamentos de dois vetores de coeficientes independentes.

Quando todos os pivôs anteriores são não nulos, as linhas já eliminadas são
zero. Para o bloco de tamanho `n`, a identidade vira uma fatoração `L D Lᵀ`
**assinada**, sem conclusão de sinal para `D`.

Declarações em `GeometryOfNumbers.Analysis`:

- `carryPairing_signed_prefix`;
- `carryPairingRemainder_row_zero`;
- `carryPairing_signed_factor`;
- `carryPairingBilinear_factor`.

## O defeito exato do candidato de Cholesky

O candidato real é definido por
`C_n(i,r) = ell_r(i) * Real.sqrt(p_r)`.
A definição de `Real.sqrt` não é uma prova de não negatividade do seu argumento.
O Lean verifica, sem hipótese de sinal ou não anulação:

\[
\boxed{
K_n=C_nC_n^T+(R_n)|_{n\times n}
-\sum_{r<n}p_r^-\,\ell_r\ell_r^T,
\qquad p_r^-=\max(-p_r,0).
}
\]

Assim, tomar raízes não transforma silenciosamente um pareamento assinado
num Gram positivo: a parte negativa e o residual ficam explícitos.
`carryPairingCholesky_defect` é a identidade geral;
`material_even_real_factor_defect` a aplica aos observáveis materiais reais.

Se os sinais `0 < p_r` forem demonstrados para `r<n`, o residual do bloco e
a parcela negativa desaparecem. Os teoremas
`carryPairingCholesky_identity`, `carryPairingCholesky_det_pos` e
`carryPairingCholesky_posDef` fornecem então fatoração, invertibilidade e
positividade estrita. Esses teoremas gerais são **condicionais nos sinais**;
não são uma prova de que a fonte os satisfaz em todas as ordens.

## Três pivôs da fonte, sem `PosDef` como hipótese

As duas primeiras extrações reutilizam o PR #19:

\[
p_0=h_2-h_1^2/h_0>0,
\]

\[
p_1=h_4-h_2^2/h_0
-\frac{(h_3-h_1h_2/h_0)^2}{h_2-h_1^2/h_0}>0.
\]

A nova igualdade de transporte da terceira extração é:

\[
\boxed{
p_2=\frac{\operatorname{nativeSourceSevenEvenDiscriminant}}
{2\operatorname{nativeSourceFiveEvenDiscriminant}}>0.
}
\]

O fator `2` é imposto pelos coeficientes históricos `a_j=2h_j`; não é um
ajuste. A igualdade é provada algebricamente. O sinal é transportado do
teorema existente `nativeSourceSevenEvenDiscriminant_pos`, demonstrado pelo
certificado do integral theta original em
`CompletedNativeChiralReturnFourteenthSourceIntegral.lean`.

Em `CarryMaterialSourceFactorComparison`:

- `material_even_pivot_two_ratio`: identidade do pivô efetivo;
- `material_even_pivot_two_pos`: sinal pela fonte theta existente;
- `material_even_cholesky_three`: fatoração dos nove cruzamentos ordenados;
- `material_even_cholesky_three_det_pos`: fator invertível;
- `material_even_bilinear_three`: pareamento com dois vetores independentes;
- `material_even_three_posDef` e `material_even_energy_three_pos`: consequência
  positiva para esse bloco finito.

## Recomposição do centro: Hankel 4 × 4

Se `C` é o fator do residual 3 × 3, o fator completo é a matriz triangular

\[
\widehat C=
\begin{pmatrix}
\sqrt{h_0}&0&0&0\\
h_1/\sqrt{h_0}&&&\\
h_2/\sqrt{h_0}&&C&\\
h_3/\sqrt{h_0}&&&
\end{pmatrix}.
\]

Os cruzamentos com o centro são literalmente `h_1,h_2,h_3`. O bloco inferior
reconstitui `h_(i+j)` porque soma `h_i*h_j/h_0` ao residual já demonstrado.
Não se altera a normalização de nenhum termo.

`material_hankel_cholesky_four_identity` prova
`widehatC * widehatCᵀ = (h_(i+j))_(i,j<4)`;
`material_hankel_cholesky_four_det_pos` prova seu determinante positivo.

Isto é uma fatoração derivada de observações escalares após a síntese. Não
identifica o produto interno do estado material de Hilbert completo com o
kernel canônico. Essa outra identificação não foi demonstrada nesta rodada.

## Válvula e duas quadraturas

O PR #19 já preservou o balanço completo da válvula, inclusive complemento
oculto, semente, retorno global ordinary/clockado e derivada do dressing.
Esta rodada reutiliza esse resultado sem modificar a fonte ou seus canais.

`material_complex_even_factor_three` verifica a igualdade complexa dos jets:
a quadratura imaginária é zero por identidade da fonte nesse bloco real,
não porque foi descartada antes da síntese.
`material_valve_even_factor_three` transporta a mesma fatoração para os jets
confluentes da válvula, para qualquer `eta != 0`.

Mantém-se o limite do PR #19: o representante por quociente tem germes
ordenados nas linhas centrais. Não há afirmação de extensão conjunta do
kernel sobre a diagonal não central, nem cancelamento de denominador zero.

## Primeira obrigação aberta

Para a próxima ampliação deste bloco par, falta demonstrar o sinal do pivô
calculado da **mesma** recorrência:

\[
p_3=R_2(3,3)-\frac{R_2(3,2)R_2(2,3)}{p_2}>0.
\]

O denominador `p_2` já é positivo. Falta o controle dessa combinação de
cruzamentos da fonte, envolvendo agora momentos até `h_8`. Não basta provar
positividade dos termos diagonais separadamente.

Para todas as ordens, continuam necessários os sinais de todos os pivôs
pares e, separadamente, dos pivôs do setor ímpar. A recorrência e a identidade
do defeito agora são uniformes na ordem; os sinais ainda não são.
O próximo pivô do bloco par não deve ser confundido com o próximo pivô do
bloco ímpar, que tem outra sequência de momentos.

Não é necessário um limite de operadores infinitos para provar
`∀ N, Hankel_N.PosDef`. Mas é necessário um argumento matemático que forneça
os sinais para `N` arbitrário. A existência de uma rotina que calcula cada
fator escolhido não fornece esse argumento por si só.

## Status

| Enunciado | Status |
|---|---|
| Recorrência sobre os observáveis materiais originais | PROVADO em Lean |
| Identidade assinada com residual, para toda ordem | PROVADO em Lean |
| Defeito do candidato real, incluindo pivôs negativos | PROVADO em Lean |
| Sinal dos três primeiros pivôs do bloco par residual | PROVADO, reutilizando theta |
| Fator real invertível do bloco nas ordens 2,4,6 | PROVADO em Lean |
| Fator real invertível do Hankel nativo 4 × 4 | PROVADO em Lean |
| Fator em ordem arbitrária, dados os sinais de seus pivôs | CONDICIONAL, provado em Lean |
| Positividade dos pivôs da fonte em todas as ordens | ABERTO |
| Gram do carrier material completo = kernel canônico | ABERTO |

Nenhuma nova obstrução à fonte é afirmada. Não há novo operador, nova métrica,
whitening ajustado, estados definidos por um Gram-alvo ou uso de dados
numéricos como premissas das provas.

## Validação e evidências

Os comandos e resultados completos ficam em `validation.json`; os footprints
por declaração em `footprints.json`; os nomes e linhas em `new-roots.json`;
os hashes e commits em `provenance.json`; os logs comprimidos em `evidence/`.

A suíte executa build focado e completo com `--wfail`, auditorias de
Foundation, Geometry e Analysis, regressões dos novos fatores e do retorno
global e ambas as comparações entre repositórios. O código da comparação
permanece fora da biblioteca padrão para não introduzir dependência nem
alterar pins. Cada raiz pública nova tem guard transitivo de axiomas e
`#print axioms`; a Analysis admite apenas os três axiomas padrão de Mathlib.
