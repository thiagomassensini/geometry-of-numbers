# Geometria vertical, síntese e o Gram canônico

## Pergunta e resultado

Partida: `main = e0145b7f8e062de5e741e6225149c56e0654d701`.

**Status: `NO_GO_ISOMETRIC_INCIDENCE_SYNTHESIS`.**

A norma quadrática e a independência das incidências não identificam, por si,
o Hankel dos momentos canônicos. Esta rodada prova um no-go **da representação**:
a reconstrução TFVD integral das incidências, seguida por qualquer mapa
real linear isométrico, mantém seu Gram de coordenadas. Esse Gram é positivo
definido em cada prefixo, mas não pode ser um Hankel de índice-soma, para
nenhuma sequência. Não foi provado que o Hankel canônico falha em ser positivo.
Não há um no-go da teoria completa.

## Objetos anteriores ao produto interno

O carrier é o existente `GlobalC2BranchCarrier`, real:

```text
ℓ²(PositiveOddCore × (C2BranchDirection × depthFromTwo), RealPlaneHilbert)
```

`RealPlaneHilbert = EuclideanSpace ℝ (Fin 2)`. As coordenadas verticais usam
`RealCarry.CarryVerticalL2`. O core, o sinal e a quadratura são labels externos;
a profundidade física é `j+2`. A família `c2RealIncidenceJet` já existia antes
de qualquer igualdade com `baseTwoCanonicalMomentSequence`: são incidências
unitárias nos dois ramos físicos do core 1, em todas as profundidades.

`c2TfvdReconstructedBranchState` extrai as duas quadraturas **depois** de
`c2FiberTfvdSynthesis (c2FiberTfvdAnalysis x)` e reagrupa cada endereço no
carrier original. Bulk e os dois dados de bordo participam da síntese.
O theorem `c2TfvdReconstructedBranchState_eq` reutiliza a reconstrução R2 e
prova igualdade de vetores inteiros com `x`, antes de tomar produtos internos.
Não é uma nova definição do observable completado ou do dressing.

Nenhuma família global de vetores completados/dressed, já identificada com os
momentos canônicos, foi localizada nas declarações atuais. Isso é resultado
da inspeção das APIs, não um theorem sobre impossibilidade de futuras provas.
O sinal escalar completo e seu dressing analítico existem; isso não fornece
ainda uma realização vetorial dos coeficientes da sua log-derivada.

## Cadeia verificada pelo kernel

1. `c2TfvdReconstructedBranchState_eq`: síntese integral recupera o estado.
2. `c2TfvdReconstructedBranchState_inner`: seus produtos internos são recuperados.
3. `c2TfvdReconstructedIncidence_not_parityMomentGram`: reconstruir as incidências
   não remove o no-go anterior.
4. `c2IsometricIncidenceSynthesis_inner`: para **qualquer** mapa real linear
   isométrico `A` do carrier existente para um espaço de produto interno real,
   `⟨A j_i,A j_j⟩ = if i=j then 1 else 0`.
5. `c2IsometricIncidenceSynthesis_linearIndependent`: independência global
   transportada, sem premissa de positividade.
6. `c2IsometricIncidenceSynthesis_gramPair_posDef`: ambos os **Grams próprios**
   even/odd são PosDef em toda ordem, por independência.
7. `c2IsometricIncidenceSynthesis_hankel_three_ne_gram`: já em ordem 3, esse
   Gram even não é `hankelGram moments 3`, para qualquer `moments`.
8. `c2IsometricIncidenceSynthesis_not_parityMomentGram` e sua especialização
   `_not_canonicalParityMomentGram`: nenhum desses mapas isométricos identifica
   o kernel de momentos exigido.

O choque finito é exato:

```text
⟨A j_even(0), A j_even(2)⟩ = 0
⟨A j_even(1), A j_even(1)⟩ = 1
```

Um kernel Hankel requer ambas as entradas iguais a `h₂`. Não se ajusta nenhuma
constante ou valor de momento. Não há argumento numérico.

## Menor seam que permanece

A igualdade exigida continua sendo, para uma família vetorial completada
`J` definida independentemente dos momentos:

```text
polarizedRealMomentCoefficient baseTwoCanonicalMomentSequence
  (parityJetNumber i) (parityJetNumber j)
= inner ℝ (J i) (J j)                            (para todo i,j)
```

Equivalente aos blocos `h_(i+j)`, `h_(i+j+1)` e mixed zero. A rota que acaba
de ser excluída não pode fornecer `J`: uma imagem isométrica das incidências
mantém os dois valores incompatíveis acima. Falta construir/identificar o
readout **vetorial completado** da mesma síntese/dressing canônico e provar
essa identidade. Não há ainda dois objetos completados locais entre os quais
se possa afirmar que resta apenas uma igualdade simples já tipada.

A API genérica `hankelPair_posDef_of_parityMomentGram` continua suficiente
**depois** de provar esse Gram e a independência dos prefixos da mesma família.
A independência das incidências, ou de seu TFVD, não é automaticamente a
independência de uma família completada ainda não construída. Não se pode
listar esse último gate como já fechado. Não foi aplicado um gerador não
limitado nesta rodada; domínio all-order continua separado.

Não há PSD/PD incondicional do Hankel canônico novo nesta rodada. Os operadores
finitos existentes e suas hipóteses não foram alterados.

## Proveniência e guardrails

- Os vetores precedem os momentos: YES.
- As incidências vêm dos endereços C2 já formalizados: YES.
- A síntese TFVD completa precede o produto interno: YES.
- Um readout ou momento define retroativamente o carrier: NO.
- Coeficientes vetoriais foram escolhidos pelos momentos: NO.
- `2^(-k/2)` foi identificado com `n^(-1/2)`: NO.
- Não há Gram do scalar response, Cholesky, positivity certificate, novos
  axiomas, alturas externas ou identificação clock/height.
- O no-go anterior da incidência nua permanece. Sua extensão a reconstrução
  integral e transporte isométrico não exclui outros readouts completados.

Provas novas exclusivamente locais: `RealTfvdCenterLegMomentSeam`,
`C2RealFiberTfvdIncidence`, `RealCarryTfvd`, `ParityMomentGram` e Mathlib.
Nenhum pacote, theorem ou fonte histórica é portado nesta rodada.
Foundation, Geometry, R2 e o dressing permanecem intactos.

## Auditoria e publicação

Todos os nomes públicos estão em `Analysis/Audit.lean` e em
`VerticalIncidenceGramObstructionAudit.lean`, com `#assert_analysis_axioms`
e `#print axioms`. Footprint dos capstones:
`[propext, Classical.choice, Quot.sound]`.

Comandos executados: todos com exit status **0**, incluindo a elaboração
direta de `VerticalIncidenceGramObstructionAudit.lean` pelo kernel.
A busca de placeholders/declarações proibidas nos módulos novos e
`git diff --check` também passaram.

```bash
lake build --wfail GeometryOfNumbers.Analysis.VerticalIncidenceGramObstruction
lake build --wfail GeometryOfNumbers.Analysis.VerticalIncidenceGramObstructionAudit
lake build --wfail GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
bash scripts/audit-analysis.sh
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
git diff --check
```

Mensagem do commit da rodada: `audit: exclude isometric incidence synthesis as canonical moment Gram`.
O SHA concreto e a confirmação `HEAD = main = origin/main = GitHub` ficam no
relatório de entrega. Não há incremento matemático seguinte nesta rodada.
