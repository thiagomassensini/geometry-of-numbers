# Krylov simétrico e a primeira coluna dos momentos canônicos

Partida: `main = c33c4cd7863bcd4d2ba0d70b89e6d865e39a7f44`.

## Incremento A: o índice-soma é consequência da simetria

`SymmetricKrylovHankel.lean` usa um operador linear **total** `L`, real ou
complexo. Logo não aplica poderes de um operador não limitado fora do domínio.
No corte material finito essa restrição é automaticamente satisfeita.

O theorem `symmetricKrylov_inner_add` prova, com a orientação conjugada correta:

```text
inner 𝕜 ((L^i) v) ((L^j) v) = inner 𝕜 v ((L^(i+j)) v)
```

A prova reutiliza `LinearMap.IsSymmetric.pow` e `pow_add`. Não é preciso
definir o kernel pelo valor desejado: a soma dos índices surge do transporte
das potências pelo produto interno. Nenhum vetor é construído a partir de
momentos. A sequência espectral auxiliar recebe um vetor e operador prévios:

```text
krylovSpectralMoment L v r = inner ℝ v ((L^r) v)
```

`krylovSpectralMoment_gramRepresentation` realiza o Hankel dessa sequência.
`firstColumn_of_symmetric_implies_hankelGram` mostra que uma identificação
independentemente provada da primeira coluna basta para o kernel inteiro.
Os teoremas `_hankel_posSemidef` e `_hankel_posDef` reutilizam a infraestrutura
Gram existente. Estritamente positivo exige independência dos prefixos da
**mesma** família de Krylov; simetria não prova essa independência.

A simetria sozinha não afirma:

- ortogonalidade entre `L^(2i)v` e `L^(2j+1)v`;
- positividade do bloco shifted sem input adicional;
- igualdade com `baseTwoCanonicalMomentSequence`;
- existência do vetor completado que realiza o response dressed.

## Unicidade da recorrência: condição independente

`krylovSpectralMoment_eq_of_logDerivativeRelations` é uma implicação genérica:
dadas duas sequências que já satisfazem a mesma identidade division-free e
`phi 0 ≠ 0`, elas coincidem. Para a sequência espectral isso exige provar:

```text
phi 0 * spectralMoment r
+ sum_{j<r} spectralMoment j * phi (r-j)
= -(r+1) * phi (r+1)
```

Não foi usada unicidade para assumir essa relação. Ela é exatamente o próximo
input necessário; auto-adjunção não fornece a log-derivada de um response
arbitrário.

## Proveniência e limites

Provas novas locais, sem fonte histórica ou dependência nova. Imports:
`ParityMomentGram`, `MomentGramPositivity`, `LogarithmicMomentHankel` e Mathlib
`InnerProductSpace.Symmetric`. Não se altera Foundation, Geometry, R2,
no-gos anteriores, scalar synthesis, dressing, Jacobi ou height.

A auditoria local permite apenas `[propext, Classical.choice, Quot.sound]`.
Todos os nomes públicos recebem guard e `#print axioms` em Analysis/Audit e
`SymmetricKrylovHankelAudit`. A relação exata dos jets finitos com as potências
de `L` será tratada no incremento seguinte, após publicação deste incremento.

Incremento A: build `--wfail` do módulo, audit específico, Analysis e
Analysis/Audit; scripts Analysis/Foundation/Geometry; `git diff --check`:
**todos exit 0**. Os sete nomes novos foram kernel-checked pelos guards e
`#print axioms`: `[propext, Classical.choice, Quot.sound]` em todos.
Mensagem do primeiro commit: `feat: derive Hankel kernels from symmetric Krylov powers`.

## Incremento B: o clock material finito e os jets reais de paridade

**Status final: `PASS_KRYLOV_HANKEL_FIRST_COLUMN_OPEN`.**

O carrier usado é o já existente `FiniteRealSpectralHilbert M =
EuclideanSpace ℂ (Fin M)`, também lido como espaço de produto interno real.
Não é um embedding do response escalar. A coordenada `j` representa `j+1`.
`L = finiteMaterialClock M = finiteRealSpectralGenerator M` é o clock
simétrico/auto-adjunto já provado. Seu autovalor é `log(j+1)`.

`FiniteClockKrylovHankel.lean` NÃO cria um segundo clock ou um vetor completado.
Ele recebe qualquer vetor finito prévio e prova:

```text
(L^r v)(j) = log(j+1)^r v(j)
(-i L)^r v = (-i)^r L^r v
iteratedDeriv r (t ↦ finiteMaterialOrbit M t v) 0 = (-i)^r L^r v
normalizedClockJet r v = ((r!)⁻¹ (-i)^r) • L^r v
L^r v = (r! i^r) • normalizedClockJet r v
```

O theorem `finiteClockStrongGenerator_skew_inner` prova literalmente
`⟨(-iL)x,y⟩ = -⟨x,(-iL)y⟩`. Não se chama `-iL` de auto-adjunto.
O caso zero é incluído, sem uma afirmação falsa de não-auto-adjunção universal.

`finiteClockSpectralMoment v r = Re ⟨v,L^r v⟩` é uma sequência **auxiliar**
determinada por `v,L`. Ela realiza o Hankel próprio, sem ser identificada com
os momentos canônicos. A convenção complexa não esconde conjugação:

```text
⟨normalizedJet_i, normalizedJet_j⟩_C
= conj((-i)^i/i!) * ((-i)^j/j!) * ⟨v,L^(i+j)v⟩_C.
```

A primeira coluna real dos jets originais é:

```text
⟨normalizedJet_(2r),v⟩_R
= (-1)^r/(2r)! * finiteClockSpectralMoment v (2r)
⟨normalizedJet_(2r+1),v⟩_R = 0.
```

Esses são `finiteClockEvenJet_firstColumn` e `finiteClockOddJet_firstColumn`.
Zero na primeira coluna odd NÃO significa que o vetor odd seja zero.

### Paridade derivada, não postulada

O witness `finiteClockRawKrylov_even_odd_pairing_pos` usa a delta material
`n=2` e prova `⟨v,Lv⟩_R = log 2 > 0`. Portanto a auto-adjunção NÃO implica
mixed zero para potências cruas pares/ímpares.

A família `finiteClockParityKrylov` retém a quadratura do gerador temporal:

```text
J_even(r) = L^(2r)v
J_odd(r)  = -i L^(2r+1)v
```

Ela é definida somente a partir de `v` e do clock. Os teoremas
`finiteClockParityKrylov_even_eq_normalizedJet` e
`finiteClockParityKrylov_odd_eq_normalizedJet` provam, respectivamente:

```text
J_even(r) = (-1)^r (2r)! • normalizedClockJet (2r) v
J_odd(r)  = (-1)^r (2r+1)! • normalizedClockJet (2r+1) v.
```

Nenhuma constante é ajustada pelos momentos. O mixed REAL pairing é zero
porque todos os pairings das potências de um mesmo clock simétrico são reais,
enquanto a quadratura odd contém `-i`. O pairing complexo mixed não é declarado
zero. `finiteClockParityKrylov_gramRepresentation` prova o kernel:

```text
q_r = finiteClockSpectralMoment v (2r) = Re ⟨v,(L²)^r v⟩
even/even = q_(i+j)
odd/odd   = q_(i+j+1)
mixed     = 0.
```

`finiteClockEvenSpectralMoment_hankelPair_posSemidef` deduz ambos os Hankels
PSD em qualquer ordem. Isso é positividade de `q`, NÃO da sequência canônica.
Não foi provada independência dos prefixos para um vetor arbitrário. `PosDef`
continua exigindo independência da mesma família no teorema genérico.

### Readout finito já existente

`finiteClockHeadCoefficient_eq_krylovReadout` reusa `finiteClockJets_to_head`:

```text
historicalFiniteHeadCoefficient weights r
= ((-i)^r/r!) * finiteHeadReadout weights (L^r historicalInitialState).
```

Isso é a HEAD finita. Não é uma igualdade entre o log-derivative moment e
um produto interno. O head não é identificado com o full signal.

## Busca do estado completado e o menor gate concreto

Os módulos `BaseTwoSynthesizedClockCompletion`, `BaseTwoSynthesizedClockMoments`
e `BaseTwoCanonicalDressingMoments` fecham o sinal completo, tail derivada,
dressing concreto, jets all-order do response e os momentos da log-derivada.
`CanonicalGreenMomentJetSeam` transporta o estado vetorial C2/Green e seus jets
mas explicitamente não certifica que são o completed boundary readout.
`RealTfvdCenterLegMomentSeam` e a auditoria de incidência mantêm seus no-gos.

A busca de declarações NÃO localizou um `v_completed` anterior aos momentos
que realize o response dressed. Os quatro objetos permanecem distintos:

1. `baseTwoCanonicalResponse`: função ESCALAR completada/dressed;
2. a source C2/Green/TFVD: estado vetorial com proveniência;
3. a incidência nua: candidato já excluído;
4. um vetor completado que realize a primeira coluna: ainda não identificado.

Esse é um resultado de inspeção das APIs, não prova de impossibilidade futura.
Poderes do clock não são meros transportes isométricos da base de incidência;
o novo mecanismo não contradiz o no-go da rodada anterior.

Para a rota Hankel simples, a igualdade suficiente é literalmente:

```text
baseTwoCanonicalMomentSequence r = Re ⟨v_completed,L^r v_completed⟩.
```

Para a rota de paridade REAL efetivamente derivada dos jets nesta rodada:

```text
baseTwoCanonicalMomentSequence r = Re ⟨v_completed,L^(2r) v_completed⟩.
```

Esta última, com o mesmo `v_completed` e os quadrature jets acima, propagaria
imediatamente ao full parity kernel. Não é recebida como premissa de um PASS
canônico, nem provada para algum candidato. Não se decide a convenção correta
do observable completado apenas pela forma do kernel.

Uma forma alternativa EXATA do gate é provar independentemente, para a
sequência espectral proposta `q` e a phi já fechada:

```text
baseTwoCanonicalPhi 0 * q r
+ ∑ j∈range r, q j * baseTwoCanonicalPhi (r-j)
= -((r+1):ℝ) * baseTwoCanonicalPhi (r+1)       (para todo r).
```

Então `baseTwoCanonicalPhi_zero_ne_zero` e unicidade identificariam `q=h`.
Não há prova dessa relação espectral atualmente. Não se usa unicidade para
supor a própria relação. Também falta a identificação do vetor completado:
não se afirma que resta somente comparar dois objetos já localmente definidos.

## Domínio, proveniência e próximos passos

Todos os powers novos são do clock FINITO, sem gate de domínio. Nenhum power
all-order de `greenStateMaterialLogGenerator` é aplicado. A source C2 geral
continua exigindo momento logarítmico para o gerador; scalar analyticity não
resolve esse gate vetorial. Nenhum `CoreState` é declarado analytic vector.

Não se troca `2^(-k/2)` por `n^(-1/2)`, não se normaliza um vetor usando h₀,
não se scalariza uma head para fabricar um carrier completado, não se portam
no-gos históricos como no-gos globais. Clock log n não é height operator.
Nenhuma positividade canônica, Jacobi ou construção de alturas é implementada.

## Teoremas/auditoria do incremento B

Os nomes públicos e seus axiomas são registrados em `Analysis/Audit.lean` e
`FiniteClockKrylovHankelAudit.lean`. A compatibilidade dos inner products real
complexo é provada pelas identidades de polarização da norma, como no módulo
local `C2GreenWhiteningGenealogy`; não requer esse import pesado.

Primeiro commit publicado: `afbf30ddd9b947fe9d65b748ae9791d23c421c92`.
Mensagem do segundo incremento: `feat: identify finite clock jets with symmetric Krylov and parity Gram`.
Os comandos de build/audit e os SHAs finais constam do relatório de entrega.

Verificação final do incremento B: build `--wfail` do módulo, audit específico,
Analysis e Analysis/Audit; elaboração direta de `FiniteClockKrylovHankelAudit`;
scripts Analysis/Foundation/Geometry; busca de placeholders nos módulos novos;
`git diff --check`: **todos exit 0**. Os vinte nomes públicos do incremento B
passam os guards e `#print axioms` com apenas
`[propext, Classical.choice, Quot.sound]`. Foundation conserva footprint vazio.
