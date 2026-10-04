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
