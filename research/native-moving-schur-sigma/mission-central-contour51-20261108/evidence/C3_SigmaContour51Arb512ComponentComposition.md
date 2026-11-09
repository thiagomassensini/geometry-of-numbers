# C3 — composição dos componentes na cota Arb de 512 arcos

`SigmaContour51Arb512ComponentComposition.lean` adiciona a estrutura
`Contour51Arb512ArcComponentBoxes k`. Ela registra, em cada arco fechado, caixas da fórmula
original para `s`, ζ, ζ′, digamma e `log π`; as três normas quadradas positivas para `s`, `s-1` e
ζ; e uma comparação racional entre `ComplexInterval.normBound` da resposta composta e o endpoint
Arb daquele arco.

## Teoremas e hipóteses

- `contour51Arb512ResponseArcEvaluatorInclusion_of_component_boxes_at_arc`: para `k<512`, um
  registro completo implica, para todo `u` no arco fechado, que a norma da resposta original
  `contour51OriginalResponse (circleMap 0 51 (-πu))` está abaixo do endpoint Arb.
- `contour51Arb512ResponseArcEvaluatorInclusion_of_all_component_boxes`: uma família desses
  registros em todos os 512 arcos implica a proposição universal
  `contour51Arb512ResponseArcEvaluatorInclusion`, usada pela ponte existente para `hR`.

O registro mantém abertas como campos as inclusões dos componentes, a positividade das normas e a
comparação final com o endpoint. O campo `sContains` pode usar a geometria provada em
`SigmaContour51ArcGeometry.lean` para a partição 512. O teorema não gera caixas analíticas para ζ,
ζ′ ou digamma e não valida os limites exportados do Arb por si só.

Os dois `#print axioms` retornam somente `[propext, Classical.choice, Quot.sound]`. Lean 4.32.0,
`-DwarningAsError=true`, saída exclusiva `/home/thlinux/tmp/c2-contour51-20261108-lean432`; não há
`sorry`, `admit` ou axiomas declarados no fonte.

O certificado Arb de 512 arcos continua externo: os endpoints racionais satisfazem
`upper[k]≤746413/1000000<4/5` em Lean, mas só após a inclusão componente a componente se obtém a
premissa de círculo em Lean. Isso não afeta a rota direta do primeiro determinante, que usa os
intervalos residuais de 4096 arcos para `n=0,1,2` e não requer `hR`.

## Build e hashes

Log de sucesso:
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51Arb512ComponentComposition-attempt4.log`.

- Fonte SHA-256: `45005370dc030387dacc3f38aa7492746503d4dbd2c66f31b6c619379024fa26`
- OLean SHA-256: `3f2037c8a552cdd4e060579eaa420d66744520d2c04ece83f09009b338973da0`
- Log SHA-256: `d0768e240ffb5b101e5dc88902e30ca7161692fe7e1dccda1d95350f4305b5be`

As tentativas falhas 1–3 também foram preservadas em arquivos
`C3_SigmaContour51Arb512ComponentComposition-attemptN-failed.log`: a primeira detectou a
dependência não importada da caixa geométrica; as seguintes corrigiram a conversão dos limites
racionais do arco para `ℝ`. A tentativa 4 é a compilação final com warnings como erros.
