# C5 — validação

**Status inicial:** nada da certificação finita está validado nesta branch por Lean.  
**Toolchain:** `leanprover/lean4:v4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.  
**Base:** geometry main `91a1af2f9663d6761a3320e2f06504fe8aaa6776`.

| Alvo | Estado no inventário |
|---|---|
| Recorrência polinomial sem divisão | Deduzida no relatório Python; não provada em Lean C5. |
| Identidade com `sigmaPadeD` original | Deduzida no relatório Python; não provada em Lean C5. |
| Caixa racional implica sinal | Script Python usa frações exatas; precisa ser portado/verificado pelo kernel Lean. |
| Inclusões da fonte original nas caixas | Não demonstradas em Lean. A geração depende de `mpmath.iv` e de código Python ainda não certificado. |
| Teoremas finais nos `sigmaPadeD` originais | Não demonstrados. |
| Axiomas transitivos C5 | Ainda não auditados. |

Os resultados C4 anteriores usam apenas `propext`, `Classical.choice` e `Quot.sound`; essa
auditoria não se transfere automaticamente aos novos teoremas C5.
