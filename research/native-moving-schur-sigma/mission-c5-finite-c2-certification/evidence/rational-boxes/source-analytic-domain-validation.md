# C5 O4 — domínio analítico da fonte deslocada

## Resultado validado

`SigmaC5SourceAnalytic.lean` prova, para `|d|≤1/10`, que os dois fatores
originais da característica deslocada permanecem no domínio analítico de
altura do Carry quando `|z|<2/5`. Consequentemente,
`displacedProductC d` é analítica no disco aberto de raio `2/5`; há também
especializações para `d=99/2000` e `d=1/10`.

Isso prova o domínio necessário para aplicar Cauchy à fonte original. **Não**
prova uma cota numérica uniforme para seu módulo, não certifica as avaliações
nos 129 nós e não prova que os coeficientes verdadeiros pertencem às caixas
O3. Portanto, C5 permanece incompleta.

## Build e auditoria

- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, fonte rastreada limpa.
- Build limpo com `warningAsError=true`: `c5-source-analytic-clean-retry1-build.log`;
  terminou com `BUILD_EXIT=0`.
- A auditoria dos quatro teoremas públicos está no mesmo log. O checker
  fail-closed é `check_c5_source_analytic_axioms.py`; resultado:
  `c5-source-analytic-clean-retry1-axiom-check.log`.
- Hashes da fonte e do `.olean` compilado:
  `c5-source-analytic-clean-retry1-source-olean-sha256.txt`.
- A primeira execução usou por engano caches de outro worktree e falhou por
  não localizar `SigmaSourceBezout.olean`. A tentativa e o erro estão
  preservados em `c5-source-analytic-clean-build.log`; a repetição usou os
  caches C4 fixados e passou.

Os quatro teoremas dependem apenas de `propext`, `Classical.choice` e
`Quot.sound`.

## Publicação

Integrado à `main` pela PR #189. Commit de prova:
`e0272bfc9099031cb127ea0db8874900d9e8eca1`. Merge:
`3513a3b3854b105419d4f2cef245efac7ce88ba0`. O GitHub não reportou status
checks para esta PR.

## Próxima obrigação O4

Provar uma cota numérica explícita para o módulo da fonte C2 completada no
disco usado pela interpolação. A prova deve usar a cabeça C2, a cauda
geométrica exata e a completação original. Depois disso ainda será preciso
certificar racionalmente as avaliações nos nós e compor as inclusões dos
coeficientes nas caixas O3.

O comando de compilação reproduzível está registrado em `RESTART_HERE.md`.
