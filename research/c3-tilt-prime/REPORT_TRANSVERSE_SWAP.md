# Troca transversal e recomposição infinita da fonte C3

**Resultado: PASS para as duas passagens de derivada no canal do tilt; PARTIAL para o sinal da fonte completada e dos pivôs.** A derivada em altura já fora transportada à soma infinita em `MixedInfinite.lean`. Esta continuação prova que a derivada transversal, em `δ=0`, também passa pela soma do **tilt original**, e recompõe a carta C3 com o carrier e seus cruzamentos. Não se demonstra positividade da Hankel em toda ordem.

## O que foi provado

Para o centro `Cₖ=3(k+1)`, altura real `t` e deslocamento `δ=σ−1/2`, denote por `Wₖ(δ,t)` o bloco original `canonicalCriticalWeightedTiltBlock`; `W∞` é a soma dos mesmos blocos. A fase material `exp(−it log Cₖ)` e a amplitude `Cₖ^(−1/2)` não são modificadas.

1. `transverseSlope_norm_le` usa a desigualdade de segunda diferença da fonte em `primos` para provar, para `−1/4<δ<1/4` e `δ≠0`, uniformemente em `t`,

   \[
   \left\|\frac{W_k(\delta,t)-W_k(0,t)}{\delta}\right\|
    \le 2(k+1)^{-3/2}.
   \]

   O majorante é somável; o cancelamento das duas pernas ocorre na desigualdade original de segunda diferença, não por apagar cruzamentos. `infiniteTransverseTilt_summable` prova separadamente a convergência da série `W∞(δ,t)` no mesmo intervalo de `δ`.
2. Pelo teorema de convergência dominada para séries, `hasDerivAt_infiniteTransverseTilt` prova, para toda altura real `t`,

   \[
   \partial_\delta W_\infty(0,t)
    =G(t)=\sum_{k\ge0}C_k^{-1/2}L(C_k)e^{-it\log C_k},
   \quad L(C)=2\log C-\log(C-1)-\log(C+1)>0.
   \]

   A ordem dessa derivada é **transversal primeiro**. O resultado da #146 anterior já prova que as derivadas em altura de `G` passam pela soma.
3. `infinite_tilt_mixed_prime_identity` e `infinite_tilt_mixed_positive` combinam as duas passagens e provam, para cada ordem `n`,

   \[
   \operatorname{Re}\left[(-1)^n\partial_t^{2n}
      (\partial_\delta W_\infty(0,t))\big|_{t=0}\right]
    =\sum_{k\ge0}C_k^{-1/2}L(C_k)\,
      \bigl(\operatorname{primeDepthLogLedger}(3(k+1))\bigr)^{2n}>0.
   \]

   `finite_jets_tendsto_infinite_mixed` identifica o limite dos jets dos prefixos finitos com esse jet do tilt infinito. A soma prima usa o adaptador já formalizado no pin do operador, que reconstrói `log Cₖ`; ela não importa diretamente a PR #47 de `primos`.
4. `infiniteCarrierRemainder_summable` e `infinite_c3_tilt_carrier_ledger` provam, no mesmo intervalo transversal, que o complemento original (curvatura do carrier e os dois cruzamentos) também é somável e que a carta é **exatamente**

   \[
   \mathrm{Chart}_3(1/2+\delta+it)=1+W_\infty(\delta,t)+R_\infty(\delta,t).
   \]

   `completed_parameter_decomposition` conserva o multiplicador original Xi/chart:

   \[
   F(t-i\delta)=V(t-i\delta)\,[1+W_\infty(\delta,t)+R_\infty(\delta,t)].
   \]

   Essa é uma identidade do readout da síntese original, não uma identidade de estados físicos ou uma Gram positiva.
5. `infiniteCarrierRemainder_hasDerivAt` e `infinite_material_transverse_ledger` provam que o complemento é diferenciável em `δ=0` e que a primeira derivada da carta completa é a soma exata da derivada do tilt com a derivada do complemento. Nenhum sinal é atribuído ao segundo termo. A diferenciabilidade vem da carta original e da identidade da soma; não foi postulada uma série de derivadas independentes para ele.

## Alcance e obstrução remanescente

A lei de sinal em toda ordem é **do canal de tilt**, não do kernel de momentos. Ainda é necessário controlar as derivadas mistas de `R∞`, os fatores de completion e o termo de Schur com seus cruzamentos. Não se demonstrou uma desigualdade que faça a contribuição positiva do tilt dominar esses termos nem que ligue essa contribuição, por si só, à positividade dos pivôs. O parâmetro `n` é arbitrário, porém a prova não oferece uma margem uniforme em `n`.

A revisão dos módulos `OfflineObstruction.lean` e `CriticalConcavity.lean` mostrou que alguns comentários chamavam uma perturbação algébrica de um único coeficiente de "fora da linha" e de "concavidade do pivô na linha". Os **enunciados Lean não identificam essa perturbação com a família física em `σ`**. Os comentários foram corrigidos; os enunciados e as provas permanecem inalterados. Não se demonstra aqui sinal ou perda de positividade física fora da linha.

## Proveniência e reprodução

`TiltPhase.lean`, `TiltQuant.lean` e `TiltBounds.lean` são cópias dos três módulos de `primos` `CpGenuineTiltPhaseCancellation`, `CpGenuineTiltQuantitativeDomination` e `CpGenuineTiltBlockBounds`, provenientes do commit de última alteração `d6b1fffa73d4289360ba2b98c2976f94cae88a84`. Somente as duas linhas de import necessárias para usar nomes locais foram alteradas. `evidence/tilt-vendor-check.log` verifica a igualdade após essa substituição; os hashes originais e das cópias constam no mesmo diretório. Os repositórios e pins originais não foram modificados.

No host `llm`, com os caches dos ancestrais da #146 disponíveis:

```bash
bash research/c3-tilt-prime/validate.sh
bash research/c3-tilt-prime/validate_infinite.sh
bash research/c3-tilt-prime/validate_transverse_swap.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

Os módulos novos são compilados individualmente com avisos como erros; `#print axioms` e a auditoria transitiva registram as dependências. Apenas `propext`, `Classical.choice` e `Quot.sound` são permitidos. A auditoria bloqueia explicitamente as caixas theta e os certificados de sinal nomeados; isso não substitui uma auditoria semântica de todas as equivalências possíveis. São reutilizados `.olean` das dependências anteriores, e não se reivindica uma reconstrução limpa dos repositórios externos.

Próxima obrigação: controlar a contribuição **mista completa do complemento e da completion**, com dependência de ordem e setor, e comparar o resultado com a correção de Schur da mesma direção crítica. A positividade do canal isolado não autoriza descartar ou minorar os demais termos sem prova.
