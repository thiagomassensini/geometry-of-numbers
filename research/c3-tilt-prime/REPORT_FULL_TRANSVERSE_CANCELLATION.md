# Cancelamento transversal e readout TFVD da síntese C3

**Resultado: PARTIAL.** O Lean demonstra, para cada ordem par em altura, o cancelamento do primeiro jet transversal da característica completada. Esse jet é identificado com a soma exata do canal de tilt, do complemento carrier/cruzamentos e da derivada do multiplicador de completamento. No centro, o compensador é não nulo. Perto do centro, o mesmo jet é ligado ao readout Wronskiano/TFVD preexistente. Nada disso prova positividade all-order dos momentos ou dos pivôs.

## A — Atualizações examinadas

Base desta investigação: `22fafd835382e0ccb8220a1b9ec11b240901ed0d`, branch `agent/c3-critical-tilt-prime`, PR #146 empilhada na #145. Depois de `b197e7f`, foram examinados oito commits: `df1cd21`, `3e3121a`, `5b22d93`, `6bdc0eb`, `12d96c2`, `ac11f0e`, `63193ab`, `22fafd8`.

- `CriticalCurvature` demonstra curvatura negativa da célula de tilt para `c > exp 1 + 1`. Não demonstra a curvatura da fonte completada.
- `NativeLogOperatorBridge` identifica frequências com o gerador logarítmico nativo. `LpNormBridge` constrói o vetor espectral em ℓ² e prova a identidade literal da norma; não formaliza a iteração da aplicação parcial não limitada do operador.
- `AccumulationMechanism` prova crescimento dos jets do tilt e apresenta um modelo harmônico separado. O modelo não é identidade da fonte completada.
- `SourceDecomposition` prova uma identidade exata para uma alteração algébrica de um coeficiente, `Q=P−D`; seus resultados de sinal recebem as hipóteses indicadas. Nenhum teorema identifica esse deslocamento com a deformação física completa em σ.
- `TiltCurvatureBridge` e `TiltLogDerivative` tratam o 2-jato e a log-derivada da sensibilidade **da célula de tilt**. A semelhança de forma com a resposta da característica não é uma identificação entre ambas.

O `origin/main` consultado estava em `e44da94f8c32ef2ac1a5a382cc19a81dfbbc980c`. `IntegerMomentGramPositivity.lean` apresenta uma família geométrica positiva de momentos inteiros finitos, com frequências de clock e pesos verticais. Essa definição própria de momentos não foi identificada com a sequência canônica da derivada logarítmica; a positividade daquela família não descarrega o gate canônico. O `main` não foi mesclado à branch desta investigação, nem arquivos ou pins foram alterados.

## B — Identidades demonstradas agora

Escreva `F(z)=completedNativeOperatorCharacteristic z`, `V=CarryTwoEvenJets.valueMultiplier`, `W∞=infiniteTransverseTilt`, `R∞=infiniteCarrierRemainder` e `G(t)=infiniteMixedTiltResponse(t)`.

1. `fullTransverseResponse_eq` usa analiticidade da **característica completada** para demonstrar, para todo `t` real,

   \[
   T(t):=\left.\partial_\delta F(t-i\delta)\right|_{\delta=0}=-i\,\partial_tF(t).
   \]

   `fullTransverseResponse_even_jet_zero` combina isso com a paridade completada já provada e conclui

   \[
   \partial_t^{2n}T(0)=0\qquad(n\in\mathbb N).
   \]

   Este é o jet **transversal primeiro, depois altura**; não se usa uma troca não demonstrada entre as duas ordens de derivação.
2. `fullTransverseResponse_eq_channels` diferencia a identidade exata `F(t-iδ)=V(t-iδ)[1+W∞(t,δ)+R∞(t,δ)]` no intervalo já certificado. Perto do centro, define-se o compensador da decomposição complexa por

   \[
   C(t)=(-iV'(t))[1+R_\infty(t,0)]+V(t)\,\partial_\delta R_\infty(t,0).
   \]

   Então `T(t)=V(t)G(t)+C(t)`. A expressão mantém o carrier, ambos os cruzamentos, a cauda e o fator de completamento, no readout após a síntese. Ela não afirma que cada contribuição separada tenha um sinal.
3. `full_channels_even_jet_cancel` prova, para todo `n`,

   \[
   \partial_t^{2n}[V(t)G(t)+C(t)]_{t=0}=0.
   \]

   O resultado é sobre a derivada da **soma**; não se afirma que o sinal do jet de `V G` seja o mesmo do jet de `G`, nem se omitem os termos da regra de Leibniz.
4. `center_exact_cancellation` prova `C(0)=−V(0)G(0)`. `center_multiplier_ne_zero` e `center_tiltResponse_ne_zero` são obtidos, respectivamente, da não anulação da característica no centro e do sinal já demonstrado da sensibilidade do tilt. `center_completionRemainder_ne_zero` conclui `C(0)≠0`. Logo, nesse readout, não é legítimo apagar o compensador.
5. `fullTransverse_eq_normalizedGreen` prova, onde `F(t)≠0`,

   \[
   T(t)=2iF(t)Q(t),\qquad Q(t)=-F'(t)/(2F(t)).
   \]

   `fullTransverse_eq_tfvdWronskian_near` reutiliza `canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed` e prova, num entorno do centro, a mesma identidade com `canonicalC3BracketTfvdNormalizedResponse M` para qualquer cutoff `M`. A não anulação local é provada pelo desenvolvimento original da característica. O readout Wronskiano é escalar após a síntese; não se anuncia igualdade unitária de estados ou positividade da forma polarizada.

## C — Interpretação e limites

O cancelamento provém da paridade e da analiticidade de `F`, não de uma lei que obrigue os pivôs a serem positivos. O sinal positivo dos jets de `G` pertence ao canal de tilt. A derivada da fonte completada inclui o multiplicador e o compensador, e seu cancelamento não permite decidir o sinal de uma diferença de Schur. Também não demonstra que o carrier isolado tenha sinal negativo: apenas a combinação especificada em `C` foi identificada.

A razão abstrata `D/P`, o 2-jato por célula, o clock logarítmico e a Gram de momentos inteiros continuam sendo instrumentos válidos com seus próprios tipos; nenhum deles foi identificado aqui com a direção crítica canônica completa. Não foi demonstrada impossibilidade geral de uma lei geométrica de sinal.

## D — Auditoria e reprodução

Os módulos novos são `FullTransverseCancellation.lean` e `FullTfvdTransverse.lean`; `FullTransverseCancellationAudit.lean` audita as raízes novas junto das raízes de proveniência já exigidas. Os `#print axioms` registram apenas `propext`, `Classical.choice` e `Quot.sound`. A auditoria transitiva verifica as constantes proibidas nomeadas e a presença das raízes exigidas; não é uma auditoria semântica de todas as equivalências possíveis.

No host `llm`, com os caches das dependências anteriores disponíveis:

```bash
bash research/c3-tilt-prime/validate_full_transverse.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

`evidence/full-transverse-cancellation.log` registra a compilação e a auditoria; as saídas compactadas do build e das auditorias de base constam em `evidence/`. O build da raiz é o da branch em questão, não do `origin/main` posterior; não se reivindica rebuild limpo dos repositórios externos.

## E — Próxima obrigação mínima

Transportar a identidade genuína do Wronskiano normalizado para a **forma polarizada completa que entra na direção crítica** e calcular seu primeiro termo transversal não trivial, incluindo variação do denominador, complemento, completion e correção de Schur. Testar primeiro ordens baixas nos dois setores, sem usar o sinal do pivô como hipótese. O cancelamento acima mostra que um argumento apoiado somente no primeiro jet transversal par do tilt ignora uma compensação não nula da síntese completada.
