# Orçamento radial efetivo da fonte original e teste crítico de seis endereços

**PASS para o teste finito solicitado; PARTIAL para positividade canônica all-order.** O orçamento dos incrementos e o saldo na mesma escala foram certificados, com corte explícito. O teste recertifica um residual ímpar já conhecido por outra rota; não é um novo pivô nem uma prova de positividade em toda ordem.

Base: PR #129, commit `7d50d6f43660769728b5cdfb04a0f9c78ec03402`, branch `agent/native-boundary-euler-reconstruction`, conferida aberta, draft e sem merge. Nova branch: `agent/native-effective-radial-budget`. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Execução no host `llm`.

## A — O que já estava demonstrado

- A #41 separou ortogonalização algébrica e sinal. Resolver o bloco antigo e selecionar uma direção crítica não prova o sinal do residual novo.
- A #128 identifica a fonte completa de seis endereços, a família dos jets 1,3,5, os 36 cruzamentos e a expansão com seu resto analítico integral. A seleção crítica u*,v* é posterior à construção da família física.
- A #129 reconstrói o bordo em duas entradas independentes por somas parciais radiais. Para seis endereços, já havia monotonicidade e somabilidade absoluta eventualmente, mas sem um índice efetivo.
- `canonicalCompletedNativeLogDerivativeMoment_sharp_decay`, do módulo `CompletedNativeLogCoefficientMajorant.lean`, já demonstra a cota absoluta em toda ordem, sem positividade Hankel:

$$|h_n|\le a^{n+1}-(1/25)^{n+1}\le a^{n+1},\qquad a=22/175.$$

Essa cota não é descoberta desta PR. A novidade é transportá-la para a **função nativa efetiva**, seu resto normalizado e sua derivada num domínio explícito, e depois aplicá-la ao balanço completo, com o mesmo dado de escala finita.

O parâmetro hₖ=1/(k+1) é a regularização radial original. O índice k não é profundidade vertical Carry, ordem de jet ou endereço material. Nenhuma amplitude, câmera, métrica, fase ou normalização foi alterada.

## B — O que foi demonstrado agora

### B.1 — Raio explícito e identidade da própria resposta

[SourceSeries.lean](SourceSeries.lean) define somente a série escalar dos coeficientes já determinados pela fonte. `source_series_radius` prova raio de convergência pelo menos 4 na variável reduzida u. Não são construídos estados físicos a partir desses coeficientes.

Se F é a característica completada original e Q=−F′/F, a relação correta de coordenadas é

$$Q(z)=2z\sum_{n\ge0}h_n(z^2)^n.$$

[SourceDisc.lean](SourceDisc.lean), `source_response_product_on_disc`, prolonga a identidade **produto** A(z)F(z)+F′(z)=0 por analiticidade no disco ||z||<1/4. Não recebe ausência de zeros em um disco como hipótese. `native_response_hasSum_on_disc` identifica a soma com Q em cada ponto regular do disco.

`imaginary_characteristic_ne_zero` descarrega a não anulação nos pontos z=iy, |y|<1/4, usando a não anulação já provada da fonte Genuine no eixo real 0<σ<1. Não há zeros ou alturas como entradas.

[ExplicitSourceTail.lean](ExplicitSourceTail.lean), `native_response_prefix_error`, fornece, para todo M, r=||z||<1/4 e F(z)≠0:

$$\boxed{\left\|Q(z)-2z\sum_{n<M}h_n(z^2)^n\right\|
\le 2r\,\frac{a(ar^2)^M}{1-ar^2}.}$$

Todas as ordens omitidas estão na cota. Igualdade de coeficientes e convergência da série são ligadas à função original; não se presume essa identificação a partir de uma semelhança numérica.

### B.2 — Resto normalizado e derivada, em toda ordem

[NormalizedRemainder.lean](NormalizedRemainder.lean) identifica exatamente

$$Q(z)=2z\sum_{n<M}h_n(z^2)^n+z^{2M+1}\mathcal R_M(z),\qquad
\mathcal R_M(z)=2\sum_{n\ge0}h_{n+M}z^{2n}.$$

`native_response_exact_remainder` prova essa igualdade para a resposta nativa nos pontos regulares do disco explícito. `source_remainder_analytic`, `source_remainder_norm_le_one` e `source_remainder_deriv_bound` provam, para **todo M**:

$$\|\mathcal R_M(z)\|\le1\quad(\|z\|<1),\qquad
\|\mathcal R'_M(z)\|\le4\quad(\|z\|\le1/4).$$

A estimativa da derivada usa Cauchy no mesmo resto analítico. O domínio maior da série normalizada não é anunciado como uma igualdade física global de Q fora do disco onde a ponte foi demonstrada.

### B.3 — Regularidade física com corte explícito

[RadialRegularity.lean](RadialRegularity.lean) usa a estimativa M=0 para obter ||Q(z)||≤1/4. Assim Q(z)+i≠0, e o denominador quiral positivo original também não se anula nos pontos radiais em questão.

`six_radial_regular` e `six_physical_at_explicit_step` provam a igualdade com a diferença das duas normas físicas originais em **cada ponto da grade com 0<hₖ<1/24**, em vez de receber apenas um conjunto eventual desconhecido. A amplitude projetiva permanece com uma única ocorrência por estado, com os fatores radiais nativos.

### B.4 — Expansão completa e orçamento de norma

[SixEffectiveRemainder.lean](SixEffectiveRemainder.lean), `six_expansion_on_disc`, transforma o resto original de Q numa igualdade exata do readout completo:

$$D(h)=L+Ch^2+h^4E(h),\qquad L=\operatorname{sixLimit}(u_*,v_*)=2p_3.$$

E conserva a contribuição de todos os coeficientes superiores e as seis avaliações nativas. Os 36 cruzamentos foram sintetizados antes da redução às avaliações. O polinômio finito e a soma dos restos são mantidos separadamente apenas depois dessa igualdade completa.

[FiniteNormBudget.lean](FiniteNormBudget.lean) verifica as tabelas de monômios como identidades dos coeficientes originais. Não se escolhe uma nova fonte nem uma métrica. Para |u|,|v|≤1, obtêm-se cotas conservadoras:

$$\|E(z)\|\le10^{20}\quad(\|z\|\le1/12),\qquad
\|E'(z)\|\le10^{22}\quad(\|z\|\le1/1000).$$

As cotas são deliberadamente largas. Elas não alteram os objetos físicos. A passagem à derivada mantém o resto inteiro.

### B.5 — Escala, saldo e todos os incrementos posteriores

[CriticalBudgetData.lean](CriticalBudgetData.lean) reaproveita as inclusões integrais primitivas existentes para certificar |u*|,|v*|≤1 e |C|≤1/1000. Não usa C>0 nem o sinal do pivô para provar o orçamento.

Escolhemos um ponto da grade existente:

$$H=10^{-20},\qquad K=10^{20}-1,\qquad h_K=H.$$

Esse corte não é reivindicado como mínimo. Não há iteração de 10²⁰ passos: o enunciado é provado para todos os índices posteriores por desigualdades simbólicas. Não foram calculados novos momentos.

[EffectiveSixBudget.lean](EffectiveSixBudget.lean), `critical_curve_derivative_budget`, prova |D′(h)|≤2h para 0<h≤H na extensão analítica cujo pareamento na grade é o original. [SquaredStepBudget.lean](SquaredStepBudget.lean) integra essa cota com a escala correta h². `six_effective_increment_budget` conclui:

$$\boxed{|D_k-D_{k+1}|\le h_k^2-h_{k+1}^2\quad\text{para todo }k\ge K.}$$

O dado da mesma escala é certificado sem receber o residual positivo como hipótese. `anchor_head_membership` verifica a expressão finita nas caixas dos momentos originais, e `six_effective_anchor_positive` inclui o erro h⁴E completo:

$$\boxed{D_K>10^{-16}.}$$

`six_effective_absolute_tail` prova o `HasSum` da cauda e sua somabilidade absoluta **a partir desse mesmo índice explícito**, sem recorrer ao corte desconhecido de monotonicidade da #129:

$$\boxed{\sum_{j\ge0}|D_{K+j}-D_{K+j+1}|\le H^2=10^{-40}.}$$

Portanto o saldo certificado supera o orçamento inteiro da cauda. `six_boundary_positive_from_effective_budget` obtém L>0, e `third_odd_residual_pos_via_effective_budget` transporta essa conclusão ao residual crítico ímpar já identificado:

$$h_5+u_*h_4+v_*h_3>0.$$

Isso é **recertificação de um caso finito conhecido por uma rota efetiva de escala finita e cauda**. A desigualdade do saldo foi computada a partir das mesmas inclusões da fonte, não deduzida de uma positividade Hankel recebida como hipótese.

## C — O que foi refutado ou delimitado

Não surgiu um NO-GO novo. O teste solicitado passou. Continuam válidas as obstruções anteriores a uma margem relativa fixa e ao gerador de Loewner investigado na #126. A prova atual controla a magnitude do erro acumulado e não pressupõe que cada gerador físico tenha sinal favorável.

A cota absoluta de coeficientes, isoladamente, ainda não determina sinais de Hankel. Aqui ela controla a cauda; o saldo de escala finita exige uma avaliação adicional da própria fonte. Não se apresenta essa avaliação finita como uma lei geométrica universal.

Os controles Python com 12 identidades exatas do stencil usam coeficientes racionais livres apenas para verificar a álgebra completa de incidência, retorno, 36 cruzamentos e resto. Não são sequências substitutas da fonte canônica. Cinco comparações racionais verificam as constantes conservadoras. Quatro diagnósticos usam os 64 momentos canônicos existentes, com 450 dígitos aritméticos, pois os dois canais individuais são grandes; isso não acrescenta precisão aos dados de entrada. Os diagnósticos não são premissas Lean.

## D — O que permanece aberto

Os controles da função Q e de seu resto normalizado valem em toda ordem de truncagem M, sem hipótese de positividade canônica. O orçamento e o saldo estrito montados nesta PR são somente da família crítica de seis endereços.

Não foi demonstrada uma família de saldos positivos em toda ordem, nem uniformidade na dimensão, uma Gram canônica infinita, um operador limite ou novas alturas. Não se afirma convergência individual das pernas. Os termos de retorno, os cruzamentos, o completion e o resto da fonte não foram descartados.

O sinal do saldo finito usa as caixas integrais previamente certificadas da sequência original. Não se descobriu uma causa geométrica de positividade all-order independente dessas avaliações. A investigação fecha o orçamento concreto; a obrigação universal de sinal continua aberta.

## E — Próximo passo mínimo e reprodução

O alvo da #129 foi encerrado no teste crítico identificado: há um B=1, um K explícito, um saldo e uma cota da cauda no mesmo ponto, todos ligados à fonte original.

O próximo avanço estrutural mais curto é generalizar o orçamento para uma família finita arbitrária de jets, com constantes calculáveis a partir de seus coeficientes e endereços originais. As cotas de R_M e R′_M já são uniformes em M; os fatores que crescem com a dimensão ainda precisam ser transportados. Fazer isso não autoriza presumir o sinal dos saldos de escala finita em todas as direções. Uma lei all-order precisa fornecer essa dominação por uma propriedade independente da fonte, não simplesmente renomeá-la como hipótese.

Reprodução no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

O cache opcional da #129 contém 190 objetos ancestrais verificados. SHA256 do arquivo de entrada: `37dcb9aa1ff3c1859aff7835b3d79cb452d0d779118c8b74e85e943be3b2ad98`; colocá-lo em `.cache/input-cache.tar.gz`. Sem cache, `python3 validate.py` recompila os ancestrais exatos. Os dez módulos novos e a auditoria são compilados nesta execução.

Checkpoint diagnóstico: `momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv`, coluna `canonical_h`, SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`. Não foram usados `raw_moments`, zeros, alturas ou uma campanha nova de momentos.

### Validação concluída

**23 etapas do roteiro passaram**, todas com exit 0, incluindo compilações com warnings como erros, alvos nativos selecionados, `lake build --wfail` e auditorias Foundation/Geometry/Analysis. Uma auditoria final reforçada acrescentou **duas verificações focadas**, também com exit 0, depois de ampliar os guards contra dependências antigas. São **57 teoremas e 18 definições públicas**, em dez módulos matemáticos novos. Os 190 objetos ancestrais foram verificados e reutilizados; não foram anunciados como recompilados.

As 75 raízes públicas têm `#print axioms` e auditoria transitiva de tipos e corpos opacos. Grupo algébrico: 17 raízes e 19444 dependências; fonte: 47 e 57727; certificação: 11 e 58935. Os guards proíbem os consumidores enumerados de positividade canônica finita e, adicionalmente, o antigo sinal de C₆, suas orientações eventuais e os teoremas da #129 com corte desconhecido de monotonicidade/cauda. A auditoria exige as pontes efetivas da função, do resto, da derivada e da fonte física original; na certificação, exige também o orçamento, o saldo e as inclusões integrais primitivas. Só são permitidos `propext`, `Classical.choice`, `Quot.sound`.

Os 12 controles exatos dos stencils, as cinco comparações racionais e os quatro diagnósticos canônicos passaram. Não há `sorry`, `admit`, `native_decide` ou novos axiomas. Fontes, métrica, amplitudes, completion, dressing, pins e trabalho anterior foram preservados. Evidências: `evidence/validation.json`, `evidence/strengthened-audit.json`, `evidence/kernel-audit-summary.json`, `evidence/upstream.json` e `evidence/preservation.json`. `SHA256SUMS` registra os arquivos. Validação observada no host `llm`, sem alegação de CI externo.

Entrega em PR draft empilhada sobre a #129, sem merge automático. Fontes e cache são arquivados e verificados localmente antes da remoção apenas do worktree próprio. A branch publicada e todos os trabalhos anteriores são preservados.

Fim do relatório — orçamento, saldo e cauda certificados na mesma escala da fonte original; generalização do orçamento e positividade canônica all-order permanecem abertas.
