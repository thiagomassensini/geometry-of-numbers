# C2 finite contour at radius 51 — checkpoints

- [x] **C0 — isolate and audit the investigation.** Branch `agent/c2-contour51-20261108` starts at B2 PR #311 HEAD `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`. Commit `96314ff` is pushed. PR #306's original branch remains untouched; its `RESEARCH.md` and `reproduce.py` are copied byte-for-byte. The numerical probe was rerun and its output is explicitly non-certified. Lean 4.32 and an exclusive output root are recorded in `VALIDATION.md`.
- [x] **C1 — exact roots in the closed disk `‖z‖ ≤ 51`.** `SigmaContour51DiskBridge.lean` compiles on Lean 4.32.0 with warnings treated as errors. The height-52 multiplicity count exhausts the ten B2 positive witnesses, RH proves simplicity and reality, and evenness reflects the roots to the negative side. The result classifies every original-continuation zero in the disk, proves the boundary is zero-free, and proves all such roots have order one. Both theorem axiom reports are `[propext, Classical.choice, Quot.sound]`; the successful build log and hashes are in `VALIDATION.md` and `evidence/C1_SigmaContour51DiskBridge-build.log`. Commit `4b10477` is pushed to the stacked draft PR #314.
- [x] **C2 — finite residue identity for every order.** `SigmaContour51FiniteContour.lean` proves finite analytic gluing across all twenty simple roots, the boundary correction, the Cauchy reduction, and the coefficient formula. `exists_completedNative_contour51_corrected_log_derivative` selects one C1 root list with its ten rational B2 height intervals and proves the correction for every kernel order. `completedNative_contour51_jet_residue_identity` uses this same list for all `n` and the Carry source bridge to prove `normalized ∮ R(z)/z^(2*n+2) = completedSigmaLogJet 0 n - ∑ i : Fin 10, (ts i)^(-2*n-2)`. The signed roots are paired algebraically; no Hadamard factorization or zero-defined moments are used. Lean 4.32.0 with warnings as errors succeeds, and all reported axioms are `[propext, Classical.choice, Quot.sound]`. The successful build evidence and hashes are in `VALIDATION.md`.
- [x] **C3 — uniform radius-51 logarithmic-derivative bound.** `certify_contour51_bound.py` proves `|R|<4/5` on 512 interval arcs covering the lower half-circle; evenness gives the upper half. Arb/Acb Taylor and Cauchy remainders are recorded in `C3_ARb_CERTIFICATE.md` and `evidence/C3_ARb_ARCS.csv`. This is rigorous external evidence, not yet a Lean theorem. The companion 4096-arc certificate also checks the bound while enclosing the first six residual integrals.
- [x] **C4 — conditional all-order residual tail.** `SigmaContour51RationalGate.lean` compiles on Lean 4.32.0 with warnings-as-errors. It proves the normalized integral bound and exact radius conversion, then yields `|e_n| ≤ 40*(1/2500)^(n+1)` assuming the C2 contour identity and the circle estimate `‖R‖ ≤ 4/5`. C2 is now proved in Lean; the C3 circle estimate remains an external Arb certificate rather than a Lean theorem.
- [ ] **C5 — Lean closure of six source residual signs.** The external 4096-arc Arb certificate rigorously encloses `e_0,…,e_5` from the original response integral and reports strict rational lower margins. The intervals do not use approximate zero sums. The Lean interval-transfer proof remains open, so the six signs are not yet Lean theorems.
- [x] **C6 — exact finite gates and conditional closure.** The same module proves all four shallow-window margins and combines them with B1 for `s ≥ 4`. It proves positivity of the original `sigmaPadeD` conditionally on the source decomposition, scale boxes, global tail, and the six signs `e_0,…,e_5 ≥ 0`. The hypotheses are explicit and not yet discharged; this is not unconditional positivity.
- [x] **C2→C4→C6 source composition.** `SigmaContour51SourceTail.lean` fixes the same C1 root list for every order, derives its reciprocal-square scale boxes and the original-jet decomposition, applies C4 to the C2 contour identity, and feeds the resulting `C=40` tail into C6. `completedNative_sigmaPadeD_pos_of_contour51_bound` is an original-source conditional theorem: assuming the radius-51 bound `‖R‖≤4/5`, the six central residual signs imply `∀ s, 0 < sigmaPadeD 0 s`. `completedNative_sigmaPadeD_zero_pos_of_contour51_bound` proves the `s=0` gate assuming only `e_0≥0` and `e_2≥0`; the C4 absolute bound controls the middle moment without assuming `e_1≥0`. Each declaration reports only standard axioms. Thus `hdecomp` and `hbox` are discharged; the analytic circle bound and the Lean transfer of the residual intervals remain open.
- [x] **Arb residual interface and first-window gate.** `SigmaContour51ArbResidualGate.lean` records exact rational endpoints from the 4096-arc JSON and proves the lower/upper coarse margins in Lean. `contour51ArbResidualIntervalBounds` states the six-interval transfer; `contour51ArbFirstThreeResidualIntervalBounds` states the minimal three-interval transfer. Under the latter, `completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals` proves `1/1000000000 < sigmaPadeD 0 0`, with no `hR` premise. Its exact gate lower bound retains the product and square cross terms. The all-window wrapper needs `hR` and all six interval inclusions.

## Adendo 2026-11-08 — caminho inferior Arb formalizado em Lean

- [x] **Paridade e parametrização exata.** `SigmaContour51ArbContourBridge.lean` prova a partir de `completedNativeCharacteristicContinuation_even` que a resposta original `R(z)=-F'(z)/(2F(z))` é ímpar e que `Q_n(z)=R(z)/z^(2n+1)` é par. C1 fornece ausência de zeros em `|z|=51`; logo o integrando angular é contínuo e integrável. Para cada `n`, o teorema compilado `contour51OriginalResidualIntegral_eq_lower_path` identifica exatamente

  ```text
  (2πi)⁻¹ ∮ R(z)/z^(2n+2) dz
    = ∫₀¹ Q_n(51 exp(-π i u)) du.
  ```

  A conversão inclui o fator `i` da derivada do `circleMap`, a orientação positiva completa, a periodicidade π por paridade de `Q_n` e a mudança de variável `θ=-πu`. Portanto a parametrização e a redução meia-volta do script Arb agora estão fechadas em Lean, sem premissa analítica adicional.
- [x] **Integração em partição uniforme.** `contour51_intervalIntegral_bounds_of_uniform_partition` prova em Lean que, se os valores reais do integrando estão entre `lower k` e `upper k` em cada arco `[k/N,(k+1)/N]`, então a integral está entre `(1/N)∑ lower k` e `(1/N)∑ upper k`. A prova usa monotonicidade do integral em cada arco e aditividade em intervalos adjacentes. Isso fecha a etapa exata de integração, condicional às inclusões ponto a ponto e às comparações racionais das somas; não importa caixas Arb como premissas.
- [x] **Transferência da forma da hipótese.** `contour51ArbLowerPathResidualIntervalBounds` enuncia as inclusões diretamente nos seis integrais parametrizados usados pelo Arb. `contour51ArbResidualIntervalBounds_of_lower_path_bounds` transforma essa proposição exatamente na entrada dos gates anteriores; o teorema `completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals` compõe o primeiro gate e preserva a margem absoluta `1/1000000000`.
- [ ] **Ainda aberto: inclusões do avaliador Arb nos integrais Lean.** O módulo prova em Lean a expansão exata de `xiLean'/xiLean` e, pelo teorema `contour51OriginalResponse_eq_arb_formula_lower_path`, identifica a resposta da fonte com a fórmula de zeta/Gamma/digamma em todo o caminho inferior `u∈[0,1]`; C1 fornece `F≠0`, e as condições geométricas são demonstradas. A não anulação de zeta é derivada da fatorização completada. Ainda falta provar que as faixas Acb por arco contêm os valores dessa fórmula Lean, incluindo os restos Taylor/Cauchy, e certificar as comparações racionais das somas ponderadas. O lema genérico de integração em partição uniforme já compõe essas etapas quando forem demonstradas; as inclusões externas ainda não são teoremas Lean.
- [ ] **Ainda aberto: cota uniforme C3 em Lean.** O certificado externo de 512 arcos continua provando numericamente com aritmética Arb `|R|<0.746413<4/5`, mas a inclusão das faixas na função de Lean e o teorema uniforme não foram formalizados. A identidade de caminho não descarrega essa obrigação.
- **Margens racionais de `e_0,…,e_5`.** Lean verifica que os endpoints externos permitem as margens estritas abaixo; elas só viram afirmações sobre os resíduos após a inclusão aberta acima.

  | `n` | margem inferior estrita disponível para `e_n` | limite superior simples disponível |
  |---:|---:|---:|
  | 0 | `9/1000` | `1/100` |
  | 1 | `9/10000000` | `1/1000000` |
  | 2 | `9/50000000000` | `1/4000000000` |
  | 3 | `1/25000000000000` | `1/10000000000000` |
  | 4 | `1/100000000000000000` | `1/50000000000000000` |
  | 5 | `1/500000000000000000000` | `1/100000000000000000000` |

- **Primeiro avanço incondicional ainda necessário.** O lema mínimo é provar `contour51ArbFirstThreeLowerPathResidualIntervalBounds`, isto é, as duas inclusões para os integrais do caminho inferior em `n=0,1,2`. Somado aos teoremas já compilados, isso fecha `sigmaPadeD 0 0 > 1/1000000000` para a fonte original, sem usar `hR`. Para todos os deslocamentos centrais, ainda são necessárias as seis inclusões e a cota uniforme C3 em Lean.
- **Termos cruzados e resíduos.** Em toda passagem para determinantes, conservar a identidade completa

  ```text
  D_s(H)-D_s(P) = P_s*e_(s+2) + e_s*P_(s+2) - 2*P_(s+1)*e_(s+1)
                 + e_s*e_(s+2) - e_(s+1)^2.
  ```

  Os limites da porta `s=0` usam intervalos absolutos para `H_0,H_1,H_2` e dão a margem racional estrita `1/1000000000`; não usam porcentagens de cancelamento nem uma hipótese de sinal para o resto. A cauda material finita de C2, o resíduo central dos dez modos `e_n`, e o resto/cota de integração no contorno são objetos diferentes; as relações provadas são `e_n=H_n-P_n` pelo C2 e `e_n` igual ao integral normalizado pelo teorema de resíduos. A cota C4 só se relaciona a esse último integral após fornecer a hipótese de círculo `hR`.
- **Coordenação C5.** Podem ser compartilhados o avaliador intervalar genérico, aritmética racional de caixas, normalização da fonte e o transporte algébrico já provado. Não se duplicou a tabela de Bernoulli nem a certificação de todos os nós zeta/Gamma. Caixas certificadas em `d=0.0495` ou `d=0.1` não se tornam caixas no centro sem a transformação quantitativa explícita para `d=0`; a ponte de centro algébrica atual não transporta intervalos deslocados.
- **Auditoria Lean.** O módulo compila em Lean 4.32.0 com `-DwarningAsError=true`; os `#print axioms` dos teoremas novos mostram apenas `[propext, Classical.choice, Quot.sound]`. Não há `sorry`, `admit` ou axioma matemático novo. O estado C3→C5 continua condicional e nenhuma positividade central incondicional é afirmada.

## Subcheckpoint 2026-11-08 — resposta original e derivada logarítmica de xi

- [x] **Identidade diferencial da fonte completada.** `contour51OriginalResponse_eq_sigmaXiLogDerivative` prova, para `F(z) ≠ 0`,

  ```text
  R(z) = -(i/2) * (xiLean'(s) / xiLean(s)),
  s = operatorHeightParameter z,
  xiLean = sigmaCompletedXiParameter.
  ```

  A prova diferencia a identidade exata `F(z)=sigmaCompletedXiParameter(s)` pela regra da cadeia e usa `ds/dz=i`. Não troca a fonte por um produto de zeros. Compila em Lean 4.32.0; a auditoria de axiomas dá `[propext, Classical.choice, Quot.sound]`, sem `sorry`, `admit` ou axioma declarado.
- [x] **Expansão para o avaliador clássico.** `contour51SigmaXiLogDerivative_eq_zeta_gamma_factors`, `contour51GammaReal_logDeriv_eq_digamma` e `contour51SigmaXiLogDerivative_eq_arb_formula` provam a decomposição por fatores e a expressão explícita de zeta/Gamma/digamma. `contour51OriginalResponse_eq_arb_formula` liga a fonte original à expressão usada por Arb sob `F(z)≠0`, `0<Re(s)` e `s≠1`; a não anulação de zeta é deduzida, não postulada. Todos compilam em Lean 4.32 com axiomas padrão somente.
- **Limite dessa ponte:** `contour51OriginalResponse_eq_arb_formula_lower_path` já aplica a identidade uniformemente ao caminho inferior e descarrega as condições geométricas usando C1. Falta a inclusão das caixas Acb na expressão Lean, a formalização dos restos Taylor/Cauchy e a verificação das somas racionais ponderadas. A integração dessas cotas ponto a ponto já é formalizada pelo lema de partição uniforme. O certificado Arb continua externo.
- **Hipóteses analíticas ainda abertas:** (i) transferir para Lean as 512 faixas Arb e provar `‖R‖≤4/5` em todo o círculo; (ii) para `e_0,…,e_5`, provar as inclusões do avaliador original em cada arco completo de 4096, validar os restos Taylor/Cauchy e verificar as somas racionais ponderadas. A integração exata das cotas ponto a ponto já é o teorema genérico compilado `contour51_intervalIntegral_bounds_of_uniform_partition`. Para o primeiro determinante bastam as inclusões de `n=0,1,2`. Não foi introduzida hipótese de sinal para resto.
- **Margens racionais externas, ainda condicionais às inclusões:** `e_0 > 9/1000`, `e_1 > 9/10000000`, `e_2 > 9/50000000000`, `e_3 > 1/25000000000000`, `e_4 > 1/100000000000000000`, `e_5 > 1/500000000000000000000`; limites superiores simples: `1/100`, `1/1000000`, `1/4000000000`, `1/10000000000000`, `1/50000000000000000`, `1/100000000000000000000`. Até provar as inclusões, estes números só comparam os extremos racionais externos; ainda não são sinais Lean dos `e_n`.
- **Próximo lema mínimo:** provar `contour51ArbFirstThreeLowerPathResidualIntervalBounds` para `n=0,1,2` a partir das faixas Arb completas: provar as inclusões ponto a ponto, verificar as somas racionais ponderadas, e aplicar `contour51_intervalIntegral_bounds_of_uniform_partition`. Junto da identidade C2, da parametrização já compilada e do gate racional, isso dá `1/1000000000 < sigmaPadeD 0 0` para a fonte original, sem a hipótese global `hR`. Todas as janelas ainda exigem as seis inclusões e a cota uniforme C3 em Lean.
- A passagem aos determinantes continua preservando os cinco termos cruzados:

  ```text
  D_s(H)-D_s(P) = P_s*e_(s+2) + e_s*P_(s+2) - 2*P_(s+1)*e_(s+1)
                 + e_s*e_(s+2) - e_(s+1)^2.
  ```

- **C5:** podem ser compartilhados aritmética racional de intervalos, avaliação em nós, normalização da fonte e transporte algébrico. Caixas em `d=0.0495` e `d=0.1` não são caixas centrais sem transformação quantitativa explícita. Não se repetiu a tabela de Bernoulli nem a avaliação dos nós zeta/Gamma.
- Build atual com a especialização inferior e a integração uniforme: `evidence/C3_SigmaContour51ArbContourBridge-attempt44-success.log`; hashes da fonte, OLean e log estão em `VALIDATION.md`.

Exact remaining Lean inputs:

```text
hR : ∀ z ∈ Metric.sphere 0 51,
  ‖-deriv completedNativeCharacteristicContinuation z /
    (2 * completedNativeCharacteristicContinuation z)‖ ≤ 4/5

hArb : ∀ n ≤ 5,
  L_n ≤ Re ((2πi)⁻¹ ∮ R(z)/z^(2n+2)) ∧
  Re ((2πi)⁻¹ ∮ R(z)/z^(2n+2)) ≤ U_n
```

Here `L_n,U_n` are the exact rational endpoints in the Lean module and JSON. The first-window
theorem takes only `contour51ArbFirstThreeResidualIntervalBounds` for `n≤2`; the all-window theorem
takes `hR` and `contour51ArbResidualIntervalBounds` for `n≤5`. The newer
`contour51ArbLowerPathResidualIntervalBounds` is the equivalent statement in Arb's lower-path
coordinates, and its adapter to these circle-integral hypotheses is now proved. No other analytic
or sign premise is hidden in those conditional theorem statements. The original response is now
proved equal to the explicit zeta/Gamma/digamma evaluator expression throughout the lower path by
`contour51OriginalResponse_eq_arb_formula_lower_path`, which discharges `F(z)≠0`, `0<Re(s)`, and
`s≠1`; zeta nonvanishing follows from source factorization. Transferring the complete arc ranges
including their Taylor/Cauchy remainders and verifying the weighted rational endpoint sums remain
open. Exact integration of pointwise arc bounds is already proved by
`contour51_intervalIntegral_bounds_of_uniform_partition`. The circle orientation, path scaling,
response oddness, quotient evenness, and half-circle reduction are compiled.
- [x] **Exact width interface for C5 residual signs.** `SigmaContour51BoxSensitivity.lean` proves that the current ten-mode power-sum boxes for `n=0,…,5` have widths strictly below `14/10^6`, `9/10^8`, `6/10^10`, `4/10^12`, `3/10^14`, and `2/10^16`. Its `completedNativeContour51Residual_nonneg_of_jet_margin` theorem shows that an original-source jet lower bound clearing `lowMoment n` by the corresponding rational budget implies `e_n≥0` for any height list in the B2 boxes. No such jet lower bound is proved here, so this does not close any residual sign. Exact per-height width diagnostics against the old non-certified probes identify likely refinement candidates; see `evidence/C2_box_sensitivity.log`.
- [x] **C5 center transport, algebraic part only.** The same module proves `displacedProductC 0 z = completedNativeOperatorCharacteristic(z)^2`; with the explicit genuine-strip condition, a second theorem identifies it with `completedNativeCharacteristicContinuation(z)^2`, the original continuation used in the contour argument. It specializes the existing source Bézout recurrence at `d=0`, identifies its source log-derivative coefficient with `2*completedSigmaLogJet 0 n`, and proves `e_n = completedSigmaDisplacedMoment 0 n / 2 - P_n`. The generic source recurrence audit compiles with standard axioms only and retains the original `completedSigmaDensity`, `displacedProductC`, and central jets. C5 interval boxes at `d=99/2000` or `d=1/10` still do not transfer to `d=0` without a separate quantitative displacement bound.

## Residual signs, available margins, and remaining inputs

- The central residuals are `e_n := completedSigmaLogJet 0 n - ∑ i, (ts i)^(-2*n-2)`. C2 now proves, for one fixed `ts` and every `n`, that this residual equals the normalized radius-51 contour integral. It is distinct from the omitted-material tail in the exact C2 finite-head identity and from C5's displaced coefficient/determinant remainders.
- The external Arb interval certificate supplies strict rational lower margins for all six original residuals, as listed in `C3_ARb_CERTIFICATE.md` and stored exactly in `evidence/C3_ARb_RESIDUALS_4096.json`. Lean checks those rational comparisons and proves the exact full-circle to lower-path identity. It does **not** yet prove that the per-arc Arb enclosures contain the Lean lower-path integrals; this interval-transfer proposition remains an explicit hypothesis. The older mpmath probes remain non-certified diagnostics only. C4's conditional upper bound `|e_n| ≤ 40*(1/2500)^(n+1)` is separate and supplies no sign by itself.
- The current B2 boxes give exact ten-mode interval widths with decimal displays `1.3038935355470468e-5`, `8.8707651982351861e-8`, `5.8021702152449330e-10`, `3.6785120434605851e-12`, `2.2551276469308842e-14`, and `1.3430971414644236e-16`. Lean proves strict rational upper budgets `14/10^6`, `9/10^8`, `6/10^10`, `4/10^12`, `3/10^14`, and `2/10^16`. Relative to the unverified probes, the widths are about `0.00136`, `0.0949`, `2.93`, `71.6`, `1.53e3`, and `3.02e4` times the corresponding probe. This comparison only guides refinement; it is not a residual margin. On that provisional scale, the leading 1, 3, 4, and 5 height intervals dominate the width for `n=2,3,4,5`, respectively; the other height boxes need no refinement on this estimate.
- The available exact-rational *determinant* margins for C6's `C=40` gate have decimal displays approximately `1.233805751396619e-10`, `2.370461448625535e-15`, `1.677704301041960e-20`, and `4.956177598481227e-26` for `s=0,1,2,3`. The Lean theorem proves each exact rational expression is strictly positive. These bounds depend on the tail/sign premises and do not certify `e_n` signs.
- These four determinant margins already use the lower and upper endpoint power sums over the full ten-scale boxes, so they account for the current box widths. `SigmaContour51BoxSensitivity.lean` proves exact width budgets, while the new Arb residual intervals evaluate the original contour source directly and so do not approximate the ten roots by their box centers. The external residual margins are absolute rational bounds, not cancellation percentages. Root-box refinement is therefore not needed to establish the current Arb signs; the remaining issue is the Lean interval-transfer proof.
- Still needed for all windows: a Lean theorem supplying the C3 circle bound to C4 and the interval-transfer theorem for all six `e_n`. The source-level wrapper has already discharged `hdecomp` and `hbox` from the fixed C2 root list.
- Smallest first-window advance: prove `contour51ArbFirstThreeLowerPathResidualIntervalBounds` from the complete Arb arc ranges for `n=0,1,2`. The compiled direct `s=0` gate consumes only those three source intervals and proves the absolute determinant margin `1/1000000000 < sigmaPadeD 0 0`; it does not need the C3 `hR` bound. The all-window theorem still requires the C3 bound and `contour51ArbLowerPathResidualIntervalBounds` for all six indices.
- C5 reuse is limited to its general rational interval arithmetic, node evaluation, original-source normalization, and transport infrastructure. Its conditional signs at `d=99/2000` and `d=1/10` are not enclosures for central `e_n`; any reuse must prove a `d=0` specialization. Do not duplicate its Bernoulli table or full zeta/Gamma node certificate.
- The center specialization is now proved for the formal source recurrence, but no nonzero-displacement source coefficient box has been transported. Reusable pieces remain the C5 rational ball arithmetic, fixed-node evaluator, original-source normalization, and coefficient transport; any numerical reuse must additionally enclose the change from the C5 displacement to `d=0`. No Bernoulli table or zeta/Gamma node evaluation was duplicated in this checkpoint.

### Certified lower margins for `e_0,…,e_5`

The Arb/Acb 4096-arc run now gives rigorous outward rational intervals for all six original-source residuals. Lean proves that the simple lower margins in this table lie strictly below the exact Arb lower endpoints, and that the displayed upper bounds exceed the exact Arb upper endpoints. These are external interval enclosures until `contour51ArbResidualIntervalBounds` is proved from the arc data in Lean. The B2 width budgets are a different quantity and are retained for comparison; they are not subtracted from these contour-integral intervals.

| `n` | External Arb interval lower endpoint | Strict rational `e_n` lower margin | Simple upper bound | B2 ten-mode width budget | Non-certified probe |
|---:|---:|---:|---:|---:|---:|
| 0 | `9.535852947110655e-3` | `9/1000` | `1/100` | `14/10^6` | `0.00956074303923091` |
| 1 | `9.180296036279536e-7` | `9/10000000` | `1/1000000` | `9/10^8` | `9.34518811591709e-7` |
| 2 | `1.874202910399414e-10` | `9/50000000000` | `1/4000000000` | `6/10^10` | `1.97785053903660e-10` |
| 3 | `4.542210478952836e-14` | `1/25000000000000` | `1/10000000000000` | `4/10^12` | `5.13925976411857e-14` |
| 4 | `1.205912260570632e-17` | `1/100000000000000000` | `1/50000000000000000` | `3/10^14` | `1.46980503972282e-17` |
| 5 | `2.797326848058986e-21` | `1/500000000000000000000` | `1/100000000000000000000` | `2/10^16` | `4.44431065896308e-21` |

The exact endpoints and certificate metadata are in `evidence/C3_ARb_RESIDUALS_4096.json`. The external calculation encloses the original response integral on complete arcs; the Lean C2 identity transports that integral to `e_n`. The missing proof is the Lean-facing enclosure of each full-circle integral, including the parameterization and half-circle symmetry. The conditional C4 upper bounds `|e_n|≤40/2500^(n+1)` remain separate and are used for the all-window tail. The first-window direct interval gate requires only the first three residual interval transfers and no C4 hypothesis; the all-window theorem requires `hR` and all six interval transfers.
