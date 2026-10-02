# R2 — relatório técnico de implementação e auditoria

## Resultado

**A — FULL R2 PASS. R2 CLOSED.** Não há gap R2 restante.
Todos os objetos verticais expostos são reais. O núcleo algébrico histórico
já genérico preserva sua generalidade natural e é especializado em ℝ nos
exemplos e no certificado. Não há import de código/repositório histórico.

A segunda diferença discreta, o Green com retorno de bordo, a TFVD e a válvula
projetiva são reconstruções exatas e compatíveis do mesmo estado discreto.
Após o gauge pela amplitude crítica b^(-k/2), a identidade vertical do carry
é GB+RTr=I. Sua análise/síntese fornece a interface mínima para R3.
Nenhuma conclusão espectral é feita.

## 1–6. Checkpoint, fontes e arquivos

- SHA inicial: `4cc4261fb2910c72d35e1746c983a28999f6d7eb`;
  HEAD, main e origin/main coincidiam após fetch.
- Branch: `r2-real-tfvd-green-valve`, worktree isolado do checkout com edits paralelos.
- Fonte carry: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Fonte primos: `e2a723b4ec3e645539de0b9ca881951d93259cda`.
- Arquivos históricos integralmente consultados, SHAs e crosswalks:
  [SOURCE_PROVENANCE.md](SOURCE_PROVENANCE.md), seção R2.
  [Manifest dos conteúdos](R2_SOURCE_MANIFEST.json) registra 26 arquivos e SHA256.

Novos módulos, todos em `GeometryOfNumbers/Analysis/`:

| Módulo | Conteúdo mínimo |
| --- | --- |
| RealDiscreteValve | diferenças, Green finito, kernel afim, readout crosswalk e recorrência causal |
| RealDiscreteValveSeries | séries G0/G1 e reconstrução multiplicativa formal |
| RealTowerValve | canal triangular, integração e seus round-trips |
| RealProjectiveGreenValve | coordenadas inversas, transportes, jacobianos e potencial/massa Green |
| RealMultiplicativeValve | ODE normalizada, equivalência e lei soma→produto |
| RealDiscreteProjectiveReconstruction | estado↔bordo+massa normalizada |
| RealCarryGreenKernel | kernel somável e bound de operador |
| RealCarryL2 | ℓ² real e shifts causais contínuos |
| RealCarryWeightedValve | bracket, trace, retorno, Green e TFVD |
| RealCarryTfvd | razão crítica local, gauge, análise/síntese e capstone |

Arquivos anteriores modificados: AGENTS.md, README.md,
GeometryOfNumbers/Analysis.lean, GeometryOfNumbers/Analysis/Audit.lean,
docs/HUMAN_THEORY.md, docs/FORMALIZATION_PLAN.md, docs/SOURCE_PROVENANCE.md.
Novos documentos: rota normativa, este relatório, manifest e R2_VALIDATION.json.
Foundation, Geometry, seus audits, scripts de auditoria, toolchain e dependências
não foram modificados. Alterações paralelas não integram o commit R2.

## 7–18. Reconstrução discreta e projetiva

Os prefixos dos nomes abaixo são relativos a `GeometryOfNumbers.Analysis`.

| Item | Definição / theorem exato |
| --- | --- |
| 7. Primeira diferença | `DiscreteValve.fdiff f k := f(k+1)-f(k)` |
| 8. Segunda diferença | `DiscreteValve.bracket f k := f(k+2)-2 • f(k+1)+f(k)`; em ℝ, nsmul é multiplicação pelo natural |
| Crosswalk ao bracket local | `DiscreteValve.bracket_eq_realCenteredReadout`; mesmo stencil, eixos distintos |
| 9. Teorema fundamental | `DiscreteValve.realDiscreteGreenReconstruction`: f(n+1)=f0+(n+1)Δf0+greenSum f n |
| Kernel | `DiscreteValve.bracket_eq_zero_iff_affine`: curvatura zero iff estado afim |
| 10. Green formal | `DiscreteValve.greenKernelSeries`: coeficiente n+1; `one_sub_X_sq_mul_greenKernelSeries`: (1-X)^2G1=1 |
| 11. Reconstrução em séries | `DiscreteValve.mk_discrete_valve`: mk f=C(f0)G0+X C(Δf0)G1+X²G1 mk(bracket f) |
| 12. Coordenada | `ProjectiveDepth.coordinate := X * geometricSeries`; inverseCoordinate:=X * inverseGeometricSeries, coeficientes alternados |
| Transporte | toProjective compõe com X(Y); fromProjective compõe com Y(X); ambos os round-trips provados |
| 13. Jacobiano Green | `ProjectiveDepth.coordinate_derivativeFun` |
| 14. Cancelamento | `ProjectiveDepth.greenKernel_subst_inverse_mul_inverseDerivative` |
| Potencial | `GreenValve.greenLogPotential`; derivative_greenLogPotential dá K'=G1 C |
| Colapso projetivo | `GreenValve.derivative_toProjective_greenLogPotential`: derivada do potencial transportado = curvatura transportada |
| 15. Massa | `ProjectiveValve.projectiveValveMass D := GreenValve.projectiveGreenMass (fromProjective D)`; a massa Green é a exponencial formal do potencial Green |
| 16. A'=DA | `ProjectiveValve.derivative_projectiveValveMass`; constantCoeff=1 por projectiveValveMass_constantCoeff |
| 17. Round-trips | `projectiveValveCurvature_projectiveValveMass`; `projectiveValveMass_projectiveValveCurvature` (massa normalizada) |
| Aditivo→multiplicativo | `ProjectiveValve.projectiveValveMass_add` |
| 18. Estado | `DiscreteProjective.stateMass f := projectiveValveMass (toProjective (mk (bracket f)))` |
| Identificação Green | `DiscreteProjective.stateMass_eq_projectiveGreenMass` |
| Curvatura recuperada | `DiscreteProjective.projectiveValveCurvature_stateMass` |
| Massas iguais | `DiscreteProjective.stateMass_eq_iff_bracket_eq` |
| Unicidade | `DiscreteProjective.eq_iff_boundary_and_stateMass_eq` |
| Reconstrução completa | `DiscreteProjective.realDiscreteProjectiveReconstructionEquiv`; `reconstruct_encode` e `encode_reconstruct` |

ReconstructionData tem initialValue, initialSlope e projectiveMass, cujo tipo
é a série com coeficiente constante um. A inversa usa somente a recorrência
causal histórica n→n+2 e a curvatura extraída/transportada. Essa inversa não
muda a direção de proveniência do encoder: estado→curvatura→massa.

## 19–27. Gauge e TFVD real

| Item | Definição / theorem exato |
| --- | --- |
| 19. Razão vertical | `criticalVerticalAmplitudeRatio b hb := realCriticalAmplitude b 1 hb` |
| 20. Origem | `criticalVerticalAmplitudeRatio_eq_rpow`: b^(-1/2); `realCriticalAmplitude_eq_verticalRatio_pow`: A_b(k)=eta_b^k |
| Contratividade | `criticalVerticalAmplitudeRatio_pos`; `criticalVerticalAmplitudeRatio_lt_one` para b≥2 |
| 21. Gauge | `realCarryWeightedSecondDifference_gauge`: d_eta²(gauge f)(k)=eta^(k+1)bracket f k |
| Compatibilidade Green | `realCarryWeightedGreenSum_gauge`: Green ponderado em n+1 = eta^(n+1)greenSum f n |
| 22. Espaço | `RealCarry.CarryVerticalL2 := ℓ²(ℕ,ℝ)` |
| Bracket | `RealCarry.carryWeightedVerticalCenteredBracket`: Bx0=0; Bx(n+1)=eta^(-1)x(n+2)-2x(n+1)+eta x n |
| Trace | `RealCarry.carryWeightedVerticalTrace`: (x0,eta^(-1)x1-x0) |
| Return | `RealCarry.carryWeightedVerticalReturn`: eta^n(a+n slope), para 0≤eta<1 |
| Kernel | `RealCarry.carryWeightedVerticalGreenKernel eta distance := distance * eta^distance` |
| Green | `RealCarry.carryVerticalL2WeightedGreen`: soma em norma de operadores de kernel×shift unilateral |
| Somabilidade e bound | carryWeightedVerticalGreenKernel_summable; carryWeightedVerticalGreen_norm_le_kernelMass |
| Green coordenado | carryVerticalL2WeightedGreen_apply: soma finita de kernel(r)x(n-r) para r≤n |
| 23. TrR=I | `RealCarry.carryWeightedVerticalTrace_comp_return` |
| 24. BR=0 | `RealCarry.carryWeightedVerticalCenteredBracket_comp_return` |
| 25. GB+RTr=I | `RealCarry.carryWeightedVerticalTfvd_identity`; especialização derivada: `realCriticalCarryTfvd_identity` |
| 26. T / S | `realCarryTfvdAnalysis`: (Bx,Trx); `realCarryTfvdSynthesis`: Gy+Rtau |
| 27. S∘T=I | `realCarryTfvdSynthesis_comp_analysis`; especialização: `realCriticalCarryTfvdSynthesis_comp_analysis` |

Todos os operadores são mapas lineares contínuos sobre ℝ. O shift causal
é o adjunto real do tail-shift contrativo, a construção auxiliar histórica;
não se introduz operador auto-adjunto ou afirmação espectral. O ℓ² é a
realização vertical esperada, não uma norma derivada retroativamente da massa.

A orientação de d_eta é eta^(-1)x(k+1)-x(k); d_eta² é
(d_eta x)(k+1)-eta(d_eta x)(k). Seu índice k corresponde à coordenada k+1
de B_eta. O Green aditivo greenSum f n reconstrói f(n+1).
A série formal G1 tem coeficiente n+1, enquanto o Green causal vestido tem
kernel r eta^r e começa em zero. Os deslocamentos são explícitos nos theorems.

## 28–32. Certificação e fronteira

- Capstone: `realCriticalCarryTfvdGreenValveCapstone`, prova do certificado
  RealCriticalCarryTfvdGreenValveCertificate, composto de resultados anteriores;
  nenhum campo é uma hipótese substituta usada para fechar uma meta.
- 166 theorems e 232 nomes declarados novos auditados explicitamente.
  Todos os capstones usam somente `[propext, Classical.choice, Quot.sound]`.
  Nenhum footprint excede a política Analysis. Foundation mantém lista vazia.
- Exemplos em Analysis/Audit.lean: sequência afim (curvatura e Green zero),
  n² (curvatura dois), Green em n=3 igual a 12 e reconstrução de f4=16,
  gauge simbólico crítico em base dois, trace/return, TFVD nas coordenadas
  0/1/2 via Fin 3, e round-trips reais da reconstrução e da massa.
- [R2_VALIDATION.json](R2_VALIDATION.json) registra cada build isolado,
  os dois builds de entrada/audit, os três scripts e diff --check,
  com exit codes e tempos. A integração repete builds/audits em main.
- Resultado: **A**, todos os oito gates R2 CLOSED.
- Menor gap restante **dentro de R2: nenhum**. R3 recebe S∘T=I e estudará
  análise→Gram→normalização/isometria posteriormente. Gaps anteriores de
  atlas/seed permanecem separados. Head/tail e momentos ficam downstream.

## 33–35. Integração e preservação

O SHA final e a igualdade HEAD=main=origin/main são conferidos na entrega,
pois o hash de um commit não pode ser armazenado dentro de seu próprio conteúdo.
O resultado válido é integrado por fast-forward e enviado a origin/main
somente após a revisão e as verificações. Os builds/audits são repetidos em main.

O checkout original tinha alterações paralelas em .gitignore e
HUMAN_THEORY.md. A implementação foi feita sobre o conteúdo commitado,
num worktree separado. Esses hunks não integram o commit R2. A integração
preserva o patch do usuário e recompõe o documento humano por merge de três
vias quando necessário; a entrega reporta o status dirty preservado.
