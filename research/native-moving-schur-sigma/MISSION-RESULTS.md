# Resultados da missão: transversal, primeira falha e costura material

Este é o relatório corrente da missão iniciada sobre o commit-base
`671bd23b5ec3a486668f74ebbf756ad1dce269f6`. O antigo `REPORT.md` permanece como
registro histórico; este arquivo registra os resultados e limites desta execução.

## Respostas aos sete quesitos

### 1. Recorrência transversal de todas as derivadas pares

**PROVADO.** `sigma_log_jet_even_deriv_all_order` demonstra, para todo `n,m : ℕ` e
`-(1/2 : ℝ) < d < 1/2`,

```text
iteratedDeriv (2*m) (fun x => completedSigmaLogJet x n) d
  = (-1)^m * ((2*n+2*m+1)! / (2*n+1)!) * completedSigmaLogJet d (n+m).
```

As hipóteses de analiticidade e não anulação necessárias à recorrência de curvatura são
obtidas dentro do intervalo a partir da analiticidade da característica e da positividade da
densidade central. `sigma_log_jet_odd_deriv_center` prova que todas as derivadas ímpares
centrais são zero, usando a paridade local e a analiticidade do jet original.

O coeficiente de Taylor é exatamente
`(-1)^m * Nat.choose (2*n+2*m+1) (2*m) * completedSigmaLogJet 0 (n+m)`.
Os testes de normalização para `n=0`, `n=1`, segunda derivada e quarta derivada estão
formalizados.

Também foram provados `completedSigmaLogJet_transverse_mean_eventually` e
`completedSigmaLogJet_centeredDifference_eventually`. O `Q` usado é apenas
`completedNativeLogResponse z = -F'(z)/(2F(z))` para a característica completada original.
As identidades valem numa vizinhança de `z=0` onde os fatores e o produto deslocado não se
anulam, para `-1/2 < d < 1/2`; a prova não divide por `z`, portanto trata `z=0` pela
identidade analítica. A segunda diferença é somente o stencil analítico de raio imaginário;
nenhuma identidade com o bracket aritmético `C2` foi afirmada.

### 2. Série local convergente

**PROVADO.** `sigma_log_jet_transverse_hasFPowerSeriesAt` identifica os coeficientes
explícitos com o `HasFPowerSeriesAt` analítico do jet original. Em seguida,
`sigma_log_jet_transverse_tsum_eventually` prova que existe uma vizinhança de `d=0` onde

```text
completedSigmaLogJet d n
  = ∑' m, sigmaLogJetTransverseTaylorCoefficient n m * d^(2*m),
```

e a série é summable. Não foi reivindicado raio global nem convergência em todo
`|d| < 1/2`.

### 3. Classificação da primeira falha finita, inclusive prefixo singular

**PROVADO.** `FiniteHankelFailure.exists_first_hankel_failure` extrai a menor ordem
positiva que falha e prova a positividade sem hipótese dos prefixos anteriores.
`block_failure_classification` classifica uma extensão ruim de prefixo PSD em exatamente:

1. `∃ w, A w = 0 ∧ ⟪b,w⟫ ≠ 0`, caso em que `kernel_crossing_negative` constrói uma
   direção de energia negativa;
2. `∃ y, A y = b ∧ c - ⟪y,A y⟫ < 0`, o residual generalizado de Schur.

Não se exige que `A` seja invertível. `generalized_residual_independent` prova que o residual
é independente da solução de `A y = b`, e
`block_nonneg_iff_generalized_residual_nonneg` prova a equivalência com a não negatividade
do bloco. Para tamanho um, `sourceMoment_size_one_failure_neg_zero` elimina o caso de
cruzamento no prefixo vazio e conclui `h 0 < 0`.

### 4. Aplicação à `sigmaMatrix` original sob a hipótese de zero

**PROVADO, CONDICIONALMENTE.** `exists_first_sigma_hankel_failure_of_zero` e
`first_sigma_failure_classification_of_zero` reutilizam
`exists_sigmaMatrix_negative_direction_of_zero` sem alterá-lo e sem trocar a sequência de
momentos. Mantêm explícitos `γ > 0`, `F (γ : ℂ) = 0` e `0 < |d| < 1/4`. A conclusão fornece
uma primeira ordem `N > 0`, todos os prefixos menores PSD, e a classificação por núcleo–
cruzamento ou residual de Schur para o bloco anterior real `sourceMomentMatrix` e seu
acoplamento original. Não determina numericamente `N` nem afirma que o prefixo é não singular.

### 5. Forma material Green/TFVD e Hankel central

**PROVADO EM ESCOPO MAIS ESTREITO; A IDENTIFICAÇÃO COMPLETA CONTINUA ABERTA.**
`nativeSourceBoundaryEnergy_even_split_sigmaMatrix` prova que a energia bruta da face
limite nativa, na dimensão par `2*n`, é quatro vezes a soma dos dois readouts Hankel centrais
originais: `sigmaMatrix 0 0 n` no canal par e `sigmaMatrix 0 1 n` no canal ímpar, cada um
aplicado à fase de paridade que a fonte original define.

Essa identidade preserva os dois canais e as fases de origem. Não é uma igualdade com uma
única forma `B_N^mat(x,y) = ∑ x_i y_j h_(i+j)(0)`, nem identifica a face limite com energia de
armazenamento em passo finito. A igualdade do ledger bilinear TFVD completo com uma forma
Hankel central ainda não foi demonstrada para a energia física completa. A auditoria distinguiu
essa lacuna de uma identidade algébrica já existente na PR #70: `source_bezout_to_hankel_congruence`
identifica o bloco do kernel de coeficientes da fonte com `C * H * Cᵀ`, e
`native_residual_literal_four_terms` preserva os quatro termos ordenados HH, HT, TH e TT na
direção crítica mônica; `literal_product_critical` dá a soma exata com o termo corretivo para
essa direção, sob `IsUnit` do prefixo. Essa é uma congruência de coordenadas do kernel de
Bézout, não uma igualdade demonstrada entre a forma física Green/TFVD completa e a forma
Hankel nas mesmas coordenadas. A PR #70 também certifica o sinal para a segunda direção par,
mas declara aberta a orientação all-order e não reivindica uma Gram física positiva.

O menor objeto material efetivamente definido aqui é `nativeSourceFiniteBoundaryEnergy`, a
expressão alternada bruta de bordo limite. Seu lema de divisão par prova a identidade exata
acima, mas o próprio módulo declara que essa energia não é o armazenamento em passo finito e
não remove os cruzamentos de coordenadas superiores nem o resto analítico. Do lado C3/TFVD,
`CanonicalC3FiniteGreenGramTransportLedger` mantém separados os canais radial, fora da
diagonal, seam, proveniência e completion; `canonicalCompletedC3FixedCenterFourCornerLedger`
mantém o peso Hermitiano externo, o denominador e os canais corretivos. O resultado disponível
para esse ledger completo identifica sua primeira variação com `h₀`, não cada coeficiente
bilinear com a Hankel central. A obrigação precisa que falta é uma identidade que leve todos
esses canais do ledger físico, no mesmo vetor de coeficientes, à forma Hankel original.

Classificação: para a face limite bruta, **Caso 1** (identidade exata em dois canais, sem sinal
deduzido); para a proposta de identificar a forma física Green/TFVD completa com uma única
Hankel central, **Caso 3 / ABERTO** (a congruência algébrica da PR #70 é um resultado mais fraco,
em outras coordenadas). Não foi encontrado um controle all-order do defeito que produzisse o
**Caso 2**.

`displacedProductC_transverse_deriv_center` também prova
`∂_d D_d(t)|_(d=0) = 0` para todo `t` real, por cancelamento das duas derivadas de cadeia
opostas. Há, porém, um diagrama escalar demonstrável através da resposta logarítmica original:
`fullTransverseResponse_eq_channels` identifica a soma dos canais tilt e completion com a
derivada transversal completa de `F`; `fullTransverse_eq_normalizedGreen`, onde `F(t) ≠ 0`,
identifica essa resposta com `2 i F(t) Q(t)`, pois a resposta Green normalizada é
`Q = -F'/(2F)`; e `completedSigmaLogJet_transverse_mean_eventually` usa os valores deslocados
desse mesmo `Q` para gerar `t G_d(t²)` localmente. Isso prova uma ponte escalar no centro e
mostra que a geradora sigma usa a mesma resposta logarítmica original. Ainda não há um diagrama
formalizado para `d ≠ 0`: a decomposição em tilt/completion não foi estendida aqui aos dois
argumentos `t±id`. Tampouco cada canal foi identificado separadamente com os termos deslocados
de `Q`, nem o cancelamento entre canais foi usado como prova do cancelamento do produto. O
primeiro é uma compensação não trivial da decomposição tilt/completion; o segundo decorre das
duas regras da cadeia opostas em `F(t-id)F(t+id)`. A ponte provada é do readout escalar central
para `Q`, não uma identidade termo a termo nem uma Gram física positiva.

### 6. Positividade central all-order

**ABERTO.** Não foi demonstrado que todos os `sigmaMatrix 0 0 N` são positivos definidos ou
semidefinidos. Recorrências, identidades de curvatura, a expansão transversal e a igualdade da
face material não provam essa positividade.

**PARTE D PROVADA CONDICIONALMENTE.** `sigmaFirstFailureOrder_tends_to_infty_of_center_posDef`
assume explicitamente que todo `sourceMomentMatrix` central original é positivo definido, além
da hipótese original de um zero em altura positiva. Define `sigmaFirstFailureOrder` pelo
primeiro tamanho ruim extraído de `exists_first_sigma_hankel_failure_of_zero` e prova que, para
cada `M`, existe `ε > 0` tal que `0 < |d| < min(ε, 1/4)` implica `M < N_*(d)`. A prova estabiliza
cada prefixo finito pela positividade dos pivôs de Schur, usando a continuidade dos jets e da
inversa do prefixo. A hipótese central all-order permanece uma hipótese; o teorema não a
demonstra.

### 7. Compilação, axiomas e Git

**PROVADO / VALIDAÇÃO.** Foi executado novamente após integrar `SigmaFailureOrder`:

```text
bash research/native-moving-schur-sigma/validate.sh
```

O resultado foi registrado em `8435f79`. Todos os módulos listados passaram com
`-DwarningAsError=true`, incluindo `SigmaTransverseJoint`, `SigmaFailureOrder` e `Audit`;
`lake build --wfail`, as auditorias `foundation`, `geometry` e `analysis`, e a busca de fontes
por `sorry`, `admit`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by` e declarações
`axiom` também passaram. Exit code: `0`. Os `#print axioms` dos novos teoremas mostram somente
`[propext, Classical.choice, Quot.sound]`.

O trabalho parte da branch `agent/native-moving-schur-sigma`, cujo HEAD no começo desta missão
era `671bd23b5ec3a486668f74ebbf756ad1dce269f6`. Os commits por resultado são:

- A, recorrência e série: `c9bf34d`.
- B, primeira falha: `b93d0d4`.
- C, costura material: `01119cd`.
- Redução radial da PDE e normalização dos logs de validação: `242b55b`.
- Relatório e integração inicial do validador: `d1d5307`.
- Atualização do relatório com a redução radial: `3a49688`.
- Representação conjunta e PDE funcional local, com validação: `b2eca71`.
- Estabilidade de prefixos e divergência condicional de `N_*(d)`: `8435f79`.

Esta atualização registra o fechamento da seção local uniforme e da PDE funcional para a
geradora sigma original e a divergência condicional da primeira ordem ruim. Os resultados estão
formalizados em `SigmaTransverseJoint.lean` e `SigmaFailureOrder.lean`, integrados ao validador
e à auditoria, com axiomas padrão e sem alterar a sequência dos jets.

## Proveniência e limites da cadeia

```text
característica completada original F
  → resposta logarítmica Q = -F'/(2F)
  → identidade local com a função geradora dos jets sigma originais
  → recorrência transversal, coeficientes, série local e PDE funcional local
  → Hankel original e classificação singular-safe da primeira falha
  → identidade material da face limite como soma dos dois canais sigma centrais
  → congruência algébrica Bézout–Hankel da fonte TFVD, com quatro termos literais preservados
```

O vínculo de `Q` com `F` é definicional. Os jets permanecem `completedSigmaLogJet`; a matriz
sigma permanece a sequência original. A equivalência entre momentos geométricos de
profundidade prima e momentos canônicos, e entre os jets centrais e esses momentos canônicos,
é usada na prova da costura material. A geometria do bracket `C2`, a média analítica
transversal e a síntese material permanecem objetos distintos, exceto pelas identidades
formalmente provadas acima.

**PDE FUNCIONAL DA FONTE PROVADA LOCALMENTE.**
`completedSigmaLogJet_joint_representation_near_center` estabelece um único `δ > 0` tal que a
média transversal original satisfaz `S(t,d) = t * G_d(t²)` para todo `|d|, |t| < δ`. A prova
usa um único disco de analiticidade de `Q = -F'/(2F)` em torno de zero e o raio positivo comum
da série original para todos os deslocamentos suficientemente pequenos. A igualdade inicial
perto de `t=0` é estendida em cada seção longitudinal por unicidade de funções analíticas reais
no intervalo.

`completedSigmaLogJetGeneratingFunction_transverse_pde_near_center` aplica então
`harmonic_radial_generating_pde_at_nonzero` e prova, para algum `η > 0`, `|d|, |t| < η` e
`t ≠ 0`,

```text
∂²_d G_d(t²) + 6 ∂_u G_d(t²) + 4 t² ∂²_u G_d(t²) = 0.
```

As derivadas são as derivadas iteradas reais das funções geradoras originais. Como `u=t²>0`,
isso cobre a equação funcional em uma vizinhança perfurada de `u=0`; a identidade coeficiente
a coeficiente no centro continua disponível. `#print axioms` mostra apenas `[propext,
Classical.choice, Quot.sound]` para os teoremas novos. O stencil de raio imaginário segue
sendo uma média analítica, sem identificação com o bracket aritmético `C2`.

**DERIVADO MATEMATICAMENTE:** quando `u=r²`, o operador radial vira
`∂²_r + (2/r)∂_r`; isso descreve uma interpretação harmônica auxiliar em quatro dimensões,
sem identificar `ℝ⁴` com o espaço material `C2/C3`.

## Referências de proveniência

- [Commit-base 671bd23](https://github.com/thiagomassensini/geometry-of-numbers/tree/671bd23b5ec3a486668f74ebbf756ad1dce269f6)
- [PR #41](https://github.com/thiagomassensini/geometry-of-numbers/pull/41), sobre a identidade entre ortogonalização algébrica e energia material de bordo, sem concluir sinal all-order.
- [PR #70](https://github.com/thiagomassensini/geometry-of-numbers/pull/70), cuja prova de transporte foi mesclada à branch `agent/c3-fourteenth-tail`: o kernel de coeficientes é congruente à Hankel e os quatro termos literais são preservados, mas não há Gram física positiva nem orientação all-order.
- [FullTransverseCancellation.lean](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/c3-tilt-prime/FullTransverseCancellation.lean)
- [FullTfvdTransverse.lean](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/c3-tilt-prime/FullTfvdTransverse.lean)
