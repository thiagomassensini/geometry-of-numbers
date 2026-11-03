# Curvatura do pivô móvel da fonte canônica, nos dois setores

**Resultado: PASS_STRUCTURAL para a ponte fixa–móvel; PARTIAL para a investigação de positividade em toda ordem.** A segunda derivada do complemento de Schur da família canônica completada foi identificada com a curvatura da mesma direção crítica fixa no centro. A única hipótese sobre o prefixo é sua inversibilidade no centro. Nenhum sinal do novo pivô ou de sua curvatura é assumido ou concluído.

## A — Base e resultados reaproveitados

Base de `geometry-of-numbers`: `474a772fb645504e0bfa7e6610f81463000d76d1`, cabeça da PR #139. A branch `agent/native-moving-schur-sigma` é empilhada sobre `agent/native-sixth-explicit-sigma`. As PRs anteriores permanecem intactas e não são mescladas automaticamente.

A PR #139 fornece os jatos da norma da característica completada original, sua igualdade com os momentos canônicos no centro, sua analiticidade central, paridade e curvatura. A sequência não é redefinida a partir de uma Gram, Jacobi ou alturas. O parâmetro d desloca a abscissa para σ=1/2+d; não é a profundidade radial k.

O estudo de `momentos`, commit `05c9314d59306383baa55ed3be80ab950e799e97`, fornece o transporte local do pivô móvel. Quatro módulos foram reaproveitados em `vendor/MomentosHankel`: `SchurPivotCurvature`, `PivotSecondDerivative`, `SchurVectorSmoothness` e `PivotLocalTransport`. O manifesto registra o commit, os hashes e a única normalização de formatação: remover uma linha vazia excedente no fim de `SchurPivotCurvature.lean`; todas as declarações e provas foram preservadas. Eles são recompilados nesta tarefa; não se depende de objetos de `momentos` sem fonte versionada.

O vetor crítico continua sendo o já identificado na cadeia da PR #41 e da #139: `canonicalCriticalVector s n = (-A⁻¹b,1)`. A família `sigmaSchur` é literalmente `sourceMomentSchur` aplicada aos jatos da característica original, com o mesmo prefixo, acoplamento e canto.

## B — O que foi demonstrado agora

`MatrixJetCalculus.lean` prova `euclideanCLM_basis_expansion` e `euclideanCLM_hasDerivAt_of_entries`: a matriz original é expandida na base finita de entradas, e as derivadas de seus coeficientes são transportadas ao mesmo operador euclidiano. Não se troca a métrica nem se acrescenta um produto interno. Essa construção descarrega as hipóteses de derivação como operador contínuo (`hG` e `hG₁`) que o estudo anterior deixava na interface.

`SigmaNeighborhood.lean` prova:

- `sigma_matrix_center`, `sigma_matrix_continuous_center`, `sigma_matrix_first_center` e `sigma_matrix_symm` para a família original;
- `exists_sigma_prefix_neighborhood`: se o prefixo canônico é invertível no centro, existe uma vizinhança aberta U contendo 0 em que ele permanece invertível e todos os finitíssimos jatos necessários são analíticos;
- `sigma_matrix_operator_first` e `sigma_matrix_operator_second_center`, obtidos dos jatos da fonte.

A vizinhança depende de setor e ordem. Não se afirma uma vizinhança uniforme para a família infinita, nem ausência global de zeros da característica.

Em `MovingSchur.lean`, os principais resultados são:

1. `sigma_schur_center`: o pivô central é exatamente o complemento de Schur dos momentos canônicos;
2. `central_schur_vector`: o vetor usado pelo transporte de `momentos` é exatamente `canonicalCriticalVector` da #139;
3. `moving_schur_curvature`: para todo setor s e ordem n cujo prefixo central é invertível,

   \[
   p_{s,n}''(0)=v_0^TG_{s,n+1}''(0)v_0;
   \]

4. `moving_schur_curvature_expanded`: preservando todos os pares ordenados,

   \[
   p_{s,n}''(0)=-2\sum_{i,j=0}^{n}(v_0)_i(v_0)_j
   (i+j+s+1)(2(i+j+s)+3)h_{i+j+s+1};
   \]

5. `moving_schur_eq_fixed_form_curvature`: a segunda derivada do pivô móvel é exatamente a segunda derivada da forma quadrática completa avaliada na direção crítica central fixa, a obrigação identificada no §E da #139.

Não há `PosDef`, `PosSemidef`, hipótese de sinal do novo pivô, `hrec`, `Hharm`, `hG` ou `hG₁` como premissa do teorema canônico final. A hipótese `IsUnit` do prefixo central é explícita e não é uma hipótese de positividade. As condições locais e as derivadas do operador são construídas na prova.

## C — Transporte para os setores par e ímpar

`SectorRegression.lean` especializa o resultado em `even_moving_schur_curvature` e `odd_moving_schur_curvature`. O setor está presente tanto no índice do momento quanto no peso. Para s=1, a fórmula é

\[
 p_{1,n}''(0)=-2\sum_{i,j=0}^{n}(v_0)_i(v_0)_j
 (i+j+2)(2(i+j)+5)h_{i+j+2}.
\]

Os teoremas `first_even_pivot_curvature` e `first_odd_pivot_curvature` conferem diretamente na fonte original os coeficientes iniciais distintos:

\[
 p_{0,0}''(0)=-6h_1,\qquad p_{1,0}''(0)=-20h_2.
\]

Não são testes numéricos. São igualdades Lean que também verificam a convenção do deslocamento. A prova genérica mantém os (n+1)² cruzamentos, incluindo antigos–novos; não reduz a análise a entradas diagonais.

## D — Validação e proveniência

Os módulos de pesquisa são compilados explicitamente com `-DwarningAsError=true`. O build raiz usa `lake build --wfail`, acompanhado das auditorias Foundation, Geometry e Analysis. `Audit.lean` imprime os axiomas das declarações novas e reutilizadas e percorre tipos e corpos das raízes principais, bloqueando certificados finitos anteriores de positividade do sexto pivô e equivalências de Stieltjes como premissas. Exige a presença do transporte local de `momentos`, da ponte de derivadas matriciais e da genealogia Green/TFVD da fonte original.

São reutilizados objetos históricos da #139 e de sua cadeia, além de Mathlib e do ambiente do operador. A árvore local do operador contém a investigação theta16 em andamento; suas alterações não são adotadas como uma nova fonte validada. Os imports herdados usam objetos compilados anteriores. O manifesto compara os objetos de pesquisa reutilizados com a worktree da #139; isso não substitui uma reconstrução histórica limpa. Não foram alterados fontes, pesos, métricas, amplitudes, pins ou o trabalho local do operador.

Reprodução no host `llm`, a partir desta worktree:

```bash
bash research/native-moving-schur-sigma/validate.sh
python3 research/native-moving-schur-sigma/cache_manifest.py
```

As evidências e os hashes ficam em `evidence/`. Os logs extensos do build e da auditoria de Analysis são compactados para publicação. Os nove módulos (quatro reutilizados e cinco de pesquisa/auditoria) recompilaram com avisos como erros. Foram impressos os footprints de 34 declarações; a auditoria transitiva de seis raízes percorreu 57.504 dependências e permitiu apenas `propext`, `Classical.choice` e `Quot.sound`. O build raiz passou com 8.849 tarefas; as auditorias separadas de Foundation, Geometry e Analysis e a busca por escapes proibidos também passaram. O manifesto comparou 273 objetos históricos, sem divergências. Os resultados finais dos checks são registrados no mesmo diretório.

## E — O que permanece aberto e próximo passo mínimo

A ponte fixa–móvel está fechada sob a inversibilidade central do prefixo. O problema remanescente de sinal é agora o somatório explícito da fonte acima, na mesma direção crítica e com os pesos corretos de cada setor. Buscar uma desigualdade independente sobre essa expressão pode orientar a curvatura; apenas defini-la como `NegativeGateDominant` não prova seu sinal.

Mesmo demonstrar curvatura negativa em todas as ordens não provaria, isoladamente, positividade dos valores centrais dos pivôs. A investigação de positividade canônica all-order continua exigindo uma desigualdade da síntese original que determine esses valores ou uma representação positiva integralmente identificada. Não se deve transferir automaticamente o sinal de uma Gram inteira auxiliar ou de uma soma de energias isoladas.

O próximo alvo curto é derivar uma identidade da fonte para o somatório ponderado, preservando o retorno e os cruzamentos, e confrontá-la com as desigualdades finitas já certificadas. As margens radiais e caudas da #139 permanecem disponíveis para a passagem física, mas esta rodada não produz uma nova margem radial all-order nem novos sinais de pivôs.

## F — Rota hipotética do operador: progresso inicial e lacunas

`MomentLogConvexity.lean` formaliza dois lemas gerais, sem importar a sequência sigma:

- `hankel_quadratic_nonneg`: uma matriz de Hankel PSD torna não negativa a forma
  quadrática de qualquer vetor finito de coeficientes;
- `logConvex_expBounded_ratio`: uma sequência não negativa, log-convexa e com cota
  exponencial satisfaz a cota de razão, inclusive quando algum termo é zero.

O módulo compila com `-DwarningAsError=true`; `#print axioms` permite somente
`propext`, `Classical.choice` e `Quot.sound`. A validação inclui agora esse módulo e
`SigmaZeroObstruction` na lista explícita de compilação.

Foi iniciado o Checkpoint B em `MomentLogConvexity.lean`. O funcional
`momentFunctional h p = ∑ k, p.coeff k * h k` está definido diretamente da sequência
original. Provamos sua aditividade, sua ação nos monômios e a expansão finita
`momentFunctional_mul_eq_double_sum`, que escreve `L(pq)` como a soma dos coeficientes
`p_i q_j h_{i+j}` nos graus efetivos de `p` e `q`. Essa ponte compila com
`-DwarningAsError=true` e usa somente os axiomas padrão do Lean.

Também estão provadas a linearidade escalar `momentFunctional_C_mul` e a consequência
`momentFunctional_square_nonneg`: H1, aplicada à matriz de ordem `p.natDegree + 1`, implica
`L(p²)≥0` para todo polinômio. A conversão entre somas de `Fin N` e somas em `range N` é
explícita, e o teorema passa `#print axioms` com apenas os axiomas padrão.

Com a positividade em todas as direções `p + C(t)q`, foi derivada a desigualdade de
Cauchy–Schwarz `momentB_sq_le_momentQ_mul`, incluindo o caso degenerado `Q(q)=0`; daí,
`momentB_eq_zero_of_momentQ_eq_zero` registra que todo vetor de norma zero é ortogonal a
todos os polinômios. Ambos são kernel-checked e passam `#print axioms` com apenas os axiomas
padrão. A construção do operador ainda não começou.

Foi definida a sequência deslocada `shiftedMomentQ h p n = Q(X^n p)`. H1 fornece sua
não negatividade (`shiftedMomentQ_nonneg`) e Cauchy–Schwarz dá sua log-convexidade
(`shiftedMomentQ_logConvex`), em ambos os casos sem exigir positividade estrita dos termos.
`shiftedMomentQ_eq_double_sum` expande cada termo em uma soma finita dos momentos originais
`h_{2n+i+j}`. A hipótese H2 então produz `shiftedMomentQ_expBounded`, com constante `K_p`
não negativa e independente de `n`. Por fim, `momentQ_X_mul_le` aplica
`logConvex_expBounded_ratio` e prova

\[
Q(Xp)\le R^2Q(p)
\]

usando apenas H1 e H2 (com `C≥0`, `R>0` e `|h_k|≤CR^k`). Este é o Checkpoint B. O resultado
passa `#print axioms` com apenas os axiomas padrão. A construção do quociente e do operador
ainda está aberta.

Isso fecha somente o lema universal de multiplicação limitada; não fecha a missão global.

**Início do Checkpoint C:** `momentQ_add` e `momentQ_C_mul` dão as identidades de soma e
escala da forma quadrática. Com `momentB_eq_zero_of_momentQ_eq_zero`, isso prova que
`momentNullSubmodule` — o conjunto dos polinômios com `Q(p)=0` — é um submódulo de
`Polynomial ℝ`. O produto interno induzido `quotientMomentInner` está agora definido no
quociente e provado independente dos representantes. `quotientMomentInnerProductCore`
fornece a estrutura positiva definida; as instâncias de Mathlib dão ao quociente a estrutura
de espaço interno. `momentHilbert` é a conclusão uniforme desse quociente, e
`momentHilbert_complete` verifica sua completude. Esses teoremas passam `#print axioms` com
apenas os axiomas padrão. `quotientMulX` é a multiplicação por `X` no quociente, bem definida
porque B dá invariância do submódulo nulo; `quotientMulX_norm_bound` prova a cota por `R`.
`quotientMulXContinuous` e `momentHilbertMulX` fornecem os operadores contínuos no quociente
e na conclusão. `momentHilbertMulX_on_quotient` e `momentHilbertMulX_coe` verificam que a
extensão preserva a ação original de `X`. Finalmente, `quotientMulX_symmetric` e
`momentHilbertMulX_symmetric` provam a simetria no quociente e em todo o espaço completado,
respectivamente. Todas essas provas passam `#print axioms` com apenas os axiomas padrão.
Ainda faltam a identificação formal do operador contínuo simétrico com `IsSelfAdjoint`, a
recuperação dos momentos pela ação do operador e a resolvente.

No Checkpoint A, `SigmaZeroObstruction.lean` agora prova que
`t ↦ log(completedSigmaDensity d t)` é analítica na origem. A partir do raio positivo de sua
série de Taylor e da normalização já provada dos jets, `completedSigmaLogJetGeneratingSeries_radius_pos`
prova raio positivo para a série em `u` com coeficientes exatamente
`completedSigmaLogJet d n`. `completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt`
certifica que a soma dessa série é uma geradora analítica local. Ambos os teoremas passam
`#print axioms` com apenas `propext`, `Classical.choice` e `Quot.sound`.

Também foi provado que `completedSigmaDensity d` e seu log são pares na variável real;
`completedSigmaLogDensity_odd_iteratedDeriv_eq_zero` registra o anulamento de todas as
derivadas ímpares na origem. Isso fecha a paridade necessária para reduzir `t` a `t²`.

Foi fechada uma etapa intermediária importante do Checkpoint A:
`completedSigmaLogDensity_derivative_eq_generatingFunction_eventually` prova, em uma
vizinhança real de zero, que

\[
\frac{d}{dt}\log(\texttt{completedSigmaDensity}\ d\ t)
=-4t\,G_d(t^2),
\]

onde `G_d` é a soma convergente da série com coeficientes exatamente
`completedSigmaLogJet d n`. A prova usa as séries de Taylor convergentes, anula os
coeficientes pares pela paridade, reindexa os ímpares e fatoriza a soma; não é somente uma
igualdade formal de coeficientes. O novo teorema também passa `#print axioms` com apenas
`propext`, `Classical.choice` e `Quot.sound`.

A mesma série foi agora complexificada coeficiente a coeficiente em
`completedSigmaLogJetComplexSeries`; provou-se que a extensão escalar preserva o raio e que
`completedSigmaLogJetComplexGeneratingFunction` possui `HasFPowerSeriesAt` em zero. Portanto,
a geradora analítica complexa com os jets originais está disponível.

Também foi provado `displacedProductC_deriv_ofReal_eq_density_deriv_eventually`: perto de zero,
a derivada complexa de `D_d`, avaliada na reta real, coincide com a derivada da densidade real.
A prova usa analiticidade local de `D_d`, sua restrição real e a igualdade já estabelecida entre
`D_d(t)` e a densidade. Isso fornece a ponte de derivadas necessária para transportar a EDO
real à expressão complexa.

O Checkpoint A está agora fechado. `completedSigmaDensity_deriv_eq_generatingFunction_mul_eventually` deriva a equação diferencial real para a densidade a partir da identidade da log-derivada. `completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually` identifica as somas real e complexa na reta. Com `displacedProductC_deriv_ofReal_eq_density_deriv_eventually`, isso prova que a expressão da EDO complexa zera numa vizinhança real. A expressão é analítica em zero; `displacedProductC_local_differentialEquation` usa o princípio de zeros isolados para obter a identidade complexa numa vizinhança complexa de zero. Assim, o resultado envolve a série convergente dos `completedSigmaLogJet` originais e não uma série formal ou postulada.

A propagação da EDO até o zero deslocado continua aberta. Também continuam abertos o lema universal de multiplicação limitada (Checkpoint B), a construção GNS (C), a resolvente (D) e a conclusão efetiva de negatividade para a `sigmaMatrix` original. Nenhuma dessas etapas é tratada como provada.

## Atualização de 2026-11-03 — operador auto-adjunto e recuperação dos momentos

A construção do Checkpoint C foi concluída no módulo independente `MomentLogConvexity.lean`.
`momentHilbertMulX_isSelfAdjoint` identifica o operador contínuo simétrico com `IsSelfAdjoint`
no espaço de Hilbert completo. `momentHilbertUnit` é o vetor constante `e=[1]` (sem pressupor
que seja não nulo). `momentHilbertMulX_pow_unit` prova por indução a ação das potências, e
`momentHilbert_recovers_moment` demonstra, para toda sequência sob H1 e H2,

\[
\langle T^n e,e\rangle=h_n.
\]

A construção continua usando a sequência de momentos original; nenhum representante por medida
foi introduzido. Esses teoremas passam `#print axioms` com somente `propext`, `Classical.choice`
e `Quot.sound`.

**PROVADO:** checkpoints A, B e C; além disso, a identidade de recuperação dos momentos que é
pré-requisito do D.

**ABERTO:** resolvente complexa e sua holomorfia, expansão de Neumann e identificação local
(Checkpoint D); estimativa de Cauchy para instanciar H2 com os jets sigma; propagação da EDO e
contradição no domínio deslocado; extração do vetor negativo para a matriz sigma original.
O resultado de negatividade all-order não está concluído.

**COMPILAÇÃO:** `bash research/native-moving-schur-sigma/compile_module.sh MomentLogConvexity`
concluiu com `-DwarningAsError=true`; todos os resultados listados passaram `#print axioms`.
`git diff --check` passou e não há `sorry` ou `admit` no módulo.

## Continuação do Checkpoint D — espaço de Hilbert complexo

Foi criado `MomentComplexification.lean`, que realiza o espaço complexo como duas quadraturas
reais `H × H` com a norma `L²`, ação escalar complexa e produto interno complexo construído
explicitamente a partir do produto interno real. A instância de `InnerProductSpace ℂ` compila;
`#print axioms` para `RealHilbertComplexification.inner_apply` lista somente os axiomas padrão.

Esse módulo fornece a estrutura de base para estender o multiplicador real e formar sua
resolvente complexa. Ainda falta construir e validar essa extensão do operador, provar a
inversibilidade fora do eixo real, a holomorfia e a expansão local. Nenhum teorema de resolvente
ou propagação foi adicionado nesta etapa.

## Checkpoint D — resolvente complexa fora do eixo real

Em `MomentLogConvexity.lean`, `momentComplexMulX_mem_resolventSet` usa a auto-adjunticidade
no C⋆-álgebra dos operadores contínuos no Hilbert complexo e o teorema de espectro real para
provar que todo `z` com `Im z ≠ 0` pertence ao resolvente do multiplicador. A partir disso,
`momentComplexMulX_one_sub_smul_isUnit` prova que `1-uT` é uma unidade para todo `u` não real,
via a mudança algébrica de parâmetro `z=u⁻¹`.

`momentResolventCoefficient` agora é a compressão escalar de `Ring.inverse (1-uT)`. O vetor
foi colocado no primeiro argumento do produto interno complexo para respeitar a convenção do
Mathlib (conjugado-linear no primeiro argumento) e manter a dependência holomorfa em `u`.
`momentResolventCoefficient_differentiableAt` e
`momentResolventCoefficient_differentiableOn` provam diferenciabilidade complexa em todo o
complemento do eixo real, por composição com a inversão em álgebra de Banach. Os quatro
resultados passam `#print axioms` com somente `propext`, `Classical.choice` e `Quot.sound`.

`momentComplexMulX_pow_unit` e `momentResolventReadout_pow_eq_moment` identificam cada potência
do operador com o momento original. `momentResolventReadout_neumann_term` calcula cada termo da
série operador-valuada, e `momentResolventCoefficient_hasSum_moments` prova que a compressão
escalar soma a série `∑ (h n) u^n` em todo o ball de convergência de Neumann. Isso é uma igualdade
de série convergente com os momentos originais, não apenas uma identidade formal. Os quatro
teoremas novos também passam `#print axioms` com somente `propext`, `Classical.choice` e
`Quot.sound`.

O multiplicador de Hilbert agora é definido pela conclusão direta do multiplicador limitado no
quociente. `momentHilbertMulX_norm_le` transporta a cota para a conclusão usando a igualdade de
norma de `NormedAddGroupHom.completion`; `complexifyMomentOperator_norm_le` transporta a mesma
cota para a complexificação. Ambos passam `#print axioms` com apenas os axiomas padrão.
`momentComplexMulX_mem_neumannBall` prova que `‖u‖ * R < 1` coloca `u` no ball de Neumann,
incluindo o caso degenerado de operador nulo. Assim,
`momentResolventCoefficient_hasSum_moments_of_radius` prova a igualdade convergente

\[
G_T(u)=\sum_{n\ge0}h_nu^n\qquad(\|u\|R<1).
\]

**ABERTO:** obter a cota exponencial H2 para os jets sigma em uma declaração reutilizável e
instanciar com `completedSigmaLogJet`; propagar a EDO até o zero deslocado e extrair a direção
negativa da `sigmaMatrix` original. A prova do limite de norma pela redução da extensão densa
foi substituída pela construção direta por conclusão, que compila.

## Atualização — estimativa H2 e instância da matriz sigma original

**PROVADO:** `completedSigmaLogJet_exponential_bound` em `SigmaZeroObstruction.lean` fornece
constantes `C ≥ 0` e `R > 0` com
`|completedSigmaLogJet d n| ≤ C * R^n` para todo `n`, quando `|d| < 1/2`. A prova deriva a
cota da série de Taylor analítica do log-density, usa a normalização exata dos jets da fonte
original e absorve o fator linear em `n` por uma potência geométrica. Não troca os jets por
outra sequência.

Também está provada a igualdade definicional
`sigmaMatrix d 0 N = hankelMatrix (completedSigmaLogJet d) N`. Assim, a hipótese all-order
`∀ N, (sigmaMatrix d 0 N).PosSemidef` alimenta exatamente H1 para os mesmos jets. O teorema
`completedSigmaLogJet_resolvent_hasSum_of_sigmaMatrix_psd` aplica o resultado geral de D e
mostra que, sob essa hipótese e H2, a compressão da resolvente soma a série complexa original
em todo o disco explícito `‖u‖ * R < 1`.

Os novos teoremas de sigma passaram `#print axioms` com somente `propext`, `Classical.choice`
e `Quot.sound`; os módulos `MomentLogConvexity` e `SigmaZeroObstruction` compilaram com
`-DwarningAsError=true`.

**ABERTO:** identificar a função resolvente com a geradora analítica complexa numa vizinhança
de zero e propagar a EDO até o zero deslocado. Em seguida ainda é necessário extrair uma ordem
finita e uma direção negativa para a `sigmaMatrix` original; a obstrução all-order não está
provada.

## Fechamento da missão — obstrução finita para a `sigmaMatrix` original

**PROVADO:** sob as hipóteses explícitas `γ > 0` e
`completedNativeOperatorCharacteristic (γ : ℂ) = 0`, para todo `d` com
`0 < |d| < 1/4` existe uma ordem finita `N` e um vetor real não nulo `v : Fin N → ℝ` tal que

\[
v^\top\,\texttt{sigmaMatrix}(d,0,N)\,v < 0.
\]

O resultado final é `exists_sigmaMatrix_negative_direction_of_zero`. A prova não pressupõe uma
medida de Hamburger, um operador representante, positividade no centro, nem uma sequência
auxiliar. Sob a hipótese temporária de PSD all-order da matriz original, H1 é transferida para
os mesmos `completedSigmaLogJet`; a cota H2 vem da série analítica da fonte geométrica. O lema
geral `momentQ_X_mul_le` prova a multiplicação limitada por log-convexidade, e os módulos de
momentos constroem o quociente, sua completude, o operador auto-adjunto limitado, a recuperação
de todos os momentos e a resolvente complexa.

`completedSigmaLogJetComplexGeneratingFunction_eq_resolvent_eventually` identifica as duas
somas convergentes dos jets originais perto da origem. A EDO local passa para a resolvente
construída e, por unicidade analítica em um conjunto preconexo, propaga-se ao domínio superior
direito até `γ+id`. A ordem analítica de um zero contradiz a EDO; o caso de ordem infinita é
excluído pelo princípio da identidade e pela não-anulação já provada perto de zero. A paridade
`completedSigmaLogJet_neg` transfere o resultado ao deslocamento negativo. Por fim, a
simetria da matriz e `posSemidef_iff_dotProduct_mulVec` extraem uma direção quadrática
estritamente negativa.

A existência de `γ > 0` com `F(γ)=0` continua como hipótese matemática explícita do teorema,
conforme delimitado na missão; este trabalho não afirma provar essa existência. O resultado
final, porém, atua diretamente sobre a `sigmaMatrix` original e fornece `N` e `v`, em vez de
uma conclusão abstrata sobre um predicado `Pole`.

**ABERTO:** somente a prova independente da existência de um zero positivo `γ`; ela permanece
fora das hipóteses da obstrução condicional solicitada. Não há obrigação pendente nos
checkpoints A–D nem na conclusão condicional sobre a matriz sigma.

**REFUTADO:** nenhuma etapa da construção foi refutada.

**COMPILAÇÃO:**

- `bash research/native-moving-schur-sigma/compile_module.sh MomentLogConvexity` — sucesso com
  `-DwarningAsError=true`.
- `bash research/native-moving-schur-sigma/compile_module.sh SigmaZeroObstruction` — sucesso com
  `-DwarningAsError=true`.
- Os novos resultados passam `#print axioms` com apenas `propext`, `Classical.choice` e
  `Quot.sound`; não há `sorry` nem `admit` nos módulos alterados.

**GIT:** alterações preparadas para publicação na branch `agent/native-moving-schur-sigma`.
