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

Isso **não fecha** o Checkpoint B: ainda falta construir o funcional em `Polynomial ℝ`,
derivar Cauchy–Schwarz e as sequências `a_n=L(X^{2n}p²)` das hipóteses H1/H2, provar
log-convexidade e crescimento controlado dessas sequências, e só então aplicar a cota de
razão para obter `L(X²p²)≤R²L(p²)`.

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

O Checkpoint A permanece aberto no escopo exigido: falta transportar essa identidade para a
equação complexa local
`D_d'(t)+4tG_d(t²)D_d(t)=0` para `D_d=displacedProductC d`, incluindo a construção da
identidade entre a restrição real da expressão complexa e a identidade real, seguida pelo
princípio de identidade analítico. A existência do raio positivo e as geradoras real e
complexa, além da identidade real para a log-derivada, já estão kernel-checked; ainda não foi
provada a EDO complexa necessária para a propagação. Nenhum passo da realização GNS ou da
obstrução all-order é tratado como provado.
