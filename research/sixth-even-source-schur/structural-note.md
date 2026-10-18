# Investigação estrutural all-order: identidade e critério residual

Base auditada: `geometry-of-numbers` em
`7e874fe8b6cfbec4463e5838a60cb359992b99b7`; operador consultado em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Nenhum módulo histórico ou
parâmetro da fonte foi alterado.

## O que já existia

`NativeSourceAllOrderSchur` fornece `sourceMomentSchur_sewing` e
`sourceMomentSchur_critical_direction`. `NativeSourceSchurThetaIntegral`
fornece inclusive `sourceMomentSchur_critical_direction_total`, sem hipótese
de positividade do prefixo, e `nativeSchurThetaPolynomial_integral`.
Estas identidades não são novidades deste estudo.

`CriticalSource.criticalBalance_tendsto` transporta a direção crítica
v=(-A^-1 b,1) ao balanço físico incidente menos retorno, com limite 2 sigma.
`criticalBalance_eq_jordan` conserva os canais positivo e negativo;
`PolarizedCritical.criticalPairing_even_odd_tendsto` e
`criticalPairing_odd_even_tendsto` anulam os cruzamentos mistos somente no
limite. Aqui os nomes estão no namespace `CarryCriticalSource`.

`CarryThetaPattern.sourceSchur_thetaGap` conserva a recorrência e todos os
acoplamentos antigos: c0 F sigma=(d+1) G, d=2n+s, F=4(2d+2)!.
A positividade de `sourceThetaIntegral d` já decorre de
`sourceThetaIntegral_eq_xiMoment` e `sourceThetaIntegral_pos`. Não implica
G>0. O setor par exige J_(2n)>-F C_(0,n); o ímpar exige
J_(2n+1)<F C_(1,n).

A densidade polinomial ímpar original tem cauda negativa em toda ordem:
`nativeSchurThetaPolynomial_odd_density_eventually_neg` e
`nativeSchurThetaPolynomial_odd_not_pointwise_norm_sq` excluem apenas sua
leitura ponto a ponto como quadrado. Não excluem outras representações da
fonte física.

## Extensão variacional nova

`VariationalSchur.lean`, namespace `CarryVariationalSchur`, recebe o prefixo
antigo A, o acoplamento inteiro b e um vetor de tentativa z arbitrário.
Define r=b-Az e E(z)=Q((-z,1)), na mesma forma de momentos. A identidade
exata requer apenas `IsUnit A` (invertibilidade); a coerção e o limite
variacional usam a positividade conhecida do prefixo antigo.

- `sourceTrialEnergy_expansion`: E(z)=c-2 b^T z+z^T A z.
- `sourceTrialResidual_inverse_of_isUnit`: A^-1 r=A^-1 b-z, somente
  invertibilidade do prefixo; `sourceTrialResidual_inverse` especializa à
  hipótese de positividade.
- `sourceTrialEnergy_eq_schur_add_residual_of_isUnit`:
  E(z)=sigma+r^T A^-1 r, somente invertibilidade.
  `sourceTrialEnergy_eq_schur_add_residual` conserva a especialização positiva.
- `sourceTrialResidual_eq_neg_solveResidual` registra que nosso r=b-Az é o
  negativo do residual usual Az-b. `residualQuadratic_neg` prova a invariância
  da forma quadrática sob r -> -r; `residualSquared_neg` conserva também
  r^T r;
  `sourceTrialEnergy_eq_schur_add_solveResidual` dá a identidade literal
  na convenção Az-b.
- `sourceMomentSchur_eq_trialEnergy_sub_residual`: sigma=E(z)-r^T A^-1 r.
- `sourceMomentSchur_lower_bound_of_inverseBound`: se o prefixo é invertível
  e, para todo r, r^T A^-1 r<=M r^T r, então sigma>=E(z)-M r^T r.
- `sourceMomentSchur_lower_bound_of_solveResidual` fornece o mesmo limite
  inferior na convenção usual Az-b.
- `sourceMomentSchur_pos_of_inverseBound`: M r^T r<E(z) é certificado
  suficiente estrito. M não é definido a partir do novo pivô.
- `sourceMomentSchur_le_trialEnergy`: sigma<=E(z). Portanto E(z)>0
  isoladamente tem a orientação insuficiente para provar sigma>0.
- `inverseResidual_bound`: se alpha>0 e alpha y^T y<=y^T A y para todo y,
  então alpha r^T A^-1 r<=r^T r.
  `inverseResidual_le_of_coercive` fornece M=1/alpha para o bound explícito.
- `sourceMomentSchur_pos_of_trialResidual`: a condição sem divisão
  r^T r<alpha E(z) implica sigma>0.
- `sourceThetaGap_pos_of_trialResidual`: transporta esse certificado à
  diferença theta literal, mantendo s:Fin 2 e todos os acoplamentos.

O controle do inverso usa a equação normal A(A^-1 r)=r, a coercividade do
prefixo antigo e a não negatividade de ||r-alpha A^-1 r||^2. Não usa o sinal
do novo pivô, Cholesky do Gram estendido, nem construção retrospectiva de
vetores físicos.

Para z inexato, a condição é conservadora; sua premissa não é simplesmente
uma nova definição equivalente de sigma>0. Ela permite, em princípio,
verificar um solve racional e seu residual sem usar inversão numérica como
estratégia principal. Ainda é necessário certificar alpha, os coeficientes
e a desigualdade estrita a partir da fonte original.

## Limite da conclusão all-order

Não foi obtida uma desigualdade nova da fonte que estabeleça o critério
residual em todas as ordens. Os resultados novos são uma identidade e um
critério suficiente; não são uma prova de positividade global. As estimativas
absolutas de `CompletedNativeLogCoefficientMajorant` e os controles de
`GeneralTails`/`ModeSchedule` não fornecem automaticamente essa margem.

Continuam distintos: caudas tendendo a zero; quadratura suficientemente
precisa; diferença de Schur positiva; retorno contrativo; realização física
coerente; limite de operador. Não se identifica o whitening/Parseval do
frame Green com a ortogonalização Hankel. Nenhum novo retorno de doze fontes,
bloco ímpar 6x6 ou passagem ao limite de operador é afirmado aqui.

## Precisão suficiente e testemunho racional recebido

O testemunho racional e sua identidade de controle de erro motivam a forma
explícita com M. O vetor de tentativa apenas seleciona uma direção na fonte
já definida; não substitui momentos, pesos, métrica ou característica.
A convenção Az-b e a convenção b-Az produzem o mesmo erro quadrático,
como provado no módulo.

Uma tolerância uniforme de 1e-25 é uma condição suficiente grosseira em uma
via perturbativa; não é uma precisão mínima necessária para certificar o
sexto pivô. A via usada no certificado finito da rodada verifica diretamente
as caixas da fonte e a diferença completa, sem derivar obrigação artificial
de refazer quadratura por esse limiar uniforme. A validação desse sinal é
separada dos lemas gerais aqui apresentados. Nenhuma estimativa perturbativa
uniforme de 1e-25 é afirmada por este módulo.
