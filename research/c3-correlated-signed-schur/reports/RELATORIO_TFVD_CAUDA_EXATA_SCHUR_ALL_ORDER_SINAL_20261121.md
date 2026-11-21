# Cauda TFVD exata e sinal all-order — conservação, massas assinadas, Schur

Data: 21/11/2026. Escopo: demonstração geométrica independente, sem pressupor RH. Genealogia mantida: bracket → Genuine → N → F=A*N → −F'/(2F) → momentos → Hankel/Schur.

RESULTADO: novas identidades e equivalências para todas as ordens, auditadas em Lean. A inequação de sinal em toda ordem AINDA NÃO foi provada.

## Fontes originais reabertas
GoN /research/tfvd-bezout-schur-residual/LiteralTfvd.lean — literal_head_tail, literal_four_terms, native_residual_literal_four_terms.
GoN /research/tfvd-bezout-schur-residual/SourceBezout.lean — mixedSourceKernel bilinear, sourceKernel_head_tail.
GoN /research/tfvd-bezout-schur-residual/SourceSchur.lean — Schur crítico e scaling c0².
GoN /research/tfvd-bezout-order-compensation/TfvdBoundaryLaw.lean — repartição material de dois cutoffs e quatro cruzamentos.
GoN /research/c3-correlated-signed-schur/lean/NativeMixedU.lean — transporte de QUALQUER par x,y para source Bézout pelo mixedSourceLift.
CSA /CarrySelfAdjointOperator/NativeSourceThetaGreenTransport.lean — Green exato de qualquer fonte e direção.
CSA /CarrySelfAdjointOperator/NativeSourceSchurThetaMasses.lean — theta positivo MENOS theta negativo; massa ímpar negativa estritamente presente em toda ordem.

## A. Conservação EXATA do Schur crítico

Para s=0 (par) ou s=1 (ímpar), n arbitrário, com prefixo antigo invertível, e dois cutoffs materiais M,P INDEPENDENTES:

  Q_HH(M,P)+Q_HT(M,P)+Q_TH(M,P)+Q_TT(M,P)
    = c0 * nativeSourceSchurRemainder(s,n)
    = c0 * [PositiveThetaMass(P_s,n) - NegativeThetaMass(P_s,n)]
    = c0 * ∫_{0}^{∞} [P_s,n''(u)-P_s,n(u)/4] * thetaTail(u) du.

c0>0 é o primeiro coeficiente original do completion; P_s,n é o polinômio crítico da mesma característica F, e NÃO um polinômio ajustado para positividade.

O total é INDEPENDENTE DE M,P. A mudança de HH ao trocar cutoff é exatamente a mudança OPOSTA da soma HT+TH+TT. Não há erro de cauda ou limite nessa igualdade.

Novos teoremas Lean em NativeExactTailSchurThetaGreenConservation.lean:
nativeCriticalExactFourTerms_eq_nativeSchurRemainder;
nativeCriticalExactFourTerms_cutoff_invariant;
nativeCriticalExactCrossings_compensate_head_change;
nativeCriticalExactFourTerms_eq_thetaMassDifference;
nativeCriticalExactFourTerms_eq_thetaGreenIntegral;
nativeCriticalExactFourTerms_pos_iff_thetaMassDominance;
nativeCritical_odd_negative_theta_mass_nonzero.

## B. Extensão all-order SEM nenhuma inversão/positividade presumida

Em NativeExactTailAllJetSignedMassGate.lean, para QUALQUER N finito, b par/ímpar, x∈ℝ^N, dois cutoffs M,P:

  Q_full(M,P,b,N,x)
    = sourceMomentQuadratic(nativeH,s,N,x)

  Re(Q_full)
    = ThetaPositiveMass(P_s,N,x) - ThetaNegativeMass(P_s,N,x)
    = ∫_0∞ [P_s,N,x''(u)-P_s,N,x(u)/4]*thetaTail(u) du.

A reconstrução inclui todas as quatro cruzadas. O vetor x é transportado pelo mixedSourceLift da matriz Toeplitz da fonte REAL, sem trocar o operador.

Demonstramos em Lean a equivalência em cada N, bem como em TODAS as ordens:

  (∀b,N, Hankel_native(s,N).PosSemidef)
    ↔ (∀M,P,b,N,x, Re Q_full(M,P,b,N,x)≥0)
    ↔ (∀b,N,x, NegativeThetaMass(P_s,N,x)≤PositiveThetaMass(P_s,N,x)).

Essas são EQUIVALÊNCIAS DE OBRIGAÇÃO, não prova de positividade incondicional. Foram certificados:
nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic;
nativeEveryJetExactFourTerms_re_eq_thetaGreenIntegral;
nativeEveryJetExactFourTerms_re_eq_thetaMassDifference;
nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance;
nativeHankel_posSemidef_iff_allExactThetaMassDominance;
nativeBothHankelTowers_allPosSemidef_iff_exactThetaMassDominance;
nativeBothHankelTowers_allPSD_iff_allExactFourTerms_nonneg;
nativeEveryJetExactFourTerms_cutoff_invariant.

## C. No-go de sinal para a identidade algébrica isolada

Em NativeExactTailSignNoGo.lean, um exemplo completamente FORMAL E GENÉRICO (NÃO o C2 original):
  C(u)=1+u, c0=1; H=T=C/2, ambos não nulos, H+T=C EXATAMENTE;
  K_Bezout,par(C)[0,0]=-1;
  (K_HH+K_HT+K_TH+K_TT)[0,0]=-1.

Portanto, a identidade exata preserva o sinal real do todo, mas não obriga o sinal positivo sem propriedades ADICIONAIS da fonte C2 efetiva. Esse toy NÃO refuta sinal do C2 nativo.

Na fonte REAL, CSA prova para toda ordem n:
  NegativeThetaMass(nativeSchurThetaPolynomial 1 n)>0.
Logo não há positividade ponto a ponto no integrando ímpar crítico. O sinal físico depende de uma DOMINAÇÃO global, não de ignorar a contribuição negativa.

## D. Próxima obrigação e ataque recomendados

O que continua aberto é provar, a partir da geometria original (sem RH):
  ∀b,N,x, NegativeThetaMass(P_b,N,x) ≤ PositiveThetaMass(P_b,N,x).

Outra forma independente e possivelmente mais produtiva: identificar um ENTRELAÇADOR exato, polarizado, entre o estado de conservação Bessel material (Primos #34) e o retorno assinado do chiral Cauchy carrier COMPLETADO (CSA #89,#105,#124; GoN #70/#316), em TODOS os vetores, cutoffs, cruzamentos e com Gamma preservada. Se a diferença incidente-retorno virar uma norma de resíduo efetiva, PSD segue; não se pode presumir essa realização.

A positividade da densidade C2 Mellin ou de uma Gram Green separada NÃO implica por si só positividade do kernel assinado do completion. A cauda e as duas pernas já estão EXATAS. Falta uma lei de signo na coerência física.

## E. Validação

Arquivos Lean:
- lean/NativeExactTailSchurThetaGreenConservation.lean
- lean/NativeExactTailAllJetSignedMassGate.lean
- lean/NativeExactTailSignNoGo.lean
- lean/AuditNativeExactTailAllOrder.lean

Comando: validate-native-exact-tail-allorder-vm.sh
Resultado: compilação -DwarningAsError=true exit 0, 20 novas declarações auditadas, axiomas SOMENTE propext, Classical.choice e Quot.sound. Sem RH e sem sorry.
