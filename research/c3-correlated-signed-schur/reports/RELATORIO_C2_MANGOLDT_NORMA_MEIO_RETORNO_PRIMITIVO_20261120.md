# Profundidade C2, átomos de Mangoldt e variação não nula do retorno nativo
Data: 20/11/2026
Status: NOVOS TEOREMAS LEAN 4.32 + exemplos intervalares Arb, com obrigação all-order de sinal ainda ABERTA.

## 0. Fronteiras de proveniência
- Geometria posicional (profundidade, centros, pernas e câmeras) vem ANTES de zeta.
- O bracket é a segunda diferença local; Genuine sintetiza seed+centros+pernas; N é o escalar nativo NÃO vestido; F=A*N é a característica COMPLETADA.
- Os momentos vêm da resposta logarítmica de F e NÃO de uma medida positiva previamente imposta.
- As caixas dos 100 momentos e a Gram de rodas não são fontes substitutas de F.

## 1. Compatibilidade quadrática e escala 1/2, provada anteriormente
A formulação original em GeometryOfNumbers/Foundation/FoundationalHalfScalingCapstone.lean demonstra, sob o modelo discreto e a hipótese EXPLÍCITA de compatibilidade quadrática de escala, que expoente formal =1/2 é a única solução. A massa vertical é b^(-k) e a amplitude compatível b^(-k/2). Não deriva a semidefinitude dos jatos de F nem qualquer propriedade dos zeros. A norma seleciona a escala; não controla sozinha a assinatura do kernel completado.

## 2. Decomposição multiplicativa reversível = a mesma informação do ledger
Arquivos já existentes:
- primos/CPFormal/Analytic/CpNativeCarryMobiusLogDerivativeGuardrail.lean
- carry-self-adjoint-operator/CarrySelfAdjointOperator/PrimeDepthTfvdLogJetCrosswalk.lean
- carry-self-adjoint-operator/CarrySelfAdjointOperator/PrimeDepthGeometricMomentRecurrence.lean
- carry-self-adjoint-operator/CarrySelfAdjointOperator/PrimeDepthAllOrderMomentBridge.lean

As identidades existentes são:
   log(n)=sum_{p|n} v_p(n) log p = sum_{d|n} vonMangoldt(d)
   vonMangoldt = log * moebius
   vonMangoldt * zeta_arithmetic = log
   L(vonMangoldt,s)= -zeta'(s)/zeta(s) para Re(s)>1.
Aqui zeta_arithmetic é a função aritmética 1 sob a convolução de Dirichlet; a última igualdade com a função analítica de Riemann vale SOMENTE na região declarada. Não substituir uma pela outra sem passagem.
O lambda de von Mangoldt é suportado em POTÊNCIAS PRIMAS; cada p^j contribui log p. A divisibilidade v_p(n) conta quantas potências de p dividem n. Isto explica a equivalência de ambas as somas sem excluir as profundidades já herdadas.

Novo teorema Lean em lean/PrimeDepthMangoldtBracket.lean:
   primeDepthLogLedger_eq_mangoldt_divisorSum
A equivalência agora é expressa diretamente com o objeto de ledger do próprio CSA, sem escolher zeta como premissa.

## 3. A incidência centro/pernas da parte primitiva tem sinais exatamente opostos
Novo módulo Lean: lean/PrimePowerLegCenterIncidence.lean.

Definição do átomo de um divisor d:
   B_d(c) = 1_{d|c-1} - 2*1_{d|c} + 1_{d|c+1}.

Para d>=2 e d|c, Lean demonstra B_d(c)=-2.
Para d>=3, se d divide EXATAMENTE uma perna, Lean demonstra B_d(c)=+1. A hipótese "exatamente" é consequência automática de d>=3 e da distância 2 das pernas.
Essas provas são puramente posicionais/aritméticas, válidas para átomos d de prime powers, sem conversão em uma matriz Gram.

O ganho conceitual: a mesma informação multiplicativa, quando lida como perna, possui coeficiente positivo; quando lida como centro, negativo. "Nova direção prima" em q<p continua perna local do stencil de q, mas seu número não ser um centro q não implica assinatura positiva da soma dos stencils.

Importante: C2 tem semântica particular de centros de profundidade >=2. Para afirmações de incidência de uma câmera Cp, respeitar a escolha original de centros e cutoffs. O teorema B_d(c) é local, não identifica sozinho os centros válidos em cada carta ou o Genuine global.

## 4. O saldo do bracket logaritmo é NEGATIVO

Novo lean/PrimeDepthMangoldtBracket.lean:
   c2PrimeDepthLogBalance_eq_mangoldt_resolution
   c2PrimeDepthLogBalance_eq_integerLog
   c2IntegerLogBalance_neg
   c2MangoldtLegCenterBalance_neg

Para todo c>=2:
   [sum_{d|c-1} Lambda(d)] - 2 [sum_{d|c} Lambda(d)] +
     [sum_{d|c+1} Lambda(d)]
   = log(c-1)-2log(c)+log(c+1)
   = log(1-1/c^2)<0.

Logo a contribuição total da DIREÇÃO LOGARÍTMICA não é positiva só porque as pernas entram com +1 e os átomos Lambda(d) são não negativos. A norma quadrática e a diferença centrada são operações distintas.

Contraste formal: para perfil 1/n no centro 5,
   1/4-2/5+1/6=1/60 >0.
Isto captura a dependência funcional da segunda diferença.

Exemplos de controle intervalar usando python-flint Arb 110 dps:
  Perfil                    C2 centro5        Cp5 centro5, raios1 e2
  n^(-1/2)               +0.01382109946      +0.07470865066
  log(n)*n^(-1/2)        -0.01489511031      -0.08465113681
  log(n)                 -0.04082199452      -0.21517538167

O bracket com log(n)*n^(-1/2) é o derivado em sigma, COM sinal trocado, do bracket com n^(-sigma), mas NÃO é automaticamente a resposta logarítmica da característica completada F. A passagem para -F'/F envolve quociente e A(z), além dos seed/centros/cutoffs. Os exemplos não provam pivô negativo.

Numerics: numerics/mangoldt_leg_center_arb_canaries.py; evidence/mangoldt_leg_center_arb_canaries.json.

## 5. A resposta física COMPLETADA: retorno depois de subtrair a cabeça velha

Código original já inspecionado:
geometry-of-numbers/research/native-return-boundary-deflation/NativeDeflation.lean:
  nativeOut(k,N)c = radialReturnedSynthesis(k,N)c - oneReturn(k)*radialIncidentSynthesis(k,N)c.
A retorno real é a síntese com o quociente de Hermite-Biehler de F, não um simples projetor aritmético.

Novo lean/NativeReturnPrimitiveVariation.lean:
  quotientVariationCoefficient
  nativeOut_eq_quotientVariation
  quotientVariationCoefficient_zero.

A identidade física exata é:
   nativeOut(k,N)c = sum_{i<N} c_i [Q(z_{k,i})-Q(z_{k,0})] phi_{k,i}
onde phi são os features originais Cauchy de norma Hilbert, Q é o quociente quiral COMPLETADO e z são os pontos originais z_{k,i}=i*(i+1)/(k+1).
A cabeça antiga i=0 realmente cancela, sem alterar a métrica, mas as demais direções percebem a VARIAÇÃO de Q.

A igualdade foi compilada em Lean; NÃO foi construída usando os momentos como entrada.

## 6. Derivada logarítmica completada FORCE o retorno não trivial
Preexistente em CompletedNativeCentralChiralQuotientCurvature.lean:
   Q'(0) = -4*i*h0,
h0=canonicalCompletedNativeLogDerivativeMoment 0 >0, já certificado incondicionalmente.

Novo lean/NativeReturnNontrivialDerivative.lean:
 - nativeRadialSourceCurvature_eq_four_zerothMoment
 - nativeSampleGapRatio_eq_tangent_difference
 - nativeSampleGapRatio_tendsto_zerothMoment
 - nativeSampleQuotient_second_ne_first_eventually
 - nativeOut_second_source_eventually_nonzero.

Como z_(k,0)=i/(k+1) e z_(k,1)=2i/(k+1),
   (k+1)[Q(z_(k,1))-Q(z_(k,0))] -> 4*h0 >0.
Assim, para k suficientemente grande,
   nativeOut(k,2) (e_1) ≠ 0.
O teorema usa a própria fonte física + derivada de F, NÃO um retorno construído para um Gram de momentos. A nova segunda direção original NÃO tem o retorno inteiro anulado pela subtração da cabeça anterior.

Isso REFUTA a leitura literal "o retorno só pode atingir a parte herdada", nesse modelo físico de jatos. Não estabelece energia negativa, nem é uma afirmação sobre uma câmera primo específica: e_1 é a segunda coordenada do grid RADIAL, não a câmera p=3!

### Dedução quantitativa sugerida para posterior formalização (AINDA NÃO TEOR. LEAN)
O quociente central Q(ih)=-1+4*h0*h+o(h), h=1/(k+1).
Logo oneDeficit(k)=1-|Q(ih)|²=8*h0*h+o(h).
O feature phi_(k,1) tem norma²=(k+1)/4=1/(4h).
O gap Q(2ih)-Q(ih)=4*h0*h+o(h).
Isso sugere, usando as identidades exatas de norma e os limites:
   ||nativeOut(k,2)e1||² / oneDeficit(k) -> h0/2 > 0.
Essa dedução não tem formalização Lean própria neste commit; requer levar os termos o(h) pelos quocientes e multiplicações. Importante: se confirmada, a perda do retorno no canal e1 NÃO desaparece ao normalizar pelo mesmo fator do Schur.
Ainda não afirma a razão sobre a direção MÔNICA crítica, que é outra combinação de e_i.

## 7. Positividade all-order: exata fronteira
Na branch prévia foi formalizado:
 - residual físico de Schur = ||remainingIncident||² - ||nativeOut||²;
 - gate condicional por dominância do retorno no resíduo crítico de ambos os setores;
 - não recorrência finita de h_n incondicionalmente;
 - PSD em todos os prefixos + não recorrência ⇒ PD em todos.

Portanto a obrigação REAL é:
  ||nativeOut(k,n,criticalResidual)||²
  ≤ ||remainingIncident(k,n,criticalResidual)||² + erro_tolerado
com erro_tolerado / oneDeficit(k) → 0, uniformemente nos vetores caso se pretenda PSD global.

Se a desigualdade mais forte eventual ≤ for provada para cada pivô, as provas de Gate existentes dão p≥0 (e via torre inteira PSD+não recorrência, p>0). O novo teorema de não anulação do retorno impede que simplesmente se imponha nativeOut=0 sobre a "parte nova".

O próximo ataque é estimar a variação Q(z_i)-Q(z_0) na NORMA Cauchy (incluindo todos os cruzamentos) em relação à norma da incidência residual, sem confundir positividade local de f_s com assinatura da forma completada e sem descartar a correção de Gamma.

Não foi provada uma medida positiva all-order nem RH. O objetivo central é a semidefinitude da fonte completada, não a propriedade dos zeros.
