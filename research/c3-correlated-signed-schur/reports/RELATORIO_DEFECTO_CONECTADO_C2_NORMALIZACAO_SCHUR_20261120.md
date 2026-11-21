# C2 conectado, escala quadrática e Schur nativo

Data: 2026-11-20. Branch: research/c3-correlated-schur-tfvd-20261120.
Estado: provas Lean exatas em uma torre de cutoffs e no-go para uma candidata Gram. Ainda NÃO há prova all-order de positividade nativa.

## 1. Proveniência e fontes reabertas

Ordem original: geometria posicional de profundidade, núcleo, resíduo, centro/pernas, câmeras; depois bracket C2, síntese Genuine, escalar nativo não vestido N, completamento F=A*N, resposta logarítmica e momentos. Não adotar a função zeta como ponto de partida geométrico.

Fontes originais verificadas:
- primos/CPFormal/Carry/C2OddCorePushforward.lean
- primos/CPFormal/Analytic/CpC2OddCorePushforwardTfvd.lean
- primos/CPFormal/Analytic/CpC2DirichletJetTfvd.lean
- geometry-of-numbers/research/native-return-boundary-deflation/{NativeDeflation,ResidualTest,SchurLimit}.lean
- GeometryOfNumbers/Foundation/FoundationalHalfScalingCapstone.lean

Para cada núcleo positivo m, a massa C2 original e finita soma pesos 2^-j das pernas 2^j m-1 e 2^j m+1, para j>=2, quando o ponto não ultrapassa T. O coeficiente unitário a_T(1)=1 é normalizado apenas na função aritmética; nosso cálculo dos vértices ímpares 3,5,9,15,25 utiliza suas massas de pernas reais sem redefinição.

A inversão de Dirichlet ORIGINAL satisfaz b_T * a_T=a_T log. Para p,q primos ímpares distintos, o teorema existente c2OddCoreLogCoefficient_distinct_primes diz:
  b_T(pq)=log(pq)*(a_T(pq)-a_T(p)*a_T(q)).
O teorema existente c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul transporta isso ao canal Dirichlet/TFVD finito.

## 2. Resultado novo, incondicional na torre T_k=60*2^k

Calculado diretamente da massa original e provado em Lean:
  a_60(3)=7/8, a_60(5)=3/4, a_60(9)=1/2,
  a_60(15)=1/4, a_60(25)=0.

A relação de escala já provada no CPFormal é:
  a_(8M)(m)=1/2+1/2*a_(4M)(m) para 0<m<=M.

Aplicando-a às massas acima, obtivemos para todo k>=0:
  a_(T_k)(3)=1-(1/8)*2^-k;
  a_(T_k)(5)=1-(1/4)*2^-k;
  a_(T_k)(9)=1-(1/2)*2^-k;
  a_(T_k)(15)=1-(3/4)*2^-k;
  a_(T_k)(25)=1-2^-k.
A fórmula de 25 exigiu base T=120 própria: em T=60 ela ainda não está no suporte de M=15. A prova em Lean preserva essa exceção e inicia a recorrência correspondente em T=120.

O defeito conectado exato para os primos 3,5 é:
  D_(T_k)(3,5) = a_(T_k)(15)-a_(T_k)(3)*a_(T_k)(5)
               = -(3/8)*2^-k-(1/32)*4^-k < 0.

Então o próprio b_(T_k)(15)=log(15)*D_(T_k)(3,5)<0. Um novo teorema Lean leva esse sinal negativo ao readout ORIGINAL TFVD no parâmetro espectral s=0. É um canal aritmético FINITO, não o Hankel completado F.

## 3. No-go para a Gram candidata

Defina K_T(p,q)=a_T(p)*a_T(q)-a_T(pq), i.e., o negativo do defeito conectado.

Em T=60, as entradas são positivas:
  K(3,3)=17/64, K(3,5)=13/32, K(5,5)=9/16.
Mas o determinante do bloco 2x2 é -1/64<0.

O teorema Lean ALL-K para a torre mostra:
  det K_(T_k)[3,5] = -(1/64)*4^-k <0.

Portanto, inverter o sinal entrada a entrada do conectado NÃO produz uma forma positiva. Isto é um no-go para ESTA escolha natural de Gram; não refuta toda representação positiva possível nem fornece um pivô nativo negativo.

## 4. Profundidade, amplitude 1/2 e assinatura

A compatibilidade geométrica original exige amplitude 2^(-k/2) para massa 2^-k. Comparar uma energia pela amplitude quadrada sugere uma normalização por 2^k.

Para o MESMO kernel aritmético candidato K, os seguintes teoremas Lean valem exatamente:
  2^k*K_(T_k)(3,5)=3/8+(1/32)*2^-k >0;
  det(2^k*K_(T_k)[3,5])=-1/64 para TODO k>=0.

A normalização remove o decaimento escalar, mas não transforma uma matriz indefinida em Gram positiva. Não foi provado que essa normalização do kernel candidato seja o operador completion verdadeiro.

Se apenas o elemento diagonal (5,5) recebe uma correção positiva delta, o determinante normalizado fica não negativo exatamente quando
  delta>=1/(16+2^-k).
O limiar tende a 1/16; provado em Lean, porém exclusivamente para ESSA candidata rank-one. Não atribuir delta à Gamma real.

## 5. Teorema condicional e verificações finitas

O teorema genérico mass_connected_nonpos_of_dyadic_contraction prova que uma função a:N->Q não negativa e antítona cujo duplicado satisfaça
  a(2m)<=2a(m)-1 sempre que a(2m)>0
tem a(pq)<=a(p)a(q) para todos p,q>=2.

Ainda NÃO fechamos essas hipóteses para a massa C2 CONCRETA em todos os cutoffs. Há evidência racional exata:
- 211.250 pares (T,m), T=0..1249, m=1..169: a_T(2m)=max(0,2a_T(m)-1);
- 149.188 cutoffs de mudança de massa para 2.500 pares ordenados p,q=2..51: 138.004 defeitos negativos, 11.184 zero, nenhum positivo;
- 13 níveis diádicos de T=60*2^k reproduzem as identidades Lean.

Isto é teste finito, NÃO prova universal da lei de duplicação ou do sinal dos conectados para qualquer T,p,q. Relatório JSON e script Python reprodutível acompanham esta branch.

## 6. Relação correta com a obrigação nativa

O verdadeiro resíduo físico do Schur, na direção mônica exata, é o limite normalizado de
  ||remainingIncident||²-||nativeOut||².
Os teoremas Lean anteriores isolam a dominância do retorno como hipótese suficiente para a semidefinitude. A não recorrência do completion, já provada separadamente, pode promover PSD a PD em todas as dimensões.

O coeficiente conectado b_T(pq), entretanto, é um número de Dirichlet de frequência multiplicativa. O pivô Schur é uma energia quadrática polarizada da resposta completada F=A*N. A igualdade entre esses dois objetos NÃO foi encontrada. O canal TFVD finito exato NÃO constitui por si uma identificação matricial, tampouco o Green fechado com sinal positivo.

Próximo objetivo genuíno: transportar os átomos primitivos e defeitos de b_T via prime-depth/TFVD até o kernel físico original, computar todos os cruzamentos e a correção Gamma, e demonstrar (caso verdadeiro) a dominância do retorno na direção crítica, uniformemente em coeficientes para cada ordem fixa. Não impor artificialmente retorno=0 na parte nova.

## 7. Reprodução

Novos módulos Lean: C2ConnectedDefectSchurObstruction.lean, C2ConnectedDyadicTowerSign.lean, C2ConnectedDyadicKernelIndefinite.lean, C2ConnectedLogTfvdDyadicSign.lean, C2DepthMassNormalizedSignNoGo.lean, C2DepthRankOneRepairGate.lean, AuditC2ConnectedDepthScale.lean.
Script numerics/c2_connected_depth_scale_exact.py. Evidência evidence/c2_connected_depth_scale_exact.json.
Compilar com -DwarningAsError=true usando CPFormal do checkout carry-c2-source-raw-green, cujo snapshot é 65d50f6. As provas não devem conter sorry ou axiomas extras.
