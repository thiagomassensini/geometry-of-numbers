# Auditoria do all-order — genealogia C2, TFVD/Bézout, Pick e orçamento de retorno
Data 2026-11-21. Todas as conclusões dizem respeito à fonte original bracket -> Genuine -> N -> F=A*N -> R=-F'/(2F) -> momentos -> Schur. NÃO ASSUMIR RH.

## Inventário de PRs efetivamente reabertas

### PRIMOS
#30 MERGED: persistência estrutural das câmeras.
#34 MERGED: norma da provenance state = soma quadrática de Bessel da fonte seeded TFVD. A identidade de Pitágoras para um estado x requer a hipótese de realização hrealizes; não a identificar automaticamente com o signed completed chiral carrier.
#43 MERGED: G_pre, fonte material finita, sem positividade global do Green.
#47 MERGED: profundidade prima/von Mangoldt e relógio; identidade multiplicativa não implica sinal Hankel.
#51 MERGED: a primeira escala de tilt domina a cauda da mesma torre, rho²=243/250<1, somente fora da meia abscissa. NÃO controla o carrier/seed.
#52 MERGED: soma seed+tilt+carrier = fator câmera * Genuine. A não compensação carrier/seed fora da meia abscissa é EQUIVALENTE a forte não anulação Genuine e não pode ser assumida como lemma de positividade sem circularidade.

### GEOMETRY OF NUMBERS
#41 MERGED: ortogonalização e direção crítica sem sinal pressuposto.
#70 MERGED: identidades Bézout/TFVD, incluindo quatro cruzamentos fonte-head-tail e limite finito.
#131 MERGED: controle de cauda nativa em famílias de tamanho FINITO N arbitrário, com M->infinity a N FIXO; não implica margem positiva em toda ordem.
#143–145 MERGED: head/tail e fonte até terceira direção, gate assinado explícito.
#152 MERGED: fonte C3 completada e prefixo ímpar.
#316 MERGED: atualização rank-one afim do último coeficiente m=2n+1 ou 2n+2, invariância do prefixo e acoplamentos anteriores, transporte para Schur e head/tail TFVD.
#323–324 MERGED: terceira direção correlacionada e cofactor quiral na fonte original.
#329 MERGED: PosDef rigorosa da quarta matriz de ambos setores a partir da fonte C3 original.
#331–333 OPEN: transporte C2/Schur/Green certificado até n=6 por H6/K6 FINITOS. A hipótese do n-ésimo prefixo é um certificado de dimensão limitada; não é all-order. #332 isola defeito quartico transversal, também condicional.

### CARRY SELF ADJOINT
#67 MERGED: relógio log e comutador. #89 MERGED: dois canais Jordan assinados. #105 MERGED: repartição em três setores e correção Gamma/Green.
#111 e #120 MERGED: PSD all-order + não recorrência finita incondicional => PD all-order.
#114 MERGED: cancelamento do polo comum antes do jato.
#116–117 MERGED: pernas C2 e erro da cauda na fonte física original. #118–119 OPEN: transporte central-leg para energia de bordo, depois Jordan.
#122–123 MERGED: Wronskiano da cauda e repartição par.
#124 MERGED: HasNativeSourceAdditiveReturnBudget implica todos Hankel PosDef. Sua hipótese é: para cada ordem n existe erro e_n(k)->0 e todos coeficientes x satisfazem norm(return)^2 <= norm(incident)^2 + e_n(k)*norm(x)^2. Gate do orçamento multiplicativo exige eta_n(k)*operatorNormBudget_n(k)->0; eta_n->0 sozinho não basta.
#125–126 OPEN: igualdade crítica C2/Jordan/Green. Green estritamente positivo por extendedPrefix.PosDef é apenas consequência da positividade finita assumida, não uma fonte independente de sinal.
#127 OPEN: fonte C2 hiperbólica positiva via Mellin identificada à série dos brackets com fator Gamma no semiplano indicado. Esta fonte escalar não é automaticamente a medida dos momentos de F completada.

### MOMENTOS
#2 MERGED: evidência/certificados finitos e experimentos de Padé, slope, transversalidade.
#3 OPEN: investigação de curvatura, Jacobi, microescala, Green, C2. Não há lá um certificado all-order nativo independente que possa ser importado como premissa.

## Novo teorema Lean: bootstrap head/tail para TODAS as dimensões

Arquivo lean/AllOrderTfvdHeadMarginBootstrap.lean.
Definição HasNativeAllOrderTfvdHeadMargins:
  para cada n e cada setor b, existem cutoff M e tolerância epsilon>=0 tais que
  abs(Re(literalTail(M,m))) <= epsilon
  e
  J_n(b) - m*c0*Re(literalHead(M,m)) > m*c0*epsilon,
  onde m=2n+1 se b=false; m=2n+2 se b=true;
  J_n(b) = sourceSchur(nativeC com APENAS coeficiente c_m zerado,b,n).
Todas essas quantidades são do objeto literal TFVD e da sequência nativeC da característica completada ORIGINAL, sem presumir momentos positivos ou zeros.

Identidade já provada na PR #316:
  sourceSchur(nativeC,b,n)=J_n(b)-m*c0*nativeC(m)
e a decomposição de #70/#316:
  nativeC(m)=Re(literalHead(M,m))+Re(literalTail(M,m)).
Assim a margem positiva na cabeça supera a contribuição POSSIVELMENTE NEGATIVA da cauda.

O novo theorem nativeSourceSchur_pos_of_allOrderTfvdHeadMargins prova:
  HasNativeAllOrderTfvdHeadMargins -> para todo b,n sourceSchur(nativeC,b,n)>0.
A indução com a lei original sourceSchur_eq_scaled e o critério do CSA sourceMomentMatrix_succ_posDef_iff prova:
  nativeCanonicalAllOrders_posDef_of_tfvdHeadMargins:
  para todo b,n, sourceMomentMatrix(nativeH, if b then 1 else 0,n).PosDef.
Os dois setores são precisamente os H_n e K_n canônicos dos momentos COMPLETADOS.

O theorem nativeBoundary_all_orders_strictly_positive_of_tfvdHeadMargins leva o mesmo gate à energia ORIGINAL de bordo para cada dimensão positiva 2n.

Esses teoremas COMPILARAM com -DwarningAsError=true, e a auditoria #print axioms mostrou apenas propext, Classical.choice, Quot.sound. NÃO SE PROVOU HasNativeAllOrderTfvdHeadMargins.

## Próxima obrigação real e critério para não cair em circularidade

Rota A: demonstrar de C2/TFVD as margens head-tail em CADA ordem (quantificador forall n exists M_n,epsilon_n; M UNIFORME em n não é necessário). GoN #131 fornece o controle da cauda a n fixo; #316 fornece o último-coeficiente, mas falta head-margin positivo geral. Testar primeira ordem maior que os prefixos H6/K6 já certificados, mantendo cutoffs e pesos originais.

Rota B: provar o orçamento additivo de retorno do CSA #124 POR MEIO do estado de Bessel Primos #34, construindo ENTRELAÇADOR exato material -> carrier COMPLETADO F e provando o controle dos canais assinados. Sem essa identificação, soma quadrática Bessel não certifica retorno contrativo.

Rota C: provar a matriz chiral Pick PSD eventualmente para TODO N da fonte COMPLETADA, preservando todos cruzamentos. O CSA já prova que esse gate leva aos dois Hankel PSD; nossas formalizações anteriores provaram o caso de duas direções no resto físico e TFVD de seis canais sem RH.

A lei da escala 1/2 controla a magnitude, não substitui as margens. A candidata de Gram construída apenas do negativo do defeito conectado C2 é indefinida até em 2x2 (certificada em nossa pesquisa), inclusive após normalização diádica. Não construir uma Gram artificial.

Prova de RH externa: APENAS métodos e intuições sobre determinação, variância e resto; nenhuma declaração da prova externa é hipótese deste bootstrap. Não confundir positividade da densidade Mellin original com a energia da derivada logaritmica de F.

## Auditoria
Compilação: lean -DwarningAsError=true, módulo AllOrderTfvdHeadMarginBootstrap.lean.
Auditoria: AuditAllOrderTfvdHeadMarginBootstrap.lean, quatro declarações com axiomas-padrão.
Dependência do SOURCE TFVD/Bézout GoN #316 no cache compilado Lean v4.32 de tfvd-bezout-order-compensation-20261110. O resultado é condicional à margem geométrica realmente ainda aberta, não incondicional.
