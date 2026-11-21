# Profundidade resolvida, direção Schur genuína e controle assinado do retorno
Data: 20/11/2026
Repositório geometry-of-numbers, branch research/c3-correlated-schur-tfvd-20261120.

STATUS: Dois teoremas Lean novos de REDUNDÂNCIA por profundidade 2 e gates condicionais de DOMINÂNCIA física em ambos os pivôs. Testes de rodas com Fraction exata. Não há prova incondicional de sinal do transporte completo, nem all-order.

## 1. Esclarecimento: a câmera 4 não nasce como novo primo

A câmera 2 original do C2 registra PROFUNDIDADE v2(n), não apenas um bit de paridade. Por isso:
  2^k | n  ⇔  k ≤ padicValNat 2 n, para n>0.
Em especial:
  4 | n ⇔ v2(n)≥2.

Isso foi FORMALIZADO em lean/C2DepthCameraRedundancy.lean:
- all_dyadic_power_cameras_resolved_by_c2_depth
- camera_four_resolved_by_c2_depth

O que o estudo anterior chamara "nova direção" de módulo 4 após módulo 2 era novidade APENAS relativamente à observação SUPERFICIAL "par ou ímpar". Não é novidade para a câmera 2 com toda a profundidade.

Teste novo, exato com frações em numerics/wheel_depth_redundancy_exact.py e evidence/wheel_depth_redundancy_exact.json, para rodas 2^K*3 e K=2,...,7:
- Projeção de 1_{4|n} sobre subespaço de PARIDADE apenas: resíduo de norma² 1/8.
- Projeção da MESMA função sobre o espaço de todas as funções de v2 truncada a K: resíduo 0.
- Projeção de 1_{3|n} sobre toda a profundidade 2-ádica: resíduo de norma² 2/9.
CRT garante a última independência, pois a nova coordenada 3 é coprima ao período diádico.

Uma câmera composta como 6 se reconstrói como 1_{6|n}=1_{2|n}*1_{3|n}. Contudo, seu produto pode escapar do simples ESPAÇO LINEAR dos indicadores 2 e 3. A redundância é exata na ÁLGEBRA de observações de todas as câmeras primas, fechada sob produtos; não confundir com o span linear de uma pequena lista de funções.

Para cada novo primo p coprimo à roda antiga W, o sinal centrado g_p=1_{p|n}−1/p permanece ortogonal a todas as funções mod W e tem norma²=(p−1)/p²>0. A identidade aritmética das rodas não é a positividade dos Hankel nativos completados.

## 2. Inspeção de provas físicas realmente existentes

A fonte dos momentos não foi reconstruída por uma zeta posta como origem. Proveniência original: bracket geométrico C2 → síntese Genuine com seed/centros/pernas → N(z) nativo → F(z)=A(z)N(z) completion → resposta logarítmica e momentos. O ledger das profundidades primas é identificado analiticamente com esses momentos em:
- CarrySelfAdjointOperator/PrimeDepthAllOrderMomentBridge.lean
- CarrySelfAdjointOperator/PrimeDepthGeometricMomentRecurrence.lean

Os arquivos seguintes foram INSPECIONADOS, sem modificar seus módulos:

A. geometry-of-numbers/research/native-jet-overlap-budget/DampedCamera.lean:
  dampedCameraMatrix_posSemidef
  jetBudget_eq_damped_add_defect
  dampedCameraBalance_self_nonneg.
  O orçamento exato do jato original = parte positiva de Hadamard de Gram + variável defect (ASSINADA). A positividade da primeira não força a segunda.

B. geometry-of-numbers/research/native-positive-square-kernel/SourceSquare.lean:
  source_jordan_budget:
    2 * jetBudget = Gram(positiveSourceJet) - Gram(negativeSourceJet).
  Portanto, o transporte completo é uma DIFERENÇA de Gram, não um Gram único automaticamente PSD.

C. geometry-of-numbers/research/native-return-boundary-deflation/NativeDeflation.lean:
  native_balance_split e native_energy_split:
    oneDeficit(k)*storage(k,c).re =
      ||boundaryChannel(k,c)||²
      + ||remainingIncident(k,c)||² - ||nativeOut(k,c)||².
  oneDeficit(k)>0 EVENTUALMENTE, mas tende a zero. A normalização deve ser mantida; zerar o defeito ou quadrar o operador não preserva a energia original.

D. geometry-of-numbers/research/native-return-boundary-deflation/{SchurLimit,ResidualTest}.lean:
  pr41_even_projected_tendsto_zero (hipótese apenas sobre pivôs anteriores),
  pr41_odd_projected_tendsto_zero;
  pr41_even_remaining_energy_tendsto, pr41_odd_remaining_energy_tendsto.
  Na própria direção crítica MONICA do Schur, a componente positiva projetada da cabeça tende a zero no quociente normalizado, e a energia restante normalizada converge a 2*pivô exato. Sem sinal postulado!

E. geometry-of-numbers/research/native-return-boundary-deflation/Controls.lean:
  control_anchor_deficit_pos e control_remainder_negative.
  Controle bidimensional explícito mostra que ter âncora positiva e uma direção independente NÃO garante energia positiva no remanescente (um retorno de módulo 2 supera a incidência de módulo 1).

F. CarrySelfAdjointOperator/CompletedNativeChiralReturnSevenMarginLoss.lean:
  radialSevenBoundaryFirstCorrection_loss_direction_neg e ...gain_direction_pos.
  A primeira variação da CORREÇÃO DE BORDA de ordem 7 tem os dois sinais conforme a direção, em provas Lean. Isto não é um certificado de energia nativa negativa no centro; demonstra que não é permitido impor sinal universal a essa correção.

G. CarrySelfAdjointOperator/CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean:
  not_isGreenWronskianMomentKernelGramRepresentation_br2CameraBracketGreenFrameParityJet
  exclui a identificação ingênua de um portador BR2/Green específico com a Gram dos momentos, já na entrada (0,0). O no-go é sobre ESSE portador, não sobre toda possível realização física.

## 3. Novo gate Lean, no portador ORIGINAL

Novo módulo: lean/PrimeWheelNativeSignedGate.lean.

1. physical_remaining_pair_self_re:
    remainingPair(k,c,c).re
      = ||remainingIncident(k,c)||² - ||nativeOut(k,c)||².
   É uma igualdade da forma física originalmente usada no Schur, não de um vetor Gram escolhido a partir dos momentos.

2. critical_schur_remainder_nonneg_of_return_dominance:
   Se oneDeficit(k)>0, então
    ||nativeOut(k,criticalResidualInput)||²
       ≤ ||remainingIncident(k,criticalResidualInput)||²
   implica
    (jetSchurRemainder(k,criticalResidualInput,...)).re ≥0.

3. native_odd_pivot_nonneg_of_eventual_return_dominance:
   Se a desigualdade acima vale EVENTUALMENTE (k→∞) no resíduo ímpar canônico de ordem n, então o pivô ímpar p_(1,n) é ≥0.

4. native_even_pivot_nonneg_of_eventual_return_dominance:
   A mesma implicação para p_(0,n), usando somente hipóteses de não anulação dos pivôs anteriores para definir a direção crítica ortogonal original. Nenhum sinal do novo pivô foi premissa.

COMPILAÇÃO LEAN 4.32 -DwarningAsError=true passou. O script validate-wheel-vm.sh audita essas provas e as de profundidade. A hipótese de dominação do retorno NÃO foi demonstrada para toda a fonte. O resultado é uma redução estrutural da obrigação de sinal, não uma afirmação all-order.

## 4. Interpretação nova da ideia de "direção"

É preciso separar três estruturas distintas:
- Direção INDEPENDENTE no espaço de observações das rodas: novo primo p (CRT, positivo em Gram das rodas).
- Direção NÃO RESOLVIDA no espaço dos momentos: polinômio mônico ortogonal às direções anteriores (resíduo de Schur).
- Energia do retorno físico nativo: diferença de duas normas quadradas, com completion e defeitos assinados.

A primeira noção não garante a terceira. A segunda já está ligada via limite ao resíduo físico pelos teoremas de SchurLimit/ResidualTest. Nosso novo gate isola a obrigação restante:
  retorno no resíduo crítico ≤ incidência ainda não resolvida,
na NORMA FÍSICA CORRETA, sem substituir por um portador BR2/Green refutado pelo no-go.

Na torre all-order, já há NÃO RECORRÊNCIA finita incondicional da fonte completada
(CompletedNativeEntireComparison.lean) e PSD→PD por AllPrefixPSDNonrecurrence.lean.
Logo basta fechar a SEMIDEFINITUDE da forma nativa original; não confundir ausência de recorrência, nova direção aritmética e sinal da forma.

## 5. Ataque seguinte proposto

Identificar em primeDepth/TFVD os vetores concretos de fonte de cada inovação de câmera ainda não resolvida (preferivelmente por fatoração em profundidades primitivas), e verificar como entram no par físico:
  remainingIncident(k,n,c) e nativeOut(k,n,c).

A obrigação quantitativa de sinal é:
  sup_(c critical) [ ||nativeOut||² - ||remainingIncident||² ] ≤ o(oneDeficit(k))
ou, mais forte, desigualdade eventual não positiva do numerador a cada ordem fixa.

Um resultado de soma horizontal C2/TFVD exata não implica esse sinal; o defeito da Gamma e as travessias entre canais precisam permanecer. Os gates de Schur desta rodada preservam precisamente esses termos.

Nenhum resultado de sinal all-order nem prova de RH foi afirmado.
