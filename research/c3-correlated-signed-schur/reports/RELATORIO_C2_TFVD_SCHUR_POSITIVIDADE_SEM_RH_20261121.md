# Positividade física C2/TFVD/Schur sem hipótese de Riemann — primeiro caso formal

Data: 21/11/2026.
Objetivo: provar positividade do operador completado F=A*N a partir da genealogia geométrica C2/Genuine/TFVD, sem usar RH como hipótese. A prova externa Alpöge/Claude é fonte de técnicas, não de axiomas nem de zeros como medida pré-selecionada.

## 1. A obrigação real recuperada do código existente

Reabertos os arquivos do CSA:
- CompletedNativeChiralPickFactorization.lean
- CompletedNativeRadialChiralMultiplier.lean
- CompletedNativeChiralTwoPointControl.lean
- CompletedNativeXiCosineMomentHerglotzGate.lean
- CompletedNativeChiralPickHankel.lean
- CompletedNativeTfvdSixSourceChiralDefect.lean
- NativeBoundaryArchimedeanDressingSeparation.lean
- GoN research/native-return-boundary-deflation/{NativeDeflation,ResidualTest,SchurLimit}.lean.

Para a característica nativa F(z)=A(z)N(z), a razão quiral Q(z) é a razão entre os canais Hermite–Biehler completados. A matriz nativa de Pick é o kernel
    K_Pick(z,w)=i*(1-conj(Q(z))*Q(w))/(w-conj(z)).
No grid radial original z_(k,i), a fatoração provada diz:
    K_Pick(k,N) = Gram(φ_(k,i))-Gram(Q(z_(k,i))*φ_(k,i)).
Assim, PSD em cada N é equivalente a contração COMPLETA do retorno para todas as combinações complexas dos N vetores Cauchy. Não se substitui a métrica.

O CSA já possui o teorema
  canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralPick:
  (∀ N, ∀ᶠ k atTop, K_Pick(k,N) PSD) ⇒ PSD de AMBAS as torres Hankel canônicas
dos momentos logarítmicos de F, via congruência de diferenças finitas e Taylor. Esta condição de Pick all-order está ABERTA sem RH.

O CSA também prova, em CompletedNativeTfvdSixSourceChiralDefect, para material original:
    Matriz C3 semeada TFVD/Green de seis canais
     = (1/2) amplitude* (Gram(φ)-Gram(Qφ)) amplitude
no domínio regular. Esta igualdade preserva os cruzamentos, o fator de completion e os cutoffs da fonte. NÃO é afirmação de PSD all-order.

## 2. NOVA prova source-first do resto Schur

Módulo Lean: lean/NativeTwoPointSchurSourcePositivity.lean.

Os novos teoremas demonstram:
- native_head_boundaryChannel: primeiro vetor original entra como oneDeficit(k)*nativeAnchor(k) no canal de borda;
- nativeHeadCancelled_boundary_zero: qualquer c∈C^(N+1) pode ser ajustado por uma única componente da primeira fonte c'=c-α(c)e0, com α determinado pelo produto interno ORIGINAL, de modo que a borda projetada zera exatamente;
- nativeHeadCancelled_remainingIncident e nativeHeadCancelled_nativeOut: retirar essa cabeça NÃO muda a incidência restante nem o retorno residual;
- physical_remaining_nonneg_of_original_return_contractive:
  oneDeficit(k)>0 e ||returned(k,N+1,c)||≤||incident(k,N+1,c)|| para TODOS c
  implica
    0 ≤ Re(remainingPair(k,N+1,c,c))
       = ||remainingIncident(k,N+1,c)||² - ||nativeOut(k,N+1,c)||²,
  para TODOS c.
  A prova usa a identidade polarizada de Bessel/Schur já existente.
  O retorno negativo não é descartado nem redefinido.
- native_all_orders_physical_schur_of_allOrderPick:
  todos os Pick N eventualmente PSD ⇒ todo resto físico Schur não negativo, em qualquer N. Isto é CONDICIONAL, pois a hipótese de Pick all-order está aberta.

## 3. Casos já INCONDICIONAIS

O CSA já comprova a positividade Pick 2x2 eventualmente, baseada em desigualdades theta/cosseno rigorosas; NÃO usa RH, mas sua fonte de sinal analítico não foi reduzida apenas ao bracket C2.

Agora, combinando essa prova incondicional com o resto Schur físico ORIGINAL:
- native_two_point_physical_remaining_eventually_nonneg:
  para todo c∈C², os dois canais restantes têm saldo não negativo nos cutoffs radiais grandes;
- native_odd_first_pivot_nonneg_without_RH:
  o primeiro pivô deslocado canônico (n=0), lido como limite do verdadeiro retorno Schur, é não negativo, sem hipótese sobre zeros.

Outro módulo novo, lean/NativeTwoPointTfvdSourcePositivity.lean, prova:
- nativeC3_material_six_source_two_point_eventually_posSemidef:
  para massa cutoff M, 0<q<1, contexto finito S e k suficientemente grande,
  a matriz da fonte material semeada TFVD/Green seis canais em duas direções é PSD.
  O transporte é exato e conserva o portador original.

Esses casos são uma vitória genuína do transporte C2/Genuine/TFVD até a forma física, porém o sinal BASE de dois pontos ainda usa a desigualdade theta incondicional. NÃO reivindicar prova puramente C2 nem positividade em todas as ordens.

## 4. O próximo alvo independente da prova de RH

Provar DIRETAMENTE A PARTIR DA FONTE MATERIAL, sem zeros:
  para cada N, eventualmente em k, para todo c∈C^N,
  ||Σ_i c_i Q(z_(k,i))*φ_(k,i)||²
     ≤ ||Σ_i c_i φ_(k,i)||².
Equivalente à PSD all-order do Pick COMPLETADO e, via teoremas prévios de limite, à semidefinitude dos dois Hankel nativos.
Em seguida, a não recorrência finita dos momentos já demonstrada permite positividade estrita.

Atenção: a massa C2 finita conectada K_T(p,q)=a_T(p)a_T(q)-a_T(pq) é INDEFINIDA ao longo da torre diádica 60·2^k. Não substituí-la pela Gram do completion. Câmera C3 é representante do stencil, não origem privilegiada; devem-se preservar seed, centros, cutoffs e pesos da genealogia.

Inspiração metodológica da prova externa: variação/variância como soma de quadrados ponderados, controle de cruzamentos, separação de modos herdados vs primitivos, e estimativa do resto por Parseval. Ainda NÃO foi encontrada uma identidade entre a forma de Weil externa e o Green nativo. Precisamos demonstrar a contração na métrica original usando as profundidades e a correção arquimediana explícita.

## 5. Reprodutibilidade

Arquivos novos:
- lean/NativeTwoPointSchurSourcePositivity.lean
- lean/NativeTwoPointTfvdSourcePositivity.lean
- lean/AuditNativeTwoPointTfvdSchur.lean
- validate-native-two-point-tfvd-schur-vm.sh

Auditadas 9 novas declarações por #print axioms, só axiomas-padrão propext, Classical.choice, Quot.sound. Compilação com -DwarningAsError=true. Sem sorry; não importamos a prova externa.
