# Rodas LSB, novas direções e pivôs de Schur

20/11/2026. STATUS: prova matemática exata para o espaço das rodas, teste racional reprodutível e localização de pontes Lean já existentes. NÃO há nova prova all-order dos Hankel nativos.

## 1. Origem e convenções

Fonte reaberta: /home/thlinux/CP/c2_roda_zeta_mecanismo_estudo.md e /home/thlinux/carry-mechanics/README.md.

Na base prima p, LSB_p(n)=n mod p. LSB zero equivale a p|n. A roda anterior W, produto dos primos já instalados, observa funções periódicas mod W. Apenas ausência de divisores primos até a raiz quadrada certifica a primalidade de n; sobreviventes de uma roda parcial também podem ser compostos.

Não identificar bracket C2, síntese Genuine, escalar nativo N e característica completada F=A*N como o mesmo objeto.

## 2. Direção nova — teorema exato das rodas por CRT

Se gcd(p,W)=1, defina em funções periódicas mod pW:

    I_p(n)=1 se p|n, caso contrário 0
    g_p(n)=I_p(n)-1/p.

Para toda função f periódica mod W,

    <f,g_p>=(1/(pW)) Σ_(n mod pW) f(n) g_p(n)=0,

pois entre n=r+kW (0<=k<p) há exatamente uma solução de p|n em cada classe r mod W. O quadrado da norma é:

    ||g_p||² = (p-1)/p² > 0.

Logo o pivô de Schur do novo sinal no GRAM DAS RODAS vale exatamente (p-1)/p²; a inovação é ortogonal a toda informação da roda anterior, não apenas aos indicadores das câmeras primas antigas. Cada novo primo produz uma direção nova, e a existência de infinitos primos fornece um número ilimitado dessas direções no espaço indutivo das funções periódicas.

Teste com fractions.Fraction, sem ponto flutuante:
W=1,p=2 -> 1/4;
W=2,p=3 -> 2/9;
W=6,p=5 -> 4/25;
W=30,p=7 -> 6/49.
Todos os cruzamentos com os indicadores das câmeras anteriores são zero.
Veja numerics/wheel_prime_schur_exact.py e evidence/wheel_prime_schur_exact.json.

A recíproca é FALSA para câmeras gerais: a câmera 4 sobre a roda 2 cria

    g_4=1_{4|n}-(1/2)1_{2|n},

com norma²=1/8>0. É informação nova de profundidade 2-ádica sem primo novo. Assim, “nova direção” e “nascimento de novo primo” só se identificam após restringir as direções às novas COORDENADAS PRIMAS.

## 3. Um canal prime-depth já alcança os momentos nativos em Lean

Inspeção direta do código já existente no carry-self-adjoint-operator:

PrimeDepthAllOrderMomentBridge.lean:
- nativeLogGenerator_basisVector_primeDepthLedger recupera o logaritmo como síntese do ledger das profundidades nas câmeras primas.
- primeDepthCanonicalLogBracketBlock_eq_canonical e primeDepthC3LogJetCutoffTail_eq_canonical preservam o bloco e a cauda log-jet originais.

PrimeDepthGeometricMomentRecurrence.lean:
- primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor identifica a resposta com o TFVD bracketado completado;
- primeDepthGeometricMoment_eq_canonical identifica a sequência inteira de momentos com a canônica.

Essa é uma ligação algébrica real entre geometria das câmeras primas e momentos COMPLETADOS, não uma analogia. Mas NÃO diz que o produto interno das rodas é o produto interno da fonte F nem que a correção Gamma/completion preserva sinais.

## 4. A ponte condicional precisa

Se for construída uma medida discreta positiva com pesos w_p>0 e pontos x_p>0 dois a dois distintos, com convergência adequada, que satisfaça para TODO k:

    h_k (da fonte nativa completada) = Σ_(p primo) w_p x_p^k,

então, para todo deslocamento s e polinômio a não nulo de grau <n,

    Σ_(i,j<n) a_i a_j h_(s+i+j)
      = Σ_p w_p x_p^s (Σ_(i<n) a_i x_p^i)^2 > 0.

O argumento de positividade é exato: um polinômio não nulo tem finitas raízes e há infinitos pontos x_p distintos. A existência de infinitos primos permitiria a independência de toda ordem, mas SOMENTE após demonstrar a identidade da fonte e a positividade dos pesos. Não escolher x_p=1/p² por conveniência e tratar a escolha como lei da fonte; o ledger de log n não é uma medida espectral das alturas.

Outra rota suficiente, mais ligada à fonte original:
    Q_native = Q_prime_positive + E_gamma_signed,
com um teorema de dominância relativa E_gamma_signed ≥ -θ Q_prime_positive, θ<1, a cada dimensão. Sem primeiro PROVAR a identificação de Q_prime_positive com parte da fonte, essa equação não resolve o sinal.

O caderno histórico PRIME_ATOM_SKELETON_COMPOSITE_DEFECT_THEOREM.md prova full row rank do ESQUELETO DE DEFEITOS composto/primo usando identidade de energia com sinal negativo. É um operador distinto do Hankel de momentos, e seu rank não se transporta automaticamente para positividade nativa.

## 5. A parte estrutural da não anulação já existe em Lean

Na branch CSA examinada:
- CompletedNativeEntireComparison.lean:
  canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation
  é não recorrência finita incondicional da sequência completada.
- AllPrefixPSDNonrecurrence.lean:
  momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt
  demonstra PSD em todos os prefixos + não recorrência ⇒ PD em todos.
- CompletedNativeSemidefiniteHardyGate.lean:
  canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg_of_harmonicNonrecurrence
  demonstra toda a positividade estrita SOB A PREMISSA
  0≤nativeSourceFiniteBoundaryEnergy(2n,x) para todo n,x.
- CompletedNativeC2LegEnvelopeTransport.lean:
  refina essa obrigação ao controle conjunto assinado de centro+pernas+cauda; a envoltória de erro permanece premissa aberta.

O nascimento de uma direção prima responde à INDEPENDÊNCIA no mundo das rodas. A não recorrência já trata a INDEPENDÊNCIA da sequência de momentos. Falta o MAPA QUE PRESERVE O SINAL entre esses mundos, isto é, positividade/semidefinitude da forma nativa original.

## 6. Contraexemplo da ponte ingênua

h_n=1+2^(-n)-3^(-n) >0 em cada n≥0, mas:
h0=1, h1=7/6, h2=41/36,
det(H_2)=h0*h2-h1²=-2/9<0.

Modos distintos e momentos individualmente positivos não bastam quando há coeficientes assinados. A Gamma e a correção das câmeras não podem ser omitidas.

## 7. Obrigação seguinte

Construir, a partir do source prime-depth / LSB CRT, um mapa explícito de inovações (direções novas das rodas) para a forma quadrática original do bordo C2/TFVD e calcular o defeito assinado do transporte; provar que não destrói a semidefinitude. Então a não recorrência Lean existente promove PSD a PD sem caixas por ordem.

Nada foi formalizado em Lean nesta investigação das rodas: o teorema CRT está demonstrado aqui matematicamente e validado no teste racional. A identidade prime-depth→momentos é um teorema Lean PREEXISTENTE. All-order permanece em aberto.
