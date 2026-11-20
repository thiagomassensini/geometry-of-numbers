# Por que o resíduo central preserva energia? — 100 momentos e o gate original

**Data:** 20/11/2026. **Estado:** teorema algébrico finito, dados intervalares Arb e localização de provas Lean anteriores. **Sem nova prova all-order incondicional.**

## Fonte e integridade
Os dois arquivos enviados pelo usuário contêm os mesmos 100 momentos decimais, com ~16 mil caracteres por momento. Conferimos a coincidência dos 300 caracteres iniciais nos índices 0,1,10,50,80,99 com o arquivo existente na VM:

    /home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json

O script usa a cópia na VM, com ~7,6 mil caracteres por momento, suficiente para as contas; não recebe posições de zeros. A identidade que fornece a sequência canônica vem da característica **F=A*N completada**, distinta do bracket C2 primitivo e da síntese Genuine. C3 não é a origem privilegiada.

## Escala versus sinal
Com rho = h99/h98 ≈ 0.0050052441235941160788, defina m_j=h_j/(h0*rho^j). Então:

    H_(s,n)(h) = h0*rho^s * D(rho) * H_(s,n)(m) * D(rho),
    D(rho)=diag(1,rho,...,rho^(n-1)).

A congruência preserva a inércia e a nulidade das matrizes. Portanto a inclinação explica o tamanho, mas **não cria** o sinal. Uma progressão geométrica pura tem posto Hankel 1: todos os h_n>0, porém o pivô de ordem 1 já é zero.

## Auditoria por intervalos dos decimais
Script: numerics/finite_jacobi_100.py. Biblioteca Arb/FLINT com 460 dígitos de trabalho e eliminação LDL simétrica:
- H_(0,50)(m): 50/50 pivôs com bola estritamente positiva; último ≈1.72379116232436e-171, raio < 5.23e-398.
- H_(1,50)(m): 50/50 positivos; último ≈9.56703606552792e-174, raio < 5.40e-398.
- Quadratura espectral independente via mpmath: 50 nós positivos e pesos positivos, erro relativo máximo da reprodução dos 100 momentos ≈1.446e-179.

Seis primeiros nós normalizados x, pesos w e alturas derivadas 1/sqrt(rho*x):
  1: x=1.000000000..., w=0.21663040965175177, altura≈14.13472514173469
  2: x=0.45209013898102619, w=0.09793647200697710, altura≈21.02203963877155
  3: x=0.31938724567983002, w=0.06918898986916626, altura≈25.01085758014569
  4: x=0.21583262771608604, w=0.04675591055834975, altura≈30.42487612585951
  5: x=0.18418649172486469, w=0.03990039515467643, altura≈32.93506158773919
  6: x=0.14142246397621081, w=0.03063640630512666, altura≈37.58617815882567

**Estas cotas intervalares dizem respeito às casas decimais armazenadas, não constituem certificados Lean dos momentos simbólicos.** Os nós são derivados dos momentos; as alturas não foram fornecidas como entradas.

Os momentos h100 e h101, que **não** estão nos dois arquivos enviados, mas existem na VM, deram por inspeção Arb um 51º pivô positivo em cada setor (~5.130187e-176 e ~2.784424e-178, respectivamente). Logo a aproximação de 50 modos não representa toda a extensão decimal. Tampouco isto demonstra all-order.

## Teorema algébrico que explica o desconto de Schur (ainda não formalizado aqui)

Se as matrizes H0=(m_(i+j)) e H1=(m_(i+j+1)), i,j<r, são PosDef, ponha no espaço R^r o produto interno <u,v>=u^T H0 v e o operador M=H0^(-1)H1. Então:
1. M é autoadjunto e positivo para esse produto interno.
2. M e_j=e_(j+1), para j<r−1, pois H1 e_j = H0 e_(j+1). Assim e0 é cíclico.
3. O teorema espectral fornece r nós positivos distintos x_l e pesos positivos w_l, com m_k=Σ_l w_l x_l^k para todos k=0,...,2r−1.
   Para k≤2r−2, escreva k=a+b com a,b<r, e use <M^a e0,M^b e0>=m_(a+b). Para k=2r−1, use <e_(r−1),M e_(r−1)>=(H1)_(r−1,r−1).
4. Para n<r, o pivô é a norma quadrática residual do polinômio mônico ortogonal P_(s,n):
      p_(s,n) = Σ_l w_l x_l^s P_(s,n)(x_l)^2 > 0, s=0 ou 1.
   Como P_(s,n) tem grau n<r, não zera em todos os r nós distintos. Esse é o mecanismo **finito** de energia restante após os descontos.

Porém a extensão de uma representação com só r nós pode ter p_r=0. Portanto os primeiros 100 valores isoladamente não provam infinitude de modos positivos.

## O mecanismo all-order já está parcialmente provado em Lean

Inspecionamos os arquivos desta branch preexistente do CSA:

    /home/thlinux/worktrees/csa-c2-local-hadamard-bridge-20261120/CarrySelfAdjointOperator/

**CompletedNativeEntireComparison.lean**:
- canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation.
- Enunciado incondicional: a sequência nativa completada não admite recorrência linear finita global. Prova analítica via log-derivada da Gamma nos inteiros pares positivos, não assumindo todos os zeros na linha.

**AllPrefixPSDNonrecurrence.lean**:
- momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt.
- Se TODOS os prefixos são PSD e não existe recorrência finita, então TODOS são PD.
- Justificativa: num prefixo PSD, energia zero faria o vetor se anular por pareamento com qualquer monômio de todos os prefixos maiores; isso geraria uma recorrência global, impossível.

**CompletedNativeSemidefiniteHardyGate.lean**:
- canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg_of_harmonicNonrecurrence.
- Hipótese explícita restante:
      para todo n e vetor x, nativeSourceFiniteBoundaryEnergy(2*n,x) >= 0.
- Conclusão: as duas torres Hankel nativas são PosDef em TODAS as dimensões. A não-recorrência usada é a incondicional acima. **A hipótese da energia NÃO está provada por este teorema.**

**CompletedNativeC2LegEnvelopeTransport.lean**:
- HasNativeSourceC2LegTailBounds e nativeSourceC2LegTailBounds_imply_gammaCorrectionEnvelope.
- Reduz a hipótese de sinal à estimativa assinada da soma centro + duas pernas + erro real de cauda para cutoff M(k) variável, uniforme em todo vetor x de dimensão fixa, com erros a(k),b(k)→0.
- Esse controle de sinal está **explicitamente como obrigação aberta**. A síntese horizontal finita exata não constitui automaticamente fechamento Green positivo.

## Conclusão e alvo

A intuição de que “não sobra um zero finito” tem uma tradução precisa: **não recorrência finita**, já provada para a sequência nativa completada. MAS ela só promove PSD a PD, não cria PSD.

**Falta demonstrar a não negatividade das energias de bordo nativas, em toda ordem**, a partir da geometria C2/TFVD e seus defeitos reais. Esta é a obrigação central, mais fundamental que repetir caixas estreitas de pivôs. Um ataque viável é construir uma envoltória assinada o(||x||²) para o defeito Gamma usando as contribuições conjunta de centro, duas pernas e cauda, com uniformidade em x e cutoff radial apropriado.

Este relatório preserva as fronteiras: dados decimais ≠ fonte simbólica; prova finita ≠ all-order; não recorrência ≠ sinal; bracket C2 ≠ Genuine ≠ F completada. Não se anunciou RH nem positividade all-order.

## Leitura transversal (modelo, não conclusão nativa)

No centro, pares de modos REAIS positivos contribuem para uma diferença
Hankel de ordem 2 como A*B*(lambda1*lambda2)^n*(lambda1-lambda2)^2>0.
Em um modelo de dois modos conjugados não reais com amplitudes conjugadas,
a diferença pode ser negativa: D_n=-4*|A|^2*|lambda|^(2n+2)*sin(theta)^2,
com lambda=|lambda|*exp(i*theta). A inclinação dominante pode continuar
praticamente a mesma; a fase muda o sinal. Isto ilustra a observação
centro versus fora, mas não é prova da lei transversal da fonte nativa.
