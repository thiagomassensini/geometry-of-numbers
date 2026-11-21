# Meia escala espectral, alturas e assinatura dos pivôs

**Investigação:** 21/11/2026. **Status:** novas provas all-order em Lean sobre normalização por escala positiva, ponte com a fonte original C2/TFVD e contramodelo de pencils com mesmos modos e assinaturas opostas. A positividade original em todas as ordens permanece aberta.

## 1. Pergunta e objetos

A pergunta não é sobre a rigidez do expoente material σ=1/2 — já demonstrada na fundação posicional — mas se o fator 1/2 da recuperação de ALTURAS por inclinação de momentos/pivôs também controla seu SINAL.

Genealogia preservada: centro + pernas C2 → bracket → Genuine → N(z) → F(z)=A(z)N(z) → R(z)=−F'(z)/(2F(z)) → momentos originais h_n → Hankel/Schur.

O material de Momentos, investigação c2_first_second_cancellation_20261110, registra primeira inclinação decimal m≈2.3005747355784 e recuperação 10^(m/2)≈14.1347251417347. Para o N-ésimo pivô vale, sob isolamento de modos e resto controlado, P_(s,N)~C_N γ_N^(−2s−2). O fator 1/2 vem da leitura de uma potência QUADRÁTICA, e essa recuperação é ASSINTÓTICA.

A compatibilidade geométrica b^(−k/2)^2=b^(−k) e a inversa quadrática dos nós espectrais têm papéis diferentes; uma isometria material→Hankel não foi provada pela simples repetição do expoente.

## 2. Novo resultado Lean: escala positiva preserva TODAS as assinaturas finitas

Para qualquer a>0 e sequência real r_n, defina h_n=a^(n+1)r_n. Para qualquer shift s e N:

  H(s,N;h) = a^(s+1) D_a H(s,N;r) D_a,
  D_a=diag(1,a,...,a^(N−1)).

Isto é igualdade exata, preserva TODAS as entradas e cruzamentos e não presume medida positiva. O determinante é multiplicado pelo fator positivo

  a^((s+1)N) * (prod_(i=0)^(N−1) a^i)^2.

NOVOS teoremas Lean demonstram para todo s,N:
  H(h).PosSemidef ↔ H(r).PosSemidef;
  H(h).PosDef ↔ H(r).PosDef;
  det H(h)>0 ↔ det H(r)>0;
  det H(h)<0 ↔ det H(r)<0.

Sob hipótese de antigo prefixo PosDef, também
  sourceMomentSchur(h,s,n)>0 ↔ sourceMomentSchur(r,s,n)>0.

Arquivo: lean/NativeQuadraticSlopeSignatureSeparation.lean.

**Significado:** o fator de inclinação a=γ^(−2) é uma reescala POSITIVA. Ele não cria, repara nem destrói uma direção negativa. A assinatura mora no residual r, isto é, nas correlações de ordem mais fina.

## 3. Ponte ao operador C2 COMPLETADO original, não a um modelo espectral

Para a SEQUÊNCIA NATIVA REAL nativeH dos coeficientes de −F'/(2F), definimos
  nativeSlopeResidual(a,n) := nativeH(n)/a^(n+1).

Lean demonstra sua reconstrução exata para QUALQUER a>0 e, em TODAS as dimensões,

  todos H(s=0,N; residual), K(s=1,N; residual) PSD
  ↔ todos os termos C2/TFVD HH+HT+TH+TT somados têm energia ≥0
  ↔ toda massa theta positiva dos polinômios de jets COMPLETADOS domina a negativa.

Esta é uma composição dos novos teoremas all-order de escala com NativeExactTailAllJetSignedMassGate.lean, cuja fonte é Genuine → N → F=A*N → momentos. Não se modifica a cauda exata, o completion, nem se inserem zeros. Nenhum sinal da massa assinada é presumido ou demonstrado: o gate continua ABERTO.

Arquivo: lean/NativeSlopeResidualExactTfvdSignGate.lean.

## 4. Contramodelo formal: mesmas ALTURAS exatas, assinatura oposta

Dois sistemas sintéticos, NÃO a nossa função C2:
  h_n^(+)=(1/2)^(n+1)+(1/4)^(n+1);
  h_n^(−)=(1/2)^(n+1)−(1/4)^(n+1).

Eles têm os MESMOS nós positivos q1=1/2 e q2=1/4 e, portanto, mesmas alturas extraíveis γ1=√2, γ2=2. TODOS os h_n^(−) são estritamente positivos.

Para TODO shift s≥0, álgebra exata formalizada em Lean:
  det H(s,2;h^(±))=±(1/8)^(s+1)*(1/4)^2.

Mais forte: o teorema já existente twoRealPolePencil_characteristic não depende dos pesos serem positivos. NOVO teorema Lean instanciado prova que ambos os pencils, com pesos +1 e −1, têm EXATAMENTE os mesmos dois autovalores generalizados q1=1/2 e q2=1/4 em qualquer shift, embora a assinatura da Gram seja oposta.

O pivô segundo (razão de determinantes) vale exatamente:
  P_s^(±)=±(1/4)^(s+1)/[16(1±2^(−s−1))],
  P_(s+1)^(±)/P_s^(±)
      =(1/4)*(1±2^(−s−1))/(1±2^(−s−2))→1/4.

A MESMA inclinação recupera γ2=2, mas o P_s é positivo num sistema e negativo no outro. A parte de limite acima é uma dedução algébrica de fórmulas exatas; a prova Lean desta rodada certifica fórmulas de determinante em todos os shifts, os modos de pencil e seus sinais, não um teorema de convergência analítica do quociente.

O modelo sintético NÃO representa resíduos de zeros da função F nem é contraprova da positividade C2; mostra somente que altura/inclinação por si só não forçam PSD.

Arquivos:
- lean/NativeTwoModeSlopeSignAdversary.lean
- lean/NativeTwoModeSamePencilOppositeSign.lean.

## 5. A pista que permanece: módulo E FASE da mesma variável inversa quadrática

Reaberto GoN SigmaTwoPoleModel.lean. Para um modelo auxiliar com ζ=(γ+id)^(−2) e peso m>0, teoremas Lean já existentes demonstram:

  |ζ|=1/(γ²+d²),
  Im ζ=−2γd/(γ²+d²)²,
  det G_model(s,2)=−4m²γ²d²/(γ²+d²)^(2s+6) < 0
  quando γ>0 e d≠0.

O MÓDULO da potência quadrática determina o decaimento (altura/radio); o defeito transversal de FASE dá negatividade proporcional a d². Ao chegar ao centro d=0 esse termo do modelo coalescido zera (NÃO resulta automaticamente em positivo). Os demais modos e cruzamentos do completado real determinam a competição de sinais.

Essa fórmula é EXATA somente para o modelo auxiliar de dois polos. Não é intercambiável com a decomposição MATERIAL da C2 inteira sem isolamento e controle uniforme do resto. Ela explica por que a mesma estrutura quadrática pode PARTICIPAR da lei de sinal, mas por mais informação que o expoente de inclinação.

## 6. Próxima obrigação independente: a microcurvatura residual

Momentos registra a identidade Toda/Desnanot-Jacobi
  τ_(s,N)τ_(s+2,N) − τ_(s+1,N)^2
     = τ_(s,N+1)τ_(s+2,N−1),
com τ_(s,N)=det H(s,N), τ_(s,0)=1.

Depois da congruência positiva, o sinal dessa microcurvatura é invariável sob remoção da inclinação de escala. Sob positividade dos níveis anteriores, a próxima dimensão positiva exige essa NOVA desigualdade de curvatura.

Alvo para a fonte C2 original, sem RH:
  para todo s,N,x, a massa theta COMPLETADA positiva domina a massa negativa,
  equivalentemente, o retorno físico assinado (com seed, pernas, câmera,
  completion Gamma, cabeça, cauda e cruzamentos) não domina a incidência.

A matemática all-order não sai só do expoente 1/2 ou da inclinação modal. Uma prova nova deve construir a desigualdade no operador original e excluir os contramodelos assinados. Não pressupor que todos os zeros já sejam reais, nem fabricar um Gram modal positivo.

Rota de trabalho: estudar microcurvaturas dos pivôs normalizados da SEQUÊNCIA NATIVA, não só suas inclinações; transportar o estado Bessel/Green ao carrier chiral COMPLETADO com uma identificação métrica exata; provar uma margem de signo em todas as ordens e controlar prefixos singulares pela forma sem divisão.

## 7. Auditoria

Lean 4.32: 5 arquivos de compilação em -DwarningAsError=true, validação EXIT 0, 25 novas declarações auditadas, apenas propext, Classical.choice e Quot.sound. Sem sorry, admit, RH ou axiomas adicionais.

Arquivos desta rodada:
- lean/NativeQuadraticSlopeSignatureSeparation.lean
- lean/NativeSlopeResidualExactTfvdSignGate.lean
- lean/NativeTwoModeSlopeSignAdversary.lean
- lean/NativeTwoModeSamePencilOppositeSign.lean
- lean/AuditNativeSlopeSignSeparation.lean
- validate-native-slope-sign-separation-vm.sh.

Fontes reabertas:
- GoN GeometryOfNumbers/Foundation/FoundationalHalfScalingCapstone.lean
- Primos CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean
- CSA CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean
- CSA CarrySelfAdjointOperator/NativeSourceSchurThetaMasses.lean
- GoN research/native-moving-schur-sigma/SigmaTwoPoleModel.lean
- Momentos investigations/c2_first_second_cancellation_20261110/NOTA_PROFUNDIDADE_NORMA_DIAGONAIS_ESPECTRAIS_C2_2026-11-10.md
- Momentos investigations/c2_first_second_cancellation_20261110/RETA_MICROCURVATURA_TODA_CONSTRUCAO_FORMAL_20261110.md
- GoN research/c3-correlated-signed-schur/lean/NativeExactTailAllJetSignedMassGate.lean.

**Conclusão:** a LEI INVERSA QUADRÁTICA participa tanto da leitura das alturas quanto do mecanismo de negatividade transversal (módulo versus fase). A INCLINAÇÃO isolada é insuficiente para a assinatura. A obrigação original é uma desigualdade de correlação/microcurvatura theta-Green, e continua aberta.
