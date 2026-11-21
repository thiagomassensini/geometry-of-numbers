# Fuga da primeira inversão transversal e PSD central: separação entre janela e dimensão

Data: 2026-11-21. Objetivo: provar positividade ALL-ORDER da característica COMPLETADA original F=A*N sem RH, usando a geometria C2, Genuine, TFVD e o limite sigma→1/2.

## 1. Fonte reaberta e classificação do resultado histórico

Momento exato da investigação:
- momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105/RELATORIO_JATOS_PARES_FRONTEIRA_2026-11-05.md
- momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105/c2_window_first_negative.py
- GoN/research/native-moving-schur-sigma/SigmaNeighborhood.lean
- GoN/research/native-moving-schur-sigma/SigmaPersistentNegativeDirection.lean
- GoN/research/native-moving-schur-sigma/SigmaCertifiedNegativeDirection.lean
- GoN/research/native-moving-schur-sigma/SigmaPadeEventualNegativity.lean

O script usa jets sigma da característica original derivada de cabeça C2 + CAUDA EXATA (Hurwitz) + câmera + completion. Define
    D_s(d) = h_s(d)*h_(s+2)(d) - h_(s+1)(d)^2,
com d = sigma - 1/2 e s = DESLOCAMENTO da janela 2x2 de momentos; NÃO é a dimensão do Hankel e NÃO é a profundidade C2 k.

Dados numéricos descritos no relatório em círculos dentro da faixa de convergência:
    d = 0.2: primeira janela 2x2 negativa em s = 7;
    d = 0.00001: primeira janela 2x2 negativa em s = 32;
    s=10: primeira raiz transversal ≈ 0.049858391577...
Eles indicam que a PRIMEIRA JANELA negativa se desloca para janelas profundas quando d→0. São experimento (mpmath) SEM certificação por intervalos e SEM teorema que prove s_neg(d)→∞ para todos d→0.

GoN SigmaNeighborhood já prova para qualquer s,N:
  sigma_matrix_center(s,N): sigmaMatrix(0,s,N)=native canonical Hankel(s,N).
  sigma_matrix_continuous_center(s,N): ContinuousAt (fun d=>sigmaMatrix d s N) 0.
GoN SigmaCertifiedNegativeDirection prova, usando a CERTIFICAÇÃO de um zero na linha (não RH), que a cada 0<|d|<1/4 EXISTE uma matriz ORIGINAL com direção negativa, sem cotar a ordem mínima N(d). SigmaPersistentNegativeDirection transporta qualquer direção negativa às dimensões maiores. O uso do primeiro zero é um input de prova sobre a estrutura transversal e NÃO deve virar o mecanismo de positividade central geométrica independente.

## 2. A rota matemática válida para fechar a PSD central

Se para cada dimensão FIXA N, nos setores s=0 e s=1, existe delta(N,s)>0 tal que
  0<|d|<delta(N,s) => sigmaMatrix(d,s,N).PosSemidef,
então, por continuidade de cada entrada e fechamento do cone de matrizes PSD,
  sigmaMatrix(0,s,N).PosSemidef para todos s,N.

Em termos de 'primeira dimensão negativa' da matriz INTEIRA, essa premissa é exatamente 'N_neg(d)→∞ conforme d→0', desde que se defina a primeira falha em cada setor. **Não é** o mesmo que primeira janela consecutiva 2x2 negativa deslocar seu índice s→∞.

Novo Lean (zero RH):
  lean/TransverseSignThresholdCenterClosure.lean:
    center_nonneg_of_punctured_transverse_nonneg;
    center_matrix_posSemidef_of_punctured_posSemidef.
  lean/NativeSigmaFirstFailureAllOrderGate.lean:
    SigmaNativeFullFailureDimensionEscapes (hipótese EXPLÍCITA e AINDA ABERTA);
    sigma_native_all_center_Hankel_posSemidef_of_failure_escape;
    sigma_failure_escape_implies_exact_allJet_tfvd_nonnegative;
    sigma_failure_escape_implies_allJet_theta_mass_dominance.

As últimas duas compõem a fuga N_neg(d)→∞, se provada, com os teoremas já demonstrados nesta branch:
  PSD ambos Hankel <=> não negatividade da fonte C2/Genuine/TFVD exata HH+HT+TH+TT em TODOS os cutoffs e jets;
  PSD <=> dominação massa theta positiva >= negativa em TODOS os polinômios de jets.
Tudo mantém N(z) separado de F(z)=A(z)N(z), sem RH e sem medida de zeros assumida.

**Limite central:** a hipótese SigmaNativeFullFailureDimensionEscapes NÃO foi provada; as demonstrações novas são implicaçõ​es condicionais entre propriedades de fonte original. Como a não recorrência dos momentos canônicos é já provada em outro módulo CSA, a PSD de todos os prefixos implica também PD; por continuidade, PD de cada prefixo central gera um delta(N)>0 com PSD também fora do centro. Portanto, neste contexto o gate de fuga da PRIMEIRA DIMENSÃO NEGATIVA é essencialmente outra apresentação da positividade central: somente vale como PROVA INDEPENDENTE se for demonstrado diretamente da geometria/estrutura transversal, sem importar como premissa a PSD central.

## 3. NO-GO rigoroso: janelas 2x2 não controlam Hankel 3x3

O novo módulo lean/TransverseTwoWindowNotEnough.lean exibe uma sequência sintética real não relacionada com C2:
  h0=1, h1=1, h2=2, h3=5, h4=63/5;
  h_n=(63/5)*3^(n-4) para n≥4.

Para TODO s≥0, o menor CONSECUTIVO de janela 2x2
    D_s = h_s*h_(s+2)-h_(s+1)^2 >= 0.
Casos iniciais: D0=1, D1=1, D2=1/5, D3=756/25; para s≥4, D_s=0.
Entretanto:
    det [[1,1,2],[1,2,5],[2,5,63/5]] = -2/5 <0.
Assim todas as janelas consecutivas são PSD 2x2 e H3 NÃO é PSD. A sequência é artificial apenas para refutar a inferência ALGÉBRICA, não diz que a sequência canônica tenha sinal negativo.

Provas Lean:
    toy_all_consecutive_two_by_two_minors_nonnegative;
    toy_three_by_three_Hankel_det_negative.
A segunda implica que a lei numérica de s_neg(d)→∞ não basta, nem se for provada globalmente, para fechar os DOIS Hankel de todas as ordens.

## 4. O próximo ataque original

Trocar 'primeira janela negativa' pela PRIMEIRA dimensão da matriz física negativa e tentar estimar uma função de limiar N(d) usando:
- SigmaTransverseAllOrder: lei diferencial dos jets transversais e coeficientes Taylor exatos a ordem arbitrária;
- GoN #131: caudas para famílias de jets de qualquer dimensão FIXA;
- GoN #316 e CSA #124: direção de Schur e balanço incidente-retorno;
- novas identidades de cauda TFVD HH+HT+TH+TT, exatas em toda ordem.

O NOVO lema de fonte necessário é uma desigualdade não trivial, para cada N e cada x, que exclua negatividade da forma física completada nos deslocamentos suficientemente pequenos; ou, mais diretamente, mostre que o retorno não domina a incidência no centro. Não assumir a premissa de fuga que já equivale ao sinal desejado.

## 5. Validação

4 módulos Lean:
    TransverseSignThresholdCenterClosure.lean
    NativeSigmaFirstFailureAllOrderGate.lean
    TransverseTwoWindowNotEnough.lean
    AuditNativeSigmaThresholdCenterClosure.lean
Todos compilados por validate-sigma-first-failure-center-vm.sh com -DwarningAsError=true (exit 0). Auditoria de sete declarações: somente propext, Classical.choice, Quot.sound. Sem sorry e sem RH como hipótese. Leitura de SigmaNeighborhood foi feita na versão realmente compilada de 4.32 do worktree de validação sigma, com o mesmo nome e declaração do GoN main research.
