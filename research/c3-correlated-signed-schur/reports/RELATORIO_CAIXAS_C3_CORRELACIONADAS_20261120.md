# C3 completada — caixas por jato, transporte nativo e sinal correlacionado
Data 20-11-2026 | VM HEX-LLM-AI-01
ESTADO: Lean PASS para caixa racional all-cutoffs, crosswalk direto na fonte TFVD, suporte finito e 4 caixas racionais. Avaliação intervalar Arb: 23 jatos e 18/18 gates até n=9 em ambos os setores com M=384. A verificação numérica Arb NÃO é um teorema Lean.

## I. Proveniência: cadeia geométrica preservada
Origem: segunda diferença centrada C2, sementes, centros, pernas e cartas; Genuine como síntese posterior; N = nativeHeightScalar, F = nativeXiCompletionFactor*N completada. Não trocar bracket, Genuine e F.
Aqui o consumidor é a fonte **completada** nativeC, via identidade original C3. A C3 é representante da câmera, não novo axioma de origem.
A função usada nas caixas é o tail original e a **correção de bordo original de 12 pesos**, multiplicados pelo MESMO valueMultiplier completado. Nada é reinterpretado como Gram positiva global.

## II. NOVO Lean — caixas rigorosas para qualquer cutoff
Arquivo C3CompletedJetBoxes.lean, import FiniteEvaluationError:
- def completedC3TailAt M w = valueMultiplier(w)*acceleratedC3Tail(M,w).
- def completedC3TailJetEnvelope M j =
     96*14!/(729*(3*M-1)^13)*4^(2*j).
- theorem completed_c3_tail_jet_bound_general:
  M>0 ==> ||sourceJet_(2j)(completedC3TailAt M)|| <= completedC3TailJetEnvelope M j.
Demonstração direta por cauchy_quarter e os limites C3 EXISTENTES para cada M; não usa xi numérica, zeros, Gram, sinal do Schur ou cotas não-provadas.
Compilação Lean 4.32 --wfail PASS, sem sorry.

## III. NOVO Lean — igualdade do tail original com os jatos acima
Arquivo C3TailNativeCrosswalkAny.lean, importa LiteralTailBounds e LiteralTfvd:
- originalC3BoundaryJetAny M j: sourceJet_(2j) de valueMultiplier * c3Boundary(3M+2).
- source_regrouped_c3_tail_any M j:
    literalTail M j - originalC3BoundaryJetAny M j
      = sourceJet_(2j) (completedC3TailAt M).
- c3_regrouped_tail_any_bound M j (M>0):
    ||literalTail M j - originalC3BoundaryJetAny M j||
       <= 96*14!/(729*(3*M-1)^13)*4^(2*j).
Passou Lean --wfail. É a ponte que faltava: NENHUMA redefinição da cauda fora do TFVD nem perda do completion. Funciona para M arbitrário, ao contrário da velha declaração em M=64.

## IV. NOVO Lean — caixas racionais pontuais efetivamente fechadas
Arquivo C3Certified384Boxes.lean, --wfail PASS:
 j=0 :  ||T_384,0|| <= 2/10^30
 j=9 :  ||T_384,9|| <= 2/10^19
 j=18:  ||T_384,18|| <= 9/10^9
 j=22:  ||T_384,22|| <= 6/10000
São provas Lean da fonte original, conservadoras demais para fechar n=9; não confundir com os limites estreitos Arb da seção VI.

## V. NOVO Lean — suporte dos jatos realmente necessários
Arquivo C3LinearSupport.lean, --wfail PASS:
- response_odd_explicit, response_even_zero, response_even_succ: leem derivada original e companion.
- response_agree_below: uma resposta no índice k depende somente dos coeficientes da fonte até k+1.
- mixed_kernel_agree_below: cada coeficiente (i,j) de mixedSourceKernel depende dos coeficientes das DUAS entradas até i+j+2.
- coefficientPair_agree_below: um bloco de dimensão r depende de jatos em índices <=2r (escolha N=2r+1).
- signed_linear_prefixTail: a resposta linear HT+TH correlacionada de S depende apenas dos jatos da cauda de um prefixo finito comum N, com N>2rB e N>2rP.
Para n=9, o bloco mais longo é rB=n+2=11 no setor ímpar. N=23, isto é, EXATAMENTE T_0...T_22. O número de caixas do cálculo Arb não foi escolhido arbitrariamente.

## VI. Arb: caixas individuais da fonte completada, de precisão auditável
Script c3_arb_jet_boxes.py, python-flint 0.8.0, FLINT/Arb acb_series, 240 dps.
- Constrói a cabeça C3 verdadeira: s=1/2+i*w, seed 1, Σ_{m<M}[(3m+2)^(-s)-2(3m+3)^(-s)+(3m+4)^(-s)], original boundary de 12 pesos /729 e original multiplicador completo Gamma/xi/chart.
- Avalia F completada por função xi clássica apenas como ALGORITMO EQUIVALENTE de alta precisão (a origem e o transporte já estão estabelecidos em Lean pela construção C3); o algoritmo de intervalos NÃO constitui a prova Lean de identidade com o xi.
- Cauda intervalar T_j = [w^(2j)](F_original_equivalente - Head_C3). Gera eps_j = m_j*10^e_j (racional decimal exato) e verifica via Arb abs_upper(T_j)<eps_j.
- Os 23 coeficientes T_0...T_22 têm caixas verificadas.
Amos.: em M384, envelopes conservadores Lean versus caixas externas Arb:
 j  | Lean M384        | Arb M384 (limite racional decimal)
 0  | 2e-30            | 881e-39 = 8.81e-37
 9  | 2e-19            | 209e-41 = 2.09e-39
18  | 9e-9             | 329e-53 = 3.29e-51
22  | 6e-4             | 163e-59 = 1.63e-57
A diferença chega a cerca de 10^53, demonstrando por que a cota Cauchy global não fecha as ordens mais altas.
Dados: C3_Arb_boxes_M384_j22_d240.json. Cada j tem o intervalo complexo completo, o valor da cabeça e o teto decimal marcado como confirmado pelo Arb.

## VII. Intervalos Arb no gate S, com Schur e source-lift
Script c3_arb_signed_gate.py, saída C3_Arb_signed_gate_M384_n9_d240.json.
Verifica COMPLETAMENTE em aritmética intervalar externa:
1. Todos os blocos precedentes H_(s+1,n) PosDef via pivôs em Arb; nenhum pivô novo é premissa.
2. O vetor mônico v é construído da matriz canônica de momentos, não ajustado por zeros. Os momentos vêm dos coeficientes do F completado via a recorrência nativa já existente.
3. Os source-lifts de v, r e e0 usam a mesma matriz Toeplitz inversa e o mesmo c0; setor ímpar insere o zero inicial.
4. O termo linear conjunto ell_j é construído por impulsos no MESMO jato de cauda, agrupando H*T e T*H dos DOIS setores antes dos módulos.
5. O erro S fica sob Elinear=Σ |ell_j|eps_j mais um TT calculado com intervalo Arb; o erro u recebe uma caixa intervalar independente.
6. Verifica source-moment congruence, |S-S_head|<E_S, |u_head|-E_u>0 e
   h_(s+1)*(E_S-S_head) < 4*(|u_head|-E_u)^2.
Foram FAVORÁVEIS 18/18: s∈{0,1}, n=1...9.
Na ordem 9:
  Q_par ≈ 0.002735418836
  Q_ímpar ≈ 0.111099551391
Q é a razão assinada (custo/margem) da versão calculada via intervalos.
Os 18 registros de JSON preservam caixas de todos os escalares, booleanos dos testes e verificação da identidade source-moment. Nenhum coeficiente de zero da zeta foi empregado.
A primeira implementação do script erroneamente tratou j como grau w^j em vez de w^(2j); ela foi rejeitada pela própria verificação da cobertura de erro. Corrigida, a reexecução confirmou simultaneamente TODOS os testes. Somente a saída corrigida é válida.

**Limite epistemológico:** FLINT/Arb é aritmética intervalar certificadora externa; esses 18 resultados NÃO foram traduzidos ainda para provas em Lean. A avaliação externa de F usa uma identidade clássica posterior cuja correspondência com a construção nativa deve ser consumida pela proveniência Lean, não usada como ponto de partida da teoria.

## VIII. Próxima obrigação
(1) Especializar a expansão L_H(T)=Σell_j*T_j em Lean, sem hipótese hCoeff: já formalizamos suporte finito em C3LinearSupport; falta a etapa de linearidade/impulsos da soma.
(2) Importar em Lean as 23 CAIXAS FINAS da seção VI com certificados de avaliação intervalar verificáveis para os jets originais Gamma/C3/completion. Provar eps_j para cada j a partir das funções, não apenas registrar decimais do Arb.
(3) Substituir o TT externo por limite Lean igualmente afinado, transportar os vetores críticos por intervalos e aplicar native_signed_head_budget_gate junto à positividade dos prefixos antigos; então certificar finitamente até n=9.
(4) Só depois investigar lei de ordem e cutoff M(n) que possa levar além de cada n fixo; finitude e monotonia do momento não demonstram all-order.
Nenhum sinal nativo all-order, RH, ou conexão zeros Genuine => tilt=0 provado aqui.

## IX. Integridade
Workdir /home/thlinux/investigacoes/tilt_schur_20261120/
Arquivos novos nesta frente: C3CompletedJetBoxes.lean, C3TailNativeCrosswalkAny.lean, C3Certified384Boxes.lean, C3LinearSupport.lean, c3_arb_jet_boxes.py, c3_arb_signed_gate.py, dois JSON de intervalos, logs.
Não houve commit nem push; fontes originais continuam sem alterações por esta frente. Provas usam caches compilados das PRs C3 e TFVD existentes, não um rebuild completo das dependências externas.

## X. Auditoria final das provas e repetição independente
- AuditC3JetBoxes.lean compilou com -DwarningAsError=true.
- A verificação de axiomas das declarações completed_c3_tail_jet_bound_general, c3_regrouped_tail_any_bound, c3_tail384_jet22 e signed_linear_prefixTail retornou somente [propext, Classical.choice, Quot.sound], sem sorryAx ou axioma adicional.
- Arquivo de auditoria audit_c3_jets.log, saída AUDIT_EXIT=0.
- Repetição intervalar Arb em 320 dps: C3_Arb_signed_gate_M384_n9_d320.json e log c3_arb_signed_gate_M384_d320.log. Mantiveram-se os 18/18 sinais e os valores do gate n=9 em ambos os setores, concordando nos algarismos apresentados com a execução de 240 dps.
- Permanecem as obrigações de transportar as 23 caixas finas do Arb ao Lean como provas de avaliação da fonte, eliminar a hipótese hCoeff da expansão linear por impulsos e fechar o orçamento TT fino formalmente. Estes resultados não equivalem à positividade all-order.
