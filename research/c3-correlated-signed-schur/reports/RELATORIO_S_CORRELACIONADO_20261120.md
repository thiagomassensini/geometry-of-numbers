# Investigação S correlacionado – TFVD/Green e Euler–Schur
Data: 20/11/2026 | VM HEX-LLM-AI-01
Status: quatro módulos Lean comprovam identidades algébricas e gates CONDICIONAIS; regressões C3 até ordem 9 favoráveis nos dois setores. Não é prova all-order, nem certificado intervalar para esses sinais numéricos.

## Proveniência
- Operador primitivo: bracket C2 (segunda diferença centrada); Genuine: síntese de centros, seed e pernas; F=A*N: característica completada. Aqui usamos a fonte nativa canônica completada, sem substituir a origem pela identidade clássica xi.
- nativeC: completedNativeRealEvenCharacteristicCoefficient.
- nativeH: canonicalCompletedNativeLogDerivativeMoment.
- Vetor crítico Schur mônico v, a=v_(n-1), pivô p=vᵀH_(s,n+1)v (por ortogonalidade), B=vᵀH_(s+1,n+1)v, r_i=(i-n)v_i, R=rᵀH_(s+1,n)r.
- Identidade Euler–Schur existente: W=alpha*B-beta*a*p+4R; alpha=(2n+s+1)(4n+2s+3), beta=16n+8s+6.
- O alvo S=alpha B-beta a p exige uma cota INFERIOR de S, não a soma grosseira alpha|B|+beta|ap|.

## 1. Quatro módulos Lean novos – compilação PASS
SignedSourceTail.lean:
- signedSourcePair e signedSourceLinear reúnem os kernels dos dois setores na fonte C comum.
- signed_source_four_terms: S(H+T,H+T)=S(H,H)+[S(H,T)+S(T,H)]+S(T,T). Mesma cauda original e seus quatro termos.
- signed_source_joint_error_bound: erro <= ||linear correlacionado||+||TT conjunto||.
- signed_source_native_even e signed_source_native_odd: transporte exato ao S dos momentos nativos nos dois setores; o setor ímpar retém a coordenada zero do H2 na carta par.
GroupedSourceBudget.lean:
- joint_linear_coefficient_budget: se ||T_j||<=eps_j, então ||Σell_j*T_j||<=Σ||ell_j||eps_j.
- signed_source_joint_interval_budget: orçamento de S usando coeficientes agrupados por JATO DE CAUDA comum. A igualdade L_H(T)=Σell_j*T_j está explicitamente como obrigação hCoeff; ainda precisa de prova formal da especialização ao sourceKernel para toda ordem.
- signed_native_even_head_error e signed_native_odd_head_error: leitura real conservando ambos os setores e cruzamentos.
NativeSignedGate.lean:
- signed_source_positive_of_head_lower e native_signed_head_budget_gate.
- Se H_(s+1,n) PSD, h_(s+1)>0, |u-uH|<=Eu, |S-SH|<=Es, Lu=|uH|-Eu>0 e
  h_(s+1)*(Es-SH)<4*Lu²,
  então 4R+S>0 (logo W>0 pela identidade Euler–Schur preexistente). O sinal de p novo não é premissa.
CombinedEulerBezout.lean:
- No setor Schur PAR, ambos B e p usam O MESMO vetor fonte-lift; kernels ímpar e par têm respostas D=-C'(X) e XD, respectivamente.
- Um único kernel fonte:
  alpha*sourceKernel(C,true)-beta*a*sourceKernel(C,false)
   = Bezout((alpha-beta*a*X)*(-C'(X)), C(X)).
- combinedEulerKernel_eq_two_parities, coefficientBlock_const_source_mul, combinedEulerKernel_pair, native_even_signed_S_one_response formalizados. Nenhuma positividade desse kernel é afirmada. X é variável FORMAL da série, não altura nem novo objeto físico.
- No setor Schur ímpar os vetores de teste pertencem a cartas/dimensões distintas; a correlação foi formalizada na primeira peça, mas não se deve substituir por um mesmo vetor artificial.

## 2. Experimento C3 correlacionado, reproduzível
joint_S_run.py + joint_S_tail_probe.py. Usa a construção C3 acelerada e a correção de bordo original de 12 pesos, cabeça H e cauda T compartilhadas, os dois vetores fontes reais, os quatro cruzamentos e o completion.
Define ell_j=L_H(e_j), onde e_j é um impulso unitário no jato de cauda; calcula E_linear=Σ|ell_j||T_j| e um orçamento conservador TT, antes de comparar a cota inferior de S.
Regressão independente: ||Σell_j*T_j - L_H(T)|| tem resíduos numéricos menores que 1e-140 nos casos examinados.
Para a comparação numérica, a única inicialização c0 de alta precisão usa identidade clássica posterior xi(1/2); os outros c_j vêm da recorrência. NÃO é a genealogia original.
Os eps_j do teste são os valores absolutos calculados de T_j, NÃO intervalos certificados em Lean.
Razão suficiente Q=h_(s+1)*(Es-S_HH)/(4*(|u_HH|-Eu)^2). Quando Q<1 e Lu>0, a condição do gate passa. Q pode ser negativa quando S_HH supera Es.

                              antigo absoluto   conjunto M=256   conjunto M=384
n=9 setor par                   1.406578          0.0660724        0.00272110
n=9 setor ímpar                 6.539401          1.1679831        0.11105216
- C3/256: 17 dos 18 casos (n=1..9, s=0/1) passaram; o único não-pass foi s=1,n=9.
- C3/384: 18/18 passaram (teste numérico).
- Na ordem 9 M=256, o agrupamento reduziu E_joint/E_sep a cerca de 0.1926 (par) e 0.1193 (ímpar).
- Em ordem 9 M=384, o orçamento conjunto excede o erro verdadeiro |S-S_HH| por fatores somente ~1.246 (par) e ~1.293 (ímpar).
Arquivos de saída: joint_S_M256_n9_numeric.json e joint_S_M384_n9_numeric.json. Scripts originais anteriores preservados.

## 3. Obrigações para tornar os resultados certificados
(1) Derivar em Lean, diretamente de mixed_kernel_coefficient e responseCoefficient, o suporte finito do linear L_H(T) e a igualdade de sua expansão por impulsos, consumindo o MESMO sourceKernel (hCoeff da peça GroupedSourceBudget). Não postular a expansão.
(2) Obter intervalos da fonte original completada para cada |T_j| até a ordem de jato necessária na combinação S e nas correções de u, incluindo Gamma, C3, cutoffs, duas pernas e bordo.
(3) Certificar TT e os vetores críticos originais por intervalos ou orçamento de prefixos anterior, sem usar o sinal do novo pivô.
(4) Verificar a desigualdade estrita do gate por aritmética intervalar, em conjunto com o prefixo H_(s+1,n) PSD já certificado na etapa adequada da indução.
A prova existente completed_tail_jet_error(r), em research/c3-fourteenth-tail/FiniteEvaluationError.lean, vale para todo índice r em C3/64:
  ||sourceJet_r completedTailError|| <= [96*14!/(729*191^13)] * 4^r.
E research/tfvd-uniform-relative-source/C3OrderRate.lean transporta esse controle em ordem arbitrária. Mas ele cresce exponencialmente e é grosseiro em ordens altas: não fornece os limites por jato que paguem as margens minúsculas. A convergência em cutoff para cada ordem fixa não prova positividade all-order.

## 4. Pista adicional, ainda NÃO formalizada
Se H=H_(s,n), G=H_(s+1,n), a matriz H^{-1}G é a companheira do polinômio crítico de Schur; logo a=v_(n-1)=-trace(H^{-1}G). Conferência numérica até n=9 em ambos os setores. Quando ambos os prefixos H e G são PosDef, segue a<0 por semelhança a uma matriz positiva definida. A identidade é matematicamente justificável por ortogonalidade, mas ainda não constitui teorema Lean compilado. Mesmo com a<0, a positividade do núcleo Green combinado não é automática.

## 5. Integridade e status
- Pasta: /home/thlinux/investigacoes/tilt_schur_20261120/
- Novos módulos Lean compilados com -DwarningAsError=true em Lean/Mathlib 4.32; sem sorry. Os módulos reutilizam as .olean originais da PR70. Não houve reconstrução limpa de todos os repositórios externos.
- Nenhum arquivo original de pesquisa foi editado neste ataque. Nenhum commit/push.
- Não provamos W>0 all-order, positividade de todos os pivôs, contratividade Green, nem transporte de zeros Genuine para tilt=0.
