# Prefixos deslocados, Green e gate de um único modo
2026-11-20 | VM HEX-LLM-AI-01
Estado: testes e teoremas condicionais Lean; NÃO é prova de positividade all-order.

## 1. Genealogia
Da fonte original (Lean antigo: CriticalReduction.lean, CanonicalBalance.lean):
W = alpha*B - beta*a*p + 4*R,
alpha=(2n+s+1)(4n+2s+3); beta=16n+8s+6;
a=v[n-1], p=Schur(H_(s,n+1)), B=vᵀH_(s+1,n+1)v;
r_i=(i-n)*v_i, R=rᵀH_(s+1,n)r.
Não alterar a fonte, os pesos, os centros, os cutoffs, as câmeras, nem os cruzamentos.

## 2. R é controlado pelo prefixo deslocado ANTIGO
Se H_(s+1,n) PSD, R>=0. Se for PosDef, o primeiro vínculo de ortogonalidade de Schur valer e h_(s+n) !=0, então r !=0 e R>0. Prova: r=0 força todos os coeficientes inferiores de v a zero, e a primeira linha ortogonal contradiz h_(s+n)!=0.
No setor par, usa o H_ímpar,n anterior; no ímpar, H_(2,n) é principal submatriz de H_par,n+1 pela identidade de zero padding já provada em NativeBoundaryBalance.lean.
ResiduePrefixGate.lean (nome real: ResidualPrefixGate.lean): R_nonneg, R_pos, residual_ne_zero_of_first_schur_row, R_pos_of_shifted_prefix_and_first_schur_row. Lean --wfail PASS.

## 3. Gate absoluto e orçamento TFVD
ResidualDominanceGate.lean PASS prova, para alpha,beta>=0:
  4R > alpha|B|+beta|ap| => W>0.
E uma versão com heads e erros:
  |B-B_head| <= e_B, |p-p_head|<=e_p,
  4R>alpha(|B_head|+e_B)+beta|a|(|p_head|+e_p) => W>0.
Erro e head devem ser produzidos pela fonte real, não assumidos como já comprovados.

Teste numérico nos momentos centrais armazenados: n=2..40 nos dois setores satisfazem o gate (78 casos). n=1 falha por ser uma cota conservadora.
n | custo/(4R) par | ímpar
2 | .67733117 | .18108729
4 | .0014905 | .00023647
8 | 7.389e-12 | 4.902e-13
40 | 5.111e-126 | 3.727e-128

## 4. Pisos log-convexos
O último momento novo em W é h_(s+2n+1) e aparece com coeficiente alpha>0 (apenas célula i=j=n, v_n=1).
Defina gap=h_(s+2n+1)-h_(s+2n)^2/h_(s+2n-1). Logconvexidade local implica gap>=0.
Então W=W_floor+alpha*gap, e W_floor depende só até h_(s+2n).
LastMomentSplit.lean PASS prova a separação e a cota de W pelo piso; em n=1..40, ambos setores, W_floor>0 numericamente (80 casos).
O contramodelo racional ControleRacional.lean (PASS) mostra que logconvexidade + H3 PosDef não asseguram o sinal para uma fonte arbitrária.

## 5. Forte redução: primeiro modo ortogonal
u=Σ_(i<n) r_i*h_(s+1+i) é o pairing do residual contra o monômio constante no prefixo deslocado.
H_(s+1,n) PSD e h_(s+1)>0 => R>=u²/h_(s+1) (Cauchy-Schwarz).
Assim:
  4*u²/h_(s+1) > alpha*|B|+beta*|ap| => W>0.
SingleModeGate.lean PASS prova a implicação escalar condicionada à desigualdade de Cauchy-Schwarz; não prova isoladamente a sua instanciação para a fonte.

Teste numérico: o gate DO PRIMEIRO MODO é satisfeito para n=2..40, nos dois setores (78 casos); n=1 falha:
n | custo/(4u²/h_(s+1)) par | ímpar
2 | .873825 | .211379
4 | .0022713 | .0002745
8 | 1.097e-11 | 5.636e-13
40 | 7.584e-126 | 4.285e-128
No n=40 a projeção no primeiro modo captura ~67.395% do R par e ~86.974% do ímpar. Os dois primeiros modos capturam ~98.0204% e ~99.5650% respectivamente.
Arquivos: first_mode_gate.py/json, R_modes.py e R_orthogonal_mode_decomposition.json. Testes não são certificados por intervalos ou Lean.

## 6. A ponte correta para TFVD/Green
A API existente preserva HH+HT+TH+TT da fonte na forma de Bézout em dois argumentos. Para transportar os três escalares u,B,p, devemos mapear seus vetores pelas transformações Toeplitz com o fator c0 original, e no setor H2 usar a inclusão com zero.
A cota histórica do orçamento é E_M*||z_x||_1*||z_y||_1. A projeção em um modo deixa UM dos argumentos de baixa ordem, mas a transformação Toeplitz não preserva automaticamente norma 1.
Precisamos certificar as cabeças e os erros e_u, e_B, e_p para os pares físicos, sem perder companion, return, cross, completion ou dressing.
Pondo lower_u=max(0,|u_head|-e_u), o gate final suficiente é:
  4*lower_u² >
   h_(s+1) * [alpha*(|B_head|+e_B)+beta*|a|*(|p_head|+e_p)].
Se o prefixo anterior for PSD, esse orçamento demonstra W>0. NÃO é um orçamento já certificado em toda ordem.
A cota histórica de cauda 16^(2r)/(M+1) aumenta com a ordem e não entrega uniformidade all-order.

## 7. Arquivos e checagens
Diretório: /home/thlinux/investigacoes/tilt_schur_20261120/
Compilados via lake env lean -DwarningAsError=true, exit 0:
ResidualPrefixGate.lean; ResidualDominanceGate.lean; LastMomentSplit.lean; SingleModeGate.lean; ControleRacional.lean.
Numéricos: curvatura_w.py e JSON de 450/750 dps, logconvex_gate.py/json, first_mode_gate.py/json, R_modes.py/json.
Código apenas na pasta de investigação; sem commit/push aos repositórios de pesquisa.
CurvatureGate_candidate_NOT_COMPILED.lean é candidato NÃO compilado por artefato histórico .olean faltante.
Ainda NÃO provamos W>0 nativo em toda ordem, positividade all-order dos pivôs, nem que zeros Genuine anulam o tilt.
