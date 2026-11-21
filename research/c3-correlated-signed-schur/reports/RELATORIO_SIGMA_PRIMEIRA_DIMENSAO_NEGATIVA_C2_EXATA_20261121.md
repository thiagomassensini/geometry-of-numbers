# Investigação: primeira DIMENSÃO negativa, σ→1/2 e pivô físico C2

**Data:** 21/11/2026. **Status:** pesquisa numérica reprodutível + auditoria de Lean preexistente; não há prova all-order nova nesta rodada. Não se assume RH nem se usam zeros como entrada.

## 1. A pergunta original

A tese é estudar a possível divergência da primeira dimensão N de uma matriz Hankel inteira que perde PSD quando d=σ−1/2→0, mantendo a fonte completada genealogicamente correta:
bracket C2 → Genuine → N(z) → F(z)=A(z)N(z) → −F'(z)/(2F(z)) → jets → Hankel/Schur.

A distinção de índices é obrigatória: k é profundidade C2; M cutoff material; s deslocamento de uma janela 2×2; n índice do pivô crítico; N=n+1 dimensão do bloco inteiro; d é deslocamento transversal.

## 2. Dados e metodologia

Fonte reaberta:
momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105/quartic_frontier_native_strip.json,
que contém 48 momentos centrais em precisão de 230 decimais, extraídos da cabeça C2 + cauda Hurwitz EXATA + fator de câmera + Gamma do completion, sem qualquer altura como input.

Para d não nulo, usamos a identidade de Taylor LOCAL (analiticamente tratada na GoN SigmaTransverseAllOrder):
h_n(d) = sum_j (-1)^j binom(2n+2j+1,2j) H_(n+j) d^(2j),
H_n=h_n(0).
Truncamos a série pelos 48 H disponíveis. Isso é um truncamento NUMÉRICO transversal, não um erro na cauda C2.

Reconstruímos as seções originais A_(s,N)(d)=[h_(s+i+j)(d)] para s=0,1, e usamos LDL com pivôs de Schur em mpmath a 180 dps. Primeira dimensão negativa = primeiro n+1 cujo pivô LDL fica negativo com prefixos anteriores positivos.

## 3. Resultado observado: primeira dimensão negativa da Hankel inteira

| d | Par | Ímpar |
|---:|---:|---:|
| 0.2 | 5 | 4 |
| 0.1 | 5 | 5 |
| 0.05 | 5 | 5 |
| 0.02 | 6 | 5 |
| 0.01 | 6 | 6 |
| 0.001 | 7 | 7 |
| 1e-5 | 9 | 8 |
| 1e-7 | 11 | 10 |
| 1e-9 | 12 | 12 |
| 1e-11 | 13 | 13 |
| 1e-13 | 15 | 14 |
| 1e-15 | 16 | 16 |

O controle numérico central d=0 encontrou os primeiros 17 blocos positivos nos dois setores; não implica all-order.
Repetimos a extração de jets usando 12 e 18 termos transversais e obtivemos os mesmos primeiros índices negativos em todos os testes. Precisão arbitrária não é aritmética intervalar.

Distinção revelada: d=0.2 tem primeira JANELA negativa deslocada em s=7, mas primeira matriz inteira não PSD em N=5 (par) e N=4 (ímpar). Janelas 2×2 não determinam a dimensão full; ver contraprova Lean já formalizada TransverseTwoWindowNotEnough.

## 4. Teste independente de reconstrução transversal

scripts/sigma_full_hankel_direct_c2_checks.py: avalia os momentos DESLOCADOS diretamente com cabeça C2 L=12, cauda Hurwitz exata e completion original, extraídos por círculo Cauchy de raio 0.25 (sem zeros).
- d=0.2; 165 dps, 224 amostras: primeiro negativo par N=5, ímpar N=4.
- d=1e-5; 235 dps, 256 amostras: par N=9, ímpar N=8.
Os pivôs negativos coincidiram com a reconstrução transversal nos 30 dígitos apresentados. Isso é confirmação numérica independente da técnica, não prova intervalar de sinal.

## 5. Raio crítico de cada pivô e curvatura original

Em GoN native-moving-schur-sigma/MovingSchur.lean, o teorema moving_schur_curvature_expanded (sob IsUnit do prefixo antigo) já demonstra:

p_(s,n)''(0)
= -2 sum_(i,j=0)^n v_i v_j (s+i+j+1)(2(s+i+j)+3) H_(s+i+j+1),

onde v é o MESMO vetor monic da direção crítica de Schur; todos os cruzamentos são mantidos. A simetria d→−d implica p'(0)=0. Se p(0)>0 e p''(0)<0, o estimador é rho=sqrt(-2p(0)/p''(0)), com resto O(d^4) não uniformemente certificado em n.

Raízes numéricas de p_(s,n)(d) (reconstruído da fonte C2 original), por ordem n:

| n | raiz par | raiz ímpar |
|---:|---:|---:|
| 3 | nenhuma abaixo de 0.25 | 0.112982707793303 |
| 4 | 0.043927446061723 | 0.016160667846670 |
| 5 | 0.005709056049746 | 0.001773959283190 |
| 6 | 0.000496637003548 | 0.000124862145499 |
| 7 | 0.0000309561565054 | 0.00000771403582270 |
| 8 | 0.00000199913026823 | 0.000000497088706826 |
| 9 | 0.000000115737617402 | 0.0000000249680364817 |

Nos pivôs 7–9, o estimador quadrático ficou a aproximadamente 0.13%–0.21% das raízes do modelo transversal reconstruído. Os raios decrescem aproximadamente exponencialmente no pequeno conjunto finito, o que sugere N_neg(d) da ordem de log(1/|d|), mas não foi provado uniformemente para todos n.

## 6. O resultado formal já EXISTENTE de dimensão 6

A inspeção da fonte GoN research/native-local-sigma-positivity/FiniteNeighborhood.lean trouxe:
- sigmaMatrix_finite_eventually_posDef: se um H_N central é PosDef, o H_N deslocado permanece PosDef numa vizinhança de 0, em qualquer N FIXO;
- both_six_sigmaMatrices_eventually_posDef: usando os certificados centrais originais CarrySixthEven.even_source_six_posDef e CarrySixthOdd.odd_source_six_posDef, existe delta6>0 com as DUAS seções H6(d),K6(d) positivas definidas quando |d|<delta6;
- não existe raio numérico explicitado nem positividade em dimensão arbitrária.

Esse resultado entrega rigorosamente N_neg(d)>6, nos dois setores, perto da linha. Os nossos experimentos confirmam qualitativamente o mesmo comportamento sem substituir essa prova.

O teorema Lean novo de 21/11, já publicado no commit 9127eec, formaliza a implicação CONDICIONAL:
primeira dimensão negativa foge para infinito (em cada setor) => TODOS Hankel canônicos no centro PSD => HH+HT+TH+TT exato é não negativo em todas as ordens.
O antecedente para todos os N AINDA NÃO está provado.

## 7. Risco de circularidade e próximo lema independente

Com a não recorrência incondicional já provada no CSA, all-prefix PSD central implica PD de cada prefixo. Pelo teorema de estabilidade acima, PD de cada prefixo implica fuga da primeira dimensão negativa. Portanto, a fuga full-dimensional e a PSD central all-order são essencialmente duas formas da MESMA obrigação: provar fuga usando positividade de todos pivôs centrais como entrada é CIRCULAR.

Para progredir genuinamente pela geometria:
1. Derivar para todo n uma desigualdade do carrier C2/Genuine/TFVD e do completion Gamma que entregue margem estrita física original p_(s,n)(0)>0 (ou não negatividade com não recorrência), sem utilizar a conclusão como hipótese.
2. Combinar a curvatura exata p''_(s,n)(0) com um majorante QUÁRTICO controlado do resto da série transversal, usando GoN #131 e SigmaTransverseAllOrder, para obter um raio positivo δ_n (não precisa uniforme em n).
3. Preferir a conservação material Bessel Primos #34 e o critério incidente–retorno CSA #124 para PRODUZIR a margem em vez de supô-la.
4. Controlar prefixos singulares pela versão sem inversa da GoN #41.

**Status honesto:** o conjunto de experimentos fortemente sustenta a lei de fuga em ordens testadas e a conecta diretamente à curvatura de Schur original, mas não prova n arbitrário nem RH. Não houve nova declaração Lean de positividade incondicional all-order.

## 8. Reprodução na VM

- scripts/sigma_full_hankel_ldl_probe.py → scripts/sigma_full_hankel_ldl_probe.json (180 dps);
- scripts/sigma_full_schur_critical_radii.py → scripts/sigma_full_schur_critical_radii.json (145 dps);
- scripts/sigma_full_hankel_direct_c2_checks.py → scripts/sigma_full_hankel_direct_c2_checks.json (165 e 235 dps);
- Fonte: original central C2 quartic_frontier_native_strip.json e módulo c2_window_first_negative.py do repositorio momentos.
