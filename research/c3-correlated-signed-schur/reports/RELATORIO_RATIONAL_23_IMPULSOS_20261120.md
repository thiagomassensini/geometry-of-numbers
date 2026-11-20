# Continuação Lean: 23 caixas C3, expansão por impulsos e orçamento assinado
**20 de novembro de 2026 — branch research/c3-correlated-schur-tfvd-20261120**

## Resultado novo comprovado
Partindo exclusivamente dos jatos da característica completada NATIVA (F=A*N), e da cauda original C3/TFVD com seus 12 pesos de bordo, foram compilados os seguintes módulos adicionais:

- `C3TwentyThreeBoxes.lean`: `all_twenty_three_c3_bounds` prova, para cada `j : Fin 23`, `‖literalTail 384 j - originalC3BoundaryJetAny 384 j‖ ≤ completedC3TailJetEnvelope 384 j`; `original_c3_linear_23_budget` consome todas as 23 caixas no orçamento do núcleo assinado. Sem números importados, sem sinal hipotético.
- `C3ImpulseLinearity.lean`: demonstra a homogeneidade em **ambos** os argumentos do kernel misto, separadamente, usando o `mixed_kernel_coefficient` original, e a homogeneidade de `coefficientPair`.
- `C3ImpulseExpansion.lean`: `signedSourceLinearMap` é um verdadeiro mapa linear em T. `prefixTail_eq_impulse_sum` decompõe o prefixo em impulsos. `signed_linear_impulse_expansion` prova a expansão de `L_H(T)` para quaisquer dimensões de blocos com `2rB<N` e `2rP<N`. **A antiga premissa `hCoeff` foi eliminada**: os coeficientes `ell_j` são o valor da própria resposta linear no impulso unitário da fonte, antes de aplicar valor absoluto.
- `C3JointSource384.lean`: `original_c3_head_tail384` demonstra o split exato da mesma fonte nativa `nativeC`, com o bordo adicionado à cabeça e subtraído da cauda. `original_c3_joint_source_budget384` usa caixas *Lean*, impulso exato e somente uma premissa remanescente sobre TT.
- `C3JointQuadraticBudget.lean`: `signed_quadratic_source_bound` dá `TT ≤ |α| directionalBudget(T,T,B)+|βa| directionalBudget(T,T,p)` sem supor positividade. `original_c3_joint_source_budget384_with_TT` remove também a premissa `hQuad`.
- `C3QuadraticRational384.lean`: `responseCoefficient_box`, `coefficientBudget_le_box` e `directionalBudget_le_box` transportam **todas as cotas racionais de jatos, em qualquer índice**, até uma cota explícita para TT. Finalmente `original_c3_joint_source_budget384_rational` prova uma desigualdade para o erro *total* do funcional assinado S, sem hipóteses `hCoeff`, `hQuad` ou interpolação por dados Arb.

Todos esses objetos usam a mesma fonte completada `nativeC` e o mesmo transporte original Bézout. Não presumem Grams de Green positivos.

## Estado da certificação de sinal

O novo teorema tem a forma
\[
 \|S(C,C)-S(H,H)\| \le
 \sum_{j=0}^{22} |\ell_j(H)| \,\varepsilon_j
 + Q_{\rm TT}(\varepsilon;z_B,z_P,\alpha,\beta a),
\]
com os `eps_j` e `Q_TT` explicitados em Lean. O teorema é de **erro da fonte**, não um certificado de que `W>0`.

**O que NÃO foi fechado:** as caixas Arb de 320 dígitos, muito mais estreitas, ainda não possuem no Lean uma prova de que os coeficientes da fonte original estão dentro dos respectivos intervalos. Os limites Lean para 23 jatos são os envelopes Cauchy/14ª diferença, crescem em j e tornam-se grosseiros. Consequentemente, não anunciamos 18 sinais de W como teoremas. As 18/18 verificações Arb externas anteriores permanecem dados reproduzíveis, não novas provas kernel.

A próxima obrigação genuína é obter as **caixas finas diretamente em Lean**, por controle termo a termo das derivadas da fonte C3 acelerada (em vez do envelope uniforme no círculo de Cauchy), mantendo completion/Gamma e ambas as pernas; e certificar uma desigualdade **estrita** para o sinal na ordem desejada. As identidades provadas nesta rodada reduzem o problema a essa obrigação, sem as hipóteses abstratas de impulso ou do termo TT.

## Comparação com a positividade já provada
- `CarrySeventhEven.even_source_seven_posDef`: fonte completada par 7×7 positiva; teorema anterior.
- `CarrySixthOdd.odd_source_six_posDef`: fonte completada ímpar 6×6 positiva; teorema anterior.
- `CarrySeventhOddCanonical.k7_matrix_posDef_iff_theta26_theta28_gate`: ordem ímpar 7×7 reduzida a um gate teta, não sinal fechado por aquela declaração.
- **Novo:** controle da *curvatura* `W = αB−βap+4R`, diferente do sinal de p, compatível com a positividade de prefixos já certificada. A versão `NativeOldPrefixSignedGate` usa só o prefixo anterior de tamanho correto.

## Proveniência / reprodução
- `validate-vm.sh` compila e audita os módulos em Lean/Mathlib 4.32 com os caches locais originais, sem tocar outros worktrees.
- `AuditC3Rational384.lean` consulta axiomas usados no teorema final.
- A definição do bracket C2, a síntese Genuine, a função nativa N e o fator A de completion são objetos distintos; esta pasta estuda a resposta da fonte **completada** em câmera C3.
- Sem afirmações all-order, RH ou equivalência de zeros Green/Genuine sem ponte adicional.

Nenhum valor de zero crítico foi usado como entrada da prova.

## Corolários Lean por setor na ordem 9

`C3NativeNineCertifiedError.lean` especializa a desigualdade original em
`native_even_nine_c3_signed_error` e `native_odd_nine_c3_signed_error`.
No primeiro setor, ambas as fontes usam a carta 10×10; no segundo, a
perna de B usa a carta 11×11 com coordenada zero inicial, e a de p usa
a carta 10×10. Ambos dependem dos mesmos 23 jatos T₀…T₂₂ do completamento
C3/384. Os enunciados quantificam qualquer vetor real de Schur de
tamanho 10, portanto não injetam um vetor ajustado à resposta numérica.

**Status:** Lean --wfail PASS; auditoria `AuditC3NativeNine.lean`
retornou exclusivamente `[propext, Classical.choice, Quot.sound]` nos
dois teoremas. São certificados FORMAIS DE ERRO, não provas da
desigualdade de margem `W>0` para n=9.
