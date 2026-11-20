# Ponte nativa do escalar misto u ao TFVD/Green completado
Data: 20/11/2026. Máquina: HEX-LLM-AI-01.
Status: **transporte exato e orçamento condicional formalizados em Lean; verificação numérica com C3/64, C3/128 e C3/256; sem prova de sinal nativo all-order.**

## 1. Objetos e genealogia
A origem geométrica continua sendo a segunda diferença centrada C2 e sua carta Genuine; esta investigação consome a característica COMPLETADA e os seus momentos CANÔNICOS, não identifica C2 bracket, Genuine e F como o mesmo objeto.
Fonte de momentos Lean: nativeH = canonicalCompletedNativeLogDerivativeMoment.
Fonte de coeficientes Lean: nativeC = completedNativeRealEvenCharacteristicCoefficient.
A carta C3 é representante canônico para a síntese, não uma reinterpretação da origem.
Na direção crítica mônica v_i (i<=n), r_i=(i-n)v_i (i<n), o escalar é
   u_(s,n) = Σ_(i<n) r_i h_(s+1+i).
O residual do prefixo deslocado é
   R_(s,n)= rᵀ H_(s+1,n)r.
As identidades anteriores (CriticalReduction.lean / CanonicalBalance.lean) dão
   W_(s,n) = α_(s,n) B_(s,n) - β_(s,n) a_(s,n) p_(s,n) + 4 R_(s,n),
   α=(2n+s+1)(4n+2s+3), β=16n+8s+6;
   B=vᵀH_(s+1,n+1)v, a=v_(n-1), p=Schur(H_(s,n+1)).
Não se assumem novos sinais desses objetos.

## 2. Ponte TFVD formalizada (PASS Lean, sem sorry)
Arquivo: NativeMixedU.lean, import TwoEvenSourceMargin da infraestrutura real PR70.
- mixedSourceLift: T_r^{-T}x, com T_r=convolutionMatrix(nativeC,r). A inversão existe porque nativeC(0)≠0 (teorema nativo anterior).
- mixedSourceLift_transport: T_rᵀ(T_r^{-T}x)=x.
- native_mixed_pair_transport: xᵀH_(s,r)y = (T_r^{-T}x)ᵀ B_(s,r)(T_r^{-T}y), para s=0 ou 1.
- native_mixed_tfvd_four_terms: o pareamento bilinear NATIVO de dois vetores distintos se decompõe exatamente em HH+HT+TH+TT (cutoffs M,P independentes).
- native_shift_two_mixed: H_(s+2,n) é a restrição do H_(s,n+1) ao subespaço com primeiro endereço ZERO, também em dois argumentos distintos, não apenas na diagonal.
- nativeMixedU_pair, nativeMixedU_even_four_terms e nativeMixedU_odd_four_terms: transportam especificamente u; no setor par usam a carta fonte ímpar (b=true), no ímpar usam a fonte par (b=false) após zero padding.
- native_mixed_tfvd_error: cota em norma complexa pelo literalErrorBudget de HT,TH,TT para os dois vetores efetivamente transportados.
- nativeMixedU_even_error / odd_error e respectivas versões REAL: |u-Re HH|≤E_u com E_u calculado dos pares transportados.
- native_mixed_repartition_error e nativeMixedU_even_repartition_real_error / odd_repartition_real_error: mesmas cotas para QUALQUER repartição de bordo U, usando head=literalHead(M)+U e tail=literalTail(M)-U. A soma total continua igual à fonte original. Isso inclui como especialização a repartição C3 original originalBoundaryJet(M), definida na infraestrutura NativeRepartition64.
Compilação em Lean 4.32 com -DwarningAsError=true: PASS; produzido NativeMixedU.olean (na pasta da investigação).

## 3. Controle de R e Cauchy–Schwarz formalizado
Arquivos ProjectedCauchy.lean e NativeMixedCS.lean: PASS Lean.
O teorema ProjectedCauchy.projected_cs deriva Cauchy–Schwarz de uma matriz semidefinida positiva no pareamento original (sem Gram auxiliar).
nativeMixedU_cs_from_shifted_prefix:
Se H_(s+1,n) é PSD e h_(s+1)>0, então
  u² <= h_(s+1) * (rᵀ H_(s+1,n)r) = h_(s+1) R.
Não pressupõe p>0 nem W>0; PSD do prefixo ANTERIOR continua hipótese explícita. Para R>0, ResidualPrefixGate.lean anterior fornece critério com H_antecedente PosDef, primeira linha ortogonal e momento não nulo.

## 4. Gate conjunto e não circular para os três scalars
NativeSingleModeGate.lean: PASS Lean. Seu teorema native_single_mode_head_budget_gate assume:
- H_(s+1,n) PSD, h_(s+1)>0, a relação R=rᵀH_(s+1,n)r;
- α,β≥0;
- erros individuais |u-uM|≤eu, |B-BM|≤eB, |p-pM|≤ep;
- L=|uM|-eu>0;
- condição finita estrita:
    h_(s+1) * [α(|BM|+eB)+β|a|(|pM|+ep)] < 4 L².
Conclui, sem supor W>0 ou p>0:
    αB-βap+4R > 0.
Com a IDENTIDADE Euler–Schur antiga, esse resultado é a porta condicional W>0.
As hipóteses de erro podem ser preenchidas pela fonte TFVD por native_mixed_repartition_error para u, B e p com os vetores reais corretos e seus próprios endereços/câmeras.
O próprio gate está formalizado; sua hipótese final de margem ainda NÃO foi certificada em toda ordem.

## 5. Diagnóstico de regressão numérica C3 da fonte original
Arquivo: c3_mixed_u_budget.py. Reconstrói C3 head e correção originalBoundaryJet de coeficientes [728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1]/729; preserva os endereços 3m+2,3m+3,3m+4, os multiplicadores Gamma/archimedianos e os quatro cruzamentos.
Coeficientes canônicos h vieram de momentos512.json. O único c0 de alta precisão foi inicializado, para CONFERÊNCIA NUMÉRICA apenas, pela identidade clássica de xi(1/2); não constitui a genealogia ou prova da construção. Os coeficientes seguintes vêm da recorrência canônica c[n+1]= -Σ h[k]c[n-k]/(n+1).
Cálculos com 115 dps; não são intervalos certificados. O par TFVD reconstruído bate com o produto fonte de momentos em diferenças muito inferiores à precisão útil.
Para cada n e s, monta o vetor crítico mônico original v, seu Euler residual r, os pares mistos u, B e p com T_r^{-T}, a cabeça HH reajustada, os três cruzamentos de erro e a razão suficiente:
  Q = h_(s+1) * [α(|BM|+eB)+β|a|(|pM|+ep)] / [4 max(0,|uM|-eu)²].
Q<1 é suficiente, SE esses orçamentos se tornarem certificados da fonte.

Cutoff   | passa em setor par           | passa em setor ímpar
M=64     | ordens n=2..6               | ordens n=2..5
M=128    | ordens n=2..7               | ordens n=2..7
M=256    | ordens n=2..8               | ordens n=2..8
n=1 exige uma desigualdade menos conservadora: Q>1 em ambos os setores embora W(centro)>0 por resultados anteriores.

Valores perto da fronteira:
M=64,n=7:   Q_par≈16.8427343, Q_ímpar≈74.3372919 (não fecha).
M=128,n=7:  Q_par≈0.0708370219, Q_ímpar≈0.519907321 (fecha).
M=256,n=8:  Q_par≈0.0194034483, Q_ímpar≈0.143320788 (fecha).
M=256,n=9:  Q_par≈1.40657791, Q_ímpar≈6.53940146 (não fecha).
Na ordem n=9, a razão IDEAL sem orçamento é par≈4.18990225e-14, ímpar≈1.61020162e-15; portanto o teste não revela falha do sinal, só perda de eficácia da cota no cutoff.

M=256,n=9: erro relativo E_u/|u|≈1.45e-13 (par), 6.86e-12 (ímpar), ainda minúsculo. Entretanto E_B/|B|≈1.68e14 (par), 2.21e16 (ímpar), devido ao cancelamento severo na forma quadrática deslocada B; E_p/|p|≈2.32e12 e 3.55e14. Na conta CONSERVADORA α(|B_M|+E_B)+β|a|(|p_M|+E_p), B representa aproximadamente 92.7% do custo par e 91.3% do ímpar para n=9. Logo o gargalo real passou a ser a margem de B e p, não a projeção mista u.
Não comparar o primeiro modo ortogonal do Hankel com a semente material C2/TFVD sem uma identificação de endereços adicional; a ponte demonstrada aqui é pelo núcleo bilinear e pelo transporte Toeplitz.

## 6. Próximo gate de pesquisa
A primitiva mais promissora é uma cota CORRELACIONADA do canal restante
  S=α B - β a p,
não a soma de majorantes separados α|B|+β|ap|. O objetivo é explorar a identidade Euler–Schur, Bézout e os cruzamentos TFVD/Green para manter os cancelamentos de S na mesma cabeça/cauda e comparar a parte assinada de S diretamente com 4R, ou com o piso 4u²/h.
Alternativamente, produzir uma lei explícita da escolha de cutoff M(n) e um orçamento que acompanhe a margem nativa de cada ordem. A convergência para cada ordem fixa NÃO fornece sinal all-order sem uma margem de fonte não circular.
O tilt radial refletido e a curvatura ainda não demonstram que todo zero Genuine mora no centro; essa obrigação permanece logicamente separada.

## 7. Arquivos e comandos, status
Diretório /home/thlinux/investigacoes/tilt_schur_20261120/
Novos:
- NativeMixedU.lean / NativeMixedU.olean
- ProjectedCauchy.lean / ProjectedCauchy.olean
- NativeMixedCS.lean / NativeMixedCS.olean
- NativeSingleModeGate.lean
- c3_mixed_u_budget.py
- c3_mixed_u_B_p_n4_numeric.json e c3_mixed_u_B_p_M128_n7_numeric.json e c3_mixed_u_B_p_M256_n9_numeric.json
- arquivos de log das verificações.
Validação Lean --root na pasta da investigação; importações da .cache de research/tfvd-bezout-schur-residual, em CSA/Lean 4.32; erros de compilação 0 nos módulos finais.
Nenhum commit/push realizado. Os repositórios de pesquisa originais não foram alterados nesta investigação; artefatos mantidos em pasta separada.
