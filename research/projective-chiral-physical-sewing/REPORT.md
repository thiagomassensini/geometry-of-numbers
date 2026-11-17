# Costura física C2 → projetivo-quiral → característica nativa completada

Data: 2026-11-17
GoN branch: task/gon-projective-chiral-c2-sewing-20261117 (base origin/main ca62176).
CSA branch: task/projective-chiral-parseval-20261117 (PR #128).

## Proveniência

A fonte é o estado COMPLETO baseTwoCompletedBoundaryHilbertState e o
companion clockado, via carryMaterialCompanionValuePair.
O complemento carryMaterialPairComplement guarda a parte invisível ao
readout seed + retorno global, incluindo o interior material.

O carrier é o real MaterialCarrier complexo em soma Hilbert:
CarryMaterialCompleteChiralArm = WithLp 2 (MaterialCarrier × MaterialCarrier).

Os DOIS braços materiais são
 P_plus(t) = (C_t+i V_t, Q(C_t-i V_t))
 P_minus(t) = (C_t-i V_t, Q(C_t+i V_t))
em que Q age componente a componente no par, não é uma constante.
A troca de chirality no complemento é essencial.

## GoN Lean - novo módulo

GeometryOfNumbers/Analysis/CarryMaterialProjectiveChiralSewing.lean

- carryMaterialChiralLegs_green:
  diferença de Grams quirais = -2i vezes o Green ordenado.
- carryMaterialCompleteChiralDifference_eq_green:
  a diferença física subtrai o Green do complemento Q.
- carryMaterialCompleteChiralGreenPairing_eq_physical:
  o quarto de volta i/2 restitui exatamente o balanço completo.
- carryMaterialCompleteChiralGreenPairing_eq_valve:
  o balanço é literalmente carryValveReturnGreen eta t u, eta != 0.
- carryMaterialCompleteChiralValveMatrix_eq_gramDifference:
  identidade matricial para TODOS os pares i,j, sem apagar os cruzamentos.

Os dois Grams separados são positivos, a diferença ASSINADA não é
positiva automaticamente.

## CSA e comparação GoN–CSA

Novo arquivo CSA:
CarrySelfAdjointOperator/RealAxisWronskianDslopeSewing.lean

Identidade genérica COMPLETAMENTE DIVISION-FREE:
 W_F(w,z) = 2 F(z) F(w) (w-z) dslope(R)(z,w)
 R = Psi/(2F).
Exige F(z),F(w) != 0 e conjugação real de F(z) e Psi(z).
O resultado usa a identidade universal sub_smul_dslope.
A versão canônica herda realidade de F e derivada no eixo real.

Arquivo externo de comparação GoN existente:
research/material-central-calibration/CanonicalComparison.lean
(no final, três teoremas novos)
- material_chiral_source_eq_completed_native_wronskian:
  a fonte física, com Q, reproduz o Wronskiano nativo completado.
- material_chiral_source_eq_native_dslope_numerator:
  conserva 2 F(t) F(u) (u-t) sem dividir na diagonal.
- material_chiral_matrix_eq_native_dslope_numerator:
  mesma identidade para qualquer matriz de amostras reais sem zeros
  de F. Preserva todos os pares i,j.

A relação é exata inclusive em t=u, mas a igualdade 0=0 nessa
diagonal NÃO determina dslope(R)(t,t); precisa limite derivativo.

## O que permanece aberto

1. A ponte fonte GoN -> carrier literal CPFormal.Analytic.Cp.CarryVerticalL2
   da PR CSA #128 ainda não foi construída. Esta etapa conserva o
   MaterialCarrier original e não o identifica automaticamente com ele.
2. O denominador (u-t) não é fator separável por índice. Sua remoção
   requer o mecanismo Cauchy/espectral correto, não uma isometria pura.
3. A fonte GoN está parametrizada por tempos reais. A grade radial
   Cauchy–Pick CSA usa pontos imaginários z_i=i(i+1)/(k+1).
   Ainda não foi construída a extensão física de pares para essa grade.
4. Não há prova de contrato para TODAS as combinações complexas
   finitas, nem positividade all-order ou não degenerescência.
5. A válvula de profundidade codifica fielmente os bordos e a massa,
   mas não deve ser confundida com a métrica de energia.

## Evidências e comandos

GoN:
 lake env lean -DwarningAsError=true
   GeometryOfNumbers/Analysis/CarryMaterialProjectiveChiralSewing.lean
 lake build GeometryOfNumbers.Analysis.CarryMaterialProjectiveChiralSewing

Cross:
 Compilar CanonicalComparison.lean com os paths de GoN e CSA,
 Lean 4.32, mesmos pins de mathlib/GreenFrame.
O log de auditoria foi salvo em
 research/projective-chiral-physical-sewing/crosscheck.log

O #print axioms dos teoremas novos contém somente
 propext, Classical.choice, Quot.sound.
Sem sorry, admit ou axiomas extras.

## Próxima obrigação física

Construir o levantamento de dois braços nativos para um carrier Cauchy
em uma grade pertinente, preservando a forma assinada com
o fator de separação (e o limite diagonal). Em seguida, demonstrar
a contração da saída em relação à incidência para todas as
combinações finitas. A identidade escalar não substitui esse passo.
