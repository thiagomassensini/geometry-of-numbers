# Checkpoint — identidade complexa C2 e gate de sinal Cauchy–Pick

Data: 2026-11-17
Branch: task/gon-complex-identity-pick-valve-20261117
Base: GoN PR #334, commit ef41fa1. Nenhum merge.
Comparador: CSA no cache já existente, sem nova dependência Lake.

## 1. Identidade complexa rigorosa

No módulo GeometryOfNumbers/Analysis/CarryMaterialComplexAnalyticIdentity.lean:

- analyticAt_eventuallyEq_of_forall_real: dois germes analíticos
  que concordam para toda altura real coincidem numa vizinhança complexa.
  Prova pela sequência não nula 1/(n+1) no eixo real.
- carryMaterialComplexValueReadout_analyticAt_zero: analiticidade do
  readout físico C2, vinda da soma normada de gradientes materiais.
- carryMaterialComplexDressedState_analyticAt_zero: analiticidade do
  VETOR físico C2 inteiro, necessário para identificar companheiros.

O comparador GoN–CSA em
research/material-central-calibration/CanonicalComparison.lean
contém as identificações:
- material_complex_value_eq_native_germ:
      F_C2(z)=F_native(z)
- material_complex_companion_eq_native_germ:
      Psi_C2(z)=Psi_native(z)=-F_native'(z)
- material_complex_response_eq_native_germ:
      R_C2(z)=R_native(z)
- material_complex_Pick_eq_native_germ: identidade de Cauchy–Pick
      físico versus nativo para cruzamentos não refletidos
- material_complex_source_chiral_quotient_eq_native_germ:
      quociente Hermite–Biehler físico versus canônico.
- material_complex_Pick_eq_native_dslope_germ:
      K_C2(z,w) = canonicalCompletedNativePolarizedDslopeKernel(z,w)
      num germ complexo para w != conj(z), com domínio native
      certificado pelo aberto de alturas.

Tudo em uma VIZINHANÇA COMPLEXA de z=0. A prova usa a igualdade
física REAL previamente certificada, mas nunca define a fonte pelo alvo.
Não há estimativa explícita do raio, nem extensão global provada.

## 2. Equivalência de positividade para cada seção finita

Módulo GeometryOfNumbers/Analysis/CarryMaterialComplexPickSignGate.lean.

Para alturas z_i com Im z_i>0, e F_C2 e coordenada HB+ não nulas:

  G_ij = i/(z_j-conj(z_i))
  q_i = (Psi_C2(z_i)-i F_C2(z_i)) /
        (Psi_C2(z_i)+i F_C2(z_i))
  D_ij = G_ij (1-conj(q_i)q_j)
  a_i = (Psi_C2(z_i)+i F_C2(z_i))/(2F_C2(z_i))

  K_C2 = diag(a)^* D diag(a)

O diagonal é inversível, pois seus fatores são não nulos.
Portanto, demonstrado em Lean:

       K_C2.PosSemidef <-> D.PosSemidef.

Teoremas:
- carryMaterialComplexSourcePickMatrix_eq_gaugedDefect
- carryMaterialComplexSourcePickMatrix_posSemidef_of_sourceDefect
- carryMaterialComplexSourcePickMatrix_posSemidef_iff_sourceDefect

Esta é uma equivalência de SINAL, mas NÃO prova que D seja PSD.

## 3. Canários mpmath 90 dígitos, não intervalares

Script: pick_multiplier_sign_probe.py
JSON: pick_multiplier_sign_probe.json

Fonte: seed C2 + soma exata de segundas diferenças
[4k+3,4k+4,4k+5], continuada por Hurwitz, câmera base 2 e
dressing arquimediano. A zeta não é definição da fonte.

| Amostra | N | menor autovalor Pick | menor autovalor D |
|---|---:|---:|---:|
| alturas imaginárias | 3 | +1.356e-12 | +5.376e-12 |
| alturas complexas | 4 | +5.666e-16 | +2.247e-15 |
| alturas imaginárias | 5 | +4.086e-24 | +1.621e-23 |
| alturas complexas | 6 | +3.971e-26 | +1.572e-25 |

Reconstrução K pela gauge D: erro menor que 1.2e-90.
Evidência numérica apenas; não constitui prova de sinal.

## 4. Próxima obrigação matemática

Provar a desigualdade coletiva do multiplicador:

  sum_ij conj(c_i) * G_ij *
    (1-conj(q(z_i))q(z_j)) * c_j >= 0

para todas as alturas físicas regulares no domínio e toda seção
finita, com qualquer vetor de coeficientes c.

A desigualdade pontual |q(z)|<=1 NÃO garante esta condição
matricial. A isometria Cauchy–Laguerre do CSA também não fornece,
sem novo transporte, esse fato para os materiais GoN.

Sem esta desigualdade, não estão demonstradas a positividade
all-order dos momentos/Hankels nem a RH.

## 5. Auditoria

Lean 4.32: focado com -DwarningAsError=true, comparador GoN–CSA.
Axiomas verificados: propext, Classical.choice, Quot.sound.
Sem sorry, sem novo axioma e sem merge.
