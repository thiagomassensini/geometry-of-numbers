# Auditoria numérica: operador finito de alturas dos momentos canônicos

## Pergunta

Partindo de momentos canônicos antes da ortogonalização, a matriz Hankel finita efetivamente fatoriza em quadrados? Qual é a Jacobi e o operador de alturas daí obtido?

**Resposta:** Sim para as ordens finitas 4 e 6 efetivamente calculadas. Não é uma demonstração para toda ordem.

## Origem dos momentos e ausência de ajuste

1. O germe da característica completada é avaliado pela expressão clássica `xi(s)=1/2*s*(s-1)*pi**(-s/2)*gamma(s/2)*zeta(s)` na linha `s=1/2+it`. Essa avaliação não chama theta nem recebe zeros como entrada. A proveniência geométrica é assegurada pela identidade de sequências já auditada no Lean, não reconstruída independentemente neste script.
2. Os coeficientes pares `phi_n=[t^(2n)]xi(1/2+it)` são extraídos por Cauchy em círculo, com 105/125 dígitos internos e uma segunda quadratura independente (mais nós e raio distinto).
3. Os momentos `h_n=[u^n](-Phi'(u)/Phi(u))` são calculados pela recorrência exata `h_n = (-(n+1)phi_(n+1) - sum_(k<n) h_k phi_(n-k))/phi_0`.
4. Só após criar os momentos definimos `G_N=(h_(i+j))`, `K_N=(h_(i+j+1))`, fazemos `G_N=L L^T`, `J_N=L^-1 K_N L^-T` e `T_N=J_N^-1/2`.
5. A escolha de `L` pelo Cholesky é um procedimento finito para testar positividade, não um dado de entrada dos momentos, nem uma fonte geométrica all-order.

## Resultado: N=4 (matrizes completas)

### G₄ = Hankel canônica
```text
        0.0231049931        3.71725993e-5        1.44173931e-7        6.6303168e-10
       3.71725993e-5        1.44173931e-7        6.6303168e-10       3.21366415e-12
       1.44173931e-7        6.6303168e-10       3.21366415e-12       1.58769345e-14
       6.6303168e-10       3.21366415e-12       1.58769345e-14       7.90332572e-17
```

### K₄ = Hankel deslocada
```text
       3.71725993e-5        1.44173931e-7        6.6303168e-10       3.21366415e-12
       1.44173931e-7        6.6303168e-10       3.21366415e-12       1.58769345e-14
       6.6303168e-10       3.21366415e-12       1.58769345e-14       7.90332572e-17
      3.21366415e-12       1.58769345e-14       7.90332572e-17        3.9464714e-19
```

### L₄ com G₄=L₄L₄ᵀ
```text
         0.152003267                  0.0                  0.0                  0.0
      0.000244551318       0.000290462707                  0.0                  0.0
       9.48492322e-7         1.4841032e-6        3.33862487e-7                  0.0
       4.36195678e-9        7.39145446e-9         2.3062513e-9       2.32800871e-10
```

### J₄ (Jacobi)
```text
       0.00160885567        0.00191089779       1.9716122e-108      -8.6886566e-108
       0.00191089779        0.00350058924        0.00114941602      1.56846684e-107
     8.01951025e-109        0.00114941602        0.00179834314       0.000697295682
     -4.0910604e-108      2.29292146e-107       0.000697295682        0.00121717883
```

### T₄=J₄^(-1/2), operador de alturas
```text
           60.480116          -34.1324137           23.8547255          -12.3919097
         -34.1324137            41.038768          -22.6872399           11.2446732
          23.8547255          -22.6872399           41.8010554          -15.5002584
         -12.3919097           11.2446732          -15.5002584           36.1841977
```

### Pivôs de Schur da Hankel

| Pivô | G₄ | K₄ |
|---:|---:|---:|
| 0 | 0.02310499311541897 | 3.717259928526969e-5 |
| 1 | 8.436858410134152e-8 | 1.038530676384723e-10 |
| 2 | 1.114641604496789e-13 | 8.081775961674645e-17 |
| 3 | 5.419624538381705e-20 | 2.96226172771769e-23 |

### Demonstração numérica da forma quadrática como soma de quadrados

Para o vetor `x=(1,-2,3,-1)^T`, a forma `x^T G_4 x` é a soma dos quadrados das quatro coordenadas de `L_4^T x`.

`xᵀG₄x = 0.02295773521683082961938`

`||L₄ᵀx||² = 0.02295773521683082961938`

Isso independe de zeros fornecidos como input e verifica apenas o prefixo de ordem 4.

### Espectro do operador finito de alturas N=4

| λ(J₄) | altura 1/√λ |
|---:|---:|
| 0.005004981601588946 | 14.13509583517826 |
| 0.002153524212392408 | 21.54890073192545 |
| 0.0008840987777807698 | 33.63176075304296 |
| 8.236228856250882e-5 | 110.1883797718456 |

## Resultado N=6: repetição sem ajustar momentos

| Ordem N | Pivôs G positivos | Pivôs K positivos | erro máximo G−LLᵀ | erro máximo J fora da tridiagonal |
|---:|:---:|:---:|---:|---:|
| 4 | sim | sim | 6.812736e-108 | 2.292921e-107 |
| 6 | sim | sim | 2.308245e-128 | 6.061856e-124 |

### Pivôs G e K na ordem 6

| Pivô | G₆ | K₆ |
|---:|---:|---:|
| 0 | 0.023104993115419 | 3.71725992852697e-5 |
| 1 | 8.43685841013415e-8 | 1.03853067638472e-10 |
| 2 | 1.11464160449679e-13 | 8.08177596167464e-17 |
| 3 | 5.41962453838171e-20 | 2.96226172771769e-23 |
| 4 | 1.66628101178248e-26 | 8.51128327798834e-30 |
| 5 | 4.12724164403434e-33 | 1.57294796421823e-36 |

### Alturas finitas N=6

| Posição | Altura |
|---:|---:|
| 1 | 14.13472518211145 |
| 2 | 21.02729395028394 |
| 3 | 25.29061242817832 |
| 4 | 33.78043463426235 |
| 5 | 55.25743687216286 |
| 6 | 182.3360658803696 |

## Resíduos de consistência

| teste | N=4 | N=6 |
|---|---:|---:|
| whitening_maxerr | 2.755615e-103 | 1.766332e-119 |
| J_symmetry_maxerr | 7.244546e-108 | 9.896774e-126 |
| T_symmetry_maxerr | 3.488121e-105 | 4.727285e-125 |
| T2_Jinv_maxerr | 3.48254e-101 | 1.466139e-118 |
| TJT_identity_maxerr | 6.638069e-105 | 1.381329e-122 |
| canon_recurrence_maxerr | 1.890914e-124 | 3.72917e-155 |

## Resultado matemático e suas limitações

- **PASS finito:** as duas Hankels extraídas da sequência canônica foram positivas definidas para N=4 e N=6, com pivôs positivos; ambas admitem soma de quadrados finita. O transporte produz Jacobi numérica simétrica, tridiagonal até erro numérico, positiva, e o operador `T=J^-1/2` é simétrico. A segunda avaliação Cauchy confirma os momentos até precisão relativa de ~1e-95 (N4) / ~1e-109 (N6).
- **Não demonstrado:** que todos os prefixos canônicos sejam PSD/PD para N arbitrário; que exista um fator geométrico comum que não dependa de fatoração finita de Hankel; que a positividade de F=|Z|² implique automaticamente a positividade dos coeficientes de -Phi'/Phi. Nenhum desses resultados segue da mera observação finita.
- **Importante:** este script usa a característica completada como avaliador numérico dos momentos já identificados no Lean com a fonte geométrica. Não executa o pipeline físico completo de TFVD/Green, nem introduz theta, nem certifica os sinais com aritmética intervalar rigorosa.

## Arquivos-fonte efetivamente consultados

- [Momentos: código histórico da norma quadrática C2 e log moments](https://github.com/thiagomassensini/momentos/blob/main/native_carry_real_jet_selfadjoint_probe.py)
- [Momentos: auditoria de igualdade com os canônicos](https://github.com/thiagomassensini/momentos/blob/main/AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md)
- [Lean: recorrência canônica](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeRealWeylMoments.lean)
- [Lean: identificação geometricMoment = canonical](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/PrimeDepthGeometricMomentRecurrence.lean)
- [Lean: congruência de Jacobi](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/FiniteJacobiTransport.lean)
- [Lean: operador finito de alturas](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/FiniteHeightOperator.lean)

## Reproduzir

```bash
python -m pip install mpmath
python operador_finito_canonico.py --N 4 --dps 105 --nodes 224 --radius 3 --check-nodes 280
python operador_finito_canonico.py --N 6 --dps 125 --nodes 260 --radius 3 --check-nodes 320
```

A segunda execução sobrescreve `operador_finito_canonico_resultados.json`; os arquivos `operador_finito_canonico_N4.json` e `operador_finito_canonico_N6.json` acompanham este relatório.
