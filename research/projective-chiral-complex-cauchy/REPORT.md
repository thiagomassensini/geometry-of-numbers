# Checkpoint — Cauchy–Pick físico C2 na variável de altura complexa

Data: 2026-11-17
Repositório: geometry-of-numbers
Branch: task/gon-projective-chiral-c2-sewing-20261117
PR principal: https://github.com/thiagomassensini/geometry-of-numbers/pull/334
Dependência comparadora, SEM novo Lake import:
https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/128

## O que foi construído

### 1. Estado material com altura complexa

Arquivo: GeometryOfNumbers/Analysis/CarryMaterialComplexCauchySource.lean

- Fonte original: baseTwoComplexMaterialGradientLp em lp(1) e lp(2)
  já existente em CompletedMaterialGradientStrongClock.lean
- Definição explícita do retorno a partir do funcional bounded
  baseTwoCompletedUndressedReadout sobre o estado ℓ¹, **não** de uma
  característica alvo ou de uma leitura escalar inserida a posteriori.
- Estado MaterialCarrier = seed + interior ℓ² + retorno completo.
- carryMaterialComplexState_ofReal: identidade VETORIAL com
  baseTwoCompletedBoundaryHilbertState t no eixo real.
- Completude/local: diferenciabilidade holomorfa nos quarter-balls já
  certificados ao redor de alturas reais.
- O material do núcleo, as pernas e o peso não são substituídos
  por theta ou uma definição inicial da zeta.

### 2. Completamento e companheiro físico

Arquivo: GeometryOfNumbers/Analysis/CarryMaterialComplexCompletedPair.lean

- Dressing genuíno: canonicalArchimedeanCompletionComplex(z) /
  baseTwoCanonicalCameraFactorComplex(z).
- Físico vestido: dressing * carryMaterialComplexState(z).
- Companheiro: -deriv do VETOR físico vestido completo.
- carryMaterialComplexCompanion_ofReal: corresponde ao real
  carryMaterialDressedCompanion t, literalmente como vetor.
- carryMaterialComplexCompanionReadout_eq_neg_deriv: o readout
  bounded do companheiro coincide com -deriv do readout do vestido,
  quando existe a derivada (comprovada perto do eixo real).

### 3. Dois canais e kernel Cauchy–Pick realmente físico

Arquivo: GeometryOfNumbers/Analysis/CarryMaterialComplexCauchyPick.lean

As duas famílias P_+(z) e P_-(z) vêm do par físico anterior,
usando carryMaterialCompleteChiralPositive/Negative com a
inversão quiral no complemento original Q.

O Green assinado físico fica

 B_C2(z,w) = (i/2) ( <P_+(z),P_+(w)> - <P_-(z),P_-(w)> )

e a prova estabelece exatamente

 B_C2(z,w) = conj(F_C2(z))*Psi_C2(w)
            -conj(Psi_C2(z))*F_C2(w),

onde F_C2 e Psi_C2 são os READOUTS dos vetores que acabamos de
construir, não funções-alvo injetadas.

Para F_C2(z), F_C2(w) != 0, w != conj(z), a definição física

 K_C2(z,w) = B_C2(z,w) / [2 conj(F_C2(z))*F_C2(w)*(w-conj(z))]

satisfaz o teorema exacto:

 K_C2(z,w) = (R_C2(w)-conj(R_C2(z)))/(w-conj(z)),
 R_C2(z) = Psi_C2(z)/(2F_C2(z)).

- matriz finita complexa para TODOS os i,j, sem descartar cruzamentos;
- o numerador é uma diferença dos dois Grams físicos;
- no semiplano superior z.im>0, diagonal w=z é regular
  pois w != conj z;
- valor F_C2(0) != 0 vem da massa física C2 original e da
  câmera não nula; continuidade fornece não anulação perto de 0;
- sobre alturas reais, P_± e R_C2 recuperam literalmente os
  estados/companion/resposta da PR GoN #334.

### 4. Costura com CSA

No comparador GoN–CSA existente
research/material-central-calibration/CanonicalComparison.lean,
a base original da PR #334 já mostra:
- Green da válvula igual Wronskiano completado na altura real;
- identidade matricial de todas as alturas reais não nulas.

Nesta etapa acrescentamos provas:
- carryMaterialComplexValueReadout(t) = F_native(t);
- carryMaterialComplexCompanionReadout(t) = Psi_native(t);
- carryMaterialComplexResponse(t) = R_native(t);
- carryMaterialComplexChiralGreen(t,u) = W_native(u,t).

As identificações acima valem para **t,u reais**, apenas.
A igualdade complexa em um aberto ainda requer uma demonstração
de unicidade de continuação analítica (ou uma identificação direta
das séries C2 com Genuine/Native) com a proveniência de câmeras.

### 5. Canário numérico independente

Script: research/projective-chiral-complex-cauchy/c2_native_complex_check.py
JSON:    research/projective-chiral-complex-cauchy/numerical-c2-vs-native.json

Origem fonte: C2 seed + bracket em centros 4k+4:
    S_C2(s)=1+sum_{k>=0}[(4k+3)^(-s)-2(4k+4)^(-s)+(4k+5)^(-s)].

A forma Hurwitz analiticamente continuada da SOMA C2 (não a
definição primitiva do projeto):
    S_C2(s)=1+4^(-s)[ζ(s,3/4)-2ζ(s,1)+ζ(s,5/4)].
F_C2(z) = A(z) S_C2(s(z)) / [(1+2^-s)(1-2^(1-s))].
Referência INDEPENDENTE: F_native(z) = A(z)ζ(s(z)).

mpmath 95 dps, amostras z = 0.05i,0.10i,0.20i,0.1+0.07i:
|F_C2-F_native| ~ 5e-97 a 1e-96;
|R_C2-R_native| <4e-99;
maior defeito 3×3 Pick <6e-98;
menor autovalor Pick 3×3 +1.3556e-12.
O truncamento direto da série C2 tem cauda finita
(100 células: 2.26e-5; 1.000: 9.05e-7; 4.000: 1.30e-7).
Esses números são **experimentos, não intervalos certificados**.

### 6. Fronteira matemática, sem inferência indevida

a. Analyticidade nativa complexa: promover a identidade física
   F_C2(t)=F_native(t), já demonstrada para todos os t reais,
   para uma vizinhança complexa com unicidade analítica,
   verificando domínios e comportamento do fator câmera.

b. Positividade: mesmo a identidade complexa final do Pick
   é uma **diferença** de Grams com denominação Cauchy.
   Não produz um Gram positivo por Parseval automaticamente.
   Falta a contração do multiplicador quiral de fonte completa,
   em todas as combinações finitas, e sua compatibilidade com
   o carrier Cauchy/Laguerre existente no CSA.

c. Todos os momentos/hankels: para inferir os blocos
   par e ímpar all-order, é necessário controlar limites
   dos jets de Green e não degenerescência. Não concluídos aqui.

d. O modelo do Cauchy-Laguerre do CSA oferece um carrier
   isométrico no subespaço Cauchy gerado pelas features;
   esse subespaço não é, por si, a fonte física GoN completa.

Nenhuma declaração nova assume PSD, RH ou a igualdade
K_source=K_target como hipótese escondida em um construtor concreto.

## 7. Fatoração Hermite–Biehler da FONTE (novo teorema Lean)

Em CarryMaterialComplexCauchyPick.lean,
carryMaterialComplexPickKernel_eq_sourceHermiteBiehler
é uma identidade algébrica EXATA no verdadeiro material completado:

  a_C2(z) = (Psi_C2(z)+i F_C2(z))/(2 F_C2(z))
  q_C2(z) = (Psi_C2(z)-i F_C2(z))/(Psi_C2(z)+i F_C2(z))

  K_C2(z,w) =
      i/(w-conj z) * conj(a_C2(z))*a_C2(w)
        * (1-conj(q_C2(z))*q_C2(w)).

Exige explícitos F_C2(z),F_C2(w),Psi_C2(z)+iF_C2(z),
Psi_C2(w)+iF_C2(w) e w-conj z não nulos.

A estrutura (1-conj(qz)*q(w)) aponta o sinal a controlar.
É fonte-first: q_C2 e a_C2 usam readouts físicos C2, não os
momentos nem o quociente canônico do CSA como definição.
O teorema compilou em Lean sem sorry nem axiomas extras;
o cálculo mpmath 95 dps verificou K_C2 vs esta fatoração
até 3.5e-96 na seção radial 3x3. Esse é um canário,
não certificado intervalar.

A identidade, sozinha, NÃO prova que q_C2 atue como uma
contração no espaço de Cauchy. A separação entre as duas
obrigações é central: identificar a fonte canônica e
demonstrar a desigualdade de energia de todas as combinações.

## Validação final

- GoN build focado: lake build
  GeometryOfNumbers.Analysis.CarryMaterialComplexCauchyPick
- Lean estrito: lake env lean -DwarningAsError=true no mesmo arquivo
- GoN–CSA: research/material-central-calibration/CanonicalComparison.lean
  compilado no cache CSA com LEAN_PATH da GoN; output em
  research/projective-chiral-complex-cauchy/cross-repo-validation.log
- Auditoria Lean mostra apenas propext/Classical.choice/Quot.sound.
