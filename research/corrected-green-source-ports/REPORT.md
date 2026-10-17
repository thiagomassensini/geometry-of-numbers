# Green corrigido: portas físicas e realização positiva finita

Base: `geometry-of-numbers` em `f8c90fcdf564a0497a8ee682f436301aa10c91b1`
(PR #24). Consulta somente de `carry-self-adjoint-operator` em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

**Resultado:** foi construída uma realização positiva exata do bloco de jets
do residual Green corrigido de ordens 0 a 6, no `L²[0,1]` físico já existente.
Recompondo o canal central da mesma fonte, obtém-se também o bloco canônico
completo dessas sete ordens. A construção usa limites de portas do retorno
original; não fatora uma Hankel para definir seus vetores.

**Validação completa concluída:** sete módulos compilados com avisos como
erros, build raiz com `--wfail` (8841 jobs), regressões e auditorias das três
zonas. Os 50 nomes públicos novos passaram pelo guard transitivo de axiomas.

## 1. Qual problema foi resolvido

O PR #24 reconstruiu o relógio material inteiro, incluindo retorno global,
cauda e cruzamentos. A candidata que usava a norma de seu complemento central
continuava separada do primeiro momento canônico por mais de `1/1024`.

Esta rodada reutiliza outra construção existente: a porta de energia do
retorno chiral canônico. Ela é definida pelo defeito do retorno sobre o espaço
incidente original de Cauchy. Não é a norma do relógio central anterior, nem
uma reescala dele. A separação anterior permanece verdadeira.

O alvo aqui é o residual já identificado pela diferença Green COMPLETA
menos o Green do complemento invisível ao readout. Os dois termos continuam
presentes na proveniência. Não se afirma que o Green do complemento seja zero.

## 2. Fonte, transformação e normalização

Seja `r` a resposta `carryMaterialNormalizedResponse`, construída pelo
companheiro vestido e pelo valor da fonte material sintetizada. Sua escala
`a0 = carryMaterialResponseScale` já foi identificada com o momento nativo
central positivo.

Usamos os coeficientes escalares da própria fonte:

    w_p = carryMaterialTaylorShift (p+1) 0 / a0.

`sourceCenterWeight_eq_coefficient` demonstra sua identificação com os
coeficientes canônicos já existentes. `w_0=1`, `w_1=0`, e os pesos são reais.
Não se introduz diferenciabilidade de ordens superiores do estado global.

A porta original é `radialReturnEnergyPort`, construída a partir de

    I − T* T,

onde `T = radialReturnTransfer k N` é o retorno efetivo no seu espaço
incidente. Seu vetor de jet `radialReturnEnergyJet` contém o fator original
`1/sqrt(2)` da forma chiral. Nenhum fator é ajustado nesta rodada.

O novo vetor residual é somente a extração central forçada:

    P_(k,N,p) = EnergyJet_(k,N,p) − w_p EnergyJet_(k,N,0).

Trabalhamos com `N+1` fontes no código, para manter o índice zero disponível.
O parâmetro `k` regulariza a grade radial; `p` é a ordem do jet. Nenhum deles
é confundido com profundidade vertical ou endereço de câmera.

## 3. O balanço assinado em qualquer ordem

Antes de usar uma desigualdade de retorno, a construção Jordan existente
fornece portas positiva e negativa da MESMA fonte. Centramos ambas com os
mesmos pesos `w_p`. O novo teorema `residualJordan_pairing_tendsto` prova,
para quaisquer ordens finitas independentes:

    <J+_(k,p), J+_(k,q)> − <J−_(k,p), J−_(k,q)>
      → Jet_(p,q)(carryMaterialRealResidual).

Os quatro cruzamentos da extração central estão explícitos. Nenhuma porta
negativa é apagada para obter esse limite.

`correctedGreenJordan_pairing_tendsto` transporta o mesmo limite para
`carryValveConfluentJet eta p q`, com `eta ≠ 0`. Essa leitura vem da diferença
Green física com o complemento, pela relação de germes de linhas já provada.
Não se usa o representante dividido nos pontos onde o fator se anula como
se fosse uma extensão regular de um kernel em duas variáveis.

## 4. Onde entra a positividade demonstrada

A desigualdade de retorno para SETE fontes já existia:

    eventualmente em k, ||radialReturnTransfer k 7|| ≤ 1.

Ela é um resultado sobre a fonte, independente da identificação de Gram
que buscamos. Reutilizá-la permite trocar o balanço assinado pela porta
positiva original, preservando o produto polarizado completo.

O novo teorema `correctedGreen_seven_positive_pairing_tendsto` prova:

    <P_(k,7,p), P_(k,7,q)> → carryValveConfluentJet eta p q,
    para p,q em {0,...,6}.

`correctedGreen_seven_synthesis_pairing_tendsto` faz o mesmo para duas
combinações complexas arbitrárias e independentes dos sete vetores. A síntese
vetorial precede a energia; todos os cruzamentos ordenados são conservados.

Até aqui há convergência de Grams, que sozinha não garantiria limites
vetoriais. O passo seguinte resolve essa questão neste bloco finito.

## 5. Limites físicos e produto interno exato

A família incidente original consiste nas funções

    sqrt(k+1) * sqrt(s) * s^i,   0 ≤ s ≤ 1,  0 ≤ i < N.

Só o escalar comum depende de `k`. `incident_mem_fixedSpan` e
`residualEnergyJet_mem_fixedSpan` demonstram que as portas residuais, para
todo `k`, pertencem ao mesmo subespaço físico finito `RadialIncidentSpan 0 N`.
O cálculo funcional que define a porta também permanece nesse subespaço.

Os limites dos Grams controlam as normas. A compacidade em dimensão finita
então fornece uma ÚNICA subsequência comum às sete colunas, com convergência
forte no `L²[0,1]` original. Isso conserva todos os produtos cruzados.

`correctedGreen_seven_physical_realization` demonstra incondicionalmente:

    existem v_0,...,v_6 em RadialIncidentSpan 0 7 tais que
    <v_p,v_q> = carryValveConfluentJet eta p q.

Os vetores são obtidos como limites subsequenciais das portas físicas.
A prova é de existência por compacidade; não fornece fórmula fechada ou
algoritmo para selecionar uma família única. Não define produto interno novo.

`physical_residual_first_calibration` verifica na MESMA família:

    v_0 = 0,
    <v_1,v_1> = h_1,
    <v_1,v_2> = 0,
    <v_2,v_4> = h_3 − h_1 h_2/h_0.

O residual tem centro nulo por construção. Isso não afirma que o momento
central do kernel completo seja zero.

## 6. Canal central, jets canônicos e quadraturas reais

A feature central já extraída da fonte possui coeficiente

    c_p = sqrt(a0) w_p.

O teorema `sourceCentralFeature_add_residual` recompõe a identidade de
coeficientes antes de qualquer escolha de vetores positivos. Com o produto
Hilbertiano direto original, definimos

    Phi_p = (c_p, v_p).

`canonical_seven_source_realization` prova que

    <Phi_p,Phi_q> = polarizedGreenMomentCoefficient h p q,
    para p,q em {0,...,6}.

Assim, a reintrodução do canal central recupera o bloco canônico completo.
Os coeficientes de fonte vêm antes dessa igualdade; uma fatoração da matriz
do lado direito não foi usada para definir `Phi`.

`correctedGreen_seven_real_quadrature_realization` conserva a estrutura real
herdada: a métrica é a parte real do produto complexo original e
`J v = i v`. Sua forma complementar é calculada após a polarização completa.
No limite canônico as entradas são reais e `<v_p,J v_q>_R=0`; não se apagam
essas quadraturas nos vetores regularizados.

## 7. Proveniência preservada e limite do transporte

Fonte material completa → par companheiro/valor com dressing derivativo
→ Green completo e complemento → leitura confluente do residual
→ portas incidentes/retorno da mesma característica canônica
→ subespaço físico de Cauchy → limites vetoriais → pareamento positivo finito.

O primeiro trecho usa o PR #24 e as identidades escalares canônicas já
conferidas em `CanonicalComparison`. Esta rodada não constrói uma isometria
do carrier material inteiro para o carrier de Cauchy. Ela identifica o
pareamento dos observáveis Green sintetizados. Retorno global, traços TFVD e
retorno chiral não são declarados o mesmo operador.

A característica canônica é a extensão escalar já identificada da resposta
material. O tempo real e a grade complexa radial só se conectam pelos germes
e coeficientes analíticos escalares existentes. Não se usa um jet holomorfo
do antigo estado radial não diferenciável.

## 8. O que continua aberto

1. **Todas as ordens:** provar a estimativa do retorno em qualquer número de
   fontes. `correctedGreen_realization_of_contractive` mostra precisamente
   o que essa estimativa forneceria em cada dimensão finita, mas não a prova.
2. **Uma família infinita coerente:** os subespaços e a escolha de subsequência
   dependem do bloco. Não foi construída uma única família física de vetores
   que realize simultaneamente todos os jets.
3. **Kernel em uma vizinhança:** realizar sete ordens confluentes não fornece
   igualdade entre kernels para todos os tempos independentes.
4. **Operador das alturas:** nenhum novo certificado HP ou identificação
   espectral foi construído. A positividade infinita não foi concluída.

| Status | Resultado |
|---|---|
| PROVADO, novo | Green corrigido → duas portas Jordan centradas, em qualquer ordem finita |
| PROVADO, novo | Gram positivo por aproximação para todas as combinações no bloco 0..6 |
| PROVADO, novo | Subespaço físico comum e limites vetoriais subsequenciais |
| PROVADO, novo | Realização positiva exata do residual no L² original, bloco 0..6 |
| PROVADO, novo | Recomposição positiva do bloco canônico completo e quadraturas reais |
| CONDICIONAL | Mesmo procedimento em dimensão finita arbitrária sob retorno contrativo |
| ABERTO | Estimativa geral do retorno e família física infinita coerente |

## 9. Fontes e validação

No operador, no commit citado:

- `CompletedNativeChiralReturnEnergyPort`: defeito real do retorno, raiz
  positiva, jets e estimativa independente para sete fontes.
- `CompletedNativeChiralReturnJordanEnergy`: ambas as portas e igualdade
  polarizada assinada, sem supor positividade.
- `CompletedNativeRadialChiralMultiplier`: carrier L² e funções de Cauchy.
- `CompletedNativeChiralReturnFiniteTransfer`: sínteses e espaço incidente.

Em geometry-of-numbers, na base citada:

- `research/prime-camera-schur/PrimeClockGreenTransport.lean`: Green completo
  da síntese prima com retorno e cauda.
- `research/material-central-calibration/CanonicalComparison.lean`:
  regularidade escalar, pesos centrais, jets reais e germes da válvula.

As novas declarações pertencem a `CarryCorrectedGreenPorts`, fora da
biblioteca padrão para não alterar dependências entre repositórios.

Reprodução no servidor llm:

    bash research/corrected-green-source-ports/audit-corrected-green-source-ports.sh

A validação compila os sete módulos com avisos como erros e roda build raiz
`--wfail`, regressões e auditorias Foundation/Geometry/Analysis. Há 50 nomes
públicos novos auditados transitivamente por tipos e corpos. O limite de
axiomas é o padrão de Analysis: `propext`, `Classical.choice`, `Quot.sound`.

As dependências inalteradas `CanonicalComparison.olean` e os módulos do
PR #24 são reutilizados do cache anteriormente compilado; não se anuncia
recompilação fresca dessas dependências. Pins, fontes, métricas e constantes
foram preservados. Os demais repositórios e trabalhos preexistentes não foram
modificados. Logs e hashes das fontes verificadas ficam em `evidence/`.
