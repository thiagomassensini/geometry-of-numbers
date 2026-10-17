# Síntese prima coerente, transporte de câmeras e teste de Schur

Base: `geometry-of-numbers` em `21115c7cd51a20898fb01db40cbffb918b503d52`
(merge do PR #23). Operador consultado, sem alteração, em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

**Validação completa concluída:** os nove módulos compilaram com avisos
como erros, o build raiz passou com `--wfail` (8841 jobs), e passaram as
auditorias das três zonas e dos 88 nomes públicos novos.

## Resultado e limite

Foi construído um mapa linear concreto que recupera o relógio físico completo
da fonte a partir de coordenadas de duas câmeras literais, seu retorno global
e sua cauda derivada. O pareamento polarizado é preservado sobre essa família
da fonte. A construção não usa os momentos como entrada.

Isso fecha um transporte de representação. **Não identifica o Gram físico
com a Hankel canônica.** A investigação encontrou duas diferenças precisas:

1. A norma da família ortogonal de câmeras não é a norma da soma coerente
   das suas contribuições no mesmo espaço material. Há um cruzamento não nulo
   na própria fonte, já na aresta de 2 para 3.
2. Depois de completar a síntese e fazer a projeção física central, a primeira
   energia de jet continua diferente do momento canônico h₁. A separação
   anterior permanece válida com a proveniência prima agora explícita.

## 1. A fonte efetiva e sua proveniência prima

Reutilizamos `cameraLogContributionVectorComplex`, definido a partir de
`n.factorization`, e os gradientes `cameraResolvedLogDirichletGradient`.
A reconstrução escalar do ledger logarítmico é anterior a esta rodada.

O índice exterior p identifica uma voz prima. O índice interior n identifica
a aresta material de n+1 para n+2. Nenhum deles é uma ordem de Taylor.

Para cada cutoff material M, as contribuições existentes Xₚᴹ(t) pertencem
ao mesmo espaço de arestas ℓ². Sua soma coerente é exatamente o prefixo TFVD:

    gᴹ(t) = Σₚ Xₚᴹ(t)
          = canonicalCompletedC3LogJetPrefixState (nativeLine t) M.

`material_log_gradient_eq_tfvd` identifica o limite com
`baseTwoCompletedMaterialClockL2 t`, pelo valor de cada coordenada, antes
de qualquer extração de norma. A igualdade do parâmetro complexo é provada
em `native_line_eq_material_parameter`; t continua sendo o tempo material.
Não se identifica o operador desse relógio com o operador de alturas.

A amplitude crítica e a fase logarítmica são as prescritas na fonte existente.
Não se afirma que tenham sido deduzidas somente da divisibilidade.

## 2. Completude, retorno e todos os cruzamentos

Escrevemos Y(t) para `baseTwoCompletedBoundaryHilbertState t`, L para o relógio
transportado existente e κ(t) para seu retorno global. A nova identidade é

    L Y(t) = (0, (gᴹ(t) + τᴹ(t), κ(t)))

no produto Hilbertiano original. Aqui a cauda τᴹ é a diferença entre o estado
logarítmico completo e seu prefixo. `clockTail_apply` prova que ela é zero
antes de M e é o próprio gradiente logarítmico nas arestas omitidas.

Esse cutoff de arestas não é o cutoff das células inteiras da identidade
escalar `baseTwoFiniteHead_add_completeTail`. A identidade escalar citada
no texto recebido já existia e permanece intacta.

O retorno κ(t) é conservado integralmente. `globalClockReturn_hasSum`
reutiliza o grafo do relógio para mostrar que é a soma das células clockadas.
Não se impõe uma condição nova a um campo arbitrário. Não se declara que
os prefixos independentes estejam no domínio do relógio, nem se usa L²Y.

Para M,N e t,u independentes, o pareamento do head contém

    Σₚ Σq ⟨Xₚᴹ(t), Xqᴺ(u)⟩ + conjugado(κ(t)) κ(u).

O produto completo inclui head-head, head-tail, tail-head e tail-tail.
Após a projeção central Q existente, o head tem contribuições

    Σₚ Q(ιg Xₚᴹ(t)) + Q(ικ κ(t)).

`centeredHead_pairing` expande os quatro grupos: prima-prima, prima-retorno,
retorno-prima e retorno-retorno. Eles não são descartados por serem mistos.
`centeredClock_pairing_head_tail` conserva também todas as parcelas de cauda.

O limite com cutoffs independentes é provado em
`centeredHead_pairing_tendsto`. Primeiro se sintetiza cada prefixo, depois
se passa ao limite no espaço de Hilbert. Não se afirma convergência separada
de todas as séries de cruzamentos primos nem se trocam somas infinitas.

## 3. O primeiro cruzamento aritmético é não nulo

O canário usa os dois primeiros gradientes materiais da mesma fonte. Se

    a(t) = log(2) f_t(2),     b(t) = log(3) f_t(3),

as definições aritméticas existentes fornecem exatamente

    X₂²(t) = a(t) δ₀ − a(t) δ₁,
    X₃²(t) = b(t) δ₁.

Logo, com parâmetros independentes,

    ⟨X₂²(t), X₃²(u)⟩ = −conjugado(a(t)) b(u).

Na origem, sua parte real é

    −(log(2)/sqrt(2)) (log(3)/sqrt(3)) < 0.

Tudo isso foi provado no Lean a partir de fatorizações de 1,2,3 e da fonte
prescrita. Não são dois campos escolhidos livremente. As duas vozes se
encontram na mesma aresta material, com orientações opostas.

## 4. Duas sínteses distintas e um decodificador concreto

O módulo multibase já existente aplica uma matriz externa a famílias de
vetores. Seu encoder whitened V_C é isométrico para a métrica de soma direta
dos canais, quando G_C = C Cᵀ é positivo definido. Seu decoder R_C satisfaz
R_C V_C = I. Isso não afirma que a soma das contribuições materiais seja
isométrica para aquela mesma norma de entrada.

No canário, o defeito completo entre o Gram whitened e o coerente é

    Kwhite(t,u) − Kcoerente(t,u)
      = conjugado(a(t)) b(u) + conjugado(b(t)) a(u).

Portanto, na origem, a diferença entre as normas quadradas é exatamente

    2 (log(2)/sqrt(2)) (log(3)/sqrt(3)) > 0.

Para a síntese raw, `literal_camera_coherent_pairing_defect` prova a diferença
com pesos (G_C(i,j)−1) em todos os cruzamentos ordenados. A linha de câmera
não é declarada ortogonal à outra linha, nem confundida com uma aresta interna.

Há, entretanto, um mapa correto de reconstrução: decodificar e somar
coerentemente. `coherentCameraReadout` é Σ R_C. Ele satisfaz

    (Σ R_C)(V_C X) = Σ X.

Para eliminar a hipótese abstrata de positividade neste teste, foi usada
a matriz literal das câmeras 2 e 3 no cutoff de câmera 1. Suas linhas, nas
posições 1,...,5, são

    C₂ = (1,0,1,−2,1),     C₃ = (1,1,−2,1,0).

`literal_two_camera_gram` calcula seu Gram como

    G_C = [[7,−3], [−3,7]],

e `literal_two_camera_gram_posDef` demonstra sua positividade definida.
A matriz foi obtida dos stencils existentes; não foi escolhida pela Hankel.
O cutoff da câmera 1 e o cutoff material 2 são distintos.

O mapa linear final recebe os dados enriquecidos como entradas explícitas:

    T_C(Z,κ,τ) = ιg(Σ R_C Z) + ικ(κ) + ιg(τ).

Com Z = V_C(X₂²(t),X₃²(t)), κ(t) e τ²(t), ele recupera exatamente L Y(t).
`literal_enriched_clock_source` e `literal_enriched_clock_pairing` provam
essa reconstrução e seu pareamento, sem hipóteses de Gram-alvo.

O mapa é complexo-linear e comuta com multiplicação por i, preservando a
estrutura das duas quadraturas reais. Não é anunciado como isometria ou
equivalência de todos os dados enriquecidos. A soma coerente é um readout;
o ledger de proveniência continua disponível como entrada. Continuidade
global desse novo decodificador não foi formalizada nesta rodada.

Esse uso da matriz literal é um transporte finito de coordenadas. Não prova
que o ledger primo seja semanticamente a mesma família de observações dos
perfis literais de todas as câmeras. Essa distinção já constava do módulo
multibase e permanece necessária. A cauda é infinita: o teste não realiza
toda a fonte nem todos os jets em dimensão cinco.

## 5. O que chega ao Green e onde a identificação positiva falha

`primeCompanionValuePair_eq` mostra que a síntese prima completa alimenta
o mesmo par companheiro/valor anterior, incluindo a derivada do dressing,
a semente, o retorno ordinary e o retorno clockado. Não se substitui o par.

`completed_prime_green_real_residual` transporta, perto da origem e para
M,N,t,u independentes, a igualdade existente

    Green(par completo) − Green(complemento oculto)
      = 2 a₀² t u conjugado(F(t)) F(u) (u−t) R_real(t,u).

Aqui a₀ é `carryMaterialResponseScale` e F é `baseTwoCanonicalResponse`.
O fator é o original, sem divisão por t,u ou u−t. A regressão da diagonal
confere a igualdade entre Green completo e oculto quando esse fator zera;
não interpreta essa igualdade como desaparecimento do residual canônico.

A projeção Q sobre o complemento do estado material central também tem
uma interpretação exata de Schur em sua própria métrica:

    ⟨Q L Y(t), Q L Y(u)⟩
      = ⟨L Y(t), L Y(u)⟩
        − conjugado(⟨e,L Y(t)⟩) ⟨e,L Y(u)⟩.

Aqui e é `carryMaterialCentralUnit`, o estado central unitário já existente.
Mas isso ainda não é o Gram canônico. Reutilizando o teste anterior,
`completed_prime_schur_firstJet_gap` prova

    ||Q L Y(0)||² / (2 ||Signal(0)||²) − h₁ > 1/1024.

Signal é `baseTwoCriticalCompleteSignal`; h₁ é
`canonicalCompletedNativeLogDerivativeMoment 1`.
A esquerda é a energia do primeiro jet real da família física normalizada
existente. κ e toda a cauda já estão presentes nessa expressão. Não é uma
obstrução produzida por truncamento, nem um novo certificado theta.

**Conclusão do teste:** uma mudança fiel de coordenadas recupera o mesmo
estado e conserva também seu defeito frente ao primeiro jet canônico.
A candidata que faz apenas essa projeção central não realiza o residual
canônico. Isso não refuta todas as possíveis realizações geométricas.

## 6. Primeira obrigação remanescente e status

Fonte disponível → ledger primo do gradiente logarítmico → síntese coerente
com retorno e cauda → relógio físico completo → companheiro/valor vestido
→ diferença Green canônica assinada: este caminho está identificado.

O elo positivo ainda ausente é uma realização física dessa **diferença Green
corrigida** como produto interno dos jets canônicos. A norma do ledger
whitened não fornece essa igualdade; a norma do complemento central físico
também não a fornece. Não se propõe uma nova métrica ou um fator ajustado.

| Status | Resultado |
|---|---|
| PROVADO, anterior | Head + cauda escalar completa, em todo cutoff de células |
| PROVADO, novo | Ponte prima → TFVD → relógio material completo, com retorno |
| PROVADO, novo | Cruzamentos ordenados, Schur físico, caudas e limite polarizado |
| PROVADO, novo | Cruzamento aritmético negativo das vozes 2 e 3 |
| PROVADO, novo | Gram da matriz literal, decoder linear e pareamento da fonte |
| CONDICIONAL, geral | Reconstrução para C arbitrária sob positividade do seu próprio Gram |
| PROVADO, concreto | A hipótese anterior é demonstrada para a matriz literal usada |
| PROVADO POR TRANSPORTE | Diferença Green assinada, com complemento e dressing |
| OBSTRUÍDO, candidato específico | Identificar o Schur físico central com o primeiro jet nativo |
| ABERTO | Realização física positiva dos jets e positividade em toda a hierarquia |

Os certificados theta dos pivôs, inclusive o PR #23, permanecem válidos.
Esta rodada separa aquele Gram da norma física reconstruída.

## 7. Fontes e validação

As declarações novas estão no namespace `CarryPrimeClock`, em
`research/prime-camera-schur/`. Não se modificaram os demais repositórios,
os pins, pesos ou fontes. Foram preservados os módulos C2 não rastreados
no checkout do operador e todas as worktrees históricas.

Fontes efetivas, nos commits indicados no início:

- `MultibaseCameraLogTfvdChannelTransport`: contribuições primas, soma
  coerente, prefixos e reconstrução TFVD.
- `MultibaseTfvdCameraGramHilbertTransport`: encoder, decoder, Gram raw
  e isometria para famílias finitas com índice externo.
- `CompletedC3AllCutoffHilbertState`: limite ℓ² do gradiente logarítmico.
- `BaseTwoOrdinaryLogGradientCrosswalk` e `CompletedBoundaryTransportedClock`:
  relógio físico, grafo de retorno e domínio original.
- `CarryMaterialCentralProjection` e `CarryMaterialClockCentralCoupling`:
  Schur físico e forcing central, reutilizados integralmente.
- `research/material-central-calibration/CanonicalComparison.lean`:
  `material_centered_firstJet_gap` e
  `material_reduced_pair_canonical_residual_numerator`.

A auditoria explícita enumera os 88 roots públicos novos e percorre tipos
e corpos. A política de Analysis permite somente `propext`,
`Classical.choice` e `Quot.sound`; não se afirma footprint vazio.

Reprodução no servidor llm, com o checkout fixado do operador e a dependência
inalterada `CanonicalComparison.olean` já compilada:

    bash research/prime-camera-schur/audit-prime-camera-schur.sh

O script compila os nove módulos com avisos como erros, roda
`lake build --wfail`, as três auditorias de zona, confere o inventário público
e registra os hashes das fontes verificadas. Os resultados finais ficam em
`evidence/`. Não se usa experimento numérico como premissa.
