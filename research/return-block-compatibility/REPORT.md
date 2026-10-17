# Retorno Carry: inclusões, transições coerentes e oitava fonte

Base: `geometry-of-numbers` em `329d832fc2a6a869ae281eecb584e9299ed3d49b`
(PR #25). Operador consultado em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`,
sem modificar seu checkout ou os módulos C2 não rastreados preexistentes.

**Resultado:** o controle incondicional do retorno foi estendido de sete a
oito fontes, a partir da mesma fonte theta infinita. As transições entre as
imagens físicas das portas foram construídas para tamanhos arbitrários, com
composição e preservação de todos os cruzamentos. Uma torre coerente dos
espaços-limite também foi construída, condicional ao controle do retorno em
cada ordem. A estimativa incondicional para TODAS as ordens continua aberta.

**Validação completa concluída:** oito módulos compilados com avisos como
erros, build raiz `--wfail` (8841 jobs), regressões e auditorias das três
zonas. As 66 declarações públicas passaram pelo guard transitivo de axiomas.

## 1. Fonte anterior às comparações de energia

Reutilizamos integralmente:

- `radialIncidentSynthesis`, soma das funções físicas de Cauchy;
- `radialReturnedSynthesis`, com a mesma fonte e seu quociente chiral;
- `radialReturnTransfer`, o operador determinado pela ação nessa fonte;
- `radialReturnEnergyDefect = I − T* T`;
- `radialReturnEnergyPort` e `radialReturnEnergyJet`, na métrica original;
- `residualEnergyJet`, extração central da resposta material do PR #25.

O padding de coeficientes que preserva fonte, retorno e storage já existia em
`CompletedNativeChiralReturnArbitraryOrder`. Não foi reimplementado. A nova
rodada o usa para construir inclusões tipadas de espaços e de portas.

O parâmetro k é a regularização radial. N é o número de fontes incidentes.
A ordem do jet é outro índice. As convenções dos fatores `1/sqrt(2)`, dressing,
quocientes e duas quadraturas foram preservadas.

## 2. Compatibilidade do operador e do defeito

Os espaços incidentes físicos satisfazem `V_(k,N) ⊆ V_(k,M)` para `N ≤ M`.
`incidentInclusion` é a inclusão literal com a norma original. O novo teorema
`return_restriction` prova a igualdade de OPERADORES sobre todos os vetores:

    T_(k,M) J_(N,M) x = T_(k,N) x.

A seguir, `defect_compression_pairing` prova, para x,y independentes:

    <J x, (I − T_M* T_M) J y> = <x, (I − T_N* T_N) y>.

Nenhum sinal é necessário para essas identidades. Todos os cruzamentos são
mantidos. O adjunto do bloco maior não é declarado igual ao do menor.

`jordanPorts_prefix_pairing` transporta também a diferença entre os produtos
das portas Jordan positiva e negativa em QUALQUER tamanho, sem hipótese de
sinal. Ambas continuam explícitas antes de se usar uma estimativa de retorno.

`return_opNorm_mono` prova também

    ||T_N|| ≤ ||T_M||.

Essa direção propaga limites superiores do bloco MAIOR para os prefixos.
Um limite no bloco pequeno não certifica a próxima fonte nem uma estimativa
uniforme em N.

## 3. Por que as raízes positivas precisam de uma transição

A compressão do defeito não autoriza concluir que a raiz positiva comuta
com a inclusão. Por isso não afirmamos `P_M J x = P_N x` no L² ambiente.

Quando o retorno maior é contrativo, os dois Grams sobre a mesma fonte são
iguais:

    <P_M J x, P_M J y> = <P_N x, P_N y>.

Esse resultado é `energyPort_prefix_pairing`. Ele vem da restrição exata do
retorno, não de um Gram canônico escolhido como premissa.

Construímos então o mapa natural sobre as imagens físicas:

    U_(N,M)(P_N x) = P_M J x.

A igualdade derivada das normas garante que fontes com a mesma imagem em
`P_N` tenham a mesma imagem no destino. `rangeTransportLinear` usa o quociente
algébrico pelo núcleo apenas para tornar essa aplicação bem definida. Os
espaços finais são subespaços do L² original com sua norma herdada; não se
introduz uma métrica sobre uma Hankel ou um quociente de Gram-alvo.

`energyTransition` é linear e isométrico. Foram provados:

    U_(N,N) = I,
    U_(M,L) U_(N,M) = U_(N,L).

A composição vale para quaisquer tamanhos, sob a estimativa do retorno do
maior bloco. Se houver direções de energia nula, elas são tratadas pelos
núcleos reais das portas, sem assumir injetividade física inexistente.

## 4. Os jets residuais atravessam as mesmas transições

`differenceInput_inclusion` prova que as combinações de diferenças finitas
antigas sintetizam o mesmo vetor incidente quando aumentamos N. Nenhum novo
coeficiente é ajustado. `residualJetSource_inclusion` mantém também a extração
central, cujos pesos vêm da resposta material sintetizada.

O teorema `residualJetImage_transition` demonstra:

    U_(N+1,M+1) ResidualJet_(k,N,a) = ResidualJet_(k,M,a).

Aqui a igualdade ocorre nas imagens físicas transportadas. É uma identidade
vetorial com domínio e codomínio construídos, não somente uma igualdade de
normas. `residualJets_prefix_pairing` preserva dois índices independentes e
todos os cruzamentos ordenados.

Os retornos e complementos do Green não foram omitidos. A porta residual
continua sendo a do PR #25, cujo pareamento limite foi identificado com a
leitura confluente da diferença Green física MENOS o Green do complemento.

## 5. Novo controle incondicional para oito fontes

O operador tinha isolado o próximo escalar em
`CompletedNativeChiralReturnEightBoundaryFace`, sem demonstrar seu sinal.
Escrevendo b_j para os coeficientes originais de bordo, o alvo é

    Delta_8 = delta_6 b_7 + b_4 C_0 − b_5 C_1 + b_6 C_2,

com delta_6 e os três C_i definidos pelos acoplamentos antigos no próprio
módulo. Nenhuma parcela foi descartada; o sinal não foi atribuído aos b_j.

`EighthReturnCheck.lean` propaga os intervalos da fonte theta infinita,
certificados no PR #23, até essa expressão LITERAL. O caminho é:

    integrais theta completas
    → coeficientes da característica
    → recorrência logarítmica original
    → coeficientes de bordo
    → acoplamentos e Delta_8.

Os intervalos incorporam caudas dos modos retidos e os infinitos modos
omitidos, pela prova anterior `material_theta_integral_input`. Não usamos
apenas os modos truncados como substituto da fonte.

O teste fechado `eighthDiscriminant_rectangle_check` é reduzido pelo kernel
Lean (`decide +kernel`). `mem_eightDiscriminantBox` liga essa conta à fonte.
Isso dá o novo resultado incondicional:

    0 < nativeSourceEightOddDiscriminant.

Reutilizando a identidade de costura anterior e sua estimativa de resto,
`eighthReturn_eventually_contractive` prova:

    eventualmente em k, ||T_(k,8)|| ≤ 1.

A prova fornece existência de um cutoff em k; não calcula um cutoff explícito.
Também não afirma uma margem uniforme em N.

## 6. Oito jets físicos e todos os seus prefixos

`correctedGreen_eight_physical_realization` aplica a compacidade física do
PR #25 à nova estimativa. Existem oito vetores no mesmo L² original tais que

    <v_p,v_q> = carryValveConfluentJet eta p q,  0 ≤ p,q ≤ 7.

A condição `eta ≠ 0` é a da leitura de válvula existente. A recomposição do
canal central fornece o bloco canônico completo 0..7, em
`canonical_eight_physical_realization`.

Escolhendo essa família uma só vez, seus prefixos já são compatíveis por
restrição. `correctedGreen_eight_nested_realization` prova isso sem refazer
sete escolhas de compacidade. Os prefixos aqui permanecem no espaço físico
de oito fontes; não se afirma que cada um pertença ao espaço mínimo anterior.

A regressão `eighth_block_calibration` verifica o momento central, primeiro
jet, nova diagonal de ordem 7 e cruzamento ordenado 5–7. A regressão
`seven_to_eight_residual_crossings` compara todos os cruzamentos antigos em
regularização finita antes do limite.

## 7. Torre-limite coerente para ordem arbitrária: resultado condicional

`AllFiniteReturnBounds` registra exatamente

    para todo N, eventualmente em k, ||T_(k,N+1)|| ≤ 1.

Não troca esses quantificadores por um único k que sirva para todos os N.

`allFiniteReturnBounds_diagonal_schedule` constrói, sob a mesma hipótese,
uma sequência estritamente crescente de regularizações. Na etapa n, todos
os prefixos até n já obedecem à estimativa. Isso fornece uma exaustão de
diagramas finitos compatíveis, sem presumir um cutoff uniforme infinito.

Sob essa hipótese, cada bloco é obtido dos limites das portas físicas pelo
teorema de compacidade já provado. `limitBlock` escolhe esses representantes
físicos finitos. Não supõe que escolhas independentes coincidam no L² ambiente.

`limitTransition` identifica suas IMAGENS de síntese pela mesma família de
coeficientes da fonte. Os pareamentos são iguais por suas identidades de
limite já provadas; essa conservação é demonstrada antes de definir o mapa.
Os mapas são isometrias com as normas físicas herdadas e satisfazem identidade,
composição e transporte de cada coluna. Isso resolve a compatibilidade como
torre de espaços físicos e mapas, condicional ao controle do retorno.

Não foi construída nesta rodada uma única sequência infinita de vetores no
L² ambiente, nem o Hilbert completado de um limite direto. A torre fornece
os dados coerentes para esse passo posterior, sem os confundir com uma
igualdade literal entre todas as escolhas de representantes.

## 8. Primeira obrigação ainda aberta

A compatibilidade não produz o sinal dos novos canais. A estimativa geral
continua exigindo controle da fonte em cada extensão. A rota fonte/Schur
upstream fornece o alvo suficiente preciso:

    para todo n,
    nativeSourceSchurRemainder 0 n > 0 e
    nativeSourceSchurRemainder 1 n > 0.

`allFiniteReturnBounds_of_source_remainders` conecta essa obrigação à nova
torre, mas não afirma que os sinais foram demonstrados. A equivalência
upstream com positividade estrita da fronteira mostra que não é uma
consequência formal da matriz de Cholesky ou da compatibilidade de blocos.

| Status | Resultado |
|---|---|
| PROVADO | Restrição exata do retorno e compressão polarizada do defeito em qualquer tamanho |
| PROVADO | Monotonia da norma do retorno por inclusão de fontes |
| PROVADO, sob retorno maior contrativo | Transições físicas isométricas, composição e transporte dos jets |
| PROVADO INCONDICIONAL | Sinal do oitavo discriminante a partir das integrais theta completas |
| PROVADO INCONDICIONAL | Controle eventual do retorno até oito fontes |
| PROVADO INCONDICIONAL | Realização física do bloco 0..7 e prefixos compatíveis |
| CONDICIONAL | Torre-limite física coerente em toda ordem, sob as estimativas efetivas de retorno |
| ABERTO | Controle incondicional em todas as ordens e uma família infinita ambiente |

## 9. Validação e proveniência

Novos módulos em `research/return-block-compatibility/`, namespace
`CarryReturnCompatibility`. Os demais repositórios são somente fontes de
consulta. Pins, fontes, métricas, pesos e normalizações não foram alterados.
As worktrees e os módulos C2 preexistentes foram preservados.

Comando de reprodução no servidor llm:

    bash research/return-block-compatibility/audit-return-block-compatibility.sh

O script compila oito módulos com avisos como erros, roda `lake build --wfail`,
as auditorias Foundation/Geometry/Analysis, regressões e inventário das 66
declarações públicas novas. O guard de axiomas visita tipos e corpos; somente
`propext`, `Classical.choice`, `Quot.sound` são admitidos pela política Analysis.

Dependências inalteradas dos PRs #23–25 e `CanonicalComparison.olean` são
reutilizadas dos caches previamente compilados. Os novos módulos, inclusive o
teste inteiro fechado do discriminante, são recompilados nesta rodada.
Logs, hashes e commits de proveniência estão em `evidence/`.
