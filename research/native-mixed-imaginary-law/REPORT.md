# Lei imaginária do pareamento nativo par–ímpar em toda ordem

**Classificação: PARTIAL para a positividade canônica em toda ordem.**
A obrigação específica desta rodada, a lei do primeiro coeficiente
imaginário recomendada no final da PR #108, foi concluída em Lean. O escopo é o pareamento COMPLETO
da fonte original, em dois inputs independentes; não é uma nova Gram positiva.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-mixed-imaginary-law`.
Base exata: `34bae07275d4426c0ad5f20f909ed16ab372bfec`, head da PR #108,
`agent/native-even-odd-complete-pairing`, aberta e draft no reconhecimento.
A base da PR #108 é a PR #107; esta investigação permanece empilhada,
sem merge automático. `main` e as PRs anteriores ficam preservadas.

## A — O que já estava demonstrado

A PR #108 provou a reflexão conjugada da resposta original a partir do
canal nativo completado, incluindo Gamma, e transportou a média e o contraste
como VETORES antes do pairing. Reutilizamos diretamente:

- `CarryMixedParity.complete_complex_pair`: pareamento complexo completo,
  com os dois kernels ordenados; nenhuma simetria do kernel ponderado suposta.
- `mixed_pair_exact`: identidade eventual para a soma finita dos jets pares
  e ímpares originais, com suas fases e amplitudes radiais.
- `mixed_pair_real_zero`: ortogonalidade REAL eventual entre paridades.
- `mixed_pair_green_recomposition`: igualdade complexa com bulk, bordo,
  correção e os DOIS pareamentos ordenados da correção.
- `first_mixed_scaled_tendsto`: somente o caso J0,J1 do coeficiente imaginário.

Das PRs #105–#107 reutilizamos `difference_power_below`,
`difference_power_diagonal`, `difference_power_one_above`,
`static_odd_divided`, as calibrações dos perfis originais e as identidades
`response_synthesis_expansion`, `finite_source_profile`,
`finite_odd_source_profile`, `kernel_sum_inputs`, `kernel_scale_inputs`.
O resto `nativeRemainder N` já é extraído do mesmo germe analítico nativo.

Não se reabre a ortogonalização algébrica da PR #41 nem se identifica seu
residual com uma norma positiva por definição. Não se usam pivôs,
autovalores, alturas, certificados posteriores H6/K6 ou positividade theta
como entradas das provas novas.

## B — O que foi demonstrado agora

Convenções: k é o índice RADIAL, não profundidade vertical de Carry;
κ=k+1, δ=1/κ; h é a sequência canônica original já existente.
As duas variáveis de ordem r,s são independentes.

### 1. Extração espacial em qualquer ordem

`divided_one_above` prova

\[
D_{m,n,m+n+2}=(-1)^n(s_m-s_n),\qquad s_m=(m+1)(m+2)/2.
\]

Todos os termos da soma de diferenças finitas desaparecem, exceto os
endereços l=n,n+1. Reutiliza-se a lei de diferenças já provada, sem
extrapolar uma tabela finita. `mixed_static_below` cancela TODOS os graus
ímpares anteriores; `mixed_static_leading` extrai o primeiro sobrevivente
para m=2r,n=2s+1. `mixed_profile_phase` calcula as fases originais nas duas
ordens, incluindo a conjugação no primeiro argumento.

O coeficiente real, denominado `mixedOrderWeight`, satisfaz exatamente
(`mixed_slope_eq_weight`)

\[
B_{rs}=s_{2s+1}-s_{2r}=(2s-2r+1)(r+s+2).
\]

Ele é positivo quando r≤s e negativo quando s<r; nunca é zero. Esses
teoremas são exclusivamente espaciais, sem sinal de momentos como hipótese.

### 2. Expansão complexa com resto da própria fonte

`mixed_response_expansion` transporta a expansão das DUAS sínteses
ponderadas completas antes de efetuar o pareamento. Se P_rs é a soma dos
dois kernels estáticos ordenados, prova-se eventualmente perto de zero:

\[
P_{rs}(q(z))=z^{2(r+s+1)+1}
\left[(-1)^{r+s+1}h_{r+s+1}B_{rs}
+z^2P_{rs}(R_{r+s+2}(z))\right].
\]

Aqui q(z) abrevia literalmente `responseSamples z`; R abrevia
`remainderSamples`, mantendo o MESMO `nativeRemainder` em cada endereço.
Não são novas fontes. `mixed_remainder_continuous` prova a continuidade
do resto já pareado, a partir da síntese física e da analiticidade nativa.

`normalized_mixed_expansion` preserva o erro exato:

\[
\operatorname{normalizedMixedRay}_{rs}(k)
=i B_{rs}h_{r+s+1}+\delta_k^2 E_{rs}(\delta_k),
\]

\[
E_{rs}(z)=(-i)(-1)^{r+s}P_{rs}(R_{r+s+2}(z)).
\]

A normalização é somente uma observação multiplicada por potências de κ,
com igualdade provada com a fonte física; não altera fonte nem métrica.
`normalized_mixed_tendsto` conclui o limite para quaisquer r,s naturais.

### 3. Lei física com dois suportes finitos independentes

`finite_mixed_pairing` demonstra a ponte exata eventual

\[
\kappa_k\operatorname{mixedPair}(S,T,c,d,k)
=\sum_{r\in S,s\in T}c_rd_s
  \operatorname{normalizedMixedRay}_{rs}(k).
\]

S,T são quaisquer conjuntos finitos; c,d são quaisquer coeficientes REAIS.
A prova mantém os dois kernels ordenados e as fases antes de somá-los.
`finite_mixed_scaled_tendsto` prova o alvo completo da PR #108:

\[
\boxed{\quad
\kappa_k\operatorname{mixedPair}(S,T,c,d,k)
\longrightarrow i\sum_{r\in S,s\in T}c_rd_sB_{rs}h_{r+s+1}.
\quad}
\]

`finite_mixed_green_scaled_tendsto` transporta o MESMO limite à recomposição
Green original, com bulk/bordo, correção e ambos os cruzamentos conservados.
`finite_mixed_imaginary_tendsto` faz a leitura imaginária APENAS ao final.

### 4. Regressões e controles

`mixed_jet_scaled_tendsto` enuncia a lei nos jets radiais literais.
`first_mixed_from_all_order` recupera o 2ih1 já certificado para J0,J1.
`mixed_weights_low_order` certifica B00=2, B01=9, B10=−3, B11=4.
`imaginary_coefficient_two_ordered_terms` identifica o coeficiente como a
DIFERENÇA de dois pareamentos deslocados dos mesmos momentos, ponderando
respectivamente os índices ímpares e pares. Não é uma nova métrica.

`mixed_orthogonality_forces_coefficient_zero` é explicitamente condicional:
se o pareamento complexo fosse eventualmente zero, seu coeficiente teria
de ser zero. Não presume que este coeficiente seja não nulo ou positivo.

## C — O que foi refutado

`not_all_mixed_weights_nonnegative` refuta a tentativa específica de tratar
todos os coeficientes espaciais B_rs como não negativos: B10=−3.
Isso não refuta a geometria, o sinal de um pivô, a positividade de H/K ou
uma realização distinta. Refuta apenas essa candidata a lei universal de sinal.

A separação REAL entre paridades não autoriza apagar o pareamento complexo.
A lei demonstrada conserva sua primeira informação imaginária. Por outro
lado, informação imaginária e forma bilinear assinada não fornecem uma
norma positiva por si mesmas. O cálculo não prova uma isometria entre
whitening de frame Green e whitening de Hankel.

## D — O que permanece aberto

A lei agora vale em toda ordem e em quaisquer suportes finitos; não depende
dos 25 pares racionais do canário da PR #108. A regularidade radial é
necessária só eventualmente e é descarregada pelos teoremas existentes,
não recebida como sinal, inversibilidade ou positividade canônica.

Continua aberta uma lei INDEPENDENTE da fonte que determine o sinal das
formas reais canônicas completas, dentro de H e de K. O novo coeficiente
é uma diferença de pareamentos e seus pesos têm ambos os sinais.
Nem o cancelamento radial nem a norma positiva dos canais separados
eliminam essa obrigação. Tampouco foi construído um operador infinito
positivo ou identificadas alturas/zeros por este resultado.

O código novo não modifica as duas quadraturas, os endereços, fases,
amplitudes, dressing, retorno, Gamma, métricas ou pins existentes.

## E — Próximo passo mínimo

O alvo curto seguinte é estender `complete_complex_pair` aos MESMOS
estados físicos, mas com dois índices radiais independentes k,ℓ. A
identidade a testar, antes de extrair coeficientes, é

\[
G(P_k(c),P_\ell(d))
=\sqrt{\kappa_k}\sqrt{\kappa_\ell}
\left[K_{q_\ell}(c,d)+\overline{K_{q_k}(d,c)}\right].
\]

Ela é uma candidata para o carrier literal `physicalCompletedFiniteSource`,
não uma identidade nova já provada nesta rodada. O teste mínimo posterior
é o cruzamento J0(k),J1(2k+1), com ambos os pesos radiais e o resto.
A diagonal k=ℓ deve recuperar exatamente a lei desta PR.

Já há resultados para OUTROS readouts entre regularizações em
`research/completed-trace-kernel/CrossRadialGeometry.lean` e
`research/mixed-radial-jet-limit/MixedRadialLimits.lean`: preservam um fator
geométrico entre regularizações, e o jet zero no caminho duplo não coincide
com a diagonal. Reutilizá-los somente após identificar tipadamente os
carriers/readouts. Não repetir a hipótese já refutada de que todos os
cruzamentos radiais brutos sejam iguais; nem dividir o kernel por um fator
escolhido para fazê-los coincidir. Qualquer discrepância deve permanecer
como defeito de interior/retorno/bordo explícito.

Essa investigação também não é, sozinha, uma lei de sinal. Uma conclusão
de positividade exigirá uma desigualdade independente para a forma REAL
inteira. A divisão entrada a entrada por B_rs, mesmo sendo B_rs não nulo,
não constitui transporte de uma Gram positiva e não resolve essa obrigação.

### Reprodução e evidências

No ambiente original `llm`, com o cache canônico acessível:

```bash
cd research/native-mixed-imaginary-law
python3 validate.py
```

A execução normal reconstrói os 45 ancestrais intactos da base. A opção
`--reuse-upstream` exige os hashes de fontes E `.olean` registrados numa
recompilação anterior. Os quatro módulos novos e Audit são sempre
compilados explicitamente com `lean -DwarningAsError=true`. Também se
executam `lake build --wfail` raiz e dos alvos pertinentes do operador,
as auditorias Foundation/Geometry/Analysis e a preservação de fontes,
pins, main e trabalhos antigos não commitados.

**Os 15 checks locais passaram com código de saída zero.** São 28
teoremas novos, cinco definições e uma abreviação: 34 raízes públicas.
`#print axioms` e a auditoria transitiva de tipos E corpos registram:

| Grupo | Raízes | Dependências únicas | Restrição adicional |
| --- | ---: | ---: | --- |
| Espacial | 14 | 5.080 | Momentos e característica canônicos proibidos |
| Proveniência/limites | 20 | 5.740 | Consumidores posteriores de sinais finitos proibidos |

Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos na
camada analítica. A fundação mantém sua auditoria própria. Não se
reivindica footprint vazio para a análise. Nenhum `sorry`, `admit`,
`native_decide` ou axioma matemático novo foi introduzido.

`evidence/validation.json` registra comandos, durações, logs e saídas;
`evidence/lean-Audit.log` contém os certificados; `public-roots.json`
lista as raízes. `evidence/upstream.json` registra hashes das fontes e dos
45 ancestrais recompilados; `bootstrap.log` e seu registro preservam essa
execução. `source-provenance.json`, `preservation.json` e `SHA256SUMS`
registram fontes, pins, trabalhos antigos e a integridade da entrega.
Os logs brutos que exigiram retirar espaços finais foram conservados em
`.raw.log.gz`, com hashes registrados. Nenhuma afirmação sobre sucesso
do CI remoto é inferida dos testes locais.

**Publicação:** commit focado nesta branch, PR draft sobre a PR #108,
sem merge em main e sem alteração das PRs anteriores. O relatório e as
provas ficam arquivados e conferidos localmente antes de remover apenas
a worktree criada nesta rodada. O SHA do commit e a URL da PR são
registrados na entrega externa, evitando um hash autorreferente.

**Fim do relatório — PARTIAL para positividade all-order; lei imaginária
em duas ordens independentes demonstrada com a fonte e o resto completos.**
