# Decomposição física do retorno e primeiro Schur canônico

**Classificação: PARTIAL.** Foi construída e formalizada uma decomposição
exata do par incidente–retorno original. Ela extrai um canal ortogonal com
energia positiva eventual, preserva a reconstrução do estado completo e
realiza o primeiro complemento de Schur do mesmo kernel canônico no limite.

O residual continua sendo uma diferença de duas energias físicas. Nas
direções ortogonais ao primeiro momento, a parcela positiva extraída tende
a zero; o residual conserva todo o pivô. Isso foi demonstrado para o residual
EXATO de grau seis da PR #41, usando somente os pivôs do prefixo antigo.
Não foi demonstrada positividade canônica em toda ordem.

Base: PR #50, commit `a5ed1d73b643cc4b24549b3ee3cfe10a5b29a59b`.
Branch independente: `agent/native-return-boundary-deflation`.
A PR #51 não é dependência desta investigação. As PRs anteriores e seus
arquivos permanecem intactos; não houve merge automático.

## A — O que já estava demonstrado

### Objetos físicos reutilizados

No repositório `carry-self-adjoint-operator`, revisão
`bfeb10fd2425400fa38139903d12bf0599f02e53`:

- `radialIncidentSynthesis` e `radialReturnedSynthesis`, em
  `CompletedNativeChiralReturnFiniteTransfer.lean`: os dois mapas lineares
  originais, no carrier Cauchy `Lp ℂ 2` com sua métrica preexistente.
- `radialIncidentSynthesis_injective`: os coeficientes materiais finitos
  não se perdem na síntese incidente.
- `radialReturnedSynthesis_eq_incident_multiply`: o retorno é a síntese
  original multiplicada pelos quocientes completados de cada nó.
- `radialReturnTransfer_polarized_balance` e
  `storage_one_eq_finiteTransfer_energy`: o balanço original coincide com
  o pareamento Green polarizado e com o storage na diagonal.
- `polarizedSourceBalance_eq_corrected_green_ledger`, em
  `CompletedNativeChiralReturnPolarizedGreen.lean`: proveniência Green com
  bordo, off-diagonal, residual, cauda e completion preservados.
- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`, em
  `CompletedNativeChiralJetStorageTransport.lean`: os jets completos são
  exatamente o mesmo par de sínteses, com o mesmo mapa de coeficientes.
- `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto`, em
  `CompletedNativeChiralBoundaryJetTransport.lean`: limite polarizado de
  toda ordem, incluindo os dois setores, sem hipótese de positividade.
- `primeDepthGeometricMoment_eq_canonical`: identifica a sequência
  geométrica do limite com os momentos canônicos originais.

A investigação não confunde o índice radial `k`, a profundidade vertical,
o endereço material, a ordem de jet e o parâmetro espectral.

### Pontes anteriores utilizadas

- PR #41: `orthogonalPolynomial_orthogonal`,
  `orthogonalPolynomial_from_coefficients`, `nativeResidualBoundary` e
  `nativeResidualBoundary_energy`. Ortogonalidade algébrica exige pivôs
  anteriores não nulos; não exige o sinal do novo pivô.
- PR #48: `jetBudget_eq_original_pairing` e
  `jet_pairing_source_balance`, que preservam o pareamento físico completo.
- PR #50: `oneReturn`, `oneDeficit`, `one_signed_energy_tendsto` e
  `one_storage_scalar`, referentes ao nó radial zero original. O limite é
  `2*h0`. Nenhum novo coeficiente é ajustado.
- O sinal central independente
  `canonicalCompletedNativeLogDerivativeMoment_zero_pos` é usado para
  obter um déficit estritamente positivo eventual no primeiro nó.

O teste concreto `ExactSeventh.lean` reutiliza também
`CarrySixthEven.even_six_pivots_pos`, exclusivamente para os seis pivôs do
prefixo antigo. Não importa o certificado de sinal do sétimo pivô.

## B — O que foi demonstrado agora

### 1. Construção vetorial anterior à energia

Sejam `I_k(c)` e `R_k(c)` as sínteses originais de uma família finita de
coeficientes `c`. Definimos, com dados já existentes:

\[
e_k=\text{primeiro vetor Cauchy original},\qquad
r_k=\text{quociente completado no primeiro nó},\qquad
d_k=1-|r_k|^2.
\]

A norma do vetor original é provada, sem escolhê-la por um momento-alvo:

\[
\langle e_k,e_k\rangle=t_k=\frac{k+1}{2}>0.
\]

O retorno age no primeiro vetor por `r_k e_k`. Usamos a projeção ortogonal
`P_k` sobre a reta física `span(e_k)` e formamos:

\[
U_k(c)=I_k(c)-\overline{r_k}R_k(c),\qquad
V_k(c)=R_k(c)-r_kI_k(c),
\]
\[
C_k(c)=P_kU_k(c),\qquad A_k(c)=(I-P_k)U_k(c).
\]

Os nomes Lean são `nativeIn`, `nativeOut`, `boundaryChannel` e
`remainingIncident`. Esses mapas são coordenadas de uma decomposição do
MESMO estado. Não são declarados uma nova fonte, um novo retorno ou uma
nova métrica. A projeção usa a norma original, não uma Gram dos momentos.

### 2. Reconstrução sem perda

Antes de qualquer leitura energética, são provadas as duas identidades:

\[
\boxed{d_k I_k(c)=C_k(c)+A_k(c)+\overline{r_k}V_k(c),}
\]
\[
\boxed{d_k R_k(c)=V_k(c)+r_k[C_k(c)+A_k(c)].}
\]

Nomes: `native_reconstruct_incident` e `native_reconstruct_returned`.
Quando `d_k≠0`, o par original é recuperado integralmente. O teorema
`channels_separate_source` prova que os três canais conjuntamente separam
todos os coeficientes finitos originais.

`nativeIn_mem_original_span`, `nativeOut_mem_original_span`,
`boundaryChannel_mem_original_span` e
`remainingIncident_mem_original_span` mostram que a decomposição permanece
no mesmo espaço finito de síntese. Não é uma projeção ambiente arbitrária.
Isso não reivindica, sem uma inclusão adicional de domínio, uma nova
propriedade para todo operador não limitado do projeto.

### 3. Balanço polarizado e complemento explícito

Para DUAS entradas independentes, definindo

\[
\mathcal B_k(c,f)=\langle I_k(c),I_k(f)\rangle-
                  \langle R_k(c),R_k(f)\rangle,
\]

o teorema `native_balance_split` prova, em todo cutoff e dimensão finitos:

\[
\boxed{d_k\mathcal B_k(c,f)=
\langle C_k(c),C_k(f)\rangle+
\underbrace{\langle A_k(c),A_k(f)\rangle-
\langle V_k(c),V_k(f)\rangle}_{\mathcal R_k(c,f)}.}
\]

`remainingPair` é exatamente `R_k` nesta fórmula. O símbolo `R_k` de
síntese retornada e o símbolo caligráfico de residual têm funções distintas.
Nenhum cruzamento é descartado: os termos entre `P_kU` e `(I-P_k)U` são
zero por ortogonalidade demonstrada em dois argumentos.

Na diagonal, `native_energy_split` fornece:

\[
d_k\,\operatorname{Re}storage_k(c)
=\|C_k(c)\|^2+\mathcal R_k(c,c).
\]

`oneDeficit_eventually_pos` prova `d_k>0` eventualmente, usando apenas a
energia central original que converge para `2*h0>0`.
Logo `||C_k(c)||²/d_k` é uma parcela positiva eventual. Não há uma margem
uniforme: a PR #50 já demonstra `d_k→0`.

### 4. A projeção realiza exatamente o primeiro Schur

Defina o cruzamento com o primeiro estado original:

\[
b_k(c)=\langle e_k,I_k(c)\rangle-
       \overline{r_k}\langle e_k,R_k(c)\rangle.
\]

`native_boundary_formula` calcula o canal, sem fatoração ajustada:

\[
C_k(c)=t_k^{-1}b_k(c)e_k.
\]

Para `d_k≠0`, `native_schur_remainder` prova:

\[
\boxed{\frac{\mathcal R_k(c,f)}{d_k}
=\mathcal B_k(c,f)-\frac{\overline{b_k(c)}b_k(f)}{d_kt_k}.}
\]

O denominador é o balanço do primeiro estado original. A eliminação é
exata: `remainingPair_head_left`, `remainingPair_head_right` e
`remainingPair_eraseHead` provam que o residual não depende do primeiro
coeficiente, em nenhum dos argumentos. Sua informação está retida no canal
separado; não é apagada do estado completo.

### 5. Transporte à fonte de jets e ao kernel canônico

`jet_deflation_balance` aplica a decomposição ao mapa nativo de jets
completo, antes da contração. `head_jet_input`, `head_jet_incident` e
`head_jet_returned` identificam o jet zero com a amplitude ORIGINAL sobre
`e_k`; não há normalização escolhida para alcançar `h0`.

Se `B(x,y)` denota o pareamento canônico de bordos já existente, com os
dois setores e as fases originais, `jetNativeBalance_tendsto` prova
`B_k(x,y)→2 B(x,y)`.

Os teoremas `jet_remaining_schur_eventually` e
`jet_remaining_schur_tendsto` dão a identidade finita e seu limite:

\[
\boxed{\frac{\mathcal R_k(x,y)}{d_k}\longrightarrow
2\left[B(x,y)-\frac{\overline{B(e_0,x)}B(e_0,y)}{h_0}\right].}
\]

Aqui `e0` é o bordo do jet zero, não o vetor Cauchy sem amplitude. A
distinção é formalizada por `headAmplitude` e `scaled_anchor_schur`.

No setor par, o kernel restante tem coeficientes

\[
h_{i+j}-\frac{h_i h_j}{h_0}.
\]

No setor ímpar, a primeira projeção par não retira uma contribuição do
limite: o cruzamento entre setores é zero no kernel canônico. Os cruzamentos
finitos são preservados até essa passagem ao limite.

### 6. Teste da direção exata da PR #41

`pr41_even_head_cross_zero` prova, para grau positivo e pivôs anteriores
não nulos, `B(e0,p_n)=0`. `pr41_odd_head_cross_zero` prova o cancelamento
correspondente em qualquer ordem ímpar, pela separação de paridade.

Consequentemente:

\[
\frac{\langle C_k(p_n),C_k(p_n)\rangle}{d_k}\longrightarrow0,
\qquad
\frac{\mathcal R_k(p_n,p_n)}{d_k}\longrightarrow2\,\mathrm{pivot}_n.
\]

Nomes: `pr41_even_projected_tendsto_zero`,
`pr41_odd_projected_tendsto_zero`,
`pr41_even_remaining_energy_tendsto` e
`pr41_odd_remaining_energy_tendsto`.

`ExactSeventh.lean` especializa o resultado a
`nativeResidualBoundary 0 6`, com os seis pivôs antigos já certificados:

- `exact_seventh_head_cross_zero`;
- `exact_seventh_projected_tendsto_zero`;
- `exact_seventh_remaining_energy_tendsto`.

Não foi substituída a direção exata pela coluna racional próxima. Também
não foi determinado aqui o sinal do resto NÃO LINEAR da PR #49 nessa
direção exata. Essa obrigação intervalar continua separada; não se deve
anunciar que esta investigação a resolveu por outra decomposição.

## C — O que foi refutado ou delimitado

### O primeiro canal positivo não basta

O teste exato da PR #41 mostra por que a positividade dessa parcela não
seleciona o sinal dos pivôs seguintes: nas direções pertinentes, sua
contribuição normalizada tende a zero e o pivô reaparece integralmente no
residual assinado. Isso não é uma obstrução à positividade do residual;
delimita o alcance desta PRIMEIRA extração.

Essa parcela também não é o termo de Euler da PR #49. Euler usa o
coeficiente constante `x0`; esta projeção usa `B(e0,x)` e, portanto, pode
desaparecer mesmo quando `x0≠0`. Não foram identificadas indevidamente essas
duas operações, nem o residual atual com `Delta`, `N` ou a porta negativa
de Jordan das investigações anteriores.

### Um déficit central positivo não obriga todos os sinais

`Controls.lean` dá um contraexemplo exato em um espaço hilbertiano de duas
coordenadas, usado somente como controle lógico. O retorno é `1/2` na
primeira direção independente e `2` na segunda. O déficit central é
positivo, enquanto na segunda direção:

\[
\mathcal B=-3,\qquad U=0,\qquad
\langle U,U\rangle-\langle V,V\rangle=-9/4.
\]

As duas direções incidentes são independentes, formalizado em
`control_anchor_incident_independent`. Não é um contraexemplo à fonte
Carry. Ele impede uma inferência puramente algébrica de positividade do
residual a partir de `d_k>0`.

Não foi assumida uma identificação do retorno nativo com o shift TFVD
finito já excluído por `radialReturn_no_finiteTfvdShift_intertwiner`.
Também não foi utilizada a raiz positiva de um defeito presumido positivo.

## D — Validação, dependências e limites

São **81 teoremas e 31 definições/aliases/instâncias** em sete módulos:
`BoundaryFeedback`, `NativeDeflation`, `JetBridge`, `SchurLimit`,
`ResidualTest`, `ExactSeventh` e `Controls`.

As 112 raízes públicas são inventariadas em `public-roots.json`.
`Audit.lean` imprime os axiomas de cada uma e percorre transitivamente
tipos e corpos em três grupos: álgebra, dinâmica nativa e teste do prefixo.
Só são permitidos `propext`, `Classical.choice` e `Quot.sound`.

Os grupos aprovados contêm, respectivamente, 33, 76 e 3 raízes; suas
dependências transitivas contêm 3.306, 6.912 e 5.789 constantes.

Todos os grupos proíbem dependências dos certificados de sinal do sétimo
pivô, de H7, da contratividade de sete fontes e da não negatividade geral
do defeito de retorno. O grupo nativo também proíbe os certificados H6/K6
e a energia estrita de seis fontes. Só o grupo `prefix_test` usa o antigo
certificado de seis pivôs, para a ortogonalidade da direção exata.

`evidence/checks.json` registra 19 verificações reproduzíveis: build dos
consumidores físicos, oito compilações de pesquisa com warnings como erros,
build focado e `lake build --wfail`, auditorias Foundation/Geometry/Analysis,
regressão H6/K6/doze fontes, controles racionais e preservação dos arquivos.

O experimento independente não calcula zeros, alturas, zeta, theta ou novos
momentos. Há nove controles complexos racionais que verificam os dois
argumentos, as duas identidades de reconstrução, o Schur e a eliminação da
primeira coordenada. Seus quocientes sintéticos são explicitamente
controles, não dados da fonte canônica. Três testes adicionais usam somente
os decimais originais do JSON de ordem 6 como racionais: não são intervalos
certificados dos integrais nativos.

Nenhuma fonte, amplitude, fase, câmera, dressing, completion, métrica ou pin
foi alterado. Os arquivos não rastreados do operador são preservados por
hash. Os arquivos locais da PR #51, fora da ancestralidade desta branch,
também são preservados. Não foi criada ou removida nenhuma worktree.

`main` local e remoto permanecem em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`, confirmado por consulta ao remoto.

As identidades sem divisão valem em qualquer cutoff. Reconstrução por
divisão e a interpretação positiva do primeiro canal valem quando `d_k≠0`
ou `d_k>0`, respectivamente; essas condições foram obtidas EVENTUALMENTE.
Não foi demonstrado controle uniforme em dimensão, convergência de cada
canal vetorial reescalado ou uma família Gram infinita coerente.

## E — Próximo passo mínimo

Agora existe uma realização física explícita do primeiro Schur, antes da
leitura escalar, com um residual independente da primeira coordenada.
O próximo alvo é controlar a diferença

\[
\langle A_k(x),A_k(y)\rangle-\langle V_k(x),V_k(y)\rangle
\]

nas direções restantes, a partir da dinâmica completada. Receber sua
não negatividade como campo de um certificado não resolve o problema.

O teste estrutural mais curto é confrontar as duas sínteses restantes com
uma relação Green/retorno independente: ou uma nova parcela ortogonal
efetivamente determinada pela fonte, ou uma estimativa relativa do retorno
`V_k` sobre a incidência `A_k`, com o resto e a ordem explícitos. A extração
seguinte só será válida se a identidade vetorial e os cruzamentos forem
demonstrados; a fórmula de Schur, isoladamente, não fornece o sinal.

A investigação pode também retomar o controle intervalar de `N` da #49 na
direção exata, mas isso é um teste de uma decomposição diferente. Não é
necessário recalcular milhares de momentos ou ajustar o operador de alturas.

**Conclusão:** há uma nova ponte física verdadeira e sem perda de
informação até o primeiro Schur canônico. A primeira parcela positiva está
identificada. O sinal all-order permanece no residual explicitado, como
mostra o teste exato da PR #41. Resultado `PARTIAL`.

### Reprodução no host canônico

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/native-return-boundary-deflation
python3 research/native-return-boundary-deflation/validate.py
```

O script usa os consumidores e caches históricos já preparados no host
canônico. Não reivindica bootstrap de um clone sem esses módulos de
pesquisa; a reconstrução histórica segue os scripts das PRs anteriores.
Comandos, logs, hashes e dados acompanham a investigação.
