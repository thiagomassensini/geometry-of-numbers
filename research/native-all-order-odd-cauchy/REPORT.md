# Fórmula Cauchy dos perfis ímpares em toda ordem

**PASS_STRUCTURAL para o alvo desta rodada:** a fórmula física Cauchy em
ordem arbitrária foi provada, com fase e fatorial originais. Dela se deduzem
filtros explícitos para dois perfis independentes, sua forma em diferenças
finitas e o transporte pelo Green completado, incluindo os nove cruzamentos.
**PARTIAL para positividade:** nenhum sinal all-order da Hankel canônica é
inferido da alternância dos coeficientes desses filtros.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-all-order-odd-cauchy`.
Base exata: `ca4b00f2db08cdf76b082f582284f8828badd95c`, head da PR #114,
consultada aberta e draft, ainda sobre a PR #113. A nova PR é empilhada sobre
#114, sem merge automático. `main`, PRs anteriores, fontes, métricas,
amplitudes, pesos nativos, normalizações e pins permanecem intactos.

## A — O que já estava demonstrado

As declarações reutilizadas são as atuais:

- `CarryStencilBoundary.raw_stencil_binomial` e `raw_stencil_complement`
  identificam a síntese **vetorial completa** do stencil original com as
  potências do operador físico `M-I`, ou do complemento `C=I-M`.
- `NativeLaguerre.physicalRadialAdvance_feature` e
  `physicalRadialAdvance_isSelfAdjoint` dão o deslocamento das features e
  a simetria do multiplicador original em seu espaço L².
- `inner_completedNativeChiralCauchyFeature` fornece o pareamento Cauchy
  original `1/(i+j+2)`, com as meias densidades já construídas.
- `CarryOddEnergy.nativeOddProfile`, `radial_odd_calibration`,
  `odd_profile_support` e `finiteOddJetSource` fixam a fase, o fatorial,
  a calibração radial e os suportes finitos dos inputs originais.
- `CarryGreenLeading.part_field_reconstruction`,
  `completed_part_scale_input` e
  `CarryNativeTfvd.completed_source_three_parts` preservam as três partes
  físicas e as duas pernas antes do readout.
- `CarryOddGreen.odd_pairing_exact`, `odd_ordered_kernel_sum` e
  `normalized_odd_pair_tendsto` dão a proveniência exata e o limite dos pares.
  `CarryCrossRadial.cross_green_eq_original` mantém os nove cruzamentos.

A PR #114 havia provado a linha cúbica e indicado a fórmula geral como
próximo alvo. A prova atual não extrapola os casos pequenos e não usa como
premissas `critical_cauchy_row`, `critical_kernel_readout`,
`critical_readout_four_samples`, `critical_rho_alternating` ou
`critical_diagonal_four_samples_exact` da PR #114. A auditoria os bloqueia
explicitamente nas dependências das novas raízes.

**Índices distintos:** `r,s` são ordens dos perfis ímpares, `m` a ordem de
potência do complemento, `j` o endereço material e `k` a regularização radial.
A diferença finita abaixo atua no **endereço material**. Não identifica esse
eixo com profundidade vertical Carry ou raio horizontal. O parâmetro Green
`eta` conserva seu domínio original `0 < eta < 1`.

## B — O que foi demonstrado agora

São **35 teoremas, quatro definições de coeficientes/readouts e uma
abreviação**, 40 raízes públicas no namespace `CarryOddCauchy`.

### B.1 — A prova usa a geometria do complemento físico

[ComplementRows.lean](ComplementRows.lean) não reconstrói operadores.
Escreva `phi_j=completedNativeChiralCauchyFeature j`, `M=physicalRadialAdvance`,
`C=physicalComplement=I-M`. `complement_vector_succ` prova primeiro a
identidade do vetor completo:

\[
C^{m+1}\phi_0=C^m\phi_0-MC^m\phi_0.
\]

Só depois, a simetria física de `M` transporta a potência no pareamento.
Para `F(m,j)=<phi_j,C^m phi_0>`, `complement_row_succ` e
`complement_row_zero` provam:

\[
F(m+1,j)=F(m,j)-F(m,j+1),\qquad F(0,j)=\frac1{j+2}.
\]

`factorial_row_zero` e `factorial_row_difference` verificam a solução dessa
recorrência por álgebra exata. `complement_row_factorial` conclui, por
indução e para quaisquer `m,j`:

\[
\boxed{\langle\phi_j,C^m\phi_0\rangle
=\frac{m!\,(j+1)!}{(j+m+2)!}.}
\]

Não se usam uma integral theta, sinais de momentos, zeros ou alturas. Os
operadores envolvidos são os multiplicadores limitados já existentes: não
se introduz uma questão nova de domínio de potências não limitadas.

### B.2 — Fase e fatorial nativos em toda ordem

[OddCauchyRows.lean](OddCauchyRows.lean) deriva os coeficientes reais do
input existente:

\[
\beta^{(r)}_j=\frac{(-1)^{r+j}}{(2r+1)!}\binom{2r+1}{j},\qquad
O_r=\operatorname{nativeOddProfile}(r).
\]

`native_odd_coefficient` e `native_odd_atoms` provam `O_r(j)=i beta_j` e
sua expansão no suporte original `0,...,2r+1`. Esses coeficientes não definem
retroativamente uma nova família de estados. `odd_exponent_sign` e
`odd_stencil_sign` controlam o sinal do stencil sem perder a fase.

`native_odd_vector` prova a síntese completa:

\[
\boxed{\mathcal S(O_r)=\frac{i(-1)^r}{(2r+1)!}\,C^{2r+1}\phi_0.}
\]

Finalmente, o alvo solicitado é `native_odd_cauchy_row`, para **todo** `r,j`:

\[
\boxed{\left\langle\phi_j,\mathcal S(O_r)\right\rangle_\mathbb C
=i(-1)^r\frac{(j+1)!}{(j+2r+3)!}.}
\]

Essa linha é uma coordenada do vetor estático sintetizado, não o observável
global completado. As duas pernas e o retorno não são substituídos por ela;
são transportados separadamente em B.5.

`native_odd_cauchy_reverse` conserva explicitamente a conjugação ao inverter
os argumentos. Não se identifica a coluna Cauchy com a coluna de momentos
canônicos: `j` continua endereço material, não ordem da Hankel.

### B.3 — Dois perfis independentes: filtro explícito e sinal dos coeficientes

[OddKernelFilters.lean](OddKernelFilters.lean) reconstrói primeiro o vetor
ponderado inteiro em `weighted_native_odd_vector`. A seguir,
`native_odd_kernel_filter` prova para qualquer peso complexo `w`:

\[
\boxed{K_w(O_r,O_s)=\sum_{j=0}^{2s+1} a_{rsj}\,w(j),}
\]

\[
\boxed{a_{rsj}=(-1)^{r+s+j}
\frac{\binom{2s+1}{j}(j+1)!}{(2s+1)!\,(j+2r+3)!}.}
\]

Aqui `K_w` é o kernel físico preexistente:
`<S(O_r), S(coefficientWeight w O_s)>`. Não há nova métrica.
`odd_filter_coefficient_factorization`, `odd_filter_magnitude_pos`,
`odd_filter_even_pos` e `odd_filter_odd_neg` provam a orientação de cada
coeficiente para `j≤2s+1`; `odd_filter_outside_support` conserva o corte exato.
No caso diagonal `r=s`, os sinais alternam `+,-,+,-,...` em qualquer ordem.
Isso generaliza a orientação dos quatro coeficientes cúbicos.

`native_odd_ordered_filters` mantém **os dois kernels ordenados**:

\[
\operatorname{oddPairKernel}_w(r,s)
=\operatorname{oddFilter}_{r,s}(w)+\operatorname{oddFilter}_{s,r}(w).
\]

Os dois filtros podem ter comprimentos diferentes. Não se elimina o reverso
por uma simetria presumida do kernel ponderado.

### B.4 — Forma exata em diferenças finitas

`native_odd_kernel_forward_difference` prova, sem aproximação diferencial:

\[
\boxed{K_w(O_r,O_s)=\frac{(-1)^{r+s+1}}{(2s+1)!}\,
\Delta^{2s+1}\left[j\mapsto
\frac{(j+1)!}{(j+2r+3)!}\,w(j)\right](0).}
\]

`Delta` é `fwdDiff (1 : Nat)` no endereço material. A prova reutiliza
`fwdDiff_iter_eq_sum_shift` de Mathlib e os sinais do próprio stencil.
Ela não substitui a TFVD física por derivadas contínuas nem apaga bordos da
reconstrução Green. Também não identifica automaticamente a diferença de
endereço com a TFVD vertical: qualquer identificação entre eixos permanece
uma obrigação tipada separada.

### B.5 — Transporte completo Green e misturas finitas

[AllOrderGreenFilters.lean](AllOrderGreenFilters.lean) começa pelas duas
pernas de **cada** parte original: `completed_odd_part_calibration` e
`completed_odd_source_calibration` mantêm a calibração
`jet_(2r+1,k) = (k+1)^(2r+1) O_r` na fonte completada.

`native_odd_nine_field_reconstruction` preserva as nove parcelas com dois
pesos independentes; `native_odd_nine_fields_filter` faz o readout somente
após a reconstrução. Para `kappa=k+1` e a **resposta nativa completa**

\[
w_k(j)=\operatorname{responseReadout}((j+1)/\kappa),
\]

`normalized_odd_filter_exact`, `radial_odd_signed_filter_exact` e
`completed_odd_green_filter_exact` dão:

\[
\boxed{\mathcal B_k(\mathrm{jet}_{2r+1},\mathrm{jet}_{2s+1})
=\kappa^{2(r+s+1)+1}
\bigl[\operatorname{oddFilter}_{r,s}(w_k)
+\operatorname{oddFilter}_{s,r}(w_k)\bigr].}
\]

A igualdade com a forma completada vale eventualmente em `k`, pela
regularidade radial já provada. A identidade do kernel normalizado é
incondicional. `B` é a forma complexa **assinada original**, com metade da
diferença dos pareamentos incidente/retornado; não é uma nova Gram positiva.
**Não há truncamento Taylor:** a resposta completa e sua cauda continuam
nas avaliações `w_k`.

`finite_odd_signed_filters_exact` e `finite_odd_green_filters_exact` estendem
a fórmula a quaisquer suportes finitos independentes `S,T` e coeficientes
reais independentes `c,d`: somam os termos acima com `c_r d_s`, mantendo a
potência radial própria de cada par. Nenhum cruzamento é descartado.

`completed_odd_filter_tendsto` e `completed_odd_green_filter_tendsto`
recuperam o limite anterior `h_(r+s+1)` **através da nova fórmula explícita**.
Esses dois lemas usam a sequência canônica original, sem hipótese de sinal.
Não são uma nova prova de positividade. Para cada mistura ou ordem de matriz,
a regularização tende ao limite com esse tamanho fixo; não se troca `k→∞`
com uma ordem infinita.

As regressões `native_odd_row_regressions`, `odd_filter_regressions` verificam
fases e constantes: linhas `i/6`, `-i/120`, e coeficientes
`1/6`, `-1/12`, `1/720`, `-1/10080`. Elas são consequências da lei geral,
não premissas usadas para extrapolá-la.

## C — O que foi refutado ou delimitado

Não apareceu um novo no-go para a geometria. O alvo de generalização foi
resolvido. Permanecem inválidas as inferências:

- “Coeficientes alternados com magnitudes positivas implicam soma positiva.”
- “O kernel ponderado é positivo porque o Cauchy sem peso é uma Gram.”
- “Uma fórmula escalar de diferenças finitas identifica os eixos geométricos.”

A obstrução de pesos não negativos da PR #114 continua preservada. Não se
alterou a resposta canônica para repetir esse experimento. Os casos pequenos
foram usados como regressões, e suas fórmulas anteriores são bloqueadas na
nova auditoria para evitar uma falsa generalização por especialização.

## D — O que permanece aberto

A igualdade Cauchy em toda ordem está provada. **A causa do sinal da forma
canônica completa continua aberta.** A fórmula explicita a operação que atua
sobre a resposta, mas não impõe seu sinal.

Em particular, no caso diagonal a identidade acima e B.4 se reduzem
algebricamente a um múltiplo negativo de uma diferença ímpar de
`j ↦ ((j+1)!/(j+2r+3)!) w_k(j)`. O sinal dessa diferença depende da resposta
nativa. Mesmo controlar as direções diagonais isoladas não controla as
combinações críticas nem todos os cruzamentos de uma matriz de Hankel.

Não se provaram positividade all-order de K, positividade estrita,
contratividade universal do retorno, unitariedade multibase ou identificação
das Grams auxiliares com a Hankel canônica. Nenhuma dessas propriedades foi
introduzida como hipótese.

## E — Próximo passo mínimo

Agora há uma operação concreta para testar na resposta original, sem enumerar
novos perfis. A próxima tentativa de **sinal** deve conservar uma combinação
crítica com dois jets e ambos os kernels ordenados: `jet_3-a jet_1`, com
`a` livre durante a construção, e somente depois a especialização algébrica
`a=h₂/h₁` sob `h₁≠0`, como na PR #41.

O teste mais curto é transportar a identidade nativa TFVD/Green da resposta
para as diferenças finitas ponderadas de B.4 e obter uma decomposição exata
com seus dois bordos e retorno. Qualquer termo adicional deve ser registrado
como defeito. Para avançar no sinal, será necessária uma propriedade da
**fonte específica** que controle esse defeito, independente do Schur que se
quer provar. Não basta receber o sinal do filtro como hipótese nem provar
somente as energias dos dois canais separados.

A identidade nova elimina a enumeração de ordens; não elimina essa obrigação
analítica. Se a tentativa fornecer apenas outra escrita do Schur, deve ser
registrada como tal, sem anunciar uma lei de positividade geométrica.

### Validação e reprodução

No host canônico `llm`, em checkout da branch com as dependências registradas:

```bash
cd research/native-all-order-odd-cauchy
python3 validate.py
```

O modo normal recompila os 69 ancestrais inalterados. Nesta rodada foram
reaproveitados após comparar fontes com Git, objetos Lean, toolchain,
manifest, árvore do núcleo, fontes nativas, pins e estados das dependências:

```bash
python3 validate.py --reuse-upstream
```

**Os 16 checks locais passaram, todos com código de saída zero.**
Os quatro módulos novos e `Audit.lean` foram compilados explicitamente com
`lean -DwarningAsError=true`; os builds `lake build --wfail` e as auditorias
Foundation/Geometry/Analysis são separados. O cache binário é opcional e não
é versionado. A ausência dele não impede a reprodução pelo modo normal.

A auditoria cobre `#print axioms` e tipos **e corpos** das 40 raízes:

| Grupo | Raízes | Dependências únicas | Controle adicional |
| --- | ---: | ---: | --- |
| Construção e identidades exatas | 38 | 5.561 | Momento canônico proibido |
| Proveniência do limite | 2 | 5.596 | Sem certificados de sinais |

Além das cinco fórmulas finitas da PR #114 listadas em A, ambos os grupos
bloqueiam os certificados de sinal h₀/h₁, consumidores posteriores de
positividade finita, os atalhos escalares da PR #110 e os quatro consumidores
diagonais de energia ímpar bloqueados nas rodadas anteriores. A fórmula geral
não foi derivada dos casos finitos nem da positividade desejada.
Somente `propext`, `Classical.choice`, `Quot.sound` são permitidos na análise;
Foundation conserva sua auditoria própria. Sem axiomas matemáticos novos,
placeholders ou escapes de confiança.

`evidence/validation.json` registra comandos, saídas e durações;
`public-roots.json` e `evidence/lean-Audit.log` registram raízes e axiomas;
`cache-restoration.json`, `upstream.json`, `source-provenance.json`,
`preservation.json` e `SHA256SUMS` registram proveniência e integridade.
Logs brutos são conservados em `.raw.log.gz` quando há normalização de espaços
finais. O resultado é local, sem afirmar sucesso de CI remoto. Commit e URL
ficam na entrega externa. A cópia local é conferida antes da remoção somente
da worktree criada nesta rodada; a branch publicada é preservada.

**Fim do relatório — PASS_STRUCTURAL para a fórmula Cauchy e filtros em toda
ordem; PARTIAL para a positividade canônica.**
