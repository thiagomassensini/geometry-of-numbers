# Transporte conservativo e retorno quiral nativo

**Classificação: PARTIAL.** Identidades exatas e obstruções específicas foram demonstradas. A identificação de uma realização conservativa com o retorno completado permanece aberta; a positividade canônica em toda ordem não foi demonstrada.

Branch: `agent/native-conservative-intertwiner`.
Base: `f2987f171914c978ed6affe7500b9d534f0e18f7`, cabeça da PR #61. Esta é uma continuação empilhada: a base não é `main`, e a PR #61 e seus predecessores continuam drafts. Nenhuma PR anterior foi modificada ou mesclada.

Fonte nativa consultada e compilada: `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. O checkout e seus arquivos não rastreados foram preservados. Os pins e a métrica não foram alterados.

## A — O que já estava demonstrado

A recomendação investigada era testar um mapa conservativo herdado da geometria sobre **os dois canais da mesma fonte**, conservando seu defeito de entrelaçamento. Conservação no espaço auxiliar não identifica automaticamente esse mapa com o retorno quiral.

Foram reutilizados:

- `physicalCauchyClosure`, `physicalCauchyFeature`, `cauchyLaguerreIsometry`: fecho das colunas físicas originais e transporte isométrico para Laguerre, em `NativeCauchyLaguerreIsometry.lean`.
- `physicalCauchyShift_feature`, `physicalCauchyShift_tendsto_zero`: ação do shift nas colunas e estabilidade forte, em `NativeCauchyLaguerreShift.lean`.
- `physicalCauchy_head_tail_inner`, `physicalCauchy_head_tail_energy`: decomposição polarizada e energética exatas, em `NativeCauchyLaguerreHeadTail.lean`.
- `physicalOriginalIncident`, `physicalOriginalReturned`, `cauchyLaguerre_originalSource_legs`, `cauchyLaguerre_nine_source_crossings`, `cauchyLaguerre_source_polarized_product_sum`: incidência, retorno, completion e todos os cruzamentos na métrica original, em `NativeCauchyLaguerreSources.lean`. O termo de completion não foi identificado com um ruído ortogonal nem removido.
- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` e `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto`: igualdade vetorial da síntese finita e seu limite de energia.
- `scaled_incident_tendsto`, `scaled_returned_tendsto`, `leadingState_ne_zero`, da PR #42: depois da observação radial, o par completo tende a `(w,-w)`, com `w≠0` quando o coeficiente superior é não nulo.
- `residualPolynomial_monic_degree`, `nativeResidualBoundary`, `nativeResidualBoundary_energy`, da linha da PR #41: coordenadas mônicas, fronteira física original e identificação do balanço com o residual algébrico, antes de qualquer escolha de sinal.

Os dois módulos necessários da PR #42 são recuperados pelo commit imutável `3e267bffdc238c82b89577cb16190d2f54cefe05`, com SHA-256 em `ancestor-sources.json`, e recompilados explicitamente. Não se recompôs uma versão nova desses teoremas a partir dos relatórios.

A independência estrutural é importante: o shift atua nas colunas Cauchy com

\[
T f_j=\rho_j f_j,\qquad \rho_j=\frac{2j+1}{2j+3}.
\]

O retorno nativo usa outra função, **a já existente**:

\[
q(z_{k,j}),\quad z_{k,j}=\frac{i(j+1)}{k+1},\quad q(0)=-1.
\]

O índice radial `k`, o endereço material `j` e a ordem de jet não foram identificados entre si.

Domínios: as igualdades de somas finitas abaixo são algébricas nos objetos totais definidos em Lean. Os teoremas que decompõem as pernas em fonte, companion e completion mantêm as hipóteses originais de faixa física e de denominador Hermite–Biehler não nulo. Para cada suporte finito fixo, o limite radial é tomado no germe central já certificado; `canonicalCompletedC3RadialTiltPoint_eventually_admissible` fornece a admissibilidade eventual da característica em cada endereço. Isso não autoriza considerar todos os endereços materiais simultaneamente admissíveis para um mesmo `k` fixo.

## B — O que foi demonstrado agora

### 1. Um candidato conservativo concreto e seu defeito completo

Em `ConservativeDefect.lean`:

\[
C_R=-T^{R+1},\qquad H_R=\mathrm{head}_R\circ\mathcal I,
\]

onde `T` é o shift físico existente e `𝓘` é `cauchyLaguerreIsometry`. O sinal negativo é o teste da orientação central original `q(0)=-1`, não um ajuste de momentos. Este candidato é declarado como candidato, nunca como o retorno físico já identificado.

`conservative_pairing` e `conservative_energy` provam

\[
\langle x,y\rangle=\langle H_Rx,H_Ry\rangle+\langle C_Rx,C_Ry\rangle.
\]

Para **dois pares independentes** `(x,rx)` e `(y,ry)`, defina `ηx=rx-C_Rx`. `polarized_defect_ledger` prova

\[
\langle x,y\rangle-\langle rx,ry\rangle
=\langle H_Rx,H_Ry\rangle
-\langle C_Rx,\eta y\rangle
-\langle\eta x,C_Ry\rangle
-\langle\eta x,\eta y\rangle.
\]

Somente depois dessa identidade vetorial e polarizada, `energy_defect_ledger` extrai

\[
\|x\|^2-\|rx\|^2
=\|H_Rx\|^2-2\operatorname{Re}\langle C_Rx,\eta x\rangle-\|\eta x\|^2.
\]

Nenhum dos três termos de erro foi descartado ou declarado ortogonal.

### 2. O mesmo estado físico e os mesmos coeficientes

Em `PhysicalJets.lean`, `physicalIncident` e `physicalReturned` apenas restringem o contradomínio da síntese original ao fecho ao qual ela já pertence. `physicalIncident_coe` e `physicalReturned_coe` provam as igualdades de vetores com `nativeSourceProjectiveBoundaryJetSynthesis`, antes do readout.

`physical_source_defect_pairing` aplica o balanço polarizado com dimensões, parâmetros radiais e entradas independentes. `physical_signed_energy_tendsto` conserva o fator nativo:

\[
2(\|I_k(x)\|^2-\|R_k(x)\|^2)
\longrightarrow\operatorname{nativeSourceFiniteBoundaryEnergy}(x).
\]

Em `PhysicalCoordinates.lean`, `original_transport_defect_columns` calcula o defeito exato:

\[
\eta_{R,k}(c)=\sqrt{k+1}\sum_j
c_j\bigl(q(z_{k,j})+\rho_j^{R+1}\bigr) f_j.
\]

Os `c_j` são os coeficientes fornecidos à própria síntese. Para os jets são literalmente `nativeSourceChiralJetInput n k x`, incluindo amplitude completada, fases, fatoriais e pesos de diferenças finitas originais. Não são coeficientes escolhidos para tornar uma Gram positiva.

`material_address_from_shift` e `radial_argument_from_shift` provam ainda a relação concreta

\[
j+1=\frac{1+\rho_j}{2(1-\rho_j)},\qquad
z_{k,j}=\frac{1+\rho_j}{2(1-\rho_j)}\,\delta_k.
\]

Essa igualdade conserva o endereço aritmético; ela não autoriza apagar `k`, nem fornece por si só um cálculo funcional limitado dessa transformação de Cayley.

### 3. O defeito não desaparece no limite vetorial

Em `LeadingObstruction.lean`, para qualquer fronteira com ordem superior `m` não nula e suporte até `m`:

\[
\sigma_{k,m}\eta_{R,k}\longrightarrow T^{R+1}w-w\ne0.
\]

Os teoremas são `scaled_transport_defect_tendsto`, `leadingTransportDefect_ne` e `conservative_return_not_eventually_source`. A não anulação decorre da estabilidade forte do shift físico: um ponto fixo de `T^{R+1}` teria de ser zero (`physical_shift_fixed_eq_zero`). Não depende do sinal de momentos.

A identidade `leading_conservative_cancellation` prova o cancelamento completo:

\[
\|H_Rw\|^2-2\operatorname{Re}\langle C_Rw,T^{R+1}w-w\rangle
-\|T^{R+1}w-w\|^2=0.
\]

Portanto, o complemento positivo desse candidato não pode ser isolado como margem positiva do retorno nativo. O balanço dominante é nulo, como exige o par original `(w,-w)`; o estado e o defeito não são nulos.

### 4. A PR #41 entra em toda ordem, sem receber positividade

Em `PR41Transport.lean`, `pr41_monic_top`, `pr41Boundary_top` e `pr41Boundary_top_ne` identificam o coeficiente superior da **mesma** direção mônica em cada setor: a ordem é `m=2*n+s`, com coeficiente `(-1)^n`.

`pr41_conservative_return_fails` aplica a obstrução a **todas** essas direções, para todo `R`, nos setores par e ímpar. Não recebe `PosDef`, não degenerescência ou sinal do próximo pivô.

`pr41_conservative_ledger_tendsto` mantém o residual completo:

\[
\|H_R I_k\|^2+\operatorname{correção}_{R,k}
\longrightarrow2\,p^{\rm alg}_{s,n},
\]

com a correção exatamente igual a `-2 Re⟨C_R I_k,η_k⟩-‖η_k‖²`. Aqui `p_alg` é `carryPairingPivot`. A construção mônica é total; sua interpretação como complemento de Schur do bloco anterior usa as condições de invertibilidade já explicitadas na PR #41. Não se chama um residual num bloco singular de Schur invertível.

### 5. Regressões exatas das primeiras duas direções

Em `LowOrder.lean`, as fronteiras `![1,0]` e `![0,1]` são identificadas com `nativeResidualBoundary 0 0` e `nativeResidualBoundary 1 0`.

A amplitude do centro é herdada da fonte: `central_amp_norm` prova `‖amp 0‖²=1/2`; não foi ajustada. Os limites são

\[
w_{\rm par}=\operatorname{amp}(0)f_0,\qquad
w_{\rm ímpar}=\operatorname{amp}(0)(f_1-f_0).
\]

Para `R=0`, os teoremas `evenLeading_norm`, `even_leading_head_energy`, `even_leading_defect_energy`, `even_leading_cross` e suas versões ímpares provam:

| Quantidade | Primeiro par | Primeiro ímpar |
|---|---:|---:|
| `‖w‖²` | `1/4` | `1/24` |
| `‖H₀w‖²` | `2/9` | `8/225` |
| `‖η‖²` | `1/9` | `19/450` |
| `2 Re⟨C₀w,η⟩` | `1/9` | `-1/150` |
| complemento menos os dois termos de erro | `0` | `0` |

O termo misto muda de sinal entre os setores. Esses números têm provas Lean; `experiment.py` apenas os reproduz com `Fraction` e verifica a polarização em duas quadraturas independentes. Seus controles detectam a exclusão de qualquer um dos cruzamentos mistos.

### 6. Obstrução mais forte, especificamente neste carrier radial

Em `StationaryObstruction.lean`, `first_incident_ray` (de `LowOrder.lean`) mostra que a primeira incidência é sempre um múltiplo da mesma coluna `f₀`.

Se um mapa complexo-linear limitado **fixo** `C` realizasse eventualmente o retorno dessa direção, os limites dos vetores obrigariam `C f₀=-f₀` (`stationary_action_on_first_feature`). Como a incidência permanece nessa reta, o balanço seria zero para todo índice onde o entrelaçamento valesse.

Mas `first_even_boundary_energy` e o limite físico original fornecem

\[
2(\|I_k\|^2-\|R_k\|^2)\longrightarrow4h_0>0.
\]

Contradição. `no_stationary_completed_return` exclui **qualquer** mapa limitado fixo nesse carrier já identificado entre valores de `k`, não apenas shifts ou contrações.

Somente esta última obstrução usa o sinal independente já certificado `h₀>0`. Os resultados do defeito, da PR #41 e das regressões anteriores não usam sequer esse sinal. Não há prova nova de positividade de pivôs superiores.

## C — O que foi refutado

1. Identificar `-physicalCauchyShift (R+1)` com o retorno nativo após a mesma síntese física: há um defeito vetorial dominante não nulo para toda direção mônica da PR #41.
2. Descartar esse defeito porque o candidato possui complemento positivo: os cruzamentos cancelam exatamente o complemento dominante.
3. Substituir o candidato por **outro mapa fixo limitado no mesmo carrier radial** para realizar toda a primeira direção: contradiz `h₀>0`.
4. Considerar os cruzamentos sempre não negativos ou sempre não positivos: as duas regressões exatas têm sinais diferentes.

Não se demonstrou impossibilidade de uma família dependente de `k`; de uma coligação conservativa em um estado original mais completo; ou da positividade canônica geral. Também não se demonstrou que o operador físico anterior à identificação radial de espaços deva ser fixo nesta carta. Um operador anterior pode adquirir dependência de `k` por conjugação com mapas que dependem de `k`.

A obstrução não é o antigo NO-GO de margem relativa fixa da PR #42: aqui o próprio entrelaçamento vetorial de um operador fixo falha, mesmo sem hipótese de contração estrita.

## D — O que permanece aberto

O primeiro passo ainda ausente é identificar, a partir das relações físicas originais, **o transporte efetivo com seu parâmetro radial e seu domínio**, ou demonstrar que uma coligação anterior se transporta para ele. Não basta a existência de uma isometria do carrier.

Em particular, a tabela original

\[
f_j\longmapsto q(z_{k,j})f_j
\]

já está nas somas finitas. Um eventual operador físico precisa também manter o domínio e as condições de denominador dessas colunas; não se pode estender o argumento a endereços fora da faixa física apenas porque a expressão Lean usa inversão total. Sua extensão limitada, eventual contratividade e eventual fatoração de defeito positivo na métrica Cauchy não foram demonstradas aqui. Independência de colunas finitas, existência algébrica dessa tabela e existência de uma contração no fecho são afirmações diferentes.

O denominador `1-ρ_j` tende a zero: a identidade aritmética de Cayley não resolve automaticamente domínios nem autoriza aplicar uma função analítica qualquer ao shift.

Também continua aberta a identificação da forma canônica completa com uma Gram positiva. A conservação do shift e a completude do dicionário Cauchy–Laguerre não descarregam essa obrigação. Não se alegou `H_N≥0`, `K_N≥0` em toda ordem, nem identidade espectral global com alturas ou zeros.

Não se apagaram bordos, fases, duas quadraturas, correções Gamma, retorno ou cruzamentos. A fonte foi sempre a completada; a positividade do seu balanço não foi presumida. A theta aparece somente a montante do certificado já existente de `h₀>0`, usado explicitamente na última obstrução; ela não forneceu uma Gram substituta.

## E — Próximo passo mínimo

**Manter o índice radial no mapa antes de tentar uma conservação positiva.** O teste seguinte mais curto é confrontar uma coligação conservativa já existente com a tabela nativa `q(z_{k,j})`, primeiro para duas colunas independentes admissíveis, incluindo seus termos de bordo e completion. A igualdade precisa ser vetorial e em dois argumentos, com os mapas da carta radial explícitos.

A relação `z_{k,j}=δ_k(1+ρ_j)/(2(1-ρ_j))` fornece o endereço exato para esse confronto. Ela é uma ponte de coordenadas agora demonstrada, não uma conclusão de sinal.

Uma possível rota legítima seria demonstrar que os mapas físicos de mudança de carta transportam uma coligação original para uma família `C_k`, e então calcular seu defeito bilinear sobre a mesma fonte. Não se deve escolher `C_k` ou sua métrica a partir dos pivôs desejados. Tampouco basta postular que a tabela nativa é contrativa: isso recolocaria como hipótese precisamente o sinal que se procura explicar.

Se a igualdade falhar já nas duas colunas, registrar o novo defeito. Se existir, controlar domínios e os cruzamentos desse defeito antes de extrair coeficientes ou limites. A informação radial eliminada por uma identificação fixa não pode ser recuperada escolhendo outro shift fixo.

## Validação e reprodução

Os módulos novos contêm **50 teoremas e 15 definições públicas**, sem contar as fontes antigas recuperadas. Os módulos novos e as duas fontes imutáveis da PR #42 são compilados explicitamente, com `warningAsError=true`. A validação também executa:

- inventário de todas as declarações públicas e `#print axioms`;
- auditoria transitiva de **tipos e corpos**; somente `propext`, `Classical.choice`, `Quot.sound` são permitidos;
- bloqueio de consumidores posteriores H6/K6/H7, de positividade Stieltjes recebida e de controles de Loewner condicionais; bloqueio de `h₀>0` nos grupos anteriores ao último;
- controle lexical de `sorry`, `admit`, `native_decide` e novos axiomas;
- regressões racionais e polarizadas;
- build focado e raiz `lake build --wfail`, auditorias Foundation/Geometry/Analysis e regressão das doze fontes;
- verificação de preservação de `main`, referências anteriores, fonte nativa, arquivos de pesquisa não rastreados, pins e worktrees.

Na mesma pilha de dependências Lean da PR #61, já compilada, e com o checkout nativo no HEAD indicado:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/native-conservative-intertwiner/validate.py
```

`prepare_pr42.py` recupera e verifica as duas fontes históricas exatas antes da compilação. `compile_module.sh` registra explicitamente os diretórios de módulos ancestrais usados; não altera dependências nem pins. Uma instalação limpa precisa compilar essas dependências anteriores, conforme os scripts dos seus próprios relatórios, antes de executar esta validação.

**Execução concluída: 21/21 checks passaram**, incluindo o build raiz, as três auditorias e a regressão das doze fontes. A auditoria pública passou nas 65 raízes; os seis grupos transitivos estão registrados em `evidence/kernel-Audit.log`.

Os resultados, comandos, tempos, logs e SHA-256 são registrados em `evidence/checks.json`, `evidence/kernel-Audit.log`, `evidence/preflight.json`, `evidence/exact-controls.json` e `evidence/source-sha256.json`.

**Alcance:** avanço formal na localização do entrelaçamento e em seu defeito; NO-GO demonstrado para uma realização fixa específica e, na primeira direção, para qualquer mapa limitado fixo na carta radial. A ponte conservativa efetiva e o sinal canônico geral permanecem abertos.
