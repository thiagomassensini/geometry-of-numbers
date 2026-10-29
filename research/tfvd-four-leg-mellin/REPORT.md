# Quatro pernas do readout: transporte Mellin e correções TFVD

**Resultado: PARTIAL.** Foi fechado o transporte das quatro pernas originais de `readoutResidual`, antes de qualquer pareamento, em todo corte finito e para dois parâmetros independentes com parte real positiva. A identificação direta desse residual apenas com o valor do comutador de rotações C2 falha já no primeiro bloco. O transporte da fonte física completa até uma Gram canônica positiva continua aberto.

## A — O que já estava demonstrado

### Base e preservação

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch desta entrega: `agent/tfvd-four-leg-mellin`.
- Base: `6c9ea4a4817ebb1befedd8bd9491cba2ef2de987`, branch da PR #73, `agent/native-camera-tail-mellin`.
- `origin/main` conferido: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. A PR #73 estava aberta e draft, sem merge. Esta continuação é empilhada sobre ela.
- Fontes do operador lidas em `/home/thlinux/carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Execução no host `llm`. Fonte, métricas, amplitudes, fases, câmeras, completion, pins e trabalhos anteriores preservados. Somente arquivos novos de pesquisa pertencem à entrega.

`evidence/source-provenance.json` registra fontes e pacotes. O checkout principal manteve seu diretório não rastreado `research/entrywise-moment-square/`; os dois módulos C2 não rastreados do operador também foram preservados.

### Teoremas anteriores utilizados

A PR #72 calibrou a porta Green finita. A #73 transportou as duas caudas originais e demonstrou o controle integral com `1 + |log x|`, a correção Gamma e a identificação do campo `completion` do ledger.

Reutilizados aqui, no namespace `CarryCameraTail`:

- `bounded_heat_mellin_hasDerivAt`.
- `native_head_from_heat`.
- `gammaUndress_gammaDress`.
- `native_ledger_with_mellin_completion`.

As quatro funções de residual e seu pareamento já existem em `CompletedC3MixedGreenWronskianDefect.lean`. As pernas efetivas são `canonicalMixedBoundaryResidualLegs`, com tipo `ReflectedBoundarySynthesisData (Fin M × Fin 2)`.

O retorno enriquecido original, `enrichedAngularTfvdDecode_encode`, recupera três gradientes: `first`, `second`, `dormant`. O bordo conserva as duas células `(first,second)` e `(second,dormant)`. A aresta central participa das duas células; seus dois papéis não são eliminados.

A nota anexada apontou `c2FiberPoint_log_increment_defect`. O teorema preexistente `c2LegFiberRealState_succ_eq_correctedStep` já demonstra também o passo corrigido do estado real. O canário `materialTfvdAnalysis_phase` usa uma rotação constante em profundidade por endereço material fixo; sua conclusão não pode ser aplicada automaticamente a uma rotação que varia em profundidade.

A PR #41 permanece relevante como consumidor posterior: sua costura inversa-Schur exige apenas inversibilidade. A identidade com o residual não determina seu sinal. Nenhuma definição de momentos da #41 é usada para fabricar as fontes desta entrega.

## B — O que foi demonstrado agora

Os nomes novos estão no namespace `CarryFourLeg`, em seis módulos separados.

### 1. Cada gradiente mantém seu valor e seu jet

`GradientMellin.lean` parte do modo original `E_n(x)=exp(-π n²x)` e define a aresta literal

\[
e_n(x)=E_{n+2}(x)-E_{n+1}(x).
\]

Não se define essa aresta por um momento ou pelo resultado pretendido. `heat_edge_norm_le` dá `|e_n(x)| ≤ E_(n+1)(x)` para `x>0`, permitindo controlar o valor e a integral com `log x`.

Com `𝓜_s[f]=∫_0^∞ x^(s/2-1)f(x) dx`, o par integral é

\[
\mathcal J_s[f]=\left(\mathcal M_s[f],-\frac12\mathcal M_s[\log x\,f]\right).
\]

`heat_edge_trace_calibration` prova, para `Re(s)>0`:

\[
\mathcal J_s[e_n]=\mathcal D_s(g_n(s),\ell_n(s)),
\]

onde `g_n = positiveDirichletGradient`, `ell_n = positiveLogDirichletGradient` e

\[
\mathcal D_s(v,\ell)=(\Gamma_{\mathbb R}(s)v,
\Gamma_{\mathbb R}(s)\ell-\Gamma'_{\mathbb R}(s)v).
\]

`native_gradient_hasDerivAt` demonstra a derivada negativa do gradiente original. O termo Gamma é mantido; não se identifica o jet material com a derivada na coordenada teta.

`materialEdgeTrace` aplica a inversa analítica já calibrada na #73. Não altera uma métrica. `material_edge_trace_eq` recupera exatamente os dois canais originais da mesma aresta.

### 2. Igualdade das quatro pernas antes do pareamento

`MixedLegs.lean` recupera os endereços por decodificação do par original. Para `mr=(m,r)`, com `r=0,1`, defina `j=3m+r`. `original_mixed_legs_addresses` prova:

| Campo original | Valor decodificado |
| --- | --- |
| `left mr` | `g_j(w)` |
| `right mr` | `g_(j+1)(w)` |
| `jetLeft mr` | `ell_j(z)` |
| `jetRight mr` | `ell_(j+1)(z)` |

Essa identificação vale para os parâmetros de codificação não nulos originais `kappa`, `omega m`; não é postulada na estrutura.

`heatMixedLegs` constrói a imagem de cada papel a partir do par integral de sua aresta. `original_four_legs_mellin` prova a **igualdade do registro de quatro funções inteiro**, para todo `M`, `Re(z)>0`, `Re(w)>0`:

\[
\operatorname{heatMixedLegs}(M,z,w)
=\operatorname{canonicalMixedBoundaryResidualLegs}
(M,\operatorname{tfvdHaarScale},1,z,w).
\]

Os parâmetros permanecem independentes. A aresta intermediária é preservada nos dois papéis por `middle_value_edge_shared` e `middle_log_edge_shared`.

### 3. Quatro resíduos e o campo readoutResidual original

`ReadoutResidual.lean` transporta também os readouts da cabeça, com a semente, usando a #73. `four_readout_residuals_mellin` prova a igualdade do quádruplo dos resíduos lineares, antes do pareamento bilinear.

`heatReadoutCorrection` usa a fórmula original `mixedBoundaryResidualCorrection`, com todos os seis termos e suas conjugações. Não é definida como diferença entre um Wronskiano desejado e uma Gram.

`heat_readout_eq_original_ledger` identifica exatamente essa expressão integral com o campo `readoutResidual` do ledger nativo.

`heat_crosses_eq_original_ledger` transporta a proveniência dos cruzamentos ordenados entre todos os rótulos bloco/aresta. `native_ledger_with_mellin_readout` dá:

\[
W=G_{\rm finito}+\Delta_{\rm green}
+\Delta_{\rm cruzamentos}^{\rm Mellin}
+\Delta_{\rm readout}^{\rm Mellin}
+\Delta_{\rm completion}^{\rm Mellin}.
\]

`greenProvenance` continua explícito. As caudas, o quociente de câmera e o dressing permanecem nos resultados anteriores; nenhum foi removido por esta substituição. A fase radial da porta Green não foi diferenciada holomorficamente.

### 4. Transporte variável exige interior e bordo corrigidos

`VariableTransport.lean` incorpora as duas provas do diagnóstico anterior, agora na branch auditável. Elas usam o bracket e o traço reais existentes, em duas quadraturas e no carrier `CarryVerticalL2` original. A pertença das sequências ao carrier e a relação coordenada de rotação são explícitas.

Para `Y_j=U_j X_j`:

\[
(B_\eta Y)_j-U_j(B_\eta X)_j
=\eta^{-1}(U_{j+1}-U_j)X_{j+1}
+\eta(U_{j-1}-U_j)X_{j-1}.
\]

Para a inclinação `tau_eta(X)=eta^(-1)X_1-X_0`:

\[
\tau_\eta(Y)-U_0\tau_\eta(X)=\eta^{-1}(U_1-U_0)X_1.
\]

`c2_phase_correction_hasDerivAt` demonstra também que o primeiro jet angular é `-(d_(k+1)-d_k)`, mesmo em tempo zero. Zerar o valor da fase não apaga esse jet.

`scalar_bracket_multiplier_defect` e `scalar_trace_multiplier_defect` demonstram as versões para um multiplicador complexo `a_k`, incluindo amplitude e fase. `multiplier_tfvd_reconstruction` aplica a identidade TFVD finita existente à sequência `a_k x_k`, mantendo a correção do interior e a inclinação inicial corrigida. Não exige uma comutação falsa e não introduz outro operador TFVD.

### 5. Correção material C2 completa

Escreva `n_k=2^k m+epsilon` e `d_k=log(1+epsilon/(2^k m))`. `c2_material_wave_step` demonstra, nos pontos materiais positivos:

\[
n_{k+1}^{-s}=2^{-s}e^{-s(d_{k+1}-d_k)}n_k^{-s}.
\]

`c2_material_correction_norm` identifica o módulo do fator extra como `exp(-Re(s)(d_(k+1)-d_k))`.

`c2_material_amplitude_factor` demonstra a comparação que a nota anterior deixava apenas derivada:

\[
n_k^{-1/2}=\operatorname{realCriticalAmplitude}(2,k)\,
m^{-1/2}e^{-d_k/2}.
\]

A amplitude de profundidade não foi substituída pela amplitude material. O fator entre elas foi demonstrado explicitamente.

### 6. Piloto C2–C3 com pontos, amplitude e jet completos

`C2CellStep.lean` define o par literal em cada ponto existente:

\[
J(n;s)=(n^{-s},\log(n)n^{-s}).
\]

Seu transporte usa o fator de onda já demonstrado, `a=2^{-s}exp(-s Delta d)`, e o incremento real `L=log 2+Delta d`:

\[
T(J)=(aJ_1,a(J_2+LJ_1)).
\]

`c2_leg_jet_step` prova que esse mapa recupera o par do ponto seguinte. O termo `LJ_1` conserva o jet do transporte; a amplitude não foi normalizada para desaparecer.

`one_block_c2_cells_before_step` identifica os dois trios concretos de centros 2 e 3 com as células do primeiro bloco C3, incluindo os jets:

\[
((g_0,g_1),(g_1,g_2)).
\]

Depois de transportar os três pontos de cada célula e só então formar os gradientes, `one_block_c2_cells_after_step` prova:

\[
\boxed{((g_2,g_3),(g_4,g_5)).}
\]

As fórmulas valem para o par valor/log-jet, e para qualquer parâmetro complexo; podem ser aplicadas separadamente a `z` e `w`.

| Célula | Pontos antes | Gradientes antes | Pontos depois | Gradientes depois |
| --- | --- | --- | --- | --- |
| Centro 2 → 4 | 1, 2, 3 | g0, g1 | 3, 4, 5 | g2, g3 |
| Centro 3 → 6 | 2, 3, 4 | g1, g2 | 5, 6, 7 | g4, g5 |

**Níveis suportados:** o piloto utiliza a família `c2FiberPoint` nos níveis 0 e 1. O centro 2 é par; não se impõe que os dois núcleos sejam ímpares. Portanto, esse teste não identifica automaticamente os níveis usados com a profundidade intrínseca máxima de ambos os centros na torre Carry.

Há ainda uma identidade polarizada nova, `c2_two_leg_green_defect`. Para duas pernas com fatores `a,b` e incrementos reais `L,K`, no Green original:

\[
\boxed{G(T_1p,T_2q)=\overline a b\,G(p,q)
+\overline a b(L-K)\langle p_1,q_1\rangle.}
\]

O termo valor–valor aparece quando as pernas têm incrementos distintos. Não foi apagado, convertido em norma nem declarado positivo. Essa identidade usa o `greenForm` de pares complexos. Sua identificação com um wedge misto C3 não é presumida; a igualdade das quatro pernas e de seus resíduos C3 foi demonstrada separadamente, com `z` e `w` independentes.

## C — O que o primeiro bloco refuta

`OneBlock.lean` verifica os papéis originais `M=1`:

\[
(\mathrm{left}_0,\mathrm{right}_0,\mathrm{left}_1,\mathrm{right}_1)
=(g_0,g_1,g_1,g_2).
\]

São os gradientes nos endereços `1→2`, `2→3`, `3→4`. O teste conserva a repetição do papel central e os dois parâmetros independentes.

`one_block_right_residual_at_center` calcula o componente direito original, para `w=1/2`:

\[
\boxed{r_R=1+2(2^{-1/2}-3^{-1/2}).}
\]

`one_block_right_residual_center_gt_one` demonstra `Re(r_R)>1`, e `one_block_right_residual_center_ne_zero` registra sua não nulidade. Não se usou positividade Hankel ou uma caixa theta.

Por outro lado, a correção angular C2 `-t(d_(k+1)-d_k)` é zero em `t=0`, por `zero_time_leg_phase`. Assim, **falha qualquer identificação direta que obrigue esse componente do residual a zerar quando os comutadores das rotações são zero**. A amplitude material, as somas de gradientes, a semente e os demais dados de reconstrução precisam participar da comparação.

Esse resultado é sobre um componente linear. Não prova que a correção bilinear total seja não nula ou positiva; os outros componentes e cruzamentos continuam presentes. Tampouco refuta um transporte com amplitude e dados de bordo completos, ou um mecanismo que utilize os jets da fase. A derivada angular foi explicitamente conservada e pode ser não nula quando o valor da fase é zero.

`one_block_middle_splits_at_one` acrescenta um controle nativo exato em `s=1`, antes de quociente de câmera ou completion. Os dois novos gradientes centrais são `-1/20` e `-1/30`: já não satisfazem a antiga igualdade da aresta compartilhada. Esse teste refuta manter literalmente a mesma restrição de sobreposição no piloto. Não é um NO-GO para a fonte completada crítica ou para uma costura com mais rótulos, bordos e cruzamentos.

Há também um teste de endereços: a aresta compartilhada dos dois trios consecutivos deixa de ocupar o mesmo endereço quando seus centros são duplicados preservando raio um. `dilated_middle_addresses_distinct` prova essa distinção aritmética. É uma limitação da reutilização literal do mesmo padrão de sobreposição, não uma impossibilidade da síntese global. Os rótulos não podem ser identificados sem um crosswalk próprio.

## D — O que está no kernel e o que permanece aberto

### Demonstrado

- Imagem integral das quatro pernas efetivas e dos quatro resíduos, para todo corte finito e parâmetros independentes em `Re>0`.
- Identificação exata dos campos `readoutResidual` e `crossProvenance` após esse transporte.
- Correções de bracket/traço e reconstrução TFVD com multiplicador variável.
- Passo material C2, módulo de sua correção e fator de amplitude frente à amplitude de profundidade.
- Teste exato do residual direito no primeiro bloco e distinção dos endereços após dilatação.

### Ainda aberto

Foi demonstrado o crosswalk local dos dois trios concretos e sua evolução com um jet completo. Continua aberto um encoder físico coerente entre toda a família crescente C2 e o registro C3 global, com suas profundidades intrínsecas, cutoffs e caudas. A igualdade local não identifica automaticamente esses estados físicos globais.

Também continuam abertos o transporte físico de todos os canais de `greenProvenance`, uma isometria da síntese completa e uma identidade de Gram positiva para o kernel canônico. Nenhum sinal all-order de Hankel ou de pivôs foi concluído.

O resultado da #41 mantém sua função: quando o balanço físico completo tiver o sinal necessário, ele poderá ser transportado ao mesmo residual inversa-Schur, sem hipótese excessiva de positividade no passo algébrico. Nesta entrega, os momentos não entram na construção nem como premissa.

### Validação

`validate.py` recompila explicitamente as dependências de pesquisa das #72/#73, os seis módulos novos e `Audit.lean`. Executa os builds focados de geometria e do operador com `--wfail`, o build raiz, as auditorias Foundation/Geometry/Analysis, hashes e verificações de preservação. O build raiz sozinho não compila a pesquisa; os módulos novos têm seus próprios logs.

`Audit.lean` imprime os axiomas das **58 declarações públicas novas: 43 teoremas e 15 definições**, e percorre **5.861 constantes transitivas**, nos tipos e nos corpos. Permite somente `propext`, `Classical.choice`, `Quot.sound` na Analysis. Rejeita os momentos canônicos, polinômios de momentos theta, consumidores de sinais e o namespace de pesquisa `CarryThetaPolarized`.

**Os 30 comandos finais passaram, todos com código de saída zero.** Os comandos, códigos de saída e hashes estão em `evidence/validation.json`; o número de raízes e dependências está em `evidence/lean-Audit.log`. Não há `sorry`, `admit`, `native_decide`, novos axiomas matemáticos ou alteração de pins.

Reprodução no host `llm`, em checkout desta branch:

```bash
cd /caminho/do/checkout/geometry-of-numbers/research/tfvd-four-leg-mellin
python3 validate.py
```

## E — Próximo passo mínimo

O próximo campo explícito do ledger é `greenProvenance`. Sua fonte original é `finiteC3EnrichedTfvdBlockGreenProvenance`: quatro transportes de pernas visíveis, quatro da célula seguinte e a compensação Green dormente.

O alvo mínimo é construir a imagem dessas componentes **célula por célula**, usando `original_four_legs_mellin` e a porta Green finita da #72, e demonstrar a igualdade dos campos antes de somar seus totais. Manter as fases radiais dos dois parâmetros e a compensação dormente.

Em paralelo à interpretação geométrica, a menor obrigação C2–C3 é estender o crosswalk local a uma costura coerente dos novos papéis entre blocos, preservando os cutoffs e suas caudas. O piloto já determina os endereços após o passo e mostra que a antiga sobreposição não se conserva literalmente. O valor do comutador angular sozinho não explica o residual; um candidato completo deve incorporar o fator de amplitude demonstrado e os dois dados de bordo.

Somente com o ledger completo identificado cabe buscar uma lei independente de sinal. A existência das imagens integrais não transforma o balanço assinado numa norma positiva.

**Conclusão:** o alvo das quatro pernas foi fechado, inclusive além do primeiro bloco. A investigação também localizou uma obstrução à identificação direta apenas com o valor do comutador de fase e formalizou os termos que um transporte completo precisa conservar. O alcance é PARTIAL para a ponte física global.

Fim do relatório.
