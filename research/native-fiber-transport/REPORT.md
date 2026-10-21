# Transporte da fibra física e correção Cauchy dos cruzamentos

**Resultado: PARTIAL**, com NO-GO específico para o consumidor de parâmetro fixo no span causal inteiro. O próximo teste da PR #46 foi executado: calculamos as imagens vetoriais das duas parcelas da fonte enriquecida pelos readouts existentes, preservando a coerência dos dados duplicados, as duas quadraturas, os dois cruzamentos ordenados e a identidade do mesmo kernel canônico. A comparação entre escalas diagonais deixa uma correção fora da diagonal; ela foi transportada pelo Cauchy ORIGINAL, sem criar métrica ou fonte substituta.

Branch `agent/native-fiber-transport`, baseada em `6e47f8908408aa268edfecc1d9769c6be346d067` da PR #46. A main permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Todas as mudanças desta rodada vivem em `research/native-fiber-transport/`. Fonte nativa consultada e compilada em `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. Sem alterações nesse repositório, em pins ou na PR #46; sem merge automático.

## A — O que já estava demonstrado

A PR #46 fornece `CarryTraceFiber.physical_reconstruct`, `invisible_orthogonal` e a decomposição do estado físico `x` em sua seção ambiente de traço e na componente `I_x`. O estado original é conservado como soma, e `I_x` é não nulo na fonte central. Isso não autorizava afirmar que cada parcela separada pertencesse ao span causal.

O carrier enriquecido que precisamos já existe: `CanonicalCompletedC3EnrichedChiralSourceCarrier`. Ele retém uma coordenada Naimark externa, o estado físico all-cutoff e o bloco arquimediano/carta. A coordenada externa e a direta armazenada são duplicações de proveniência sujeitas à condição `canonicalCompletedC3EnrichedDirectCoherentSubmodule`; não são duas fontes independentes.

Também existem todos os consumidores usados aqui: `canonicalCompletedC3EnrichedNormalizedFullWronskianReadout`, os readouts quiral positivo/negativo, `canonicalCompletedC3EnrichedCoisometricChiralReadout` e sua versão em coordenadas de câmera. O estado canônico é `canonicalCompletedC3EnrichedChiralSourceState`.

**A obstrução de dimensão para o consumidor com parâmetro fixo já existia** em `CompletedC3CausalChiralKernelObstruction` e `CompletedC3CoisometricAmbientStrictPositivity`. Não a apresentamos como descoberta desta rodada. Reutilizamos a independência das fontes em expoentes reais distintos e refinamos o teste para um testemunho no núcleo do readout Wronskiano COMPLETO, com energia e parcelas identificadas.

O Cauchy físico é `completedNativeRadialChiralCauchyState`, e a identidade existente `ChiralReturn.radialCauchy_inner_mul_separation` diz que seu pareamento cancela a separação espectral com fator exatamente `i`. Nenhum desses objetos foi reconstruído a partir de momentos desejados.

## B — O que foi demonstrado agora

### B.1 — As duas parcelas preservam a coerência

Para `u=(a,(x,A))` no carrier enriquecido existente, definimos somente a decomposição contábil

\[
V_u=(0,(\operatorname{balancedLift}(Px),A)),\qquad
H_u=(a,(I_x,0)).
\]

`source_reconstruction` prova `V_u+H_u=u`. `tracePart_coherent` e `fiberPart_coherent` mostram que ambas respeitam a coerência do direto duplicado quando `u` a respeita. Não afirmamos que pertençam individualmente ao span causal; a combinação original permanece intacta.

`tracePart_orthogonal_fiberPart` e `source_pairing_split` preservam a métrica L2 original do carrier enriquecido. O produto real da coordenada Gamma usa apenas a restrição de escalares da estrutura complexa existente, com a mesma norma. Não foi introduzido peso ou produto interno escolhido para ajustar momentos.

### B.2 — Imagens dos mesmos mapas nativos

Escrevemos `T_z` para o readout Wronskiano completo, `P_z,N_z` para suas duas projeções quirais, e `C_z` para o readout ampliado existente. Se `a_z=sqrt(2 Im z)`, então os teoremas `full_trace`, `full_fiber_zero`, `plus_trace`, `plus_fiber_zero`, `minus_trace`, `minus_fiber_zero`, `enlarged_trace` e `enlarged_fiber` dão

\[
T_z V_u=T_z u,\quad T_z H_u=0,
\]

\[
P_z V_u=P_z u,\quad N_z V_u=N_z u,\quad P_z H_u=N_z H_u=0,
\]

\[
\boxed{C_z V_u=(0,N_z u),\qquad C_z H_u=(a_z\,a,0).}
\]

A versão câmera satisfaz as mesmas identidades, com a imagem coisométrica do direto. `enlarged_trace_fiber_cross` e `enlarged_fiber_trace_cross` provam os DOIS cruzamentos complexos nulos, para `z,w,u,v` independentes. O zero vem das imagens calculadas em blocos distintos, não de uma hipótese de ortogonalidade descartando termos.

Para o defeito do consumidor existente,

\[
\mathfrak d_{z,w}(u,v)=\langle P_z u,P_w v\rangle-\langle C_z u,C_w v\rangle,
\]

`defectPair_split` conserva a polarização inteira. Para `Im z>=0`, `fiber_defect_exact` e `defectEnergy_budget` provam

\[
\boxed{d_z(H_u)=-2\operatorname{Im}z\,\|a\|^2,}
\]

\[
d_z(u)=\|P_z u\|^2-\|N_z u\|^2-2\operatorname{Im}z\,\|a\|^2.
\]

A fibra transportada NÃO constitui automaticamente uma margem positiva nesse consumidor.

### B.3 — Teste no span de fontes verdadeiras

`nativeSources` reutiliza os treze pontos originais, com expoentes `(j+1)/14`, estritamente dentro do strip. `nativeSynthesis` sintetiza suas fontes COMPLETAS com coeficientes reais. A independência de suas saídas Naimark é deduzida do teorema nativo já existente; não é hipótese de Gram canônica.

`full_trace_native_kernel_witness` prova, para cada parâmetro fixo `z`, a existência de coeficientes `c_j`, não todos nulos, tais que

\[
u=\sum_{j<13}c_jY_j,\qquad T_z u=0,\qquad a(u)\ne0.
\]

São coeficientes reais obtidos existencialmente pelo núcleo de uma aplicação para o carrier de dimensão real 12. Não fornecemos seus valores racionais ou uma tabela numérica.

`nativeSynthesis_causal` prova que `u` pertence ao span causal ORIGINAL. `causal_full_trace_negative_witness` prova, para `Im z>0`,

\[
d_z(V_u)=0,\qquad d_z(H_u)<0,\qquad d_z(u)<0.
\]

O teste não usa um vetor ambiente arbitrário de direto externo. O readout completo, incluindo os blocos completion/carta, é anulado depois da síntese. `nativeSynthesis_ambient_port` e `nativeSynthesis_ambient_norm_camera` provam que a promoção Naimark e a igualdade de normas com a câmera sobrevivem a essa mesma síntese finita.

### B.4 — O kernel canônico e os quatro canais permanecem os mesmos

`native_wronskian_trace_signature` recupera o Wronskiano original pela assinatura quiral na parte `V`, em dois argumentos e sem divisão. `native_kernel_trace_signature` dá o kernel `K_Q`, com `Q=-F'/(2F)`, nos domínios nativos, com `F(z),F(w)` não nulos e `w!=conj(z)`.

`native_four_channel_fiber_identity` prova para o defeito de quatro canais EXISTENTE

\[
\boxed{D_4(z,w)=(w-\bar z)G_H(z,w)-i\,\Sigma_V(z,w),}
\]

onde `G_H` é o pareamento Naimark transportado da fibra das duas fontes canônicas e `Sigma_V` é a diferença quiral completa da parte do traço. Nenhum defeito foi anulado ou substituído por uma norma positiva.

### B.5 — O termo que a diagonal não detecta

O produto `a_z a_w` dos dois fatores diagonais não é, em geral, a separação `(w-conj z)/i`. Definimos a sua diferença, como observável de comparação,

\[
\eta(z,w)=(w-\bar z)-i\sqrt{2\operatorname{Im}z}\sqrt{2\operatorname{Im}w}.
\]

`native_four_channel_separation_correction` identifica exatamente

\[
\boxed{D_4(z,w)=-i\,\mathfrak d_{z,w}(Y_z,Y_w)+\eta(z,w)G_H(z,w).}
\]

`separationCorrection_diagonal` prova `eta(z,z)=0` no semiplano superior. Mas, em pontos radiais, `separationCorrection_radial` prova

\[
\boxed{\eta(ia,ib)=i(\sqrt a-\sqrt b)^2\qquad(a,b\ge0).}
\]

O termo é não nulo se `a!=b`. `admissible_separation_correction_nonzero` testa dois pontos do domínio nativo, `i/16` e `i/64`. Portanto uma coincidência na diagonal não autoriza identificar os dois kernels polarizados.

### B.6 — Proveniência Cauchy da correção

Se `U_{k,j}` são os vetores Cauchy ORIGINAIS e `z_{k,j}` os pontos radiais ORIGINAIS, escrevemos

\[
O_{ij}=a_i a_j\langle U_{k,i},U_{k,j}\rangle.
\]

`radialOverlap_inner` identifica `O` com o pareamento dos mesmos vetores observados nas escalas diagonais já determinadas pelo consumidor. Isso é uma comparação de coordenadas; a fonte e seus coeficientes não são renormalizados. `radialOverlap_diagonal` e `radial_observed_norm_sq` provam a escala unitária diagonal.

Usando a separação Cauchy original, `radial_cauchy_separation_correction` prova

\[
\boxed{\langle U_i,U_j\rangle\eta(z_i,z_j)=i(1-O_{ij}).}
\]

Assim `radial_four_channel_overlap_identity` mantém, após o transporte original,

\[
\langle U_i,U_j\rangle D_{4,ij}
=-i\langle U_i,U_j\rangle\mathfrak d_{ij}+i(1-O_{ij})G_{H,ij}.
\]

`finite_radial_overlap_transport` soma essa identidade com duas famílias complexas de coeficientes independentes e dimensões finitas possivelmente diferentes. Conserva todos os cruzamentos ordenados. Os coeficientes de fonte originais podem ser substituídos literalmente; nenhum peso é escolhido para melhorar um sinal.

## C — O que foi refutado e o que não foi

A tentativa de construir uma contração uniforme do consumidor de parâmetro FIXO no span causal inteiro falha. A obstrução já conhecida foi refinada com uma combinação de fontes verdadeiras que anula o traço completo e tem defeito estritamente negativo. Também está refutada a substituição geral da separação Green pelo produto das escalas diagonais: há um termo exato fora da diagonal.

Isso NÃO demonstra que a Hankel canônica tenha uma direção negativa. No testemunho finito o mesmo parâmetro `z` é usado pelo consumidor de todas as fontes; no kernel canônico cada fonte tem seu próprio parâmetro e a separação de dois argumentos deve ser conservada. Essa diferença é explicitada pela correção `eta` e pelo overlap Cauchy.

Não mostramos que `V_u` ou `H_u` separados pertençam ao span causal. O testemunho inteiro `u` pertence, e sua reconstrução é exata. Não concluímos que toda representação positiva seja impossível.

## D — Certificação e lacuna atual

Os módulos são `CoherentSplit`, `TransportBudget`, `SourceSpan`, `KernelBudget`, `SeparationCorrection`, `NativeCauchyOverlap` e `Audit`. São **58 teoremas públicos e 19 definições/abreviações**. Os nomes públicos são enumerados em `public-roots.json`. `#print axioms` e o guard transitivo percorrem **77 raízes públicas e 7.073 constantes** de tipos e corpos. Permitem somente `propext`, `Classical.choice` e `Quot.sound`, rejeitam os certificados de sinal finito listados e os dois teoremas prontos de NO-GO que poderiam esconder o cálculo do novo testemunho.

A inspeção das hipóteses é necessária além do guard nomeado. A aplicação a momentos continua sendo uma forma assinada; não recebeu `PosDef`, `PosSemidef` ou hipótese equivalente para anunciar sucesso.

A reprodução e os resultados finais estão em `evidence/checks.json`, `evidence/kernel-Audit.log` e `evidence/source-sha256.json`. A validação concluiu **20 checks com código zero**. Recompila os três módulos herdados da PR #46, os sete módulos desta rodada, os módulos nativos usados, build focado e da raiz com `--wfail`, auditorias Foundation/Geometry/Analysis, regressão H6/K6 com doze fontes e preservação de arquivos históricos, pins e arquivos não rastreados do usuário no autoadjunto.

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/native-fiber-transport/validate.py
```

Sem campanha numérica, recálculo de momentos, novos axiomas ou substituição de fonte. A versão do checkout nativo e seus hashes são registrados pelo preflight. A cadeia de PRs preserva a base da PR #46; main não foi alterada.

## E — Próximo passo mínimo

A obrigação do final da PR #46 — calcular as duas imagens, seus cruzamentos e a identidade do mesmo kernel — está executada para os readouts nativos analisados. Não deve ser tratada novamente como uma promessa aberta.

O consumidor uniforme com parâmetro fixo está bloqueado no span causal inteiro. A investigação positiva precisa trabalhar com a família de parâmetros corretos e com o Cauchy físico completo; não pode aplicar esse consumidor fixo como se fornecesse automaticamente o kernel de momentos.

O próximo teste concreto é transportar a última identidade aos stencils/jet syntheses canônicos já existentes, mantendo `O_ij` e o defeito variável `d_ij` sob a MESMA soma. Identificar se há cancelamento exato entre essas duas contribuições na família de jets ou uma desigualdade independente da positividade dos pivôs que controle sua combinação. Não basta controlar `d_ii`, substituir `O_ij` por sua diagonal unitária ou descartar os termos com `i!=j`.

A identidade finita desta rodada é a entrada para esse teste, não uma estimativa de sinal. Para `K_Q` positivo ou para todos os pivôs positivos ainda falta um mecanismo de sinal proveniente da fonte. O resultado permanece **PARTIAL**; o NO-GO é restrito à realização fixa testada.
