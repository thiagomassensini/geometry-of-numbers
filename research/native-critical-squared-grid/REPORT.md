# O que sobrevive quando as amostras da fonte coalescem

**Resultado global: PARTIAL.** Foram provadas uma nova identidade polarizada
da fonte crítica original, a reconstrução exata das quatro amostras, os
limites de suas curvaturas e a taxa do defeito de malha. Um contraexemplo
racional formal refuta a suficiência dos três sinais escalares de curvatura.
Não é um contraexemplo à fonte Carry canônica; sua positividade all-order
permanece aberta.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-critical-squared-grid`.
Base exata: `24741f75b8f2ebd72ccd53a1e7211d476014afd0`, head da PR #115,
consultada aberta e draft, ainda sobre #114. A nova PR é empilhada sobre #115,
sem merge automático. `main`, PRs anteriores, fonte, amplitudes, métrica,
completion, retorno, normalizações físicas e pins permanecem intactos.

## A — O que já estava demonstrado

Usamos as declarações atuais, não apenas a narrativa dos relatórios:

- A PR #115 provou `CarryOddCauchy.native_odd_cauchy_row`,
  `native_odd_kernel_filter`, `native_odd_kernel_forward_difference` e o
  transporte Green de perfis e misturas finitas, sem sinais canônicos.
- `CarryCubicOdd.critical_source_profiles`, `critical_field_vectors` e
  `critical_completed_parts` já constroem o mesmo input físico
  `C_k(a)=jet_(3,k)-a jet_(1,k)`, com `a` livre, fase e fatorial originais,
  três partes e duas pernas.
- `critical_signed_readout_exact` e `critical_green_readout_exact` identificam
  os **dois kernels ordenados** e os nove cruzamentos com a soma Cauchy de
  `criticalSampleReadout`. Reutilizamos essa proveniência completa.
- `critical_signed_tendsto` dá o limite
  `h₃-(a+b)h₂+ab h₁`, sem hipótese de sinal.
- `CarryEnergyCorrection.native_response_expansion` e
  `native_remainder_analytic` conservam o resto da resposta nativa original.
  São usados para o limite das amostras, não para substituir a fonte por um
  truncamento em identidades finitas.

A PR #41 continua determinando a direção lógica: escolher `a=h₂/h₁` após a
construção exige `h₁≠0` para a interpretação de Schur, mas não fornece seu
sinal. A investigação atual não fabrica vetores de uma Hankel-alvo.

**Índices:** `k` é regularização radial; `j` endereço material; `a,b`
coeficientes reais de ensaio independentes; `eta` é o parâmetro Green
original, `0<eta<1`. A malha quadrática abaixo é uma coordenada dos readouts,
não outra câmera, profundidade Carry, métrica, relógio ou operador físico.

## B — O que foi demonstrado agora

São **38 teoremas, nove definições de coordenadas/readouts e três
abreviações**, 50 raízes públicas no namespace `CarryCriticalGrid`.
As definições novas não são fontes, momentos ou produtos internos ajustados.

### B.1 — A malha é determinada pelos quatro endereços originais

Ponha `kappa=k+1`, `epsilon=kappa^(-2)` e

\[
x_j=j+1,\qquad u_j=\epsilon x_j^2,
\qquad (u_0,u_1,u_2,u_3)=\epsilon(1,4,9,16).
\]

A resposta original é `Q=responseReadout`. Somente **depois** da síntese e
do pareamento completos fazemos a mudança reversível de coordenadas:

\[
f_{k,j}=\frac{\kappa}{j+1}\,
Q\!\left(\frac{j+1}{\kappa}\right).
\]

`normalized_four_samples_recover` prova a inversa exata dessa leitura.
Não se multiplicou uma perna física por esse fator nem se alterou uma
amplitude. `squared_scale_nonzero`, `squared_scale_real_positive` e
`native_four_samples_real` descarregam os domínios da malha e a realidade
dos readouts a partir das definições originais.

### B.2 — Reconstrução com valor, inclinação e curvaturas

[SquaredGrid.lean](SquaredGrid.lean) define somente diferenças divididas dos
mesmos quatro valores, em malha não uniforme:

\[
\begin{aligned}
D_1f&=\frac{f_1-f_0}{3\epsilon},\\
D_2f&=\frac{(f_2-f_1)/(5\epsilon)-(f_1-f_0)/(3\epsilon)}{8\epsilon},\\
D_2^{\rm dir}f&=\frac{(f_3-f_2)/(7\epsilon)-(f_2-f_1)/(5\epsilon)}{12\epsilon},\\
D_3f&=\frac{D_2^{\rm dir}f-D_2f}{15\epsilon}.
\end{aligned}
\]

`grid_third_barycentric` conserva os quatro termos:

\[
D_3f=-\frac{f_0}{360\epsilon^3}
+\frac{f_1}{180\epsilon^3}
-\frac{f_2}{280\epsilon^3}
+\frac{f_3}{1260\epsilon^3}.
\]

`squared_grid_reconstruction` prova, para cada endereço, a reconstrução
Newton completa:

\[
\boxed{f_j=f_0+(u_j-u_0)D_1f
 +(u_j-u_0)(u_j-u_1)D_2f
 +(u_j-u_0)(u_j-u_1)(u_j-u_2)D_3f.}
\]

`squared_grid_data_injective` prova que os quatro dados
`(f₀,D₁f,D₂f,D₃f)` identificam exatamente os quatro readouts quando
`epsilon≠0`. **Isso não é injetividade do estado físico por um readout.**
Valor e inclinação são os dois dados iniciais dessa interpolação; não são
identificados automaticamente com os dois traços físicos da TFVD. Os
traços físicos continuam conservados pelo transporte Green anterior.

`grid_third_mul_node` e `grid_third_top_factors` provam, incluindo o termo
de extremo que seria perdido numa integração discreta incompleta:

\[
D_3(u f)=D_2f+16\epsilon D_3f,\qquad
D_3((u-9\epsilon)(u-16\epsilon)f)=D_1f.
\]

### B.3 — O polinômio exato e o defeito que não pode ser apagado

[CriticalGridPolynomial.lean](CriticalGridPolynomial.lean) introduz o
polinômio **derivado dos coeficientes críticos originais**:

\[
P_{a,b,\epsilon}(u)=1+(a+b)(u+12\epsilon)
+ab(u-9\epsilon)(u-16\epsilon).
\]

`critical_polynomial_limit_product` e
`critical_polynomial_shifted_product` provam as duas escritas exatas:

\[
\begin{aligned}
P={}&(1+au)(1+bu)
+\epsilon[12(a+b)-25ab u]+144ab\epsilon^2,\\
\boxed{P={}&[1+a(u+12\epsilon)][1+b(u+12\epsilon)]-49ab\epsilon u.}
\end{aligned}
\]

Os números `12,25,49` não são parâmetros de ajuste. Surgem da álgebra dos
quatro endereços, da métrica Cauchy e dos coeficientes com fase e fatorial
já provados. O fator `49=7²` mantém o cruzamento da polarização. A identidade vale para
a,b livres nesta combinação de dois jets; não se demonstrou que 49 seja a
correção de perfis de toda ordem.

Em [NativeCriticalGrid.lean](NativeCriticalGrid.lean),
`critical_readout_squared_grid` prova primeiro a identidade para qualquer
peso complexo dos quatro endereços. `native_critical_grid_exact` então
transporta a **forma nativa original**, eventualmente na regularização:

\[
\boxed{\mathcal B_k(C_k(a),C_k(b))
=-D_3\{P_{a,b,\epsilon_k}(u_j)f_{k,j}\}_{j=0}^3.}
\]

`B` permanece a forma complexa assinada original, com metade da diferença
dos pareamentos incidente/retornado. O resultado conserva dois inputs
independentes, as duas pernas e os nove cruzamentos Green. Não se substitui
a resposta por Taylor na igualdade finita.

`critical_grid_curvatures`, `grid_mixed_from_pairs`, `grid_first_from_pairs`
e `native_critical_curvatures_exact` extraem:

\[
\boxed{\mathcal B_k(a,b)=
-D_3f_k-(a+b)(D_2f_k+28\epsilon_kD_3f_k)-abD_1f_k.}
\]

O `28` contém o extremo `16` e o deslocamento `12`; não é descartável.
Os dados são recuperados por pares polarizados, inclusive os dois
cruzamentos `B(1,0)` e `B(0,1)`, não apenas por normas diagonais.

### B.4 — Produto principal e correção da mesma fonte

`critical_grid_product_defect` e
`native_critical_product_defect_exact` preservam:

\[
\mathcal B_k(a,b)=\mathcal P_k(a,b)+\mathcal D_k(a,b),
\]

\[
\begin{aligned}
\mathcal P_k(a,b)&=-D_3\{[1+a(u+12\epsilon_k)]
 [1+b(u+12\epsilon_k)]f_k\},\\
\mathcal D_k(a,b)&=49ab\epsilon_kD_3(u f_k).
\end{aligned}
\]

Na diagonal, o produto dentro de `P` é um quadrado escalar. **Uma diferença
dividida aplicada a um quadrado vezes a resposta não é automaticamente uma
norma de Hilbert.** Não se provou positividade de `P`, nem foi definida uma
nova métrica para obtê-la.

### B.5 — Os valores coalescem; os dados relacionais retêm os coeficientes

Para cada um dos quatro endereços, `native_four_sample_tendsto` prova:

\[
f_{k,j}\longrightarrow h_0.
\]

Apesar desse limite comum, `native_grid_first_tendsto`,
`native_grid_second_tendsto`, `native_grid_third_tendsto`,
`native_grid_mixed_tendsto` e `native_newton_data_tendsto` provam:

\[
\boxed{(f_{k,0},D_1f_k,D_2f_k,D_3f_k)
\longrightarrow(h_0,-h_1,h_2,-h_3).}
\]

Aqui aparece precisamente a informação que seria perdida ao substituir
prematuramente as quatro amostras por seu valor limite comum. A malha tem
divisores de ordem `epsilon`, `epsilon²` e `epsilon³`; não se pode pôr
`epsilon=0` nas fórmulas antes de tomar seus limites controlados.

São limites de **readouts**, não afirmações de convergência ou igualdade dos
estados materiais. A realidade do readout não elimina a segunda quadratura
do estado físico. A síntese completa permanece anterior a essas projeções.

`grid_constant_cancellation` e `critical_grid_constant` mostram por que a
parcela constante de `f` desaparece exatamente do balanço. Ela continua
presente nos dados de reconstrução. Não se declara o estado nulo porque um
observável seu se anula.

### B.6 — A taxa do defeito foi provada, não presumida

`squared_scale_tendsto_zero`, `native_grid_node_third_tendsto`,
`native_grid_defect_scaled_tendsto` e `native_grid_defect_tendsto_zero`
concluem para a mesma resposta completada:

\[
\boxed{\frac{\mathcal D_k(a,b)}{\epsilon_k}\longrightarrow49ab h_2,
\qquad \mathcal D_k(a,b)\longrightarrow0.}
\]

A presença de `epsilon` sozinha não justificaria o segundo limite. Foi
necessário controlar a diferença dividida que o acompanha. A prova faz isso
pelo limite das curvaturas da fonte original, sem assumir seus sinais.

Esse é o defeito **relativo ao produto deslocado acima**, não o primeiro
coeficiente de `B_k` menos seu limite total. Nada aqui prova monotonicidade
ou uma aproximação universal por cima/baixo ao Schur.

`native_critical_grid_tendsto` e `native_critical_grid_schur_tendsto`
recuperam a proveniência canônica anterior:

\[
\mathcal B_k(a,b)\to h_3-(a+b)h_2+ab h_1,
\qquad a=b=h_2/h_1:\quad \mathcal B_k\to h_3-h_2^2/h_1,
\]

com `h₁≠0` na especialização de Schur, sem hipótese de positividade.

## C — O que foi refutado

[GridSignObstruction.lean](GridSignObstruction.lean) testa a proposta de
controlar o balanço somente pelos sinais das curvaturas. A função racional
**diagnóstica** `f(u)=1/(1+u)²`, amostrada na malha original de `k=31`,
`epsilon=1/1024`, satisfaz formalmente:

- Quatro valores reais estritamente positivos.
- `D₁f<0`, `D₂f>0`, `D₃f<0`.
- Os três coeficientes `U=-D₁f`, `V=D₂f+28epsilon D₃f`, `W=-D₃f`
  são estritamente positivos.

Entretanto, com o mesmo padrão de coeficientes de ensaio `a=b=3/2`:

\[
\boxed{W-3V+\frac94U
=-\frac{12349553402974306304}{62570745502766028125}<0.}
\]

São `diagnostic_samples_positive_real`,
`diagnostic_three_curvature_signs`, `diagnostic_positive_entries`,
`diagnostic_critical_negative` e `no_sign_from_three_curvatures`.
A redução racional foi verificada no kernel Lean.

**O modelo diagnóstico não é a resposta nativa e não é inserido em nenhum
teorema canônico.** O no-go atinge somente o critério de sinais escalares
isolados. Não demonstra negatividade de h, falha da geometria ou
impossibilidade de uma realização física mais completa.

`mechanism_probe.py` também compara por `Fraction`, em 12 casos com inputs
independentes, quatro rotas: os coeficientes originais e a soma Cauchy dupla;
a diferença dividida; as três curvaturas; o produto com seu defeito.
Essas comparações são evidência executável independente, separada das provas
Lean; não entram como premissas nelas.

## D — O que permanece aberto

Falta uma propriedade específica da resposta completada que controle o
**acoplamento** de suas curvaturas. Os sinais de `U,V,W` não bastam.
A desigualdade `UW≥V²` é o critério quadrático de duas direções, não uma
nova causa geométrica descoberta. Não foi renomeada como hipótese resolvida.

O termo principal `P_k` permanece uma forma assinada sem representação
Hilbert positiva provada. O controle de `D_k→0` não determina o sinal do
limite da forma principal nem do Schur. A positividade all-order canônica,
a independência linear estrita e o operador infinito continuam abertos.

A interpolação da malha é um transporte exato de quatro readouts **após a
síntese**. Não foi demonstrado um intertwiner dos operadores da TFVD vertical
com a diferença não uniforme em u, nem uma isometria multibase. Os dois dados
iniciais de Newton não substituem os dois traços físicos.

## E — Próximo passo mínimo

O próximo teste de sinal deve focar o termo principal identificado em B.4,
com **dois argumentos independentes**. Procurar na fonte completada uma
identidade física para

\[
-D_3\{[1+a(u+12epsilon)][1+b(u+12epsilon)]f_k\},
\]

conservando retorno, bordo, dressing e correções. Se uma Gram física já
existente for candidata, comparar a primeira entrada e o cruzamento misto
exatos; qualquer falha deve produzir seu defeito. Não construir vetores dos
momentos desejados nem escolher uma métrica que ajuste a resposta.

A taxa do defeito de malha agora é conhecida. O alvo principal é seu
controle conjunto com a forma principal, com margem válida nas direções
críticas. A mera convergência do defeito a zero não fornece esse controle
relativo e não permite apagá-lo. A literatura interna contém bridges
condicionais, como `canonicalCompletedNativeGreenForwardDifferenceGramResidual`
e `positiveObservableNativeConvolutionDefect`; suas hipóteses de identificação
não foram descarregadas aqui nem tratadas como provas incondicionais.
Não voltar a um candidato de jatos Taylor brutos já refutado.

Se a próxima identidade só receber como hipótese a positividade dessa forma,
não resolverá a lacuna. O avanço necessário é uma relação independente da
fonte original que restrinja os cruzamentos, e não mais sinais diagonais.

### Validação e reprodução

No host canônico `llm`, em checkout da branch com as dependências registradas:

```bash
cd research/native-critical-squared-grid
python3 validate.py
```

O modo normal recompila os 73 ancestrais intactos. Nesta rodada foram
reaproveitados após verificação dos hashes das fontes contra Git, objetos
Lean, toolchain, manifest, árvore do núcleo, fontes nativas, pins e estados
das dependências:

```bash
python3 validate.py --reuse-upstream
```

**Os 17 checks locais passaram, todos com código de saída zero.**
Os quatro módulos novos e `Audit.lean` foram compilados explicitamente com
`lean -DwarningAsError=true`. Builds `lake build --wfail`, auditorias
Foundation/Geometry/Analysis, prova racional diagnóstica, probe independente
e preservação de fontes são verificações separadas. O cache não é versionado
nem obrigatório para reproduzir pelo modo normal.

A auditoria cobre `#print axioms` e tipos **e corpos** das 50 raízes:

| Grupo | Raízes | Dependências únicas | Restrição adicional |
| --- | ---: | ---: | --- |
| Construção e identidades exatas | 39 | 5.433 | Momento canônico proibido |
| Proveniência e limites | 11 | 5.165 | Sem certificados de sinais |

Ambos bloqueiam os sinais canônicos h₀/h₁, consumidores posteriores de
positividade finita, atalhos escalares da PR #110 e consumidores diagonais
bloqueados nas rodadas anteriores. Também bloqueiam as antigas fórmulas
`critical_cauchy_row`, `critical_readout_four_samples`,
`critical_rho_alternating` e `critical_diagonal_four_samples_exact`:
a nova polarização não foi inferida omitindo cruzamentos de uma diagonal.
Somente `propext`, `Classical.choice`, `Quot.sound` são permitidos na análise;
Foundation conserva sua auditoria própria. Sem axiomas matemáticos novos,
placeholders ou escapes de confiança.

`evidence/validation.json`, `public-roots.json`, `evidence/lean-Audit.log`,
`mechanism-probe.json`, `cache-restoration.json`, `upstream.json`,
`source-provenance.json`, `preservation.json` e `SHA256SUMS` registram os
comandos, resultados, fontes e integridade. Logs brutos são conservados em
`.raw.log.gz` quando há normalização de espaços finais. O resultado é local,
sem afirmação de CI remoto. Commit e URL ficam na entrega externa. A cópia
local completa é conferida antes de remover somente a worktree desta rodada;
a branch publicada é preservada.

**Fim do relatório — PARTIAL: mecanismo de extração e defeito de malha
controlados; critério escalar refutado; sinal canônico conjunto permanece aberto.**
