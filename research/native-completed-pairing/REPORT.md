# Pareamento completado da fonte e kernel canônico em dois argumentos

**Resultado: PARTIAL.** A fonte integral da PR #75 foi transportada até o pareamento completado original, com igualdade vetorial e igualdade dos seis campos do ledger antes do readout. O kernel normalizado extraído dessa fonte recupera exatamente os momentos canônicos em todos os jets mistos, incluindo os três testes solicitados. Isso ainda não é uma realização Gram positiva.

Há também um NO-GO específico, com defeitos exatos: os jets pares da **projeção escalar de bordo normalizada**, tomada isoladamente como família de Gram, produzem `1/2, 0, 0` nos pares `(0,0), (0,1), (1,1)`. Eles não são `h0,h1,h2`. Essa projeção não substitui o estado físico enriquecido completo.

## A — O que já estava demonstrado

### Base e proveniência

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch: `agent/native-completed-pairing`.
- Base: `2b4c3decbaa53c2940acf1fb929c5de37d8c4b11`, branch da PR #75, `agent/tfvd-green-provenance-mellin`.
- A #75 foi conferida aberta, draft, empilhada sobre a #74; nenhuma delas foi presumida integrada à `main`.
- `origin/main`: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Operador consultado: `/home/thlinux/carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Host de execução: `llm`. Só arquivos novos deste diretório de pesquisa foram adicionados.

A PR #41 foi conferida aberta, draft e independente, com base `main` e HEAD `ee56930a2c30456cfbd214a29bb31b12d3977204`. Seus módulos não estão implicitamente importados na branch da #75. Não houve merge ou alteração da #41 para forçar compilação. Sua identidade residual assinada continua sendo um consumidor posterior, não a origem das features.

### Fundação e reconstrução aritmética

`foundational_half_scaling_capstone` foi conferido na fonte atual. Ele mantém hipóteses explícitas de capacidade emergente, mudança no primeiro passo e profundidade positiva. Essa compatibilidade seleciona o expoente formal de metade; não prova por si só positividade Hankel.

O checkout local de `primos` está numa branch antiga e contém trabalho não rastreado/preexistente. Foi mantido somente para leitura. Os arquivos de reconstrução prima nomeados na especificação não existem nesse checkout nem no pin CPFormal usado pelo operador. Suas declarações foram conferidas na fonte oficial de `primos/main`, via GitHub, sem alterar pins:

- `sum_primeVerticalScale_primeFactors_eq_log`, para `n ≠ 0`;
- `primeDepthLogCoordinate_eq_log`, para `n ≠ 0`;
- `nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm`, para `0 < n`;
- `finiteChart_primeDepthWave_eq_dirichlet`, com câmera prima e ímpar explícitas.

Esses resultados são contexto geométrico; não foram introduzidos como novas dependências de compilação desta entrega. `completedNativeCameraUniversality` foi conferido no operador: normalização, jets, momentos e as duas Hankels coincidem entre câmeras admissíveis. Isso não fornece automaticamente isometria dos estados enriquecidos.

### Resultados anteriores efetivamente reutilizados

As #72–#75 já calibraram a porta Green material, as caudas, as quatro pernas, seus cruzamentos e o ledger bruto. Reutilizados:

- `CarryFourLeg.material_edge_trace_eq`, `original_four_legs_mellin`, `material_head_trace_eq`;
- `CarryCameraTail.native_head_from_heat`, `native_tail_from_heat`, `native_completed_trace_from_mellin`;
- `CarryGreenProvenance.full_ledger_mellin`, `green_form_mellin`;
- o completamento original `CarryCameraTail.nativeCompletionTrace`.

O operador já contém **um ledger completado de seis canais** em `CompletedC3FNegFPrimeMixedKernel.lean`, anterior a esta investigação:

`CanonicalCompletedC3FNegFPrimeMixedChannels` e `canonicalCompletedC3FiniteFNegFPrimeMixedChannels`.

Seus campos são Green radial, proveniência Green, cruzamentos off-diagonal, residual de readout em altura, completion de cauda em altura e canal archimediano/câmera. A identidade de readout com `(F,-F')` também já existia. A nova contribuição é sua **calibração integral campo a campo**, com a expansão explícita do mapa sobre as células originais.

Também já existiam a identificação dos momentos por `CompletedNativeTfvdWronskianMoments.lean`, os limites analíticos de diferenças em `CompletedGreenForwardDifferenceLimit.lean` e a polarização assinada em `CompletedC3FullWronskianPolarization.lean`. Nenhuma dessas equivalências condicionais foi tratada como prova incondicional de Gram positiva.

## B — O que foi demonstrado agora

Os nomes novos pertencem ao namespace `CarryCompletedPairing`.

### 1. Completion original sobre os vetores de valor e log-jet

Escreva `s(z)=operatorHeightParameter z`, `C(z)=cpChartFactor 3 s(z)`, `A(z)=nativeXiCompletionFactor z`, e `Aᶜ(z)=nativeXiCompletionBoundaryCompanion z`. O mapa existente é exatamente

\[
T_z(v,\ell)=(a_zv,\ b_zv+d_z\ell),
\]

onde

\[
a_z=\frac{A(z)}{C(z)},\quad
d_z=\frac{iA(z)C(z)}{C(z)^2}=ia_z,\quad
b_z=\frac{A^c(z)}{C(z)}+
\frac{iA(z)\,\operatorname{deriv}(\operatorname{cpChartFactor}\ 3)(s(z))}{C(z)^2}.
\]

`native_completion_matrix` e `jet_gain_height_factor` provam essas identidades, incluindo a convenção total de divisão. As calibrações analíticas seguintes usam os domínios originais, onde os fatores pertinentes são não nulos.

`integral_completion_matrix` mantém também a derivada Gamma: se `G=Gammaℝ(s(z))`, o mapa sobre o par integral bruto `p` é

\[
\left(\frac{a_z}{G}p_1,
  \left(\frac{b_z}{G}+\frac{d_zG'}{G^2}\right)p_1+
  \frac{d_z}{G}p_2\right).
\]

Não se identifica o jet material com uma derivada do normalizador radial dependente da parte imaginária.

`completedIntegralCells` conserva todos os índices `Fin M × Fin 3` e os dois componentes de cada valor/log-jet. Cada entrada é a aplicação do mapa original ao par Mellin da aresta material original. `completed_cells_mellin` prova igualdade da família inteira com `completedNativeCells`, **antes de qualquer soma ou pairing**. `completed_cells_two_inputs` e `completed_cell_pairing` permitem blocos, índices, cutoffs e parâmetros independentes.

Essa família é uma descrição coordenada da fonte, não a declaração de uma nova métrica ou de uma Gram Hankel.

### 2. Defeito exato do pareamento sob a completion

Para `W(p,q)=p₂ conj(q₁)-p₁ conj(q₂)`, provamos:

\[
W(T_zp,T_wq)=d_z\overline{a_w}\,W(p,q)+D_J+D_A,
\]

\[
D_J=(d_z\overline{a_w}-a_z\overline{d_w})p_1\overline{q_2}
=2i a_z\overline{a_w}p_1\overline{q_2},
\]

\[
D_A=(b_z\overline{a_w}-a_z\overline{b_w})p_1\overline{q_1}.
\]

Os dois termos permanecem em campos separados de `CompletionPairingChannels`, antes de `.total`. Os teoremas são `native_completion_pairing` e `completion_jet_transport_exact`.

Equivalentemente, `native_completion_pairing_expanded` mostra o efeito da coordenada de altura:

\[
W(T_zp,T_wq)=ia_z\overline{a_w}
 (p_2\overline{q_1}+p_1\overline{q_2})+D_A.
\]

Portanto, não basta multiplicar a forma antissimétrica bruta por um fator escalar. O companion e a troca para a combinação simétrica têm proveniência determinada pelo mapa original.

### 3. Cabeça, caudas e seis canais completados

`integralMaterialTrace` sintetiza cabeça e cauda da mesma fonte. `integral_material_trace_eq` identifica simultaneamente seus dois campos armazenados; `completed_trace_mellin` identifica o vetor completado com `canonicalC3BracketTfvdCompletedTracePair`.

Só depois desse transporte é definido `completedIntegralPairing`. Os teoremas `completed_pairing_mellin` e `completed_pairing_eq_original` provam sua igualdade com o Wronskiano completado original em dois argumentos independentes. O segundo admite cutoffs independentes `M,N`.

`integralCompletedChannels` reutiliza o **tipo de seis campos já existente**. Cada campo tem sua expressão integral própria; nenhum é definido como um Wronskiano menos os demais. `completed_channels_mellin` prova igualdade do registro completo com `canonicalCompletedC3FiniteFNegFPrimeMixedChannels` antes de `finalReadout`.

O domínio desta identificação é

\[
0<\Re s(z)<1,\qquad 0<\Re s(w)<1.
\]

O intervalo superior vem das portas refletidas e dos quocientes de câmera originais. Na reta real de alturas, `Re s=1/2` e essa condição é automática. Nenhuma hipótese sobre zeros ou sinais de Hankel entra na calibração.

`completed_channels_pairing` obtém a identidade do pareamento após o readout completo e a remoção do peso de câmera comprovadamente não nulo. A compensation dormente e os cruzamentos da #75 permanecem no campo de proveniência; não foram apagados por sua anulação especial na linha crítica.

### 4. O kernel de momentos correto e seus jets

`mellinResponse` usa o readout centrado/normalizado original do Wronskiano completado da fonte integral. Não é definido pela sequência `h`.

`mellin_response_on_domain` identifica essa resposta com

\[
R(z)=-\frac{F'(z)}{2F(z)}.
\]

`mellin_response_eventuallyEq` e `mellin_response_analyticAt` identificam seu germe analítico no centro. `mellinMomentKernel M x y` é a diferença dividida total `dslope (mellinResponse M) x y`. Na colisão, ela usa a derivada; não a divisão total `0/0`.

`moment_kernel_from_completed_pairing` prova, para alturas reais distintas e `F(x),F(y)≠0`, a relação efetiva em dois argumentos:

\[
K_M(x,y)=
\frac{\operatorname{completedIntegralPairing}_{M,M}(y,x)}
 {2F(y)\overline{F(x)}(y-x)}.
\]

Para parâmetros complexos, o pareamento anterior é sesquilinear e mantém a conjugação de um argumento. O `dslope` usado para extrair coeficientes é a versão holomorfa em dois endpoints. As diferenças finitas são amostradas na reta real, onde as convenções coincidem. Não foi postulado um kernel Gram complexo.

`mellin_mixed_jets` aplica o teorema analítico existente de diferenças mistas à **resposta construída da fonte**, identificando o limite com `polarizedGreenMomentCoefficient` da sequência canônica concreta. Não recebe `HasCompletedNativeRealAxisNormalizedGreenKernel` como hipótese.

Os resultados em toda ordem são:

- `mellin_even_jets`: ordens derivativas `(2i,2j)` recuperam `h_(i+j)`;
- `mellin_shifted_jets`: `(2i+1,2j+1)` recuperam `h_(i+j+1)`;
- `mellin_even_odd_jets_zero`: `(2i,2j+1)` recuperam zero.

Os três testes solicitados são as especializações compiladas `mellin_jet_00`, `mellin_jet_01`, `mellin_jet_11`. Os índices `(0,0),(0,1),(1,1)` do setor par correspondem às ordens de derivada `(0,0),(0,2),(2,2)` e recuperam exatamente `h0,h1,h2`.

São limites analíticos de diferenças mistas de uma função efetiva, não aproximações numéricas nem coeficientes declarados iguais por definição. A generalização usa o teorema anterior da resposta nativa; não reivindicamos ter redemonstrado essa recorrência.

### 5. Fatoração tentada na energia original

`integral_pairing_full_operator` transporta o mesmo pareamento até o operador completado original, na métrica existente. `integral_pairing_chiral_difference` obtém a fatoração **assinada**:

\[
\frac{W_{\mathrm{integral}}(z,w)}{2F(z)\overline{F(w)}}
=i\bigl(K_+(w,z)-K_-(w,z)\bigr).
\]

`K_+` e `K_-` são os kernels dos dois estados quirais já existentes, ambos Grams positivas no carrier original. `mellin_response_signed_germ` identifica o mesmo germe com o balanço quiral centrado original.

Essa identidade não permite suprimir `K_-`, nem transforma a diferença dividida do balanço em uma Gram positiva. Nenhuma desigualdade universal entre as contribuições foi demonstrada nesta entrega.

## C — O que foi refutado, com defeitos exatos

### Completion não é simples covariância escalar

`completion_basis_defect` calcula o defeito do mapa nos probes de valor/log-jet `p=(1,0)` e `q=(0,1)`:

\[
W(T_zp,T_wq)-d_z\overline{a_w}W(p,q)
=2ia_z\overline{a_w}.
\]

`completion_basis_defect_ne_zero` prova que ele é não nulo no domínio original. Esses probes testam o mapa linear; não foram anunciados como estados completos da fonte. O resultado exclui a lei de covariância simples nesse espaço de dados, não a geometria Carry.

### Projeção escalar de bordo não é a família Gram procurada

Só após a reconstrução completa foi testado o atalho de usar o traço escalar `(Psi,F)` isolado no seu carrier **preexistente** `CompletedScalarBoundaryTraceCarrier`, com a normalização original `1/(sqrt(2) F)`.

`normalized_scalar_trace_germ` prova que seus componentes são

\[
\left(\sqrt2\,R(z),\frac1{\sqrt2}\right).
\]

Como `R` é ímpar, `projected_even_jet_exact` determina todos os jets pares: o zeroth é `(0,1/sqrt(2))`, e os demais são zero. Na métrica original desse carrier, a Gram dos três pares testados é

\[
\left(\frac12,0,0\right).
\]

`projected_gram_three_defects` dá a contraexpressão exata:

\[
\left(\frac12-h_0,-h_1,-h_2\right).
\]

`LowOrderControls.lean` reaproveita **somente como regressões separadas** os fatos anteriores `h0<1/16` e `h1≠0`. Assim, os dois primeiros defeitos são formalmente não nulos. `not_projected_even_gram_representation` refuta essa realização específica.

Não se afirma um novo sinal de `h2` nessa prova. O terceiro defeito é identificado exatamente como `-h2`. O teste não descarta informação do estado completo durante sua construção e não exclui uma realização pelo carrier físico enriquecido.

### Sobreposição C2–C3

As duas utilizações da aresta intermediária da #74 continuam separadas como papéis de bordo. `height_readout_defect` e `integral_height_readout_defect` calculam exatamente a alteração do residual ao rotacionar os dois log-jets alvo, mantendo as pernas e os cruzamentos fixos:

\[
R_I-R=(i-1)b\overline c+(i+1)a\overline d.
\]

Portanto, não é lícito multiplicar apenas o residual bruto por `i` ou apagar um papel compartilhado.

O piloto da #74 continua dando, após o passo C2, `(g2,g3)` e `(g4,g5)`, em vez das células com aresta intermediária compartilhada `(g0,g1)` e `(g1,g2)`. Seu contraexemplo numérico exato em `s=1` é **anterior ao quociente de câmera**: `C=0` ali. Não foi transportado indevidamente para o domínio completado.

`completion_preserves_value_distinction` prova que, dentro do domínio genuíno, a completion preserva distinções já demonstradas nas coordenadas de valor, pois `a_z≠0`. Isso não constrói uma costura C2–C3 global. Tal costura, com novos papéis e caudas, permanece aberta.

## D — O que permanece aberto e o que foi auditado

A identificação integral do pareamento completado e dos coeficientes canônicos foi fechada. A identidade positiva

\[
h_{i+j}=\langle V_i,V_j\rangle
\]

para **uma única família física enriquecida original**, e sua versão deslocada, continuam abertas. Nenhuma feature nova foi construída por momentos, Cholesky, zeros, alturas, `PosDef` ou uma métrica escolhida para ajustar a resposta.

O limite de diferenças mistas do kernel escalar não é, por si só, uma construção de vetores-limite. Para aplicar o teorema Gram → Hankel positiva, ainda seria preciso identificar esse kernel como o produto interno da síntese física completa, ou provar uma desigualdade independente que controle sua parte assinada. A existência de `K_+` e `K_-` separadamente positivos não resolve isso.

`MomentGramPositivity`, whitening, Jacobi e os módulos de #41 não foram importados como fornecedores de positividade. Permanecem consumidores posteriores. As únicas desigualdades theta usadas estão isoladas nos controles finitos de uma realização refutada.

### Reprodução e confiança

```bash
cd research/native-completed-pairing
python3 validate.py
python3 record_provenance.py
```

O validador compila explicitamente o stack de pesquisa e todos os módulos novos, executa builds focados, `lake build --wfail`, auditorias Foundation/Geometry/Analysis e verificações de preservação. Pesquisa não importada pelo build raiz é compilada separadamente.

`Audit.lean` usa `#print axioms` e o fecho transitivo de tipos e corpos em três grupos: construção da fonte/features, identificação de momentos, controles finitos. O primeiro proíbe a definição canônica de momentos; os dois primeiros proíbem os certificados de sinal finitos e os polinômios de momentos theta. Os canários ficam separados. Um quarto passe audita o fecho total, sem somar indevidamente os números dos três grupos.

Os axiomas permitidos em Analysis são somente `propext`, `Classical.choice`, `Quot.sound`; as políticas mais restritas de Foundation e Geometry são verificadas por seus próprios scripts. Não foram adicionados escapes de confiança ou axiomas matemáticos.

Os comandos, contagens finais, hashes e logs executados estão em `evidence/validation.json`. O relatório não apresenta validação local como sucesso de CI externo. O objetivo completo e o estado de cada requisito estão em `GOAL_AUDIT.md`.

A auditoria executada encontrou **71 raízes públicas e 6.352 dependências transitivas na união total**. Os grupos separados têm 47 raízes de fonte/features, 21 de identificação e 3 de canários. Há 49 teoremas novos, 18 definições e uma estrutura de dois campos; as raízes incluem também seu construtor e projeções. Os números de dependências dos grupos se sobrepõem e não são somados.

## E — Próximo passo mínimo

A próxima obrigação não é recalcular momentos nem repetir o transporte do Wronskiano. O alvo preciso é construir, na síntese física enriquecida original, o mapa que realiza a **diferença dividida do balanço quiral completo** como um pareamento positivo, mantendo o termo negativo e todos os termos de completion até uma identidade que os controle efetivamente.

O primeiro teste deve permanecer polarizado: comparar `(0,0)` e `(0,1)` antes de qualquer eliminação de coordenadas. O carrier de teste não pode ser apenas o traço escalar normalizado, pois a contraexpressão acima já o exclui. Se for usado o estado enriquecido C2–C3, primeiro é necessário explicitar a costura das arestas que deixam de compartilhar o mesmo endereço após o passo, com seus dois dados de bordo e caudas.

Uma alternativa é provar diretamente uma estimativa da fonte para a energia **assinada** do bordo residual. A PR #41 então transportaria o sinal ao pivô, após integração de dependências explícita. Nem a hipótese de Gram nem a positividade do próprio pivô podem ser recebidas como premissa dessa estimativa.

**Conclusão:** aceitação parcial A fechada; kernel escalar canônico identificado em toda ordem; atalho da projeção escalar refutado com defeitos exatos. A Gram física positiva all-order permanece aberta. Resultado PARTIAL, sem merge automático.

Fim do relatório.
