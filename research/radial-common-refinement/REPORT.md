# Refinamento radial isométrico: fonte completada, kernel e jets conjuntos

**Resultado: PASS_STRUCTURAL para o transporte radial; PARTIAL para a Gram positiva canônica.**
24/10/2026. `thiagomassensini/geometry-of-numbers`.
Branch `agent/radial-common-refinement`, baseada na PR #80, commit
`0618317827981136657cb1b5bb728a8e93cea50d`.
Nenhum merge automático. `origin/main` verificado:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

Construímos uma isometria no **carrier Cauchy físico já existente**, a partir
da mudança de potência na coordenada do intervalo. Ela transporta cada grade
radial para um refinamento comum, conserva os dois canais e remove por
identidade vetorial o fator misto da PR #80. Depois desse transporte, o
pareamento assinado coincide exatamente com o kernel canônico de dois
argumentos. Seus jets conjuntos recuperam os momentos canônicos em toda ordem.

A forma continua assinada. Não foi demonstrada uma Gram Hilbert positiva
all-order, nem uma isometria de todo o estado material multibase para esse
carrier. Essas distinções são parte do resultado.

## A — O que já estava demonstrado e foi reutilizado

- `completedNativeChiralCauchyFeature`: meia densidade original
  `φ_j(x)=√x x^j`, em `Lp ℂ 2 volume` do intervalo unitário.
- `inner_completedNativeChiralCauchyFeature`:
  `〈φ_i,φ_j〉=1/(i+j+2)`, com a métrica original.
- `NativeLaguerre.physicalCauchyEmbedding`, sua densidade e
  `PhysicalCauchySpace`: fecho desse span no **mesmo** carrier físico.
- `CarryPhysicalTrace.EndpointDomain`, `coefficientEquiv`, `endpointTrace`,
  `dirichletTrace`, `eulerAction`, `physical_euler_green`, da PR #78.
  O domínio algébrico não é a coleção de todos os representantes de Lp.
- `canonicalCompletedNativeRadialProjectiveChiralState`,
  `projectiveChiralDifferenceJet`, forma chiral assinada e amplitude
  completada originais. Nenhuma dessas definições foi modificada.
- `GammaMaterialSewing.nativeCoupledCompletion_originalSource_legs`:
  decomposição vetorial do companion em nativo mais completion, com
  incidência/retorno `C ± iV`.
- PR #79, `native_kernel_cross_factor`: fator exato do cruzamento entre
  duas grades originais, antes de qualquer colagem.
- PR #80: impossibilidade de inferir um limite conjunto bruto a partir das
  diagonais; diferença física com balanço assinado negativo eventualmente.
- `completedNativePolarizedDslope_shiftedRadial_tendsto`: limite analítico
  de duas diferenças finitas independentes do kernel nativo.
- `physicalCauchy_head_tail_inner`: identidade exata de cabeça **mais** cauda.
- PR #41, ainda draft independente, head
  `ee56930a2c30456cfbd214a29bb31b12d3977204`: energia residual original igual
  a quatro vezes o pivô de Schur, uma identidade assinada. Não foi importada
  como se estivesse integrada à branch atual.

A nota `NOTA_CARRY_CENTRO_PERNAS_MOMENTOS_KERNEL_2026-10-23.md` foi lida
integralmente como contexto de investigação. SHA-256 e delimitação de uso
estão em `evidence/user-note.json`. Suas propostas não foram tratadas como
teoremas Lean já existentes nem como instruções que substituíssem o objetivo.

## B — O que foi demonstrado agora

Todos os novos nomes estão em `CarryRadialRefinement`.

### B.1 — Uma mudança de coordenadas literal, anterior aos momentos

Para um inteiro `θ=m+1≥1`, a mudança `x↦x^θ` tem Jacobiano
`θ x^(θ−1)`. A meia densidade transforma-se por:

\[
U_\theta f(x)=\sqrt{\theta x^{\theta-1}}\,f(x^\theta).
\]

No código, `powerIsometry m` representa `U_(m+1)`.
`power_column_function` prova essa fórmula **nas colunas físicas originais**:

\[
\boxed{U_\theta\varphi_j
 =\sqrt\theta\,\varphi_{\theta(j+1)-1}.}
\]

O endereço é `refinedAddress m j=(m+1)j+m`. O fator de raiz é o Jacobiano,
não uma amplitude escolhida a partir de `hₙ`. A fórmula vale inclusive no
bordo `x=0`, com as potências naturais indicadas.

`power_column_inner` e `power_synthesis_inner` demonstram, para dois
suportes finitos independentes, a conservação de **todos os cruzamentos**.
`power_extension_norm` estende a norma preservada por densidade ao fecho
físico original. Daí `powerIsometry : PhysicalCauchySpace →ₗᵢ[ℂ]
PhysicalCauchySpace` e `power_isometry_inner`.

Não foi definida outra métrica nem outro espaço de estados. A construção
não recebe momentos, Hankel, alturas, zeros ou positividade canônica.
Surjetividade/unitariedade não foi presumida nem demonstrada.

### B.2 — Refinamento da grade com o mesmo parâmetro espectral

Se `κ=k+1`, a amostra original é `z_(k,j)=i(j+1)/κ`. Aplicamos:

\[
\kappa\mapsto\theta\kappa,\qquad j+1\mapsto\theta(j+1).
\]

`refined_point` prova que `z` fica **exatamente igual**.
`power_isometry_radial` prova que a imagem do vetor radial é a coluna
original da grade refinada, com sua amplitude original `√(θκ)`.
As funções completadas `F`, `−F′`, amplitude chiral e retorno são avaliadas
no mesmo ponto. Não há ajuste de seus valores.

`pair_power_refines_projective` transporta **os dois canais simultaneamente**:

\[
(U_\theta I_{k,j},U_\theta R_{k,j})
 =(I_{\theta\kappa-1,\,\theta(j+1)-1},
   R_{\theta\kappa-1,\,\theta(j+1)-1}).
\]

Para duas grades `κ,λ`, o refinamento comum tem massa radial `κλ`:
na primeira aplica-se `U_λ`, na segunda `U_κ`. Os endereços antigos são
conservados por uma inclusão injetiva com espaçamento explícito; não se
apagam direções dentro de uma representação.

`power_composition` prova `U_θ U_η=U_(θη)` no fecho inteiro, e
`power_identity` prova `U₁=I`. `further_refinement_pairing` conserva os
pareamentos após mais um refinamento comum.

`equal_radial_point_common_states` prova que duas representações do mesmo
**nó radial** têm os mesmos estados quirais completos depois do refinamento.
Isso não identifica estados materiais/câmeras apenas por igualdade de um
readout escalar. O nó radial e o estado completo de uma câmera são objetos
diferentes.

### B.3 — Domínio, bordo e fase material não foram ignorados

`powerCore` é a restrição ao `EndpointDomain`. `power_core_coe` prova que
ela é a mesma isometria, não outro mapa definido pelo resultado desejado.
O domínio finito é preservado.

`coefficient_euler_power` e `euler_power_core` dão:

\[
E U_\theta=\theta U_\theta E.
\]

Aqui `E` é a ação Euler `p+Xp′` já existente no domínio, **não** o clock
material logarítmico e **não** um gerador identificado dos momentos.
`endpoint_power_coefficient` mantém a lei de bordo:

\[
\tau_0(U_\theta f)=\sqrt\theta\,\tau_0(f).
\]

A leitura Dirichlet material separada tem uma covariância distinta,
provada em `dirichlet_power_coefficient`:

\[
\mathcal D_s(U_\theta f)
 =\sqrt\theta\,\theta^{-s}\mathcal D_s(f).
\]

O fator complexo foi preservado. `critical_dirichlet_factor_norm_sq`
prova que seu módulo quadrático vale 1 quando `Re(s)=1/2`.
Isso não elimina sua fase nem prova invariância da característica
completada sob uma dilatação aritmética. Também não identifica refinamento
radial com mudança de câmera ou profundidade vertical Carry.

### B.4 — Completamento e cabeça/cauda antes do pareamento

`originalFields` empacota os seis campos preexistentes: valor, companion,
companion nativo, completion, incidência e retorno.
`six_fields_common_isometry` conserva seus 36 cruzamentos ordenados sob
um refinamento comum, com coeficientes, radii e dimensões independentes.

`original_source_legs_refined` transporta primeiro as identidades vetoriais
`C=N+Γ`, `I=N+Γ+iV`, `R=N+Γ−iV`.
`refined_complete_balance` só depois contrai os vetores e obtém os quatro
cruzamentos Green/completion, com refinamentos independentes nos argumentos:

\[
\langle U I,U' I'\rangle-\langle U R,U' R'\rangle
=-2i\{\langle U V,U' N'\rangle+\langle U V,U'\Gamma'\rangle
      -\langle U N,U' V'\rangle-\langle U\Gamma,U' V'\rangle\}.
\]

Não se substitui esse balanço por uma soma de normas positivas.
`refined_head_tail` mantém a decomposição exata de cada cruzamento em
cabeça e cauda, inclusive depois de refinamentos diferentes. Nenhuma cauda
foi descartada ou declarada pequena sem estimativa.

### B.5 — Kernel canônico exato em duas entradas independentes

`commonPairing` é definido pelos vetores transportados, usando a **mesma
forma assinada** nativa com seu fator `1/2`. Não é definido dividindo um
kernel por `ρ`.

`common_radial_gram` demonstra diretamente:

\[
\langle U_\lambda u_{k,i},U_\kappa u_{\ell,j}\rangle
=\frac{i}{z_{\ell,j}-\overline{z_{k,i}}}.
\]

`common_pairing_same_grade` identifica o resultado com uma amostragem
esparsa da fonte original numa única grade comum. Sob as condições nativas
explícitas de regularidade — strip e não anulação dos denominadores nos
pontos envolvidos — `common_pairing_kernel` prova:

\[
\boxed{\frac12\{\langle U_\lambda I_{k,i},U_\kappa I_{\ell,j}\rangle
 -\langle U_\lambda R_{k,i},U_\kappa R_{\ell,j}\rangle\}
 =K(z_{k,i},z_{\ell,j}).}
\]

`K` é exatamente `canonicalCompletedNativePolarizedDslopeKernel`.
O fator misto da PR #80 desaparece por um transporte vetorial isométrico,
não por uma nova métrica ou por normalização dos momentos.

### B.6 — Todos os jets, com limite realmente conjunto

`physical_jet_original` prova a igualdade vetorial com
`projectiveChiralDifferenceJet`, conservando os pesos de diferenças finitas,
fatoriais e fases já presentes na definição original.
`common_jet_pairing_weighted` mantém cada cruzamento ordenado dos dois
stencils. `common_jet_pairing_dslope` identifica a expressão completa com
a diferença dividida nativa, agora com **dois índices radiais independentes**.
A regularidade é descarregada eventualmente em ambos os índices pelo germe
original, sem hipótese global de sinal.

`common_jet_pairing_tendsto`, `common_even_jets`, `common_odd_jets` e
`common_even_odd_jets` demonstram, para todas as ordens:

\[
\begin{aligned}
\widetilde Q_{k\ell}(2i,2j)&\to h_{i+j},\\
\widetilde Q_{k\ell}(2i+1,2j+1)&\to h_{i+j+1},\\
\widetilde Q_{k\ell}(2i,2j+1)&\to0,
\end{aligned}
\qquad (k,\ell)\to\infty.
\]

São coeficientes normalizados. Os testes `h₀`, `h₁`, `h₂` correspondem
respectivamente aos pares de ordens `(0,0)`, `(0,2)`, `(2,2)`; o par bruto
`(0,1)` tem limite zero. A identificação não usa sinais H6/K6.

### B.7 — Como a nota centro–pernas ajudou

A nota separa corretamente a identidade universal
`P_(n+1)=xy P_n+x^(2n+2)+y^(2n+2)` da conjectura de sua origem material.
A soma geométrica finita dá a telescopagem `(x−y)P_n=x^(2n+1)−y^(2n+1)`;
o reagrupamento dos graus dá o centro e os pares refletidos. São identidades
algébricas válidas, incluindo a colisão `x=y`.

Também é correta a ressalva da própria nota: o quadrado ponto a ponto em
`(xy)^(n−r)(x^r−y^r)^2` não torna `P_n` um kernel Gram positivo.
Seu contraexemplo `P₁` nos pontos `0,1`, com determinante `−1`, permanece.

O avanço formal desta PR ocorre antes da extração dos coeficientes: uma
mudança de coordenadas física demonstrada e um pareamento independente de
duas grades. Isso fornece uma parte concreta do diagrama proposto pela
nota. Não prova que o centro dos graus seja o centro posicional de uma
câmera, nem que o acréscimo de uma capacidade Carry seja literalmente o
incremento de `P_n`. As seis propostas algébricas da nota não foram
contabilizadas como novas provas Lean desta entrega.

## C — O que foi refutado ou corrigido

A PR #80 continua válida: os estados **não transportados** têm cruzamentos
brutos com fator `ρ`, limites dependentes do caminho e uma forma assinada
negativa em certas diferenças. Uma única isometria aplicada a todos eles
preservaria esse defeito.

Esta PR usa isometrias **diferentes em cada representação**, derivadas da
mesma mudança de potência e coerentes por composição. Os novos cruzamentos
entre representações são calculados, não declarados iguais aos brutos.
Portanto, não há contradição com a PR #80 nem apagamento de um defeito.

Ficam rejeitadas as interpretações:

- igualdade de duas diagonais implica colagem dos estados;
- dividir um kernel por `ρ` já constrói um transporte físico;
- o novo pareamento assinado é automaticamente uma norma positiva;
- uma fase Dirichlet de módulo 1 pode ser apagada antes da síntese;
- um centro de graus polinomiais já é um centro material Carry.

## D — O que permanece aberto

A forma canônica foi realizada por um balanço **assinado** coerente de
estados físicos existentes, não por uma única norma positiva. Não foi
provado que o retorno completado seja contractivo em todos os prefixos.
Não foram construídos vetores Hilbert cujas Grams positivas sejam as duas
Hankel canônicas em toda ordem. Os limites provados são de pareamentos
assinados; não foi demonstrada convergência forte dos vetores-jets nem
independência linear de uma família infinita de vetores-limite.

Também continua faltando a identificação isométrica do **estado material
multibase integral** com esse carrier radial, incluindo sua lei dinâmica de
TFVD/Green. A covariância Dirichlet explicitada acima precisa fazer parte de
qualquer tentativa desse transporte; não pode ser confundida com invariância
literal do readout. As grades radiais não foram identificadas com câmeras.

O sinal da forma residual da PR #41 continua uma obrigação específica da
fonte. Reformular esse sinal como contractividade ou positividade Pick não
o demonstra. Os certificados finitos H6/K6 não foram extrapolados.

## E — Próximo passo mínimo, validação e reprodução

A próxima obrigação operacional concreta é provar no domínio original o
intertwiner do avanço/Green com a mudança de potência. Para o multiplicador
nativo `M_x=physicalRadialAdvance`, o primeiro teste é:

\[
U_\theta M_x=M_x^\theta U_\theta,
\qquad
U_\theta(I-\eta M_x)^{-1}
 =(I-\eta M_x^\theta)^{-1}U_\theta.
\]

Aqui `η` é o peso geométrico do Green, distinto do quociente chiral `q`.
Esse é um enunciado de operadores preexistentes e suas potências, anterior
aos momentos; não é um predicado equivalente à positividade desejada.
Deve preservar os bordos e o fator material Dirichlet já calculado.
Depois é necessário comparar seu readout completado com `−F′/(2F)`,
conservando `N`, `Γ` e os quatro cruzamentos exibidos em B.4. Não se deve
identificar esse resolvente com os momentos por simples semelhança formal.

Esses intertwiners de Green não foram demonstrados nesta PR. Mesmo sua
prova não autorizaria anunciar positividade sem a identificação específica
do readout e o controle do sinal do retorno/complemento original.

**Certificação desta etapa:** 51 teoremas, 17 definições e uma abreviação,
em sete módulos. 69 raízes públicas auditadas por `#print axioms` e
inspeção transitiva de tipos **e corpos**, totalizando 6.238 dependências.
65 raízes de construção/transporte não dependem da sequência de momentos;
quatro raízes posteriores identificam os coeficientes, sem sinais finitos.
Somente `propext`, `Classical.choice`, `Quot.sound` são permitidos.

Validação: 17 comandos com saída zero, incluindo os sete módulos e o audit,
build de fontes usadas no operador, `lake build --wfail` na raiz e auditorias
Foundation/Geometry/Analysis. Oito módulos ancestrais foram recompilados de
fontes idênticas ao commit base. Não foram adicionados `sorry`, `admit`,
`native_decide` ou axiomas. Fontes históricas, pins e arquivos preexistentes
foram preservados.

Reprodução no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

Comandos, códigos de saída, logs e hashes constam de `evidence/`.
O objetivo completo permanece ativo em `GOAL_STATUS.md`.

**FIM DO RELATÓRIO — transporte radial e jets conjuntos provados; Gram positiva canônica all-order aberta.**
