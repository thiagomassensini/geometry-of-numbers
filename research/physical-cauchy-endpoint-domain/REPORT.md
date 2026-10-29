# Domínio do readout material na fonte Cauchy original

**Classificação: PARTIAL.** Há um transporte algébrico efetivo dos traços
materiais para um núcleo denso do espaço físico original, uma identidade
polarizada exata de bordo e uma obstrução à extensão contínua da leitura
material de Dirichlet na linha crítica. A Gram positiva dos momentos
canônicos completos continua aberta.

Esta etapa segue a PR #77, sem modificar as PRs anteriores ou integrar
automaticamente a PR #41. A branch é
`agent/physical-cauchy-endpoint-domain`, baseada em
`70a8c1f6ecfca3a173195d804789b588bd9f6f66`.
O snapshot de `origin/main` é
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
O operador foi consultado no commit
`bfeb10fd2425400fa38139903d12bf0599f02e53`, preservando os dois arquivos
de pesquisa preexistentes não rastreados. Caminhos, hashes e pins efetivos
estão em `evidence/source-provenance.json`.

## A — O que já estava demonstrado

O carrier efetivamente utilizado é o espaço fechado
`NativeLaguerre.PhysicalCauchySpace`, dentro do `Lp ℂ 2` original. Seus
vetores materiais são as classes das meias densidades

\[
\phi_j(x)=\sqrt{x}\,x^j,\qquad
\langle\phi_i,\phi_j\rangle=\frac1{i+j+2}.
\]

As definições e provas reutilizadas são:

- `completedNativeChiralCauchyContinuousFeature`,
  `completedNativeChiralCauchyFeature` e
  `inner_completedNativeChiralCauchyFeature`, em
  `CompletedNativeRadialChiralMultiplier.lean`.
- `physicalCauchyEmbedding`, `physicalCauchyEmbedding_dense` e
  `physicalCauchyFeature`, em `NativeCauchyLaguerreIsometry.lean`.
- `physicalFiniteSynthesis` e `physicalFiniteSynthesis_injective`, em
  `NativeCauchyLaguerreHeadTail.lean`. A injetividade usa a geometria
  Cauchy auxiliar já provada; não usa positividade da Hankel canônica.
- `physicalEndpointJetInput_finite`,
  `physicalEndpointJetInput_nativeSourceInput` e
  `physicalEndpointJetInput_wholeSource`, em
  `NativePhysicalEndpointEncoder.lean`: os jets do polinômio material
  já alimentavam exatamente a fonte física, com sua fase e passo radial.
- `norm_positiveDirichletValue`, em `CPFormal.Analytic.CpFiniteGreenPositivity`:
  a leitura material é \((j+1)^{-s}\), com norma
  \((j+1)^{-\Re s}\).
- `cauchyLaguerre_originalSource_legs` e
  `cauchyLaguerre_nine_source_crossings`, em
  `NativeCauchyLaguerreSources.lean`: as duas pernas e os canais nativo,
  valor e completion já estavam preservados no carrier original.

A PR #76 identificou o pareamento completado com o kernel canônico
assinado; a PR #77 refutou identificações específicas da norma do estado
inteiro com o primeiro momento. Nenhuma delas entregou uma Gram física
positiva do kernel completo. Esse limite é mantido aqui.

A PR #41 permanece relevante pela separação entre ortogonalização
algébrica, inversibilidade e sinal. Seu head consultado é
`ee56930a2c30456cfbd214a29bb31b12d3977204`, ainda aberto. Esta investigação
não precisa importar seus módulos nem pressupor seus resultados para
construir o domínio material.

## B — O que foi demonstrado agora

### 1. Núcleo material denso e coeficientes únicos

`physical_embedding_injective` prova a injetividade da síntese em todo
suporte finito. `EndpointDomain` é precisamente sua imagem, com a norma
herdada do espaço físico. `coefficientEquiv` recupera os coeficientes
originais, e `endpoint_domain_dense` prova densidade.

Nesse núcleo, para \(f=S(c)\), definimos os traços algébricos legítimos

\[
\tau_a(f)=\sum_j j^{\underline a}c_j,
\qquad
\mathcal D_s(f)=\sum_j c_j(j+1)^{-s}.
\]

São `endpointTrace` e `dirichletTrace`. Eles são definidos somente depois
de provar unicidade dos coeficientes. Nenhuma avaliação de representante
arbitrário de `Lp` é introduzida. Para \(a>0\), o jet é do polinômio
material \(p\), e não da meia densidade \(\sqrt{x}p(x)\).

`native_encoder_trace` demonstra exatamente

\[
\texttt{physicalEndpointJetInput}\ N\ k\ v\ a
=\texttt{endpointGauge}\ k\ a\;
 \tau_a(\texttt{finiteMaterialState}\ N\ v).
\]

O gauge original não foi ajustado: contém a fase e o passo radial
originais. `finite_material_state_coe` identifica o estado com a síntese
física já existente.

### 2. Green de bordo em dois argumentos independentes

A ação `coefficientEuler` é \((Ec)_j=(j+1)c_j\).
`euler_polynomial` prova sua origem literal:

\[
p_{Ec}=p_c+Xp'_c.
\]

Essa ação é o Euler do polinômio material. Não foi identificada com o
clock logarítmico, com profundidade Carry ou com um gerador dos momentos.

Para quaisquer dois vetores do núcleo, `endpoint_green` prova

\[
\boxed{
\overline{\tau_0(f)}\tau_0(g)
=\langle Ef,g\rangle+\langle f,Eg\rangle.
}
\]

A prova mantém os dois argumentos complexos e todos os cruzamentos. Usa
o cancelamento exato
\((i+1+j+1)/(i+j+2)=1\). Portanto, não depende de integração por partes
com um bordo omitido. No modelo diferencial, corresponde à ação
\(Ef=xf'+\tfrac12f\) sobre as meias densidades; o bordo em zero se anula
para os polinômios materiais finitos.

Só após a identidade polarizada, `endpoint_green_energy` e
`endpoint_graph_bound` obtêm

\[
|\tau_0(f)|^2=2\Re\langle f,Ef\rangle
\leq\|f\|^2+\|Ef\|^2.
\]

É uma desigualdade de domínio na métrica original. Não redefine a
métrica física e não identifica essa energia com o saldo quiral canônico.

### 3. As duas pernas e o completion pertencem ao mesmo núcleo

`radial_finite_material` preserva exatamente o fator radial
\(\sqrt{k+1}\), uma única vez. Aqui \(k\) é o índice da regularização
radial; não é profundidade vertical Carry. O endereço material é
\(n=j+1\), distinto da ordem do jet \(a\).

`original_incident_in_domain` e `original_returned_in_domain` provam
pertença das duas pernas originais ao domínio. O quociente quiral
completado permanece literalmente nos coeficientes da perna retornada.
Os teoremas `original_value_in_domain`, `original_companion_in_domain`,
`original_native_companion_in_domain` e
`original_completion_companion_in_domain` conservam os demais canais,
incluindo o termo de derivada do completion. Não se removem Gamma,
denominadores ou contribuições invisíveis.

Esses resultados autorizam aplicar o Green do núcleo aos vetores
originais finitos. Não afirmam que seu bordo seja o kernel canônico.

## C — O que foi refutado

### Avaliação de extremidade contínua no espaço inteiro

`physical_column_norm_sq` e `physical_column_tendsto_zero` dão

\[
\|\phi_j\|^2=\frac1{2j+2}\longrightarrow0,
\qquad \tau_0(\phi_j)=1.
\]

`no_bounded_endpoint_extension` exclui uma extensão linear contínua de
\(\tau_0\) ao fecho físico com essa norma. `endpoint_graph_witness`
registra explicitamente o testemunho sequencial: o gráfico contém uma
sequência convergindo para \((0,1)\). Não se pode tratar essa leitura
como um funcional limitado do `Lp` inteiro.

### Readout nativo de Dirichlet limitado na linha crítica

Defina, apenas como teste de continuidade,
\(u_j=\sqrt{2j+2}\,\phi_j\). `unit_column_norm` prova \(\|u_j\|=1\),
e `unit_column_weak_zero` prova

\[
\forall v\in\mathcal H_{\rm físico},\quad
\langle v,u_j\rangle\longrightarrow0.
\]

A prova passa primeiro por cada coluna, depois por toda combinação
finita, e finalmente pelo fecho usando densidade. O passo é vetorial;
não infere convergência fraca somente de normas diagonais.

Entretanto, para **qualquer parte imaginária** de \(s\), se
\(\Re s=\tfrac12\), `critical_column_readout_norm_sq` prova

\[
\left|\sqrt{2j+2}\,(j+1)^{-s}\right|^2=2.
\]

Toda leitura linear contínua aplicada a \(u_j\) teria de tender a zero,
por `bounded_readout_unit_tendsto_zero`. Logo
`no_bounded_critical_dirichlet_columns` e
`no_bounded_critical_dirichlet_extension` excluem a extensão limitada
que concorde com essa leitura em **todas** as colunas materiais originais.

A normalização \(u_j\) serve só para testar continuidade. Não define
outra fonte, outra sequência de momentos ou outra norma. A fase
\(e^{-i\Im(s)\log(j+1)}\) permanece na expressão original.

**Alcance exato:** o NO-GO é para uma leitura limitada nesse fecho
material inteiro. Não exclui leitura não limitada em domínio próprio,
restrições específicas de fontes, cancelamentos do completion ou outra
realização física legítima. O traço de extremidade também não é a
característica completada: brackets centro–pernas podem ter traço zero
na extremidade e resposta de Dirichlet não nula. Os dois readouts foram
mantidos separados nas definições.

## D — O que permanece aberto

Não se demonstrou
\(h_{i+j}=\langle V_i,V_j\rangle\), nem a identidade deslocada, para
os momentos canônicos completos. Também não se identificou a ação
Euler com sua operação espectral. As provas não usam momentos para
fabricar vetores e não fornecem positividade Hankel all-order.

O novo Green calcula exatamente um bordo do núcleo material. A
passagem desse bordo, dos retornos e dos canais de completion ao
pareamento canônico completado ainda exige igualdade efetiva. A
igualdade entre funções escalares não substitui essa passagem.

A estimativa de gráfico foi provada para \(\tau_0\), e não para
\(\mathcal D_s\). Não se presume continuidade da leitura de Dirichlet
nessa topologia de domínio.

Não há contradição com os certificados finitos H6/K6 ou com a
ortogonalização algébrica da PR #41. A questão atual é a topologia e o
domínio de uma leitura anterior à interpretação positiva, não o sinal
de um pivô já certificado.

## E — Próximo passo mínimo e reprodução

O próximo cálculo concreto é especializar os traços \(\tau_a\) aos
vetores **já existentes** `physicalSourceValue`,
`physicalNativeCompanion`, `physicalCompletionCompanion` e às duas
pernas, em dois argumentos independentes. A pertença ao núcleo agora
está provada. É preciso manter os gauges, denominadores e quociente
de retorno e comparar a identidade polarizada resultante com
`completedIntegralPairing`, identificada na PR #76.

O resultado aceitável desse cálculo é uma igualdade exata ou a fórmula
literal da diferença. Para limites fora do núcleo finito, será preciso
demonstrar controle do domínio das leituras usadas. A hipótese de uma
extensão limitada no fecho inteiro já foi excluída para a leitura crítica
de Dirichlet; não deve reaparecer implicitamente no transporte.

Essa é uma obrigação anterior a procurar o sinal do residual. Mesmo
que ela feche, o Green de bordo positivo acima não autoriza descartar
o saldo assinado e os termos de completion da forma canônica.

Há **46 teoremas novos, 10 definições e 1 abreviação**, distribuídos em
seis módulos Lean. A lista integral de 57 raízes públicas está em
`public-roots.json`. `Audit.lean` executa `#print axioms` e percorre
tipos e corpos transitivos, rejeitando momentos canônicos usados na
construção, certificados finitos de sinal e axiomas além dos três
fundacionais permitidos na camada analítica.

Reprodução no host de pesquisa, na raiz deste diretório:

```bash
python3 record_provenance.py
python3 validate.py
```

O validador compila explicitamente os seis módulos e a auditoria com
`warningAsError=true`; executa `lake build --wfail` dos consumidores
originais e da raiz, as auditorias Foundation/Geometry/Analysis, a
preservação integral da base e `git diff --check`. Registra comandos,
códigos de saída, tempo e memória em `evidence/`. Verifica também os
hashes das fontes originais e dos arquivos de pesquisa preexistentes.

Validação concluída: **15 comandos com saída zero**. A auditoria das 57
raízes percorreu **5.568 dependências** de tipos e corpos, com apenas
`propext`, `Classical.choice` e `Quot.sound`. Nenhuma dependência dos
momentos canônicos ou dos certificados finitos de sinal foi admitida
nessas construções. Os resultados não reivindicam footprint vazio da
camada analítica.

**FIM DO RELATÓRIO — PARTIAL; Gram canônica positiva completa aberta.**
