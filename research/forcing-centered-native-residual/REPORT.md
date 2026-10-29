# Forcing físico centralizado e residual crítico da PR #41

**PARTIAL.** Foi construída uma centralização da fonte que anula exatamente
o canal negativo forcing–forcing da PR #37, conservando os cruzamentos.
O kernel restante foi aplicado aos polinômios exatos da PR #41 e ligado ao
limite físico da PR #53 nos dois setores.

**A estimativa positiva solicitada para todos os pivôs não foi obtida.**
A tentativa de apagar o forcing completo por Bessel encontrou uma obstrução
na própria fonte: o cancelamento do coeficiente negativo deixa uma segunda
perna física não nula, com cruzamento nativo estritamente detectável.
Esse termo precisa continuar na investigação do sinal.

Base: `845829bacd623f044ba779e23da0bb4c48d25c11` da PR #53.
Branch: `agent/forcing-centered-native-residual`.
Host: `ssh llm`, repositório `/home/thlinux/geometry-of-numbers`.
PR #37 consultada no commit imutável
`bf2ff244e363b110a4e54ba897e475b81552bbdb`; PR #41 em
`ee56930a2c30456cfbd214a29bb31b12d3977204`.
Nenhuma delas é presumida integrada à main. Sem merge automático.

## A — O que já estava demonstrado

A PR #37 fornece o forcing original `v(t)=f(t) w`, com
`f = carryMaterialClockForcingScalar` e
`w = carryMaterialClockCentralForcing`. Esse vetor w vem do clock aplicado
ao centro físico e projetado no complemento central. A fonte demonstra
`w≠0` e `f(0)≠0`; eles não são escolhidos pelos momentos.

Denotando por `a = carryMaterialResponseScale = h₀ > 0`, a identidade
`physical_forcing_schur` e a definição do restante dão

\[
\mathcal F(t,u)=-a\langle v(t),v(u)\rangle,
\qquad \mathcal R(t,u)=\mathcal B(t,u)-\mathcal F(t,u),
\]

\[
\mathcal B(t,u)=2a^2tu\,\overline{F(t)}F(u)R_s(t,u).
\]

`F` é `baseTwoCanonicalResponse`; `R_s` é `carryMaterialRealResidual`,
obtido da resposta completada original. `physical_remainder_factor` mantém
os canais central/central, compressed/compressed, os dois cruzamentos
compressed/forcing e o Green oculto pelo readout.

A PR #41 constrói o mesmo polinômio mônico residual Pₙ sem hipótese de sinal
e prova `nativeResidualBoundary_energy`: a energia de bordo exata é 4dₛ,ₙ.
A ortogonalidade usa somente a não anulação dos pivôs anteriores.

A PR #53 identifica as duas sínteses residuais no mesmo frame Cauchy,
sem projetar o retorno, e transporta seu balanço normalizado ao primeiro
Schur canônico. Não prova a contratividade dessas sínteses.

As identidades bivariadas já existentes
`material_residual_jet_even_even`, `material_residual_jet_odd_odd` e as
identidades de paridade foram reutilizadas; não se refez a auditoria da
recorrência ou uma construção de Cholesky.

## B — O que foi demonstrado agora

### 1. Centralização vetorial do forcing, antes da energia

Para uma família finita original `(cᵢ,tᵢ)`, acrescentamos a observação
original no centro, com coeficiente determinado pelo forcing:

\[
\widehat t=(0,t_1,\ldots),\qquad
\widehat c_0=-\frac{\sum_i c_i f(t_i)}{f(0)},\qquad
\widehat c_{i+1}=c_i.
\]

`forcing_vector_centered` prova a identidade VETORIAL

\[
\sum_i\widehat c_i v(\widehat t_i)=0.
\]

`centeredCoefficients_injective` preserva os coeficientes originais como
cauda. Isso não é uma afirmação de independência física de toda família de
estados: é a injetividade explícita desse mapa de coeficientes.

`forcing_kernel_centered` anula o canal forcing–forcing em dois argumentos
independentes. Como a linha central de B é zero, obtém-se a identidade
`remainder_centered_bilinear`:

\[
\boxed{\mathcal R[\widehat c,\widehat d]=\mathcal B[c,d].}
\]

Os demais canais de R não são descartados nem recebem sinal presumido.
Esta é a realização por famílias originais da subtração de Schur da #37.

### 2. Pullback para o kernel original, com todos os fatores

Nos nós regulares `tᵢ≠0` e `F(tᵢ)≠0`, o coeficiente de entrada

\[
c_i=\frac{z_i}{t_i F(t_i)}
\]

apenas inverte os fatores literais da identidade Green já existente.
`physical_pullback_exact` prova, para duas famílias complexas diferentes,

\[
\boxed{\mathcal R[\widehat c,\widehat d]
=2a^2\sum_{i,j}\overline{z_i}R_s(t_i,u_j)\zeta_j.}
\]

Nenhuma amplitude, dressing, fonte ou métrica foi alterada. A igualdade
física com o quociente Green vale no conjunto regular da vizinhança comum
da PR #37. Nas colisões, usamos o coeficiente de extensão já definido pela
fonte; não anunciamos uma nova regularidade vetorial em toda ordem.

### 3. Aplicação exata aos polinômios da PR #41

Definimos somente a observação bilinear dos jets do residual completo:

\[
\mathcal J_s(p,q)=\sum_{i,j}p_iq_j
\,\operatorname{Jet}_{2i+s,2j+s}R_s.
\]

`green_even_bilinear` e `green_odd_bilinear` provam

\[
\mathcal J_0(p,q)=\mathcal L_h(pq)-
\frac{\mathcal L_h(p)\mathcal L_h(q)}{h_0},\qquad
\mathcal J_1(p,q)=\mathcal L_{h_{\bullet+1}}(pq).
\]

Para o mesmo Pₛ,ₙ da #41, `exact_even_green_residual` e
`exact_odd_green_residual` identificam `𝓙ₛ(Pₛ,ₙ,Pₛ,ₙ)=dₛ,ₙ`.
No par exige-se `n>0` e pivôs anteriores não nulos, para remover a linha
central por ortogonalidade; no ímpar essa subtração já é nula por paridade.
O caso par `n=0` foi removido pelo primeiro Schur e não é anunciado como
residual de energia h₀.

`even_green_boundary_energy` e `odd_green_boundary_energy` dão energia
nativa = 4𝓙ₛ. `even_cauchy_green_limit` e `odd_cauchy_green_limit` identificam
o limite da comparação física da #53 com 2𝓙ₛ, nos mesmos coeficientes.

São identidades de formas e readouts completos. Não demonstram uma
isometria entre o carrier material e o Cauchy, nem vetores de Hilbert
definidos a partir dos momentos. Também não foi construído um limite
vetorial material para todas as famílias confluentes críticas. Não foram diferenciados separadamente
todos os canais materiais em ordem arbitrária: a extração de jets ocorre
na expressão completa, cuja regularidade escalar já está provada.

## C — Obstrução encontrada na própria fonte

O par de forcing reduzido original possui duas pernas:

\[
\operatorname{red}_t\mathsf F_t=(v(t),at\,v(t)).
\]

Na família centralizada mais curta, usamos o MESMO coeficiente que anulou
o forcing vetorial no kernel de energia:

\[
\widetilde{\mathsf F}(t)=\operatorname{red}_t\mathsf F_t-
\frac{f(t)}{f(0)}\operatorname{red}_0\mathsf F_0.
\]

`centeredForcingPair_as_synthesis` identifica esse par com a família
centralizada acima. `centeredForcingPair_exact` prova

\[
\boxed{\widetilde{\mathsf F}(t)=(0,at\,v(t)).}
\]

O par é não nulo para t suficientemente pequeno e não zero. Primeiro vem
a identidade vetorial; depois `retained_pair_tangent` conserva o par inteiro:

\[
t^{-1}\widetilde{\mathsf F}(t)\longrightarrow(0,a v(0))\ne0.
\]

Somente então são extraídas as energias e os pareamentos:

\[
\frac{\|\widetilde{\mathsf F}(t)_2\|^2}{t^2}
\longrightarrow a^2\|v(0)\|^2>0,
\]

\[
G(\widetilde{\mathsf F}(t),\widetilde{\mathsf F}(u))=0,
\qquad
\operatorname{Re}\frac{G(\widetilde{\mathsf F}(t),\operatorname{red}_0\mathsf F_0)}{t}
\longrightarrow a\|v(0)\|^2>0.
\]

A última afirmação sobre sinal refere-se à parte REAL do quociente;
`native_cross_positive_near` prova uma margem eventual igual à metade
desse limite. O cruzamento usa um estado original da fonte, sem probe
sintético. Isso não é a margem dos pivôs canônicos de ordens superiores.

`native_isotropic_not_radical` e `no_green_preserving_erasure` refutam
qualquer apagamento linear desse par que pretendesse preservar esse
cruzamento Green nativo. Não é um NO-GO da síntese completa nem do uso de
Bessel conservando todas as parcelas.

Há DOIS objetos distintos: o núcleo do canal negativo de coeficientes é
legitimamente anulado pela síntese de v; o par completo não pertence ao
radical da forma Green no espaço dos pares. A forma Green é a forma
original assinada/antissimétrica, não um produto interno positivo.
Confundir esses dois núcleos apagaria a segunda perna e seus cruzamentos.

## D — O que permanece aberto e validação

Não foi provada, da geometria, a dominância dos canais restantes na direção
crítica. Portanto não foi obtida uma cota positiva sobrevivente ao limite,
nem positividade canônica all-order. As identidades de Schur e de jets
localizam o sinal; não são anunciadas como sua causa positiva.

Há **37 teoremas públicos e sete definições**, em três módulos novos,
auditados em 44 raízes. O inventário e `#print axioms` estão em
`public-roots.json` e `Audit.lean`. O guard percorre tipos e corpos e permite
somente `propext`, `Classical.choice`, `Quot.sound`. Ele rejeita dependência
dos certificados H6/K6/H7, de sinais de seis/sete pivôs e da positividade
geral do defeito do retorno. Os sinais finitos antigos só aparecem na
regressão separada das doze fontes.

`prepare_pr37.py` recupera as fontes imutáveis da #37 em `.cache/`, sem
modificar os arquivos históricos. Um import recebe um alias local; todos
os corpos matemáticos são byte a byte preservados. O manifesto registra os
hashes originais e recuperados. Os caches da #41 já eram fornecidos pela
infraestrutura das PRs anteriores.

`validate.py` executa 18 verificações: recuperação da #37, geração da
auditoria, build de consumidores, seis compilações explícitas com warnings
como erros, teste racional, build focado e raiz com `lake build --wfail`,
auditorias Foundation/Geometry/Analysis, regressão das doze fontes,
preservação do histórico e `git diff --check`.

O controle independente usa `Fraction` nas duas componentes complexas:
oito famílias retangulares, incluindo entradas regulares, e três casos de
perna retida. Os dados são sintéticos e explicitamente separados da fonte
canônica. Nenhum zero, altura, novo momento ou ajuste de parâmetro entra
nas provas nativas.

Fonte, câmera, amplitude, fases, duas pernas, dressing, retorno, correções,
métrica, dependências e pins foram preservados. Arquivos não rastreados do
operador e caches da PR #51 são conferidos por hash. Nenhuma worktree foi
criada ou removida; main local/remota permanece em `59e53d8`.

## E — Próximo passo mínimo

O forcing–forcing pode ser retirado EXATAMENTE como coeficiente negativo,
mas seu estado completo não pode ser apagado. O teste por Bessel precisa
conservar a perna `at v(t)` e seus cruzamentos com o canal comprimido.

O próximo alvo concreto é obter uma identidade polarizada do grupo
compressed/forcing + forcing/compressed − complemento oculto, no mesmo
quociente Green regular e seu prolongamento confluente, após a centralização
provada aqui. Não basta o canal forcing–forcing nulo, nem um bound das
normas de cada canal. Qualquer estimativa deve ser avaliada no polinômio
exato Pₛ,ₙ e manter o resto analítico.

A margem que ainda precisa ser DERIVADA da fonte é, em cada ordem,

\[
\frac{\|A_kx_{s,n}\|^2-\|V_kx_{s,n}\|^2}{d_k}
\ge\varepsilon_{s,n}>0,
\]

onde x é `nativeResidualBoundary`, d é o déficit central da #52, e A/V são
as sínteses residuais da #53. O limite já é 2dₛ,ₙ. Uma hipótese recebendo
essa margem seria circular para o objetivo; positividade eventual sem
margem também não impediria limite zero.

**Conclusão:** a aplicação #37 → #41 → #53 foi demonstrada como identidade
bilinear da mesma fonte. A tentativa de reduzir o problema apagando o
forcing isotrópico foi refutada por um estado e um cruzamento nativos.
A estimativa positiva do balanço completo permanece aberta: `PARTIAL`.

### Reprodução no host preparado

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/forcing-centered-native-residual
python3 research/forcing-centered-native-residual/validate.py
```

O script explicita os caches históricos necessários; não reivindica
bootstrap de um clone sem esses módulos de pesquisa. Nenhum merge automático.
