# Somação por partes do Green completo e jets do retorno nativo

**PARTIAL.** A somação por partes foi demonstrada nos dois argumentos do
Green material original, incluindo dressing e a redução da fonte. O mesmo
fluxo e o mesmo interior aparecem no complemento oculto e se cancelam
exatamente em cada cutoff. O balanço canônico continua no bordo/retorno
global, com os três cruzamentos de cauda explicitamente conservados.

Foi também demonstrada a extração dos jets dos DOIS retornos pela soma
absolutamente convergente das células originais em toda ordem fixa. Há
identidade exata de prefixo+cauda, cota pela cauda absoluta e convergência
dessa cota a zero. **Não há taxa quantitativa nova, margem positiva nova
nem prova de positividade canônica all-order.**

Base imutável: `9f1bf62c55b04dadc79e4f7438eab48d5ac7e558`, PR #57.
Branch: `agent/material-green-summation-parts`.
Host: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
PR empilhada sobre a #57; sem merge automático. Main local/remota na abertura:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Nenhuma worktree foi criada ou removida. Resíduos alheios, módulos históricos,
fontes, domínios, métricas, pesos, amplitudes, fases, pins e PRs anteriores
foram preservados. O repositório do operador permanece sem modificações.

## A — O que já estava demonstrado

- A #57 conservou o estado material completo pelo TFVD e demonstrou
  `tfvd_whole_factor` e `tfvd_native_residual_regular`, com os fatores literais
  da resposta e o complemento oculto. A separação vertical é oblíqua; o
  negativo do bracket ponderado não é positivo em toda direção.
- A forma `carryMaterialPairGreen`, a redução
  `carryMaterialPairReduction_green` e o ledger
  `carryMaterialForcingRemainder_ledger` já conservavam forcing, comprimido,
  central, ambos os cruzamentos e complemento oculto.
- `carryMaterialPairGreen_readout_ledger` já implicava a representação do
  balanço pelo readout do bordo. `carryValveReducedReturnBalance_physical`
  já a identificava com o retorno global original. **Essa igualdade global
  não é apresentada aqui como descoberta nova.** O que se explicita agora
  é o cancelamento de fluxo/interior/cauda material em cada cutoff, sua
  aplicação aos slots nativos e a extração forte dos jets de células.
- O gradiente original já tinha continuação complexa local em ℓᵖ para p≥1,
  e o retorno já era um readout limitado de ℓ¹. Reutilizam-se
  `baseTwoComplexMaterialGradientLp_differentiableOn_ball`,
  `baseTwoComplexMaterialGradientLp_ofReal` e
  `baseTwoCompletedUndressedReadout`, sem estender a soma de células a ℓ².
- A #41 construiu os polinômios residuais mônicos Pₛ,ₙ sem receber o sinal
  do próximo pivô. A ligação efetiva com o mesmo residual é
  `exact_even_green_residual` (n>0 e pivôs anteriores não nulos),
  `exact_odd_green_residual` e `nativeResidualBoundary_energy`.

Notação: a=h₀ é a escala original, Y o estado completo, D seu dressing,
F a resposta completada, β o retorno global ordinário e κ o retorno com
log material. O parâmetro real t não é profundidade nem cutoff. N é cutoff
de observação do INTERIOR material; M,L são cutoffs de CÉLULAS do retorno.

## B — O que foi demonstrado agora

### 1. Somação por partes polarizada no índice material

`DiscreteParts.lean` reutiliza `DiscreteValve.fdiff` e `bracket`, avaliados
em sequências explicitamente deslocadas dos valores materiais. A identidade
`polarized_summation_parts`, para quaisquer f,g:ℕ→ℂ e N, é

\[
\sum_{n<N}\overline{\Delta f_n}\Delta g_n
=\overline{f_N}\Delta g_N-\overline{f_0}\Delta g_0
 -\sum_{n<N}\overline{f_{n+1}}\Delta^2g_n.
\]

O fluxo usa Δg_N e o último bracket também usa esse valor; o termo de
fronteira está exatamente compensado. O caso N=0 também está provado.

`ordinarySamples(t,n)` é `criticalMaterialSample(t,n+1)`, com a amplitude
material e fase −t log(n+1) originais. `clockSamples` multiplica pelo log material original.
`ordinary_difference` e `clock_difference` identificam suas diferenças com
os dois gradientes já construídos; `ordinary_clock_parts` e
`clock_ordinary_parts` conservam separadamente as duas orientações.

A identidade é FINITA e não pressupõe que a onda material crítica pertença
a ℓ². Somente seus gradientes entram nos carriers normados existentes.
Usar o mesmo stencil não identifica endereço material com profundidade
vertical; não se transporta a conclusão da #57 entre esses eixos.

### 2. Decomposição completa e cancelamento em cada cutoff

`FullGreenParts.lean` fornece, para pares complexos independentes X,Y,

\[
G(X,Y)=G_\partial(X,Y)+\sum_{n<N}I_n(X,Y)
                   +\sum_{k\ge0}I_{k+N}(X,Y).
\]

Aqui I_n contém AMBAS as orientações do pareamento dos interiores. A
somabilidade segue dos dois produtos ℓ² existentes por Cauchy–Schwarz,
sem hipótese de sinal. `full_green_head_tail` conserva a cauda integral.

O complemento oculto Qro é o readout complement ORIGINAL, que preserva
exatamente o interior nos dois slots. `hidden_interior_exact` e
`hidden_tail_exact` demonstram

\[
I_n(Q_{ro}X,Q_{ro}Y)=I_n(X,Y).
\]

`full_hidden_equals_finite` e `finite_hidden_cancellation` concluem

\[
\boxed{
G(X,Y)-G(Q_{ro}X,Q_{ro}Y)
=G_N(X,Y)-G_N(Q_{ro}X,Q_{ro}Y)
=G_\partial(X,Y)-G_\partial(Q_{ro}X,Q_{ro}Y).}
\]

Nenhum limite é necessário para esse cancelamento. Ele não afirma que
X=Qro X nem que o interior seja redundante. O estado completo, seu domínio
e seu retorno continuam sendo os mesmos. G_N é uma OBSERVAÇÃO prefixada
após construir o par, não uma nova fonte ou um clock truncado.

### 3. Aplicação ao par nativo completado e ao mesmo residual da #41

`NativeGreenParts.lean` define as sequências escalares que já são os slots
do companheiro/valor original:

\[
C_t(n)=iD(t)\log(n+1)f_t(n+1)-D'(t)f_t(n+1),
\qquad V_t(n)=2D(t)f_t(n+1).
\]

Os slots reduzidos são A_t=C_t−at V_t e B_t=at C_t.
`companion_difference`, `value_difference`, `reduced_first_difference` e
`reduced_second_difference` demonstram que suas diferenças são exatamente
as coordenadas dos pares originais, no domínio já provado. Não se cria um
novo operador nem se assume Dom(Lᵐ) para todas as ordens.

`native_interior_parts` aplica a somação por partes a

\[
\sum_{n<N}\left[
 \overline{\Delta B_t(n)}\Delta A_u(n)
-\overline{\Delta A_t(n)}\Delta B_u(n)\right].
\]

O termo `nativeFluxBulk` conserva as duas orientações, os dois fluxos e as
duas curvaturas. `native_prefix_parts` e `native_hidden_prefix_parts`
mostram que o MESMO `nativeFluxBulk` aparece no Green físico e no oculto.
Não há licença para conservar sua parte positiva em apenas um dos lados.

`native_tfvd_ledger` identifica essa diferença com `tfvdWholeGreen` da #57,
com todos os termos do ledger. `native_cutoff_boundary_exact` vale em cada N.

`ReturnTailParts.lean` demonstra a independência de N e de DOIS índices de
jet do numerador completo (`native_numerator_jets_cutoff`). O numerador
ponderado não é declarado igual, isoladamente, à Hankel dos momentos.
`native_cutoff_canonical_factor` e `native_cutoff_canonical_regular` chegam
novamente ao MESMO `carryMaterialRealResidual`:

\[
G_N- G_{N,\mathrm{oculto}}
=(u-t)\,2a^2tu\,\overline{F(t)}F(u)\,\mathfrak R(t,u).
\]

A fatoração é local na vizinhança da fonte. A divisão usa somente a carta
original com t,u não nulos, distintos e F(t),F(u) não nulos. Não se atribui
valor confluente por uma convenção 0/0. A extração já demonstrada dos jets
de \(\mathfrak R\) e a avaliação em Pₛ,ₙ da #41 permanecem as mesmas, com
as hipóteses antigas de não degenerescência, sem acrescentar o sinal desejado.

### 4. A cauda GLOBAL não desaparece junto com a cauda do interior

Para x=(companheiro,valor), y=(companheiro,valor), `reducedCellForm` é a
expressão assinada original

\[
\mathcal E_{t,u}(x,y)=a^2tu\,G(x,y)
 -\frac{a(u-t)}2\overline{x_1}y_1.
\]

O segundo termo do companheiro não é apagado em nenhum cruzamento.
Se H_M e T_M são prefixo e cauda dos pacotes de células originais, então
`reduced_return_four_cells` conserva HH, HT, TH e TT. O defeito exato é

\[
\boxed{
\mathcal E_\infty-\mathcal E_{M,L}
=\mathcal E(H_M,T_L)+\mathcal E(T_M,H_L)+\mathcal E(T_M,T_L).}
\]

Isso é `reduced_return_tail_defect`. O cancelamento do interior material
não autoriza descartar essas três contribuições do retorno global.
O estado oculto não é eliminado da teoria; usa-se sua contribuição exata
no balanço que já definia o kernel observado.

### 5. Jets das células originais nos DOIS retornos, em toda ordem fixa

`CellReturnJets.lean` prova `material_l1_analytic`, usando a continuação
complexa já disponível para p=1. `ClockReturnJets.lean` prova
`material_clock_l1_analytic`: o gradiente logarítmico original é i vezes a
derivada forte do gradiente ℓ¹. Isso dá regularidade da CURVA original,
sem afirmar domínios de potências do clock infinito.

Os jets fortes `materialL1Jet m` e `materialClockL1Jet m` são extraídos
dessas curvas, antes do readout. `map_l1_jets` prova a comutação com os
mapas lineares contínuos. Não se usa uma sequência de momentos como entrada.

Se β_k(t) é a célula centro–duas pernas original e κ_k(t) sua versão com o
log material, `cell_jet_source` e `clock_cell_jet_source` identificam os
somandos com os jets dessas MESMAS células. Assim,

\[
\boxed{
\operatorname{Jet}_m\beta(0)=\sum_{k\ge0}\operatorname{Jet}_m\beta_k(0),
\qquad
\operatorname{Jet}_m\kappa(0)=\sum_{k\ge0}\operatorname{Jet}_m\kappa_k(0).}
\]

`cell_jet_norm_summable` e `clock_cell_jet_norm_summable` provam convergência
ABSOLUTA para cada m. `return_jet_head_tail` e `clock_return_jet_head_tail`
retêm a cauda exata. Em ambos os canais também foi demonstrado

\[
\left|\operatorname{Jet}_m\beta-\sum_{k<M}b_{m,k}\right|
\le\sum_{k\ge0}|b_{m,k+M}|\longrightarrow0,
\]

e a fórmula correspondente para κ. As identidades são de coeficientes de
Taylor via dslope, com a normalização fatorial correspondente; não de
derivadas não normalizadas.

A regularidade do retorno completo e a soma dos jets não são deduzidas
apenas de convergência escalar ponto a ponto. Elas vêm do jet forte em ℓ¹
e do readout já limitado. Não se presume positividade, uniformidade em m,
cutoff computável para uma tolerância, ou sinal de qualquer jet.

## C — O que foi refutado ou delimitado

- Uma contribuição positiva do INTERIOR não pode ser mantida no Green
  canônico enquanto se omite sua cópia exata no complemento oculto. A
  somação por partes completa mostra o cancelamento de ambos, inclusive
  fluxo e cauda material. Não é um novo contraexemplo à Hankel canônica.
- Independência do cutoff de observação N não implica independência dos
  cutoffs M,L do retorno global. O defeito HT+TH+TT está explicitamente
  presente, com a mesma subtração assinada de companheiros.
- Convergência das caudas em cada ordem não dá uma margem uniforme nem
  prova o sinal do limite. Não se repete o orçamento absoluto all-order
  anterior como se fosse suficiente. Não foi certificado sinal novo.
- A leitura de bordo não reconstrói sozinha o estado; não se transforma
  invisibilidade de um observável em redundância geométrica ou isometria.

## D — O que está no kernel e validação

Os seis módulos matemáticos novos são `DiscreteParts`, `FullGreenParts`,
`NativeGreenParts`, `ReturnTailParts`, `CellReturnJets` e `ClockReturnJets`.
`Audit.lean` imprime axiomas de todas as raízes e audita tipos/corpos
transitivamente, permitindo apenas `propext`, `Classical.choice`, `Quot.sound`.
São rejeitados os consumidores posteriores de positividade H6/K6/H7 e a
positividade geral do retorno. Todos os grupos salvo a carta canônica
regular também rejeitam `material_scale_pos`: jets e somação por partes
não recebem aquele sinal. Na carta regular, o não zero de a=h₀ é o
resultado central anterior, não a positividade do novo pivô.

`experiment.py` verifica exatamente, com frações complexas, 45 casos de
somação por partes polarizada e o defeito de retorno com três cruzamentos
não nulos. São controles SINTÉTICOS de álgebra, não certificados nativos de
sinal, de momentos ou de caudas. Não usam zeros, alturas ou theta.

`validate.py` compila explicitamente os sete módulos com warnings como
erros, executa os controles, builds focado/raiz com `lake build --wfail`,
auditorias Foundation/Geometry/Analysis, regressão das doze fontes, comparação
dos arquivos históricos e diff check. Comandos, resultados, axiomas, refs,
manifestos e hashes ficam em `evidence/`.
**As 17 verificações passaram.** São 56 teoremas e 23 definições/abreviações,
em 79 raízes públicas auditadas. Os fechamentos transitivos de tipos/corpos
têm 2.786 constantes no grupo parts, 3.424 no ledger, 5.961 no native,
5.729 no boundary, 3.430 no jets e 4.473 no clockjets. Somente os três
axiomas fundacionais permitidos foram encontrados. As dependências de
positividade posterior proibidas pelo guard não foram usadas.

Reprodução no ambiente canônico preparado pela #57:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/material-green-summation-parts/validate.py
```

Não há `sorry`, `admit`, `native_decide` ou novos axiomas matemáticos.
Não foi demonstrada positividade da Hankel em toda ordem, contratividade
all-order, sinal da fase nativa, uma nova Gram positiva completa ou alturas
espectrais incondicionais. A fonte permanece a original em toda a cadeia.

## E — Próximo passo mínimo

A somação por partes do par original, o cancelamento do interior e a
extração dos jets celulares de β e κ em toda ordem fixa estão demonstrados.
Não é preciso reabrir essas três obrigações.

O próximo teste concreto é produzir uma COTA QUANTITATIVA das caudas
celulares dos jets necessários a um residual Pₛ,ₙ da #41 e transportar essa
cota pelos três termos HT+TH+TT de `reduced_return_tail_defect`, mantendo D,
D′ e todos os coeficientes originais. O ponto a controlar é o residual
CRÍTICO completo, depois dos cancelamentos, com precisão dependente da ordem.

Um primeiro alvo econômico é fixar uma direção não trivial já certificada
como regressão e derivar o erro do MESMO balanço diretamente das células,
sem theta e sem recalcular milhares de momentos. A convergência qualitativa
provada não fornece ainda um M executável para uma tolerância prescrita.
Uma cota bruta que exija cutoffs impraticáveis não será tratada como avanço
de sinal; será necessário preservar cancelamentos ou acelerar a mesma cauda
com uma identidade analítica/discreta provada, sem modificar a fonte.

Para positividade all-order, ainda é necessária uma relação independente
que oriente o sinal desse balanço na família residual nativa. Receber o
pivô positivo ou uma contratividade equivalente como hipótese seria circular.
A redução ao retorno global não resolve automaticamente essa obrigação.

Resultado PARTIAL: nova contabilidade exata no cutoff, extração forte dos
jets dos dois retornos e caudas qualitativamente controladas; nenhuma nova
margem positiva anunciada.
