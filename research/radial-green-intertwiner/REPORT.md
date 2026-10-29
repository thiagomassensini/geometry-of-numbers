# Green original, refinamento radial e leitura após a síntese completa

**Classificação: PASS_STRUCTURAL para o intertwiner e o domínio da leitura;
PARTIAL para a positividade canônica all-order.**

24/10/2026. Repositório `thiagomassensini/geometry-of-numbers`.
Branch `agent/radial-green-intertwiner`, base PR #81,
`ee6301bf05e59a246d3d8f7e1d4d1bb482a4f57d`.
`origin/main` verificado: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Não houve merge automático nem alteração de fontes, pins ou métricas.

O passo operacional recomendado pela #81 foi demonstrado: a mudança de
potência conjuga o avanço original e seu resolvente Green, no carrier físico
preexistente. A reconstrução TFVD completa conserva os dois bordos e todo o
residual. Sua forma normalizada coincide com o mesmo kernel canônico.

Há também uma redução exata da forma de sinal: o setor residual–residual
anula-se na seção regular, mas os dois cruzamentos bulk–residual permanecem.
Um diagnóstico numérico da fonte original encontrou bulk negativo e cruzamentos
compensadores positivos já no jet zero. Esse sinal numérico não é anunciado
como novo certificado Lean de desigualdade.

## A — O que já estava demonstrado

1. PR #81, `CarryRadialRefinement.powerIsometry`: isometria literal da
   mudança `x↦x^θ` com raiz do Jacobiano, `θ=m+1`, no fecho Cauchy físico
   original. Composição, domínio finito, fonte de dois canais, kernel
   polarizado e jets conjuntos canônicos já estavam demonstrados.
2. `NativeLaguerre.physicalRadialAdvance`: multiplicação pelo próprio
   `x∈[0,1]` no carrier original. É positiva e autoadjunta, com norma ≤1.
   Não é o clock material `log(n+1)` e não foi identificado com a Jacobi.
3. `physicalGreenResolvent`, seus inversos esquerdo/direito e
   `physicalGreenOperator_isPositive` em `NativePhysicalGreenResolvent.lean`.
4. `physicalCompletedFiniteGreen_numerator`,
   `physicalCompletedFiniteGreen_reconstruct` e os quatro setores originais.
   A fonte e o residual são os originais de `NativeCompletedFiniteGreenResidual`.
5. `regular_residual_equal_legs` e `regular_finiteResidual_equal_legs`:
   a igualdade das duas pernas do residual **já era um teorema existente**.
   Ela usa o gap constante das coordenadas chirais normalizadas. Não é uma
   descoberta reivindicada nesta PR.
6. `EndpointDomain`, `coefficientEquiv`, `dirichletTrace` e a injetividade
   do embedding físico, da PR #78; covariância material da PR #81.
7. A PR #41 permanece draft independente, head
   `ee56930a2c30456cfbd214a29bb31b12d3977204`. Sua identidade energia
   residual = quatro vezes o pivô de Schur não foi promovida a positividade,
   nem importada como se a branch estivesse integrada.

Os módulos Lean originais foram lidos e reutilizados. Os checkouts
compartilhados e os dois arquivos não rastreados preexistentes do operador
foram preservados.

## B — O que foi demonstrado agora

Os novos nomes pertencem a `CarryRadialGreen`.

### B.1 — O mesmo avanço, restrito ao mesmo carrier físico

`advance_preserves_closure` prova a invariância do fecho físico sob o
multiplicador original. `nativeAdvance` é somente sua restrição de domínio
**e codomínio** a `PhysicalCauchySpace`.

`native_advance_coe`, `native_advance_feature`,
`native_advance_norm_le_one` e `native_advance_isPositive` conservam a
identificação com o operador original, suas colunas, norma e positividade.
A única instância nova, `physicalSpaceNontrivial`, é uma proposição provada
pela norma não nula da coluna física zero; não acrescenta axioma ou métrica.

Com `A=nativeAdvance` e `U_θ=powerIsometry(θ−1)`,
`power_advance` demonstra em todo o fecho:

\[
\boxed{U_\theta A=A^\theta U_\theta.}
\]

A prova começa nas colunas **originais** e estende a identidade por
linearidade e densidade. Nenhum momento define o mapa.

### B.2 — O resolvente Green foi identificado, não substituído

Para `0≤η<1`, definimos apenas o inverso efetivo do denominador preexistente:

\[
D_r=I-\eta A^r,\qquad G_r=D_r^{-1}.
\]

`green_denominator_isUnit`, `green_left_inverse` e `green_right_inverse`
provam invertibilidade no domínio declarado. Não se usa a inversa total
fora desse domínio como se fosse um operador físico invertível.

`green_resolvent_one_original` prova que `G₁` coincide, no carrier original,
com **o** `physicalGreenResolvent`. Portanto, a notação nova não introduz
outro Green ajustado aos momentos.

`power_green_resolvent` e `power_green_resolvent_squared` demonstram:

\[
\boxed{U_\theta G_1=G_\theta U_\theta,\qquad
       U_\theta G_1^2=G_\theta^2U_\theta.}
\]

`η` é o peso geométrico do Green; não é o quociente chiral de retorno `q`.
Também não é uma altura ou autovalor inferido da sequência canônica.

### B.3 — Reconstrução TFVD original, com os dois bordos e o residual

`completedSource`, `completedResidual`, `bulkBoundary` e
`residualNumerator` são os objetos originais, apenas apresentados no fecho
físico. Quatro teoremas `_original` identificam literalmente suas imagens
com as definições anteriores do operador.

`completed_numerator` e `completed_reconstruct` recuperam o numerador e a
reconstrução corrigida preexistentes. `refined_completed_reconstruct` então
transporta a **identidade vetorial inteira**:

\[
U_\theta X
 =\eta G_\theta^2\bigl(U_\theta B+U_\theta E\bigr),
\]

onde `B` contém o bulk e **os dois traços**, enquanto `E` é todo o numerador
residual original. Ambas as pernas entram no mesmo operador de refinamento.
Coeficientes, fases, amplitude completada, retorno e correções não são apagados.

`refined_completed_four_sectors` mantém, com dois inputs e dois refinamentos
independentes, os setores `BB`, `BE`, `EB`, `EE`. Só depois dessa identidade
vetorial se aplica a forma assinada física.

### B.4 — O kernel canônico é o readout da expressão completa

Definimos os dois vetores reconstruídos:

\[
\widehat B_\theta=\eta G_\theta^2U_\theta B,
\qquad \widehat E_\theta=\eta G_\theta^2U_\theta E.
\]

`correctedGreenPairing` soma os quatro pareamentos da forma nativa
`Φ(u,v)=½(〈u₊,v₊〉−〈u₋,v₋〉)`.
`corrected_green_pairing_is_common` prova igualdade com o pareamento físico
refinado da #81. Sob as condições nativas explícitas de regularidade nos
pontos — strip e denominadores não nulos —
`corrected_green_pairing_is_canonical` prova:

\[
\boxed{K(z,w)=\Phi(\widehat B_z,\widehat B_w)
 +\Phi(\widehat B_z,\widehat E_w)
 +\Phi(\widehat E_z,\widehat B_w)
 +\Phi(\widehat E_z,\widehat E_w).}
\]

É exatamente `canonicalCompletedNativePolarizedDslopeKernel`, com dois
nós independentes e o refinamento comum original. Não se compara uma Gram
auxiliar com a Hankel por semelhança de diagonais.

`corrected_green_weight_independent` prova que a soma completa é independente
da escolha válida de `η`. Alterar esse parâmetro do instrumento não fabrica
outra sequência de momentos. Por igualdade de kernels, os jets já
identificados na #81 continuam sendo os canônicos; não são reivindicados
como nova prova de sinais all-order desta PR.

### B.5 — Domínio: a leitura depois da síntese é uma exigência matemática

`resolvent_first_column_not_finite` demonstra, para `0<η<1`:

\[
G_1\varphi_0\notin\operatorname{range}(\text{physicalCauchyEmbedding}).
\]

O resolvente bounded existe no carrier completo, mas não preserva em geral
o span **finito** onde o readout estava originalmente definido.
A prova usa a recorrência forçada `c₀=1`, `c_(n+1)=ηc_n`; todos os
coeficientes seriam não nulos, contradizendo suporte finito.

Em contraste, `whole_green_material_readout` prova que a reconstrução
**completa e corrigida**, depois do refinamento, possui um testemunho no
domínio algébrico original. `whole_green_core_witness_unique` prova sua
unicidade pelo embedding físico injetivo.

Assim o readout é aplicado à soma completa que já voltou ao domínio, sem
inventar uma funcional em todo Lp nem atribuir leituras separadas a parcelas
fora do domínio. Os dois valores quirais continuam separados.
A covariância material mantém o fator complexo original:

\[
\mathcal D_s(U_\theta X)
 =\sqrt\theta\,\theta^{-s}\mathcal D_s(X).
\]

O módulo crítico e sua fase são aqueles já demonstrados na #81. Esse
readout material `𝒟_s` é distinto da resposta normalizada `−F′/(2F)`;
nenhuma igualdade entre funções de parâmetros distintos foi postulada.

### B.6 — Redução exata do sinal: residual nulo não é vetor apagável

Reutilizamos a igualdade preexistente das pernas do residual, agora para
todo o numerador TFVD, os resolventes e **refinamentos independentes**.
`residual_numerator_equal_legs` e `reconstructed_residual_equal_legs`
provam essa propagação sem descartar componentes.

`reconstructed_residual_pairing_zero` demonstra a anulação exata de `EE`.
As condições de regularidade se referem só aos suportes finitos efetivos.
`numerator_regular_eventually` e `residual_pairing_eventually_zero` as
descarregam eventualmente, de modo independente nos dois índices radiais.

`corrected_green_three_sectors` deixa, portanto:

\[
\boxed{K=\Phi(\widehat B,\widehat B')
       +\Phi(\widehat B,\widehat E')
       +\Phi(\widehat E,\widehat B').}
\]

Na diagonal de uma direção finita original, `signed_energy_bulk_plus_mixed`
prova exatamente:

\[
\boxed{\operatorname{Re}\Phi(U_\theta X,U_\theta X)
 =\operatorname{Re}\Phi(\widehat B,\widehat B)
  +2\operatorname{Re}\Phi(\widehat B,\widehat E).}
\]

A igualdade é de partes reais, com o mesmo objeto e coeficientes. Não se
presume que qualquer parcela seja positiva. A anulação de `EE` não torna
`E` nulo nem o coloca no radical da forma: os termos mistos permanecem.

## C — Obstrução demonstrada e diagnóstico do sinal

**Obstrução formal de domínio:** é falsa a preservação geral do core finito
pelo resolvente, já na coluna literal zero. Isso refuta aplicar o readout
do core a cada imagem Green arbitrária sem justificar um domínio ampliado.
Não refuta o Green bounded nem a leitura da reconstrução completa, que
possui o testemunho finito demonstrado em B.5.

**Diagnóstico numérico, separado das provas Lean:**
`probe_green_sectors.py` avaliou a mesma característica completada pela
identificação posterior com xi, sem zeros, alturas, Cholesky ou momentos
como entradas. Usou `η=1/√2`, a razão crítica C2, e montou os dois perfis
físicos integrais do Green. A síntese material completa não foi reexecutada
nesse diagnóstico; a proveniência é a identidade analítica já existente
`completedNativeOperatorCharacteristic_eq_completedRiemannZeta`.

Foram comparadas 80 e 120 casas de trabalho; os resultados coincidiram em
mais de 40 casas nas quantidades comparadas. Na execução de 120 casas,
os resíduos numéricos de reconstrução ficaram abaixo de `9×10⁻¹²⁰`.
Isso é resíduo observado, **não** uma cota intervalar certificada.

| `κ=k+1` | bulk `BB` | misto `BE+EB` | kernel total |
| --- | --- | --- | --- |
| 10 | −0,06341534883 | 0,08651997023 | 0,02310462140 |
| 100 | −0,06342462668 | 0,08652961608 | 0,02310498940 |
| 1000 | −0,06342471947 | 0,08652971255 | 0,02310499308 |

Portanto, o bulk desta decomposição **não deve ser apresentado como a
parte Gram positiva** sem prova. O diagnóstico aponta precisamente o
contrário já no primeiro jet. O total positivo conhecido é recuperado
pelos cruzamentos. A negatividade dessas parcelas nos exemplos não foi
convertida aqui em uma nova desigualdade certificada pelo kernel.

Para orientar o próximo teorema, a especialização analítica sugere:

\[
J_\eta=\int_0^1x^2\frac{\eta(2-\eta x)}{(1-\eta x)^2}\,dx,
\qquad \frac{BB}{h_0}\to1-2J_\eta,
\qquad \frac{BE}{h_0}\to J_\eta.
\]

No peso C2, o diagnóstico dá `J≈1,87253277014716` e
`BB/h₀→−2,74506554029432`. A expressão fechada de `J` foi conferida
numericamente por integração independente. Essas fórmulas de limite e seus
sinais são **a próxima formalização**, não teoremas Lean anunciados nesta PR.

### Relação com a nota centro–pernas recebida

Foi lida a nota `NOTA_CARRY_CENTRO_PERNAS_MOMENTOS_KERNEL_2026-10-23.md`
(SHA256 `1b4c78fb2f6e3c6d34a73146b37c070a1256aef9fcb6a0a73fc94c8da147b5cd`).
Sua recorrência `P_(n+1)=xyP_n+x^(2n+2)+y^(2n+2)` é uma identidade
polinomial exata útil para organizar os coeficientes do kernel, mas vale
independentemente da fonte e não determina seu sinal. O contraexemplo de
`P₁` nos pontos `0,1`, com determinante `−1`, impede interpretar seus
quadrados pontuais como uma Gram positiva.

O avanço desta PR é complementar: transportar o Green e a fonte vetorial
originais, antes da leitura. Não foi identificada a graduação dos monômios
com incrementos materiais de câmeras, nem formalizado nesta PR o perfil
`f_(n;x,y)` proposto pela nota. O centro de graus não foi identificado com
um centro posicional. Essa ponte material e a positividade continuam abertas.

## D — O que permanece aberto e onde poderia haver circularidade

Não foi demonstrada uma Gram positiva dos momentos canônicos em toda ordem.
A igualdade com o kernel completo está provada, mas sua forma continua
assinada. A positividade do multiplicador/operador Green original não
implica positividade dessa diferença de canais.

O numerador residual contém a amplitude completada e o retorno da própria
fonte. A reconstrução Green não constitui, por si só, uma lei independente
que determine o sinal do retorno; é uma identidade exata preservando esses
dados. Usar sua existência como prova de passividade seria uma inversão lógica.

Também não se demonstrou aqui um transporte isométrico de todo o estado
material multibase para o carrier Cauchy, nem que o readout material seja
uma norma positiva. A genealogia Carry → fonte completada e os resultados
finitos H6/K6 são preservados; nenhum foi extrapolado para positividade infinita.

O sinal restante é o da **soma bulk mais cruzamento misto** da fonte original.
Chamá-lo de contractividade, Pick positivo ou dominância não resolve a
obrigação. Não foi introduzido um novo predicado equivalente ao alvo como
se fosse uma causa geométrica já demonstrada.

## E — Próximo teorema mínimo e validação

O próximo teste concreto é formalizar a compensação do jet zero observada
em C, usando a derivada central da resposta original e o multiplicador
Green literal. Um alvo curto é demonstrar o limite do termo misto com
coeficiente `J_η` e uma cota racional para esse integral, mantendo o bulk
com seu sinal real. Isso testará rigorosamente o mecanismo físico de
compensação antes de supor qualquer lei de sinal em ordens superiores.

Para avançar all-order, será necessária uma desigualdade **da fonte
material/completada**, anterior à positividade desejada, que controle a
soma de B.6 para todos os inputs. O passo correto é desembrulhar o residual
nos campos nativo e Gamma antes de estimar o cruzamento. Receber o próprio
sinal dessa soma ou a positividade Hankel como hipótese seria circular.

**Validação formal:** 58 teoremas, 19 definições, uma abreviação e uma
instância proposicional provada, em sete módulos. As 79 raízes públicas
foram auditadas por `#print axioms` e inspeção transitiva de tipos **e corpos**,
com 5.943 dependências. Todas passam no grupo de construção sem dependência
da sequência de momentos, sinais finitos posteriores ou positividade all-order.
Somente `propext`, `Classical.choice`, `Quot.sound` são usados.

**Execução:** 18 comandos com saída zero: módulos explícitos, fontes originais,
`lake build --wfail`, auditorias Foundation/Geometry/Analysis e um diagnóstico
Python separado. O diagnóstico não integra a base de confiança Lean.
Quinze módulos ancestrais foram recompilados de fontes idênticas à base.
Sem `sorry`, `admit`, `native_decide` ou novos axiomas matemáticos.

Reprodução no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

O diagnóstico usa o Python Miniforge já existente, sem instalação de pacotes.
Comandos, versões, hashes, logs e resultados estão em `evidence/`.
O objetivo integral permanece ativo em `GOAL_STATUS.md`.

**FIM DO RELATÓRIO — Green e domínio transportados; residual–residual nulo; controle de sinal misto e Gram positiva all-order abertos.**
