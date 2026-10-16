# Carry — projeção central da fonte completa e teste do residual

Data: 2026-10-16. Repositório alterado: `geometry-of-numbers`, base `ce809345a79d7f2aa1bbc51ba69605e408c53899` (PR #6). Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

**Resultado principal:** a projeção proposta foi construída sobre a fonte completada efetiva. Guardando o plano central junto com seu complemento, o transporte preserva exatamente o produto interno com dois argumentos. Contudo, **o complemento dessa candidata não realiza o residual canônico**, nem mesmo como germen da diagonal real: seu primeiro jet tem energia maior que 1/512, enquanto h1 é menor que 1/1024.

A separação é provada em Lean. Não depende dos valores aproximados de um experimento, de mudar a métrica ou de ajustar a normalização. É uma obstrução para esta candidata precisamente definida, não para todas as possíveis realizações geométricas do residual.

## 1. Fonte e normalização utilizadas

Mantêm-se os objetos dos PRs anteriores:

\[
Y_t=(1,g_t,\beta_t),\qquad S_t=\ell(Y_t),\qquad F(t)=D(t)S_t.
\]

Y é `baseTwoCompletedBoundaryHilbertState`, no produto Hilbert original de semente, gradiente material ℓ² e retorno global de células completas. D e F são o dressing e a resposta escalar já existentes. A fonte completa precede os readouts usados neste estudo.

Definimos a candidata com a normalização fixa já testada:

\[
V(t)=\frac{D(t)Y_t}{\sqrt2 F(t)}.
\]

`carryMaterialNormalizedState_cancel` prova a igualdade algébrica

\[
\boxed{V(t)=\frac{Y_t}{\sqrt2 S_t}.}
\]

Em uma vizinhança de zero, os denominadores são não nulos pelas provas anteriores de não anulação central e regularidade. As definições Lean têm inversos totais; a interpretação usual das divisões mantém essa restrição. O cancelamento de D não elimina o retorno nem a conexão que entrou na construção de F e de sua companheira.

## 2. Transporte geométrico efetivamente construído

Sejam

\[
e=Y_0/\|Y_0\|,\qquad
\Pi y=\langle e,y\rangle e,\qquad C=I-\Pi.
\]

Y0 é não nulo porque sua semente é 1. A direção e vem exclusivamente da fonte efetiva; nenhum momento ou Gram desejado entra na definição. A normalização de e escolhe uma base unitária para projetar e não altera Y, V ou a métrica.

O carrier existente é complexo e também admite a leitura em duas quadraturas reais. A linha complexa de e corresponde ao plano real de e e Je, com J dado por multiplicação por i. Foram provados

\[
\|e\|=1,\quad \langle e,Cy\rangle=0,\quad
C(iy)=iC(y),\quad C(e)=C(ie)=0.
\]

O mapa limitado e linear construído é

\[
\boxed{\mathcal T(y)=(\Pi y,Cy)}
\]

no produto Hilbert padrão das duas componentes. `carryMaterialCentral_reconstruct` e `carryMaterialCentralSplit_pairing` provam

\[
\Pi y+Cy=y,\qquad
\boxed{\langle\mathcal T(x),\mathcal T(y)\rangle=\langle x,y\rangle.}
\]

Assim, o transporte completo não perde informação ou cruzamentos. Somente ao estudar Cy isoladamente se retira o plano central. Os termos entre o plano e o complemento são nulos por ortogonalidade demonstrada, não por apagamento de um canal físico.

## 3. Pareamento completo do complemento

Definimos `carryMaterialCenteredState` por Z(t)=CV(t). Para t e u independentes, `carryMaterialCenteredState_pairing` prova

\[
\boxed{\begin{aligned}
\langle Z(t),Z(u)\rangle
={}&\langle V(t),V(u)\rangle\\
&-\overline{\langle e,V(t)\rangle}\,\langle e,V(u)\rangle.
\end{aligned}}
\]

Essa é a fórmula de Schur **do pareamento físico original**. Em notação H(t,u)=⟨V(t),V(u)⟩, ela equivale a H(t,u)−H(t,0)H(0,u)/H(0,0), porque V0 pertence à mesma linha não nula de Y0. Não se assumiu H=kernel canônico.

Z(0)=0, portanto a calibração central do residual passa automaticamente. Isso exige investigar o primeiro jet; o valor central sozinho não distingue as candidatas.

## 4. Domínio e relógio: a projeção não é um entrelaçamento dinâmico

K continua sendo `completedBoundaryTransportedClock`, o mapa linear parcial já existente. Não se construiu um operador das alturas ou uma extensão autoadjunta.

`carryMaterialCentralComplement_mem_clockDomain` prova que C preserva seu domínio: o vetor central subtraído já pertence ao domínio e este é um submódulo.

Entretanto, para k0=KY0, `carryMaterialCentralComplement_clock_center_ne` prova

\[
\boxed{CKY_0\ne KCY_0=0.}
\]

Ou seja, o relógio envia a direção central para fora do plano retirado. O transporte completo mantém essa informação entre suas duas componentes; descartar o plano não produz por si só uma dinâmica fechada no complemento. Nenhum entrelaçamento CK=KC é presumido.

## 5. Primeiro jet e seu defeito exato

A diferenciabilidade forte real de Y e a ação do relógio são reutilizadas. Não se introduz holomorfia vetorial ou identificação de profundidade com ordem de jet.

Como CY0=0, a derivada da normalização escalar multiplica o vetor nulo na origem. `carryMaterialCenteredState_hasDerivAt_zero` prova

\[
\boxed{Z'(0)=-\frac{i}{\sqrt2 S_0}\,Ck_0.}
\]

O relógio e seu retorno global permanecem inteiros em k0. A energia é

\[
\boxed{\|Z'(0)\|^2=
\frac{\|k_0\|^2-|\langle e,k_0\rangle|^2}{2|S_0|^2}.}
\]

É `carryMaterialCenteredState_firstJet_energy`. O cruzamento entre estado central e relógio foi conservado. Sua expansão fornece o defeito preciso a comparar:

\[
\mathcal E_1=
\frac{\|k_0\|^2-|\langle e,k_0\rangle|^2}{2|S_0|^2}-h_1.
\]

## 6. Por que a diferença é rigorosamente positiva

O novo observável usado para a estimativa é um contraste de coordenadas da fonte:

\[
L(y)=y_{g,0}-g_0(0)y_{seed}.
\]

Ele usa a amplitude efetiva g0(0), sem pesos escolhidos para obter um sinal. Foram provados

\[
L(e)=0,\quad L(Cy)=L(y),\quad |L(y)|\le2\|y\|,
\quad L(k_0)=\frac{\log2}{\sqrt2}.
\]

Logo, esse contraste material sobrevive à retirada do plano central. Usando o limite certificado log2>1/2, obtemos

\[
\|Ck_0\|^2>1/32.
\]

Separadamente, o majorante já existente da segunda diferença de **células completas** e uma comparação telescópica dão |S0|≤5/2. Os limites são aplicados depois da síntese, sem substituir o retorno por termos independentes.

Conclui-se, no Lean:

\[
\boxed{\|Z'(0)\|^2>\frac1{512}.}
\]

Do lado canônico, reaproveitam-se a fórmula do coeficiente ímpar da fonte e as caixas racionais certificadas dos momentos theta a,b,c:

\[
2h_1=\frac{3b^2-ac}{6a^2}.
\]

Esses certificados existentes implicam h1<1/1024. Os teoremas externos `canonical_first_shifted_moment_lt`, `material_centered_firstJet_gap` e `material_centered_firstJet_ne_canonical` provam

\[
\boxed{\mathcal E_1>\frac1{1024}>0.}
\]

As frações exibidas são margens das estimativas. Nenhuma delas é aplicada à fonte, à métrica ou à normalização.

## 7. Obstrução direta para o residual, além do teste de coeficientes

O residual ponderado do PR #6 é

\[
\mathscr R(t,u)=\overline{r_0(t)}r_0(u)\operatorname{dslope}r_1(t,u).
\]

As identidades já provadas r0(t)=t·a(t), a(0)=h0 e r1′(0)=h1/h0² fazem seu primeiro coeficiente misto ser h1. A prova nova `material_centered_residual_firstJet_necessary` usa inclinações divididas reais, continuidade e o limite perfurado para provar que

\[
\|Z(t)\|^2=\mathscr R(t,t)\ \text{num germen real de zero}
\quad\Longrightarrow\quad \|Z'(0)\|^2=h_1.
\]

Essa consequência contradiz a separação estrita acima. `material_centered_not_residual_diagonal_germ` exclui formalmente a igualdade do germen diagonal. Portanto a igualdade de dois argumentos também não pode valer para esta candidata num aberto em torno da origem.

Isso não é um no-go para outra aplicação derivada da fonte e de sua companheira, nem para um transporte corrigido da forma Green. É o resultado do teste específico proposto: retirar o plano central do lift literal normalizado não fornece o residual canônico.

## 8. TFVD, retorno e o próximo problema

O gradiente do estado projetado ainda é um elemento do ℓ² material original. As leituras TFVD existentes continuam disponíveis para esse elemento e reconstroem cada coordenada por Green + retorno de traço. A regressão testa explicitamente essa aplicação à candidata Z.

`carryMaterialTfvd_edge_pairing`, já existente, mantém os quatro cruzamentos GG,GR,RG,RR para entradas e endereços independentes. A semente e o retorno global permanecem no produto Hilbert do estado completo. O retorno global não é identificado com o retorno de traço TFVD.

Reexpressar Z por um transporte isométrico preservaria sua energia do primeiro jet. Assim, uma simples mudança fiel de coordenadas dessa candidata não remove o defeito certificado.

Há uma diferença concreta entre as duas rotas: o dressing D cancela exatamente no vetor V, enquanto a resposta canônica já transportada conserva a conexão

\[
r_0(t)=\frac{iB(Y_t)}{2S_t}-\frac{D'(t)}{2D(t)}.
\]

B é o retorno global do relógio existente. Portanto, projetar o vetor de valor normalizado não reproduz automaticamente a extração realizada no par valor/companheira. Essa comparação orienta a próxima busca para o estado Green com a companheira e a conexão preservadas. Não demonstra que a diferença inteira venha somente de D, nem que acrescentar um termo específico já repare o pareamento.

O diagnóstico fica:

**Fonte completada Y → normalização fixa V → transporte fiel (ΠV,CV) → Gram de CV → diferença estrita no primeiro jet diante do residual canônico.**

A interface ainda aberta é uma aplicação derivada da síntese física cujo pareamento seja exatamente a resposta Green residual. Este estudo sugere manter acoplados o plano central, a companheira e os termos do relógio que o conectam ao complemento. Não demonstra a existência dessa aplicação e não fornece motivo para ajustar uma constante de Z.

## 9. Status e evidências

| Afirmação | Status |
| --- | --- |
| Projeção e complemento definidos pela fonte real completada | **CONSTRUÍDOS no Lean**, notação complexa das duas quadraturas |
| Reconstrução e preservação do pareamento completo com dois argumentos | **PROVADO no Lean** |
| Complemento preserva o domínio do relógio | **PROVADO no Lean** |
| Complemento sozinho comuta com o relógio | **OBSTRUÍDO** na própria fonte central |
| Fórmula exata da energia do primeiro jet, com retorno e cruzamento central | **PROVADO no Lean** |
| Energia do primeiro jet >1/512; momento canônico h1<1/1024 | **PROVADO no Lean** |
| Gram de Z realiza o residual canônico | **OBSTRUÍDO**, inclusive no germen diagonal real |
| TFVD reconstrói as coordenadas projetadas mantendo Green e retorno | **REUTILIZADO e testado** na regressão |
| Outra realização física do residual canônico | **ABERTO** |
| Positividade canônica em todas as ordens ou fechamento do operador das alturas | **NÃO DEMONSTRADO** por este estudo |

Código: [CarryMaterialCentralProjection.lean](../GeometryOfNumbers/Analysis/CarryMaterialCentralProjection.lean), [CarryMaterialCentralProjectionBounds.lean](../GeometryOfNumbers/Analysis/CarryMaterialCentralProjectionBounds.lean) e [CanonicalComparison.lean](../research/material-central-calibration/CanonicalComparison.lean), namespace novo `CarryMaterialCentralProjectionComparison`.

São 28 teoremas de biblioteca e cinco teoremas externos novos. Os nove roots de definições incluem um simples alias do carrier existente; não há carrier com métrica nova. A lista completa está em [new-roots.json](../research/material-central-projection/new-roots.json).

Validação em `llm`: build focado (8.790 jobs) e completo (8.829 jobs) com `--wfail`; auditorias Foundation/Geometry/Analysis; regressões 72, TFVD aplicado ao estado projetado, domínio, relógio, retorno e companheira; comparação externa com warnings como erros. Os 42 novos roots foram auditados transitivamente por tipos e corpos, permitindo somente `propext`, `Classical.choice` e `Quot.sound`, com impressão explícita dos axiomas. Os 53 teoremas externos anteriores permanecem rechecados.

Proveniência, hashes, footprints e logs estão em [research/material-central-projection](../research/material-central-projection/). Pins, pesos e normalizações preservados. Operador e momentos foram apenas consultados; trabalhos preexistentes preservados. O diagnóstico numérico auxiliar não integra as provas nem suas premissas.
