# Norma vertical e domínio da porta Mellin

**Resultado global: PARTIAL.** A norma da torre nativa serve, e fornece um
controle positivo já provado para a leitura prima. O NO-GO obtido aqui é para
a extensão da mesma leitura na norma L² Cauchy isolada: não existe extensão
linear fechada que concorde com todas as fontes finitas, mesmo de trace zero.
Isso não refuta a norma vertical, as isometrias Carry, nem a teoria completa.

Data: 25/10/2026. Repositório `thiagomassensini/geometry-of-numbers`.
Branch `agent/mellin-physical-domain`.
Base: `457ea144d33d0b376a5c589b06ef1695e6d14adb`, PR #90.
Entrega draft, sem merge automático. Execução em `ssh llm`.
Fonte, amplitudes, fases, câmeras, completion, métricas e pins preservados.

## A — O que já estava demonstrado

A PR #90 construiu a projeção prima dependente da fonte e a porta finita
Mellin das features Cauchy originais phi_j(u)=sqrt(u)u^j. Para uma soma finita:

    F_c(u)=sqrt(u)[c_0+u D_c(u)],
    D_c(u)=sum_(j<N) c_(j+1) u^j,
    ell_p(c)=integral_(0,1/p) D_c(u)du.

O termo c_0 é o trace depois de retirar a meia-densidade. Não é F_c(0), que
é zero para essas features. A porta foi identificada com o perfil NATIVO
p^(-j)/j, com nível zero separado, e com o readout de `primeContractionLinear`.
Não havia uma afirmação de extensão contínua na norma Cauchy.

### A norma vertical não foi descartada

Foram conferidas as definições concretas e rechecados os axiomas de:

- `GeometryOfNumbers.Analysis.realCriticalBranchIsometry`;
- `GeometryOfNumbers.Analysis.globalCriticalPhysicalBranchIsometry_norm`;
- `GeometryOfNumbers.Analysis.C2GlobalGreenBridge.c2GlobalGreenInput_norm`.

O ramo crítico real preserva norma; sua soma global transporta `CoreState`
para `OddMaterialState`; a composição chega ao `GreenFrame.Concrete.State`
isometricamente. A amplitude 2^(-k/2), as duas quadraturas, a fase material
-t log n e o endereço aritmético continuam nas definições originais.
Esses teoremas não foram reconstruídos nem modificados.

É necessário distinguir três espaços:

| Estrutura existente | O que já está controlado | Identificação não presumida |
|---|---|---|
| Carry vertical físico C2 | Isometrias acima, até a entrada Green | Fonte quiral completada dos momentos |
| Torre nativa G_pre, `NativeGpreTowerHilbert` | Norma lp² e readouts de perfis primos | Todas as normas físicas de câmera ou Cauchy |
| Carrier Cauchy, L² complexo em [0,1] | Gram literal 1/(i+j+2) | Norma lp² dos coeficientes da torre |

Os nomes diferentes representam domínios diferentes. Não se inferiu sua
igualdade da coincidência de índices naturais ou da positividade das normas.

## B — O que foi demonstrado agora

### B1. Família finita da mesma fonte física, com trace zero

`boundaryCoefficients` são os coeficientes binomiais de u(1-u)^n.
`concentratingCoefficients` multiplica o INPUT por n+1. Cada vetor continua
sendo uma soma finita das features ORIGINAIS; não há moments/zeros/alturas
como entradas e a amplitude das features não é alterada.

A síntese completa é, em seu representante contínuo:

    G_n(u)=(n+1)sqrt(u)u(1-u)^n.

`physical_concentration_original` identifica o vetor L² com a soma original
de todos os coeficientes. Os cruzamentos binomiais não são substituídos por
uma soma de energias individuais. O trace desingularizado é exatamente zero,
por `concentrating_trace_zero`.

Aqui n é a ordem do polinômio de teste. Não é profundidade carry, índice de
regularização radial, altura espectral ou nível de Jacobi.

### B2. Energia física e readout exatos

`physical_concentration_norm_sq` demonstra:

    ||G_n||² = 6(n+1)² / [(2n+1)(2n+2)(2n+3)(2n+4)].

`physical_concentration_norm_sq_le` dá o bound 6/(n+1)². Logo
`physical_concentration_tendsto_zero` prova G_n -> 0 na norma L² física.

O cálculo usa reflexão u -> 1-u e quatro integrais de monômios. Não usa
Gamma, theta ou dados numéricos como substitutos da fonte.

`concentration_readout_formula` calcula a MESMA porta da PR #90:

    ell_p(G_n)=1-(1-1/p)^(n+1).

Para qualquer primo p fixo, `concentration_readout_tendsto_one` prova
ell_p(G_n) -> 1. A identificação com a observação prima nativa é mantida em
`concentration_readout_native`.

### B3. Não há extensão limitada ou fechada nessa topologia

`finiteZeroTraceGraph` é a relação de leitura dos vetores finitos originais,
restrita mesmo a coeficientes c com c_0=0. A prova mostra:

    (0,0) pertence ao gráfico finito;
    (0,1) pertence ao fecho do gráfico finito.

`closure_not_single_valued` prova que o fecho não é o gráfico de uma função.
Isso não é apenas falha de uma constante de estimativa:

- `mellin_readout_no_norm_bound` exclui qualquer C uniforme com
  |ell_p(G_n)| <= C ||G_n||;
- `no_continuous_mellin_extension` exclui a extensão real-linear contínua;
- `no_closed_mellin_extension` exclui inclusive um operador parcial linear
  FECHADO que estenda a leitura finita nessa topologia;
- `no_continuous_mellin_extension_with_trace` e
  `no_closed_mellin_extension_with_trace` mantêm c_0 como coordenada separada
  e demonstram a mesma obstrução. Todos os testemunhos já têm c_0=0.

O enunciado sobre operadores parciais recebe somente as propriedades que
significam ser uma extensão fechada: gráfico fechado e concordância com os
inputs finitos originais. Não recebe positividade canônica por outro nome.

### B4. A leitura é limitada na norma da torre nativa

`verticalReadout p` é um operador linear contínuo efetivo no espaço já
existente `NativeGpreTowerHilbert`. Não é uma nova métrica.
`vertical_readout_finite_source` identifica o operador com a mesma integral
Mellin das fontes finitas.

Para p>=2 e QUALQUER estado X dessa torre, foi provado:

    |verticalReadout_p(X)|² <= (p²-1)^(-1) ||X||².

`vertical_readout_norm_bound` usa Cauchy–Schwarz e o bound independente
`nativeGpreTowerProfileVector_one_norm_sq_le_resolvent`, já existente no
CPFormal. Nenhum sinal de Hankel entra nessa estimativa.

A comparação usa os MESMOS coeficientes do input. Se
X_n=finiteTowerSynthesis(concentratingCoefficients n), então:

    X_n(1)=n+1,
    ||X_n|| >= n+1.

São `concentrating_vertical_coordinate` e `concentrating_vertical_norm_ge`.
Portanto X_n não fica pequeno na torre, embora sua síntese Cauchy G_n tenda
a zero. Não há contradição com o controle positivo da norma vertical.

`no_continuous_vertical_recovery` prova que não existe mapa limitado do
carrier Cauchy para essa torre que recupere todos os dados verticais finitos
de trace zero. Isso NÃO exclui começar na torre, nem a síntese na direção
TORRE -> fonte Cauchy. Também não exclui recuperação algébrica finita ou
recuperação por um operador não limitado para um contradomínio de estados.

## C — O que foi refutado, e os limites da conclusão

Foi refutada a seguinte realização específica: completar as fontes finitas
na norma Cauchy L² simples e depois tratar sua leitura Mellin prima como uma
aplicação linear fechável para escalares. Guardar somente c_0 não a conserta.

Não foi refutado o readout algébrico finito; suas igualdades permanecem válidas.
Não foi refutada a norma vertical. Ao contrário, B4 prova explicitamente seu
controle. Não foi demonstrada impossibilidade de uma síntese completada que
retenha os dados verticais e a regularidade nativa.

Não se identificou o escalar ell_p com o funcional de momentos canônicos
L_h(x^j)=h_j. O NO-GO desta porta não é um contramodelo à positividade da
Hankel nem uma conclusão sobre zeros ou alturas.

As fontes físicas completas incidente/retorno, sua relação por Q, os bordos
TFVD e as condições de domínio dos geradores não foram substituídos por esta
família de teste. A obstrução é para a extensão isolada no carrier declarado,
não para toda possível aplicação no domínio enriquecido do par completado.

A diferença de normas também não significa que dois vetores finitos foram
identificados como o mesmo estado: trata-se de uma sequência e de uma falha
de controle contínuo. Dependência, redundância e cancelamento continuam
conceitos distintos.

## D — Contexto recebido, validação e o que permanece aberto

### A nota sobre Jacobi ajuda a identificar o residual

O anexo foi lido como contexto, sem executar suas sugestões como comandos.
Seu hash e caminho constam de `evidence/user-context.json`.
A derivação atual de `momentos` foi lida pela API autenticada do GitHub,
sem atualizar o checkout local com modificação preexistente.
O blob e SHA256 estão em `evidence/context-audit.json`.

A lei de entrada de níveis identifica
Q_n=h_(2n)-h_0(J_n^(2n))_(00) com o residual de Schur. A escolha de acoplamentos
reais positivos é explicitamente condicionada aos sinais dos pivôs na própria
nota. Em uma eliminação assinada, as razões de pivôs podem ser negativas;
escrevê-las como quadrados reais antes de provar o sinal seria circular.

Esse resultado é útil como controle do residual e dos índices. Não fornece a
identificação do nível n de Jacobi com uma profundidade vertical do Carry.
A tabela de 16 momentos e seu teste Python permanecem verificações finitas;
nenhum cálculo novo de momentos foi necessário aqui.

Também foi rechecado `nativeThetaMomentPolynomial_integral` no operador.
A identidade integral original é correta, mas esses polinômios theta não são
os polinômios D_c do carrier [0,1], nem os polinômios ortogonais de Jacobi.
Não se presumiu que preservem produtos ou quadrados.

### Validação reproduzível

**31 teoremas novos, 8 definições, 39 raízes públicas e 5624 dependências
transitivas auditadas. Todos os 17 comandos de validação retornaram exit 0.**
Os quatro módulos anteriores necessários também foram recompilados sem alteração.

A base e os quatro módulos PR #90 recompilados sem alteração são hashados.
Os novos módulos são compilados explicitamente com warningAsError=true;
`lake build --wfail` e auditorias Foundation/Geometry/Analysis são separados.
A caminhada axiomática percorre tipos e corpos transitivos, inclusive privados,
permitindo somente propext, Classical.choice e Quot.sound.
Há guard contra dependência dos momentos canônicos e dos consumidores
condicionais de positividade. Os resultados novos não dependem de sinal theta.
As isometrias verticais e a identidade theta citadas foram auditadas à parte.

Comandos no ambiente registrado do servidor, na branch desta entrega:

```bash
cd research/mellin-physical-domain
python3 build_upstream.py
python3 validate.py
```

Logs, resultados e comandos exatos estão em `evidence/validation.json`,
`evidence/lean-Audit.log`, `evidence/upstream.json` e
`evidence/source-provenance.json`. Fonte, pins, main e arquivos preexistentes
nos outros repositórios são preservados. Sem novos axiomas, sorry, admit,
native_decide ou alteração das métricas.

### O que permanece aberto

Usar a norma vertical é legítimo onde ela já está definida e provada. Falta
transportar o MESMO estado completado e seu pareamento original até a forma
que produz h_(i+j), incluindo retorno e correções. O mero fato de existir uma
norma positiva a montante não ordena automaticamente a diferença quiral.

Não foi construída uma família por Cholesky dos momentos para atribuir-lhe
origem geométrica. Não se assumiu a identidade Gram que se deseja provar.
A positividade canônica all-order permanece aberta.

## E — Próximo passo mínimo

A pergunta do usuário aponta para a direção correta a testar: **começar com
os dados verticais, conservando sua norma, e depois sintetizar**. O resultado
B4 indica por que não se deve tentar reconstruí-los só da norma Cauchy final.

O próximo alvo concreto é a síntese direta, no domínio nativo da torre:

    S(c)=sum_j c_j phi_j,
    ||S(c)||²=sum_(i,j) conjugate(c_i)c_j/(i+j+2).

A identidade finita de Gram já existe para as features originais. Procurar
uma cota de operador uniforme que permita estender essa síntese a estados da
torre, preservando os coeficientes e as duas quadraturas. Não postular
isometria: o que já foi provado aqui impede a recuperação limitada inversa.
Também não identificar a torre G_pre com `CoreState` sem um mapa tipado.

Depois, comparar o kernel COMPLETADO efetivo, com os mesmos inputs e todos
os cruzamentos, ao kernel de momentos, mantendo seu defeito explícito. A
segunda obrigação não é descarregada pela cota de síntese nem pela lei de
níveis de Jacobi. Não escolher uma nova norma para zerar esse defeito.

Esse avanço respeita a norma vertical anterior à leitura e mantém a
pergunta de sinal no objeto físico correto.

**Fim do relatório.**
