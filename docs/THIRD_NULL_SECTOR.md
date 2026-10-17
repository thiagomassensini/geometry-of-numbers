# Sexta ordem da mesma energia residual material

## Resultado verificado

Para toda família finita **fixa** de coeficientes reais `c_i` e direções
materiais reais `a_i`, escreva

\[
 M_j=\sum_i c_i a_i^j,\qquad
 h_j=\texttt{canonicalCompletedNativeLogDerivativeMoment}\ j.
\]

No setor

\[
 M_1=M_2=0,\qquad M_3\ne0,
\]

a energia do **mesmo residual** dos PRs #8, #9 e #10 é positiva em escalas
não nulas suficientemente próximas de zero. As identidades são:

\[
 E_R(\varepsilon)=\varepsilon^6 Q_3(\varepsilon),\qquad
 Q_3(\varepsilon)\longrightarrow h_3 M_3^2>0.
\]

A fatoração exata vale em uma vizinhança da origem, incluindo zero.
O quociente `E_R(epsilon)/epsilon⁶` tem o limite indicado no filtro
**perfurado** `nhdsWithin 0 {0}ᶜ`. Não foi feita divisão em zero.

Foi provada também uma margem inferior local:

\[
 E_R(\varepsilon)\ge\frac{h_3M_3^2}{2}\varepsilon^6.
\]

A vizinhança depende de `(n,c,a)`. O fator `1/2` expressa uma margem obtida
por continuidade; não modifica fonte, métrica, kernel ou normalização.
O setor `M1=M2=M3=0` permanece sem sinal decidido por este resultado.

## Proveniência

- Repositório de destino: `geometry-of-numbers`.
- Base: `ee02d8deaf46e9b26e771a76434de7ea1050128a`, merge do PR #10.
- Fonte externa somente consultada: `carry-self-adjoint-operator`,
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Os estados materiais, dressing, retorno global, TFVD, correções Green e
  fonte completada dos trabalhos anteriores permanecem sem alterações.

A resposta de partida continua sendo `r = carryMaterialNormalizedResponse`,
lida **depois** da síntese completada. O residual é literalmente

\[
 R(t,u)=\operatorname{Re}
 \left(\overline{r(t)}r(u)\operatorname{dslope}r_1(t,u)\right),
\]

com `r1 = carryMaterialReducedResponse`, conforme sua definição anterior.

O kernel e seu canal central já estavam identificados, no mesmo parâmetro
material real, pela comparação externa anterior. A nova declaração
`material_residual_centered_kernel` reaproveita essa identidade e sua
normalização para escrever, localmente e também nas diagonais,

\[
 R(t,u)=\operatorname{Re}\left(
 \operatorname{dslope}r(t,u)-\frac{A(t)A(u)}{h_0}\right),
 \qquad A(t)=\operatorname{dslope}r(0,t).
\]

A realidade da resposta no eixo real, das diferenças divididas e de seus
coeficientes é demonstrada. A notação complexa empacota as duas quadraturas
já existentes; nenhuma parte imaginária foi apagada por conveniência.

## Diferenças divididas da própria resposta

Definimos apenas os shifts de Taylor centrais da resposta já sintetizada:

\[
 T_0=r,\qquad T_{j+1}(t)=\operatorname{dslope}T_j(0,t).
\]

No código: `carryMaterialTaylorShift j`. A operação é a iteração da API de
`dslope` de Mathlib. Esses índices são analíticos; não representam profundidade
vertical, câmera, raio, índice material ou novo estado de Hilbert.

Esses `T_j` também **não são** as respostas `r_j` da cadeia de reduções
recíprocas. Não foi reconstruída ou substituída aquela cadeia.

A identidade elementar de reconstrução fornece

\[
 f(t)=f(0)+t\operatorname{dslope}f(0,t).
\]

Sua aplicação duas vezes dá a identidade polarizada exata

\[
 \operatorname{dslope}f(t,u)
 =\operatorname{dslope}f(0,u)+tT_2^f(t)
  +tu\operatorname{dslope}T_2^f(t,u),
\]

onde `T2^f = dslope (dslope f 0) 0`. Fora da diagonal, a prova usa a
identidade de diferenças; na diagonal, usa a regra de derivação da mesma
reconstrução, com diferenciabilidade escalar explícita. Assim, não se
presume uma extensão de quociente em denominador nulo.

Para coeficientes `d_i` cuja soma é zero, os dois termos de bordo cancelam
**após a soma completa**, dando

\[
 \sum_{i,j}d_id_j\operatorname{dslope}f(t_i,t_j)
 =\sum_{i,j}d_it_i d_jt_j
       \operatorname{dslope}T_2^f(t_i,t_j).
\]

É o teorema `carryScalar_finite_energy_shift`. Todos os pares ordenados,
inclusive coincidências, permanecem presentes.

## Fatoração completa, com a correção retida

A remoção do canal central original permite escrever exatamente

\[
 R(t,u)=\operatorname{Re}\left[
 tu\left(\operatorname{dslope}T_2(t,u)
              -\frac{T_2(t)T_2(u)}{h_0}\right)\right].
\]

Para `t_i=epsilon*a_i`, o primeiro cancelamento é
`sum c_i*t_i=epsilon*M1=0`. A identidade de energia desloca `T2` para `T4`.
O segundo é `sum c_i*t_i²=epsilon²*M2=0`, deslocando `T4` para `T6`.

A correção central não desaparece: como `T2(0)=T4(0)=0`,

\[
 \sum_i c_it_iT_2(t_i)=\varepsilon^4 S_4(\varepsilon),\qquad
 S_4(\varepsilon)=\sum_i c_i a_i^4 T_5(\varepsilon a_i).
\]

Logo a identidade completa é

\[
 \boxed{
 E_R(\varepsilon)=\varepsilon^6
   \sum_{i,j}c_ic_ja_i^3a_j^3
      \operatorname{Re}\operatorname{dslope}T_6
        (\varepsilon a_i,\varepsilon a_j)
 -\frac{\varepsilon^8}{h_0}|S_4(\varepsilon)|^2.}
\]

A segunda parcela é uma correção real com sinal negativo. Ela foi
**mantida**, não descartada ou renormalizada. A definição
`carryMaterialThirdNullEnergy` é precisamente a expressão entre colchetes
após fatorar `epsilon⁶`. Seu primeiro termo não é definido como um Gram
positivo nem recebe sinal por hipótese.

Isso contabiliza a energia total, incluindo contribuições que, em uma
extração por canais, reaparecem em jets superiores de canais anteriores.
O coeficiente não foi confundido com apenas a próxima escala recíproca.

## Regularidade e calibração pela fonte

As novas declarações `material_taylor_shift_germ`,
`material_taylor_shift_center` e `material_taylor_shift_hasDerivAt_zero`
reutilizam `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope` e a
identificação já provada dos jets canônicos. Para todo `j`, fornecem a
regularidade dos shifts da **mesma** resposta analítica da fonte.

Em particular:

\[
 T_2(0)=T_4(0)=T_6(0)=0,\qquad T_6'(0)=h_3.
\]

`material_taylor_shift_regular` fornece diferenciabilidade local;
`material_taylor_shift_deriv_continuous` fornece continuidade da derivada
no centro. A ferramenta anterior `carryReal_scaledSlope_continuous`
trata também direções iguais no limite da diferença dividida.

A síntese `S4` é contínua; sua correção em `Q3` tem fator `epsilon²` e tende
a zero. A soma Green completa tende a

\[
 h_3\sum_{i,j}c_ic_ja_i^3a_j^3=h_3M_3^2.
\]

Nenhuma nova derivada forte do estado global em Hilbert foi postulada.

O sinal usa somente certificados já existentes da fonte:

\[
 h_1>0,\qquad h_1h_3-h_2^2>0
 \quad\Longrightarrow\quad h_3>0.
\]

Essa última consequência foi formalizada em `material_moment_three_pos`.
Não foi preciso descobrir outro discriminante ou ajustar uma constante.

## Regressões e status

O canário do PR #10, `c=(3,-3,1)` e `a=(1,2,3)`, tem
`M1=M2=0` e `M3=6`. Agora sua positividade local é demonstrada, e
`Q3(epsilon)` tende a `36*h3>0`.

Uma regressão separada verifica que `M3=0` produz coeficiente central zero.
Ela não declara energia identicamente nula nem sinal do próximo resto.
As regressões anteriores de 72, duas quadraturas, relógio, dressing,
retorno global e quatro cruzamentos Green/retorno foram preservadas.

| Status | Resultado |
| --- | --- |
| **Provado em Lean** | Identidade polarizada de shift e seu transporte para somas finitas com coeficientes de soma zero. |
| **Provado em Lean** | Regularidade e coeficientes dos shifts centrais da mesma fonte material. |
| **Provado em Lean** | Fatoração de sexta ordem, com correção central completa de ordem oito. |
| **Provado em Lean** | Limite do quociente no filtro perfurado e do prolongamento contínuo `Q3`. |
| **Provado em Lean** | Positividade e margem local por família fixa com `M1=M2=0,M3!=0`. |
| **Com hipóteses explícitas** | A infraestrutura de Analysis recebe a identidade e regularidade; a comparação externa verifica essas hipóteses para a fonte efetiva. |
| **Aberto** | Sinal no setor `M1=M2=M3=0`, controle uniforme em todas as famílias e positividade global do residual. |

Há **29 teoremas novos e 3 definições**, com **32 roots públicos** auditados
transitivamente por tipos e corpos. Os únicos axiomas admitidos nesta camada
analítica são os usuais `propext`, `Classical.choice`, `Quot.sound`.
Foundation e Geometry mantêm auditorias separadas e seus contratos anteriores.
Sem novos axiomas, `sorry`, `admit` ou escapes de confiança.

O build focado e o completo usam `--wfail`; a comparação externa e as
regressões tratam warnings como erros. Comandos, logs, fingerprints dos
roots e proveniência estão em `research/material-third-null-sector/`.

A próxima obrigação matemática é controlar o setor com três momentos
cancelados, conservando a mesma correção e seus cruzamentos. Esta rodada
não constrói outro operador, não fornece realização positiva global nem
identifica um novo Gram físico com todos os momentos canônicos.
