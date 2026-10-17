# Residual normalizado: extração real e positividade de famílias fixas

## Resultado da tentativa

**A realização positiva completa do residual ainda não foi demonstrada.**
Esta rodada prova um sinal novo da fonte para famílias finitas fixas,
identifica exatamente a força da obrigação global e constrói os mapas de
extração ortogonal quando uma realização positiva completa for fornecida.
Esses mapas condicionais não são apresentados como prova de existência.

Não foram alterados fonte, métrica, dressing, amplitude ou normalização.
Não se construíram estados por fatoração do Hankel ou do Gram pretendido.
Não se introduziram contramodelos com campos livres.

Base de geometria: `12da1bf7d48881a608a3df545fd561e766233ecb`, merge do PR #8.
Consulta do operador: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, sem alterações.
O inventário de declarações, hashes, pins e proveniência está em
`research/material-residual-realization/provenance.json`.

## 1. Os kernels comparados são os da mesma fonte

Sejam `r0 = carryMaterialNormalizedResponse`,
`r1 = carryMaterialReducedResponse`, `A(t)=dslope r0 0 t` e
`alpha = carryMaterialResponseScale = h0 > 0`. Usamos:

\[
 \phi(t)=\operatorname{Re}\frac{A(t)}{\sqrt\alpha},\quad
 K(t,u)=\operatorname{Re}\operatorname{dslope}r_0(t,u),
\]

\[
 R(t,u)=\operatorname{Re}\left(
 \overline{r_0(t)}r_0(u)\operatorname{dslope}r_1(t,u)\right).
\]

As partes reais não descartam uma quadratura: foram provadas as identidades
literais entre a inclusão real desses três objetos e suas expressões
complexas completas no eixo real. A conjugação comuta com a diferença
dividida real, inclusive na diagonal, por sua linearidade contínua real.
Isto não afirma holomorfia do estado material global.

A fonte continua sendo o estado completado `Y=(semente,gradiente,beta)` dos
PRs anteriores. `r0` é o readout do seu par valor–companheira, com relógio e
`D'`; o retorno global e os retornos TFVD não foram identificados entre si.
A identificação escalar já demonstrada com a fonte canônica é reutilizada.
Não se identifica tempo material com outro operador.

O PR #6 fornece uma vizinhança aberta real `U` de zero onde, para todos os
dois argumentos independentes, incluindo a diagonal:

\[
 K(t,u)=\phi(t)\phi(u)+R(t,u).
\]

Também se verificam `phi(0)=sqrt(alpha)>0` e
`R(0,u)=R(t,0)=0`. O PR #8 fornece o balanço Green completo correspondente,
com seu complemento e fatores explícitos. Nenhum desses termos foi
silenciosamente anulado nesta rodada.

## 2. Positividade nova: cada família fixa que não cancela o primeiro momento

Da própria resposta, `r0(0)=0`, segue a fatoração exata
`r0(t)=t A(t)`, sem divisão por `t`. Definimos o núcleo auxiliar, ainda sem
lhe atribuir qualquer sinal global:

\[
 C(t,u)=\operatorname{Re}\left(
 \overline{A(t)}A(u)\operatorname{dslope}r_1(t,u)\right),
 \qquad R(t,u)=tu\,C(t,u).
\]

Os coeficientes certificados da fonte dão

\[
 A(0)=h_0,\qquad r_1'(0)=h_1/h_0^2,\qquad C(0,0)=h_1>0.
\]

Essa calibração é exata; o sinal de `h1` vem do teorema theta anterior,
não de uma constante ajustada para esta construção.

Fixemos qualquer número finito de observações `n`, coeficientes reais `c_i`
e direções materiais reais `a_i`. Para qualquer escala real `e`, provou-se:

\[
 E_R(e):=\sum_{i,j}c_ic_jR(ea_i,ea_j)=e^2 Q_{c,a}(e),
\]

\[
 Q_{c,a}(e)=\sum_{i,j}c_ic_j a_i a_j C(ea_i,ea_j),\qquad
 \lim_{e\to0}Q_{c,a}(e)=h_1\left(\sum_i c_i a_i\right)^2.
\]

Todos os cruzamentos ordenados são somados antes de concluir o sinal.
A continuidade exigida da diferença dividida em pares rescalados foi
provada separando direções iguais e distintas; utiliza apenas a
regularidade da resposta escalar e de sua derivada já disponível.
Não se postulou uma segunda derivada forte do estado em Hilbert.

Consequentemente, se `sum c_i*a_i != 0`, existe uma vizinhança de escala
onde `E_R(e)>0` para toda escala não nula. O teorema aplica-se a qualquer
família fixa, com qualquer tamanho finito.

**A ordem dos quantificadores importa:** a vizinhança pode depender de
`n`, `c` e `a`. Não se obteve uma única vizinhança positiva simultaneamente
para todos os vetores de coeficientes. Se o primeiro momento cancela,
`Q(0)=0` e esta prova não decide o sinal. Logo, isso não é positividade do
kernel inteiro nem realização de Gram para todas as famílias.

O teste cruzado concreto `c=(1,-1)`, `a=(1,-1)` tem primeiro momento `2`:
sua energia é positiva em escalas pequenas, com ambas as fontes fora do
centro. O teste `c=(1,1)`, `a=(1,-1)` cancela o termo principal; ele permanece
fora do resultado de sinal. Essa degenerescência é registrada, não apagada.

## 3. A obrigação global é exatamente equivalente à original

Escreva `E_K(c,t)=sum c_i*c_j*K(t_i,t_j)` e analogamente `E_R`.
A identidade da fonte dá:

\[
 E_K(c,t)=\left(\sum_i c_i\phi(t_i)\right)^2+E_R(c,t).
\]

Agora acrescentamos **a mesma fonte no parâmetro central**, com coeficiente

\[
 c_*=-\frac{\sum_i c_i\phi(t_i)}{\phi(0)}.
\]

Provou-se para qualquer família finita em `U`:

\[
 \boxed{E_K((c_*,c),(0,t))=E_R(c,t).}
\]

Esse é um teste real da fonte, não uma escolha de campo independente.
O canal central cancela exatamente na síntese. Os termos residuais que
contêm a observação zero são zero por `r0(0)=0`; os demais cruzamentos
permanecem íntegros.

Portanto, em qualquer subconjunto `V` de `U` que contenha zero:

\[
 [\text{todos os testes finitos de }K\text{ são não negativos em }V]
 \iff
 [\text{todos os testes finitos de }R\text{ são não negativos em }V].
\]

Esta equivalência é incondicional para a fonte atual. Ela não prova nenhum
dos dois sinais gerais. Mostra por que retirar um canal positivo não torna
a obrigação de positividade de todas as famílias automaticamente mais fraca.

## 4. Qual seria a realização geométrica positiva?

Suponha que seja efetivamente fornecida uma realização do kernel **completo**
no produto interno original de algum Hilbert real `H`:
`<v(t),v(u)>=K(t,u)`. Então a aplicação concreta

\[
 z(t)=v(t)-\frac{\phi(t)}{\phi(0)}v(0)
\]

satisfaz exatamente `<z(t),z(u)>=R(t,u)`, com reconstrução de `v(t)` pelo
canal central e `z(t)`. Os coeficientes da projeção são impostos pelos
pareamentos centrais existentes, não escolhidos para fabricar o sinal.

Reciprocamente, se houver uma realização `z` de `R`, o mapa
`t -> (phi(t),z(t))`, no produto Hilbert real usual, realiza `K`.
Ambos os transportes foram formalizados. **Nenhum deles fornece o `v` ou o
`z` que falta.** O código mantém a hipótese de realização exposta no tipo.
Não se usa uma construção abstrata a partir do Gram-alvo como substituto
da proveniência física.

## 5. O canal central bruto precisa continuar separado

Qualquer realização positiva de `R` deve ter `z(0)=0`, pois `R(0,0)=0`.
Mas o par material reduzido bruto do PR #8 tem

\[
 W_0=(P_0,0),\qquad P_0\ne0.
\]

Foi formalizada a obstrução específica: uma realização de `R` não pode
preservar simultaneamente a energia integral desse par bruto no centro.
Isto não proíbe uma realização com o centro conservado em um canal auxiliar,
nem identifica automaticamente um quociente ou projeção com o kernel.
O no-go do primeiro jet da projeção literal do PR #7 também permanece.

A perda para o readout, a retirada ortogonal e a conservação do estado
completo são operações diferentes; esta comparação não as iguala.

## 6. Caminhos consultados e a primeira lacuna

A auditoria também reutilizou/consultou:

- `NativeCompletedSourcePositiveReduction[Jet]`: primeira escala, readout
  canônico, regularidade e recorrência da fonte;
- `NativeCompletedSourceTwoPositiveChannels`, `ThirdPositiveChannel`,
  `FourthPositiveChannel`, `ReductionChain`: prefixos positivos certificados
  com residual terminal explícito; não fornecem sinal em todas as etapas;
- `NativeSourceSchurThetaMasses`: massas theta positivas e negativas da fonte;
  os termos negativos ímpares são realmente presentes, e sua dominação geral
  permanece uma obrigação, não uma consequência de theta ser positiva;
- PR #8: forma Green completa, dressing derivativo, complemento nulo para o
  readout e transporte sem perda no centro.

**Fonte disponível → transformação existente → destino → igualdade exigida
→ dado ainda ausente:**

`Y(t)` com relógio/retorno/dressing → par completo e redução do PR #8 →
balanço Green normalizado e kernel `K` → realização de seus pareamentos no
carrier físico → extração ortogonal `z` e kernel residual `R` → **falta a
identidade positiva de pareamento de um carrier físico concreto, fornecendo
o sinal para todas as combinações finitas, sobretudo as que cancelam o termo principal.**

O novo teste central torna essa última obrigação equivalente para `K` e
`R`; não a esconde numa definição de operador ou de métrica. O resultado
assintótico fornece um sinal verdadeiro em uma classe explícita de testes,
sem fechar essa equivalência por hipótese. Uma prova abstrata do sinal,
isoladamente, também não identifica um mapa a partir do carrier físico `Y`.

## Status

| Status | Resultado |
|---|---|
| **Provado em Lean** | Fatoração exata `R(t,u)=tu C(t,u)` e calibração `C(0,0)=h1>0`. |
| **Provado em Lean** | Limite da energia rescalada com todos os cruzamentos e positividade de cada família fixa com primeiro momento não nulo. |
| **Provado em Lean** | Teste central aumentado e equivalência dos sinais finitos gerais de `K` e `R`. |
| **Provado em Lean** | A representação real recupera literalmente as expressões complexas no eixo real. |
| **Condicional** | Extração ortogonal e montagem por soma Hilbert, quando uma realização do kernel de entrada for fornecida. |
| **Obstruído para esta candidata** | Preservar a energia do par reduzido bruto no centro como energia do residual normalizado. |
| **Aberto** | Sinal nas direções que cancelam o termo principal; vizinhança uniforme para todos os testes; realização positiva completa com proveniência física. |

Builds focado e completo com `--wfail`, auditorias das três zonas,
comparação externa com warnings como erros, footprints transitivos e
regressões estão registrados em `research/material-residual-realization/`.
Não há novos axiomas ou provas admitidas. Foundation não foi modificada;
a análise permite apenas os axiomas padrão já registrados pelo projeto.

Foram acrescentados 15 teoremas e 11 definições públicas no módulo
`CarryMaterialResidualPositiveTransport.lean`, mais 19 teoremas na comparação
externa. Os 45 novos roots têm guards transitivos e `#print axioms`.
Os teoremas de tentativa e seus limites estão listados em `new-roots.json`;
`footprints.json` registra os axiomas efetivamente encontrados.
