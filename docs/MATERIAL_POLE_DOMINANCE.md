# Uma rota quantitativa para a obrigação theta em toda ordem

## Resultado e limite

Foi obtido um critério quantitativo que implica a obrigação das massas theta
**em todas as ordens**, com margem explícita e sem impor sinal às potências
superiores da cauda complexa. A fonte efetiva fornece incondicionalmente as
duas cotas baixas usadas no argumento.

**A obrigação original ainda não está provada incondicionalmente.** Não foi
construída a expansão em polos da característica nativa que instancia o
critério. Os novos teoremas conservam essa igualdade como hipótese explícita.
Não foi produzido um Gram positivo nem uma realização física do residual.

Base: `geometry-of-numbers` em `b76a061766537e04e7bffc405f3f6216b92f077f`,
PR #13. Operador consultado em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
Os pins e módulos de origem estão no inventário desta investigação.

## 1. O resto é definido a partir da própria fonte

Escreva \(h_n\) para `canonicalCompletedNativeLogDerivativeMoment n` e
\(C_k\) para `carryMaterialNullCoefficient k`, já identificados com a
resposta material sintetizada nas rodadas anteriores. Para um parâmetro
real \(a\), o novo ledger define somente

\[
e_n(a)=h_n-a^{n+1}.
\]

Essa subtração não identifica \(a\) com um polo e não altera o estado,
a fonte, o kernel, os pesos ou sua normalização. Ela registra uma
decomposição do coeficiente existente.

O ledger `AllOrderLogJet.nativeMoment_eq_finiteFactors_add_remainder` já
existente foi localizado e reutilizado, sem reprovar sua regra de fatores
finitos. Sua especialização fornece uma identificação **incondicional**:

\[
\boxed{e_n(a)=-\frac1{n!}\left.
 \partial_u^n\operatorname{logDeriv}
 \left(\frac{\chi(u)}{1-au}\right)\right|_{u=0},}
\]

como igualdade complexa, com o membro esquerdo real. Aqui
\(\chi=\texttt{completedNativeEvenCharacteristic}\) é o germe já existente
na variável altura ao quadrado, não tempo material. Portanto o resto tem
uma função de origem concreta. Não foi definido a partir de um Gram-alvo.

Na ordem par, Lean verifica a igualdade exata

\[
\boxed{C_{2p}=a^{2p+1}\left(1-\frac a{h_0}\right)+e_{2p}
       -\frac{2a^{p+1}e_p}{h_0}-\frac{e_p^2}{h_0}.}
\]

Os dois cruzamentos ordenados entre a parcela principal e o resto estão
no termo de fator 2. O quadrado do resto também permanece.
Na ordem ímpar, \(C_{2p+1}=a^{2p+2}+e_{2p+1}\), pela calibração anterior.

A ligação formal com a válvula existente é exata. Se \(\Phi\) é a série
formal da característica par normalizada e \(V\) é a válvula original:

\[
\boxed{\Phi(X)=(1-aX)V\!\left(-\sum_{n\ge0}e_n(a)X^n\right).}
\]

Essa identidade vale para todo \(a\), inclusive valores que não vêm de
zero algum da fonte. **Uma fatoração formal não prova a existência de um
polo analítico:** a série do segundo fator pode não convergir até \(1/a\).
Nenhum novo carrier foi definido por essa fatoração.

## 2. Dois controles efetivos da fonte

Reaproveitando as integrais theta e os limites de momentos já certificados,
Lean prova sem hipótese de polos:

\[
\boxed{h_0\ge\frac1{50},\qquad h_1\le\frac{19}{500000}.}
\]

O segundo limite usa as três integrais theta de ordens 0, 2 e 4 e a
identidade original

\[
h_1=\frac{\mu_1^2}{4\mu_0^2}-\frac{\mu_2}{12\mu_0},
\qquad \mu_j=\int_0^\infty u^{2j}\Phi_{\theta}(u)\,du.
\]

Não foi feita nova quadratura externa para provar essas cotas.

## 3. A estimativa que sustentaria todos os degraus

Suponha que um parâmetro da fonte satisfaça

\[
\frac{25}{5041}\le a\le\frac1{196}
\]

e que seu resto efetivo obedeça ao controle, para todo \(n\ge1\),

\[
\boxed{|e_n(a)|\le\frac35a^{n+1}
                      \left(\frac{51}{100}\right)^{n-1}.}\tag{T}
\]

Lean deduz, para todo \(k\ge1\),

\[
\boxed{C_k\ge\frac{71}{2500}a^{k+1}>0.}\tag{M}
\]

Na ordem par, conservando as correções do ledger:

\[
C_{2p}\ge a^{2p+1}\left[
  1-\frac35\frac{51}{100}-\frac{13}{50}\left(\frac85\right)^2
\right]=\frac{71}{2500}a^{2p+1}.
\]

Usa-se \(a/h_0\le13/50\), consequência das cotas acima. Na ordem ímpar,
a margem obtida é ainda maior, \((2/5)a^{2p+2}\).
Não se exige que \(e_n\) seja positivo.

O teorema é uma implicação quantitativa; **não foi provada a hipótese (T)
para um parâmetro identificado da fonte infinita**. Fatorar uma potência
na estimativa não muda a normalização dos estados. A margem decai,
compatível com o limite \(C_k\to0\) demonstrado no PR #13.

Um corolário formula a obrigação diretamente como cota uniforme dos jets
normalizados do quociente \(\chi(u)/(1-au)\). Ele usa a igualdade acima;
não exige escolher um campo ou um readout independente. A rota por polos
abaixo é um mecanismo possível para obter essa cota concreta.

## 4. Um mecanismo para controlar o resto sem supor seus sinais

O critério mais forte substitui (T) por um readout específico da fonte.
Considere candidatos complexos \(v_j\), não vetores de um novo Hilbert, com

\[
\sum_j|v_j|^2<\infty,\qquad |v_j|\le\frac1{400},\qquad
\Re(v_j^2)\ge\frac{99}{100}|v_j|^2.
\]

A igualdade ainda necessária é

\[
\boxed{h_n=a^{n+1}+\sum_j\Re(v_j^{n+1}),\qquad n\ge1.}\tag{P}
\]

**(P) está nos tipos como hipótese, não como uma estrutura cuja existência
foi anunciada.** A sequência \(h\) é a original, fixa; não se escolhe um
campo independente para substituir a fonte.

Lean prova a partir dessas premissas:

\[
\frac{99}{100}\sum_j|v_j|^2\le h_1-a^2,
\qquad \sum_j|v_j|^2\le\frac35a^2,
\]

\[
|e_n|\le\left(\sum_j|v_j|^2\right)(1/400)^{n-1}
\le\frac35a^{n+1}(51/100)^{n-1}.
\]

Logo, esse orçamento quadrático da cauda implica (T), depois (M), e por
fim a desigualdade theta \(M^-(\Pi_k)<M^+(\Pi_k)\) em toda ordem.
As potências complexas superiores podem ter partes reais negativas.
Elas são controladas em módulo, não removidas da soma.

## 5. A geometria concreta dos candidatos a polos

Há também um cálculo geométrico sem hipótese sobre os momentos. Para
\(\tau=x+iy\), Lean verifica

\[
x\ge20,\quad |y|\le\tfrac12,\quad v=\tau^{-2}
\quad\Longrightarrow\quad
|v|\le\tfrac1{400},\quad
\Re(v^2)\ge\tfrac{99}{100}|v|^2.
\]

O deslocamento imaginário é mantido. Não foi assumido que todos os polos
sejam reais. Se o primeiro parâmetro real for \(14\le t\le71/5\), então
\(a=t^{-2}\) cai no intervalo requerido. Um corolário tipado combina esses
dados com (P) e a somabilidade para obter a dominação theta em toda ordem.
O corolário não constrói os polos nem prova que enumeram a fonte.

## 6. A primeira ponte que permanece aberta

**Fonte disponível → transformação existente → destino → igualdade necessária:**

Característica completada nativa e seus coeficientes theta → recorrência
logarítmica, quociente analítico e válvula formal existentes → um primeiro polo real simples
e uma cauda de polos complexos com multiplicidades → identidade (P),
convergência absoluta e localização dos polos.

Uma maneira suficiente de justificar (P) é uma fatoração analítica
normalizada

\[
F(z)=F(0)e^{b z^2}(1-az^2)\prod_j(1-v_jz^2),
\]

com os parâmetros e multiplicidades corretos e sem um fator analítico
adicional que altere os coeficientes logarítmicos de índices n≥1. O termo
linear b modifica apenas h0, cuja cota é obtida diretamente da fonte. Um fator
\(\exp(G(z^2))\) introduziria a correção
\(-(n+1)[X^{n+1}]G\) em (P). Uma lista de zeros sem essa identificação
de produto não basta.

A literatura clássica sobre [superzetas de Voros](https://arxiv.org/abs/1403.4558)
é uma referência para essa expansão. A [proveniência dos dados da LMFDB](https://www.lmfdb.org/zeros/zeta/Source)
explica sua localização finita por aritmética intervalar e método de Turing.
Esses resultados externos **não foram importados como axiomas Lean** nem
usados para anunciar uma costura física. A origem aritmética do produto
interno e a identificação física/canônica continuam obrigações distintas.

## 7. Diagnóstico finito da própria fonte

Foi lido, sem modificação, o arquivo canônico preservado em `momentos`:
`native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json`.
O script encontra uma raiz do polinômio finito da característica, sem
fornecer um zero de zeta como entrada. Com 240 casas de trabalho:

- Grau do polinômio: 256; raiz em altura ao quadrado aproximadamente
  `199.7904548323868594633651859614`.
- Parâmetro finito \(a\) aproximadamente `0.005005244123594116078809401235`.
- Nas ordens 1 a 255, o maior quociente entre o resto calculado e o
  orçamento de (T) foi aproximadamente `0.806317`, na ordem 1.
- O menor \(C_k/a^{k+1}\) observado foi aproximadamente `0.672829`, na ordem 2.

É um **diagnóstico numérico finito não intervalar**. Não certifica a raiz
da fonte infinita, simplicidade, completude dos zeros, (P), a cauda além
dos dados ou a positividade em todas as ordens. O JSON registra essas
limitações e o hash da entrada. Não houve alteração no repositório `momentos`.

## 8. Status, código e validação

| Resultado | Status |
|---|---|
| Duas cotas baixas da fonte original | **PROVADO em Lean** |
| Ledger com todos os cruzamentos e deflação formal da válvula | **PROVADO em Lean** |
| Resto igual ao jet do quociente da característica original | **PROVADO em Lean, sem hipótese de polos** |
| Orçamento geométrico de \(\tau^{-2}\) na faixa indicada | **PROVADO em Lean** |
| (T) implica margem (M) em toda ordem | **PROVADO como implicação** |
| (P) e cauda separada implicam (T) e dominação theta em toda ordem | **PROVADO como implicação** |
| Teste de 255 ordens com a fonte preservada | **APENAS DIAGNÓSTICO NUMÉRICO** |
| Existência e identificação da expansão (P) da fonte original | **ABERTO no desenvolvimento formal** |
| Cota uniforme dos jets do quociente da fonte | **ABERTO; alvo direto equivalente à estimativa (T)** |
| Obrigação theta incondicional, Gram positivo global, realização física | **NÃO DEMONSTRADOS nesta etapa** |

O código fica no namespace `CarryMaterialPoleDominanceComparison` do arquivo
de comparação externa já existente. A biblioteca não recebe dependência do
operador; fonte, pins, métrica, amplitudes e normalizações são preservados.
O corpo anterior é preservado literalmente após dois imports. O PR aberto
#62 do operador foi consultado: sua ponte de profundidade conserva o
remainder de fatores finitos; ela não fornece a expansão infinita (P).

O build padrão da biblioteca e a checagem desse arquivo de pesquisa são
separados. As evidências registram ambos, as auditorias Foundation/Geometry/
Analysis, regressões e guardas transitivas de axiomas com `#print axioms`.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos na análise.
Os teoremas condicionais permanecem condicionais mesmo depois da auditoria.
