# Fonte theta inteira: controle certificado dos modos omitidos

## Resultado

Provamos em Lean um controle quantitativo da contribuição dos modos omitidos
da **fonte theta original**, válido para qualquer polinômio já sintetizado e,
portanto, para todos os coeficientes da hierarquia dos PRs #12 e #13.
A cota é gaussiana no número de modos. Não usa localização de zeros,
representação por polos, positividade de Hankel ou uma hipótese de sinal.

**A positividade de toda a hierarquia continua aberta.** O avanço é descarregar
a estimativa do erro modal nesta representação e isolar a margem assinada
que ainda precisa ser demonstrada. Não obtivemos um novo sinal além de C1–C6.

Base geometry: `97a56861309b2f9b7fc7455f9521ecbc696908bf`.
Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
Metadados, pins e arquivos preservados: `research/material-theta-tail/provenance.json`.

## 1. A fonte é a mesma, inclusive no infinito

Reutilizamos literalmente os momentos canônicos, os polinômios `P_j`, a
síntese `Pi_k = carryMaterialNullThetaPolynomial k` e a identidade do PR #13:

\[
C_k=\int_0^\infty\Pi_k(u)\Phi(u)\,du,
\qquad \Phi=\texttt{completedNativeXiCosineKernel}.
\]

Em ordem par a síntese conserva os dois cruzamentos e a diagonal central:

\[
\Pi_{2p}=P_{2p}-2(h_p/h_0)P_p+(h_p/h_0)^2P_0.
\]

Os modos positivos `W_j = nativeThetaModeWeight j` já existiam no operador,
com \(\Phi=\sum_{j=0}^\infty W_j\). Seu índice zero corresponde ao primeiro
modo theta positivo; não corresponde a profundidade, câmera ou ordem de jet.
Definimos somente leituras finitas da série já existente:

\[
\Phi_K=\sum_{j<K}W_j,\quad T_K=\Phi-\Phi_K,
\quad I_K(P)=\int_0^\infty P(u)\Phi_K(u)\,du.
\]

**Os coeficientes de `Pi_k` continuam sendo os da fonte inteira.** Nunca
recalculamos os momentos ou esses polinômios usando uma fonte truncada.
O objeto original permanece a integral completa; `T_K` permanece no ledger.

## 2. Cota pontual demonstrada a partir dos modos efetivos

A fórmula literal dos modos fornece, para todo \(u\ge0\) e \(j\in\mathbb N\),

\[
\boxed{W_j(u)\le2e^{-3j^2-2j}W_0(u).}
\]

A prova conserva os coeficientes originais \(8\pi^2\) e \(12\pi\).
Usa \(e^{2u}\ge1\), \(\pi>3\), \((j+1)^4\le e^{4j}\) e uma cota
inferior do próprio primeiro modo. As constantes são estimativas; não
reescalam o estado, a fonte ou a métrica.

Somando a série infinita dos modos omitidos, Lean verifica

\[
\boxed{0\le T_K(u)\le q_K\Phi(u),\qquad
q_K=\frac{128}{63}e^{-3K^2-2K}.}
\]

O fator \(128/63\) vem de uma majorante geométrica: \(e^{-5}\le1/64\).
Também foi provado o corolário \(W_j\le2\,64^{-j}W_0\).
A cota é uniforme em \(u\), sem condição sobre o grau do polinômio integrado.

## 3. Identidade exata e erro integrado em toda ordem

Antes de estimar, conservamos o residual **assinado**:

\[
I(P)=I_K(P)+\int_0^\infty P(u)T_K(u)\,du.
\]

Definimos dois orçamentos de erro, sem introduzir métrica física:

\[
A(P)=\int_0^\infty |P(u)\Phi(u)|\,du,
\]

\[
B(P)=\sum_{d\in\operatorname{supp}P}|[u^d]P|
       \int_0^\infty u^d\Phi(u)\,du.
\]

Integrabilidade, convergência e as duas estimativas são verificadas:

\[
0\le A(P)\le B(P),\qquad
\boxed{|I(P)-I_K(P)|\le q_K A(P)\le q_K B(P).}
\]

O principal `I_K(P)` conserva seu sinal e seus cancelamentos. O valor absoluto
é aplicado somente ao orçamento do erro, depois de sintetizar `P`. Não
afirmamos monotonicidade das integrais assinadas em `K`.

Para a hierarquia efetiva, em **qualquer** ordem:

\[
\boxed{|C_k-I_K(\Pi_k)|\le q_K B(\Pi_k).}
\]

A regra prévia \(K(k)=k+2\) recebe uma cota formal explícita:

\[
|C_k-I_{k+2}(\Pi_k)|\le
\frac{128}{63}e^{-3(k+2)^2-2(k+2)}B(\Pi_k).
\]

Isso não prova que esse erro seja menor que `C_k` em toda ordem: ainda falta
uma margem inferior assinada. O tamanho de `B(Pi_k)` também importa.

## 4. A obrigação positiva ficou concreta

Lean prova o intervalo

\[
I_K(\Pi_k)-q_KB(\Pi_k)\le C_k\le
I_K(\Pi_k)+q_KB(\Pi_k).
\]

Como \(q_K\to0\) e \(I_K(P)\to I(P)\), obtivemos a equivalência exata

\[
\boxed{C_k>0\iff\exists K:\ I_K(\Pi_k)>q_KB(\Pi_k).}
\]

A consequência em toda ordem também está formalizada com os quantificadores
corretos: para cada `k>0` é necessário construir algum corte e sua margem.
Não provamos que um corte fixo funcione para todas as ordens, nem que
`K(k)=k+2` descarregue a margem. Não assumimos a própria desigualdade desejada
para anunciar existência de uma realização.

Se a margem for demonstrada para um `k`, o teorema novo alimenta diretamente
a positividade radial por família fixa do PR #12, mantendo o residual completo
e todos os pares ordenados. A vizinhança ainda pode depender da família.

**Primeira obrigação restante nesta rota:**

\[
\forall k\ge1:\quad
I_{K(k)}(\Pi_k)>\frac{128}{63}e^{-3K(k)^2-2K(k)}B(\Pi_k)
\]

para uma regra de corte e uma prova derivadas da fonte. A primeira ordem sem
certificado de sinal continua sendo `C7`, como no PR #13.

## 5. Relação com Green, polos e o pareamento físico

O PR #13 já identifica a mesma integral completa com a integral Green,
incluindo o controle de fluxo no infinito e os traços centrais. Como não
alteramos seu lado esquerdo, os novos intervalos controlam esse mesmo valor.
Não substituímos o peso Green por um kernel escolhido para ser positivo.

Esta é uma aproximação direta de `Phi`, diferente da aproximação de seu
**score logarítmico** por médias de modos. Não alegamos ter preenchido a
estimativa pendente daquele outro funcional em `NativeThetaAdaptiveBudget`.

A nova prova não depende das condições por polos do PR #14. Essas condições
permanecem uma rota suficiente alternativa, sem assumir uma representação
infinita por polos para estabelecer o controle aqui obtido.

Mesmo a positividade de todos os `C_k` não seria, por si, a positividade de
todo Gram, uma vizinhança comum de positividade do residual, a isometria física
com o carrier canônico ou o fechamento HP/RH. Esses gates permanecem distintos.

## 6. Diagnóstico numérico auxiliar

O script somente lê os coeficientes canônicos já preservados em `momentos`.
SHA256 da entrada:
`50bc111bc10174e406260a90fe8271ba3f6897c7467e3472822a0bee8d5d351a`.

Com 1100 dígitos de trabalho, reconstruímos os polinômios pela recorrência
original e calculamos `B(Pi_k)` nas ordens 1–255. Para `K=k+2`, o maior quociente
numérico orçamento/`|C_k|` foi aproximadamente `2.62410e-13`, na ordem 1.
Para o corte fixo exploratório `K=3`, o maior foi aproximadamente
`1.10182e-10`, na ordem 12.

Esses números testam a escala do orçamento perante os coeficientes já
armazenados. **Não calculam independentemente `I_K`, não são intervalos
certificados e não provam a margem nem o sinal em todas as ordens.** A
reconstrução do readout usa os mesmos dados de entrada, não uma validação
independente da integral theta. Nenhum valor numérico entrou nas provas Lean.

## 7. Status e validação

| Resultado | Status |
| --- | --- |
| Majorante gaussiana de cada modo original | **PROVADO em Lean** |
| Cota pontual do residual infinito, para todo corte | **PROVADO em Lean** |
| Identidade assinada, integrabilidade e erro integrado para todo polinômio | **PROVADO em Lean** |
| Erro para `Pi_k`, cruzamentos completos e corte `k+2`, em toda ordem | **PROVADO em Lean** |
| Critério de margem finita, necessário e suficiente por ordem | **PROVADO em Lean** |
| Positividade radial ao verificar a margem | **CONDICIONAL à margem explícita** |
| Positividade C1–C6 | **PROVADO anteriormente, preservado** |
| Comparação de orçamentos nas ordens 1–255 | **TESTE NUMÉRICO NÃO RIGOROSO** |
| Margem principal em toda ordem ou para corte fixo | **ABERTO** |
| Novo sinal C7, Gram global ou realização HP | **NÃO DEMONSTRADO** |

O código acrescenta 4 definições e 27 teoremas públicos no namespace
`CarryMaterialThetaTailComparison`, no arquivo externo
`research/material-central-calibration/CanonicalComparison.lean`.
O conteúdo anterior foi preservado literalmente após um import adicional.
O build padrão da biblioteca não compila esse arquivo externo: sua auditoria
separada é indispensável.

Validações no servidor `llm`:

- Build focado `lake build GeometryOfNumbers.Analysis.CarryMaterialNullHierarchy --wfail`.
- Build completo `lake build --wfail`: **8834 jobs**.
- Auditorias Foundation, Geometry e Analysis, com seus footprints distintos.
- Comparação externa com `warningAsError`, pins compartilhados e HEAD do operador conferidos.
- Guardas transitivas nos tipos e corpos e `#print axioms` para as 31 raízes novas:
  somente `propext`, `Classical.choice` e `Quot.sound`.
- Regressões de corte vazio, primeiro modo, orçamento em zero, cruzamento par
  literal e compatibilidade com os sinais já provados até seis.
- Todos os testes antigos do arquivo de comparação preservados e recompilados.
- Sem `sorry`, `admit`, axiomas novos, mudanças de fonte, pins ou normalizações.

Fontes reutilizadas no operador: `NativeThetaModeScore.lean`,
`NativeThetaAdaptivePrefix.lean`, `NativeSourceThetaMomentPolynomials.lean`,
`NativeSourceThetaGreenTransport.lean`. A biblioteca geometry não ganhou
dependência nova desse repositório.

Evidências e script reproduzível ficam em `research/material-theta-tail/`.
