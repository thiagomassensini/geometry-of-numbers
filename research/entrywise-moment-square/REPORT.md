# Teste literal dos momentos elevados ao quadrado

## Resultado e alcance

**STOP / NO-GO para a transformação literal `g(n)=h(n)^2` como antecipação
exata de `J_N^(-1/2)` no mesmo procedimento finito.** A incompatibilidade já
ocorre na seção de ordem 1 dos momentos canônicos originais. Ela foi provada
no Lean, incluindo a independência em relação à escolha de whitening.

Isso não exclui uma operação de alturas definida independentemente pela
geometria completa. Tampouco é um teorema de impossibilidade para qualquer
construção alternativa com limites próprios. O resultado refuta a identidade
finita exata proposta; não afirma que um desacordo em ordem 1, sozinho,
refutaria todo possível teorema espectral assintótico.

Não houve mudança na fonte, na métrica, nos estados, nas amplitudes, nas
câmeras, no dressing ou nos momentos canônicos. `squaredMoments h` designa
uma candidata separada, investigada a pedido explícito do usuário.

Base: `a5ed1d73b643cc4b24549b3ee3cfe10a5b29a59b`, PR #50.
Branch: `agent/entrywise-moment-square`. Dependência de publicação: PR #50.
`main` local, `origin/main` e a consulta direta ao remoto permaneceram em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Nenhum merge automático.

## A — O que já estava demonstrado

1. `IsLogDerivativeMomentSequence.unique`, em
   `GeometryOfNumbers/Analysis/LogarithmicMomentHankel.lean`: uma característica
   completada fixa, com coeficiente central não nulo, determina uma única
   sequência de momentos logarítmicos.
2. `hankelGram`, `shiftedHankel`, `FiniteGramWhitening` e
   `finiteJacobiSection`: as duas formas são `G(i,j)=h(i+j)` e
   `K(i,j)=h(i+j+1)`, e a seção transportada é `B K Bᵀ`, com `B G Bᵀ=I`.
3. `finiteHeightOperator` e `finiteHeightOperator_charpoly`, em
   `GeometryOfNumbers/Analysis/FiniteHeightOperator.lean`: o operador atual
   aplica `x ↦ 1/sqrt(x)` aos autovalores positivos da Jacobi finita.
4. `CarrySixthOdd.mem_compactMomentBox`: intervalos racionais já certificados
   para os momentos da fonte original, não uma nova sequência. Só os casos
   `n=0,1` são usados na testemunha desta investigação.
5. A PR #41 separa eliminação algébrica e existência de norma positiva. Esse
   resultado permanece intacto: a candidata foi testada sem interpretar uma
   fatoração como prova da origem física de seus coeficientes.

A seleção fundacional do expoente de meia escala não foi modificada nem
utilizada como premissa de uma identificação espectral ainda não provada.

## B — O que foi demonstrado agora

### 1. As matrizes candidatas são produtos de Hadamard

Para `g(n)=h(n)^2`, os teoremas `hankel_square` e `shifted_square` provam:

\[
G_N(g)=G_N(h)\odot G_N(h),\qquad
K_N(g)=K_N(h)\odot K_N(h).
\]

O produto é entrada a entrada. Não é o produto matricial `G_N^2`, nem a
aplicação de cálculo funcional a `J_N`.

`squared_psd_of_psd` e `squared_shifted_psd_of_psd` reutilizam o teorema de
Schur de Mathlib. Sua hipótese é a positividade da matriz original: esses
lemas não descarregam a obrigação canônica de positividade.

### 2. Obstrução exata em ordem 1

O teorema `actual_singleton_section` prova, para **qualquer** whitening real
exato e `h(0) ≠ 0`:

\[
J_1(h)=\left[\frac{h_1}{h_0}\right].
\]

Assim, a escolha de uma fatoração ou a reorganização das coordenadas não
altera esse autovalor. `singleton_square` prova:

\[
\lambda_1(g)=\frac{h_1^2}{h_0^2}=\lambda_1(h)^2.
\]

Por outro lado, a altura original é `t_1(h)=lambda_1(h)^(-1/2)`.
`singleton_square_not_height` prova que, se `0<h_1<h_0`, então

\[
\boxed{\lambda_1(g)<1<t_1(h).}
\]

`native_first_pair` verifica essas hipóteses para a sequência nativa, pelas
caixas de fonte preexistentes. `native_squared_eigenvalue_not_height` aplica
a obstrução à fonte original. Não recebe autovalores ou alturas como entradas.

Se ainda aplicarmos a transformação de alturas à nova Jacobi, em ordem 1,
`singleton_squared_height` prova:

\[
t_1(g)=\lambda_1(h)^{-1}=t_1(h)^2.
\]

**Essa última identidade é de ordem 1.** Não foi extrapolada para as seções
maiores. `singleton_mass_cancels` também mostra que um fator de massa global
não corrige a discrepância; nenhum fator foi ajustado nos testes.

### 3. A sequência original deixa de ser preservada

`native_squared_mass_changed` prova `h_0^2<h_0` na fonte canônica. Já no
coeficiente central, a sequência foi alterada.

`square_changes_logarithmic_sequence` prova, genericamente: se a característica
tem termo central não nulo, `h` satisfaz sua recorrência logarítmica e
`0<h_0<1`, então `h^2` não satisfaz a mesma recorrência. O argumento usa a
unicidade original, não uma caracterização por zeros.

### 4. O significado algébrico do quadrado

`finite_product_moments` prova, sem hipótese de positividade dos pesos:

\[
\left(\sum_a w_a x_a^n\right)^2
=\sum_{a,b}w_aw_b(x_ax_b)^n.
\]

Portanto, quando tal representação existe, elevar o momento ao quadrado
introduz produtos de dois índices independentes. A transformação não é
`x ↦ x^(-1/2)`. Esta é uma identidade algébrica genérica: não se presumiu
uma representação positiva para os momentos canônicos.

`paired_feature` prova a versão de Gram em coordenadas finitas:

\[
\langle u,v\rangle^2
=\sum_{a,b}(u_au_b)(v_av_b).
\]

Se uma Gram física já for conhecida, seu quadrado corresponde a uma família
de pares de coordenadas. Isso conserva todos os termos dessa nova expressão,
mas não demonstra que ela seja o pareamento bilinear original.

### 5. Experimento com os arquivos entregues pelo usuário

`experiment.py` lê os JSON de ordens 4 e 6 sem executar o script de geração.
Não calcula zeta, theta, zeros ou novos momentos. Os decimais de 28 algarismos
significativos são tratados como racionais exatos.

Os pivôs de `G` e `K`, originais e quadrados, foram calculados por eliminação
racional exata nas seções 1, 2 e na ordem completa de cada arquivo. Todos
foram positivos **para os decimais armazenados**. Isso não é um certificado
de intervalos para os integrais originais.

Os espectros foram avaliados a 100 e 160 casas de trabalho; a concordância
testada excedeu 45 casas absolutas. Aumentar a precisão de trabalho não
acrescenta dígitos aos dados de entrada. Resultados arredondados:

| Ordem | Autovalores de `J(g)`, mínimo e máximo | Alturas de `T(h)`, mínimo e máximo |
| --- | --- | --- |
| 1 | `2,58841658168e-6` | `24,9311009175` |
| 4 | `2,00485101570e-7` a `2,50487754302e-5` | `14,1350958352` a `110,188379772` |
| 6 | `7,97884290529e-8` a `2,50524682206e-5` | `14,1347251821` a `182,336065880` |

Em ordem 1, o autovalor original é aproximadamente `0,00160885567460`.
Seu quadrado é aproximadamente `0,00000258841658168`. O alvo solicitado,
a altura original, é aproximadamente `24,9311009175`.

## C — O que foi refutado

1. **Antecipar exatamente a raiz inversa mediante `h_n ↦ h_n^2`**, mantendo
   as definições de Hankel, whitening e Jacobi: a obstrução nativa em ordem 1
   independe da fatoração escolhida.
2. **Obter positividade apenas por quadrar os momentos:** para
   `h=(1,2,1,...)`, a seção quadrada é `[[1,4],[4,1]]`. Na direção `(1,-1)`
   sua forma vale `-6`. `squared_bad_quadratic` e `squared_bad_not_psd`
   certificam esse contraexemplo.
3. **Inferir positividade da forma original a partir da forma quadrada:**
   para `h=(1,1,-2,...)`, a seção original tem uma direção de valor `-2`,
   enquanto a seção quadrada `[[1,1],[1,4]]` é positiva semidefinida.
   `masked_original_not_psd` e `masked_square_psd` provam as duas afirmações.

Os contraexemplos são controles algébricos, não substitutos da fonte Carry.
Nenhum refuta a geometria original ou suas realizações finitas certificadas.

## D — O que permanece aberto e o que foi validado

A identidade física completa `h_(i+j)=<V_i,V_j>` continua aberta em toda
ordem, assim como sua versão deslocada. Os novos teoremas não assumem essa
identidade para declará-la demonstrada.

Também permanece aberta uma construção física independente cuja operação
seja diretamente a altura. Nenhum novo operador foi introduzido para ajustar
os resultados. Uma igualdade entre uma compressão desse eventual operador
e `J_N^(-1/2)` exigiria prova própria; cálculo funcional e compressão não
comutam em geral.

Foram acrescentados **21 teoremas e 4 definições**, em dois módulos de
pesquisa, sem alterar os módulos históricos. `Audit.lean` imprime os axiomas
de todas as 25 raízes e percorre transitivamente tipos e corpos:

- `EntrywiseSquare`: 22 raízes, 1.529 constantes na dependência transitiva.
- `NativeWitness`: 3 raízes, 5.058 constantes na dependência transitiva.
- Apenas `propext`, `Classical.choice`, `Quot.sound`; nenhum axioma novo.
- A auditoria também rejeita dependências das positividades H6, K6, H7,
  da energia estrita de seis fontes e da não negatividade geral do defeito
  de retorno. Nenhuma delas foi necessária à nova obstrução.

Os registros de `evidence/checks.json` documentam 12 verificações: os três
módulos Lean com warnings tratados como erros; o experimento; o build focado
e `lake build --wfail`; auditorias de Foundation, Geometry e Analysis;
geração da auditoria e verificações de preservação/diff.

Os arquivos não rastreados do operador, seus hashes, os pins e as branches
anteriores foram preservados. Nenhuma worktree foi criada ou removida.

## E — Próximo passo mínimo

Há duas operações distintas a testar na continuação:

1. Para obter positividade dos momentos originais, demonstrar o pareamento
   físico em dois argumentos independentes, com bordo, retorno e correções:
   `h_(i+j)=<V_i,V_j>`. Quadrar os coeficientes não elimina essa obrigação.
2. Para antecipar uma transformação espectral, identificar uma operação já
   presente na síntese cuja ação sobre o parâmetro seja efetivamente
   `x ↦ x^(-1/2)`, com seus domínios, e provar o transporte do readout.
   Não basta uma lei de homogeneidade com o mesmo expoente, e não basta
   definir essa operação a posteriori por `J^(-1/2)`.

A fundação de escala permanece anterior a essas duas questões. A conclusão
atual é exata e limitada: **o quadrado de cada momento não realiza a mudança
de variável solicitada.**

### Reprodução no host canônico

```bash
ssh llm
cd /home/thlinux/geometry-of-numbers
git switch agent/entrywise-moment-square
python3 research/entrywise-moment-square/validate.py
```

O script usa o Lean já configurado e o Python existente em
`/home/thlinux/miniforge3/bin/python` para `mpmath`, sem instalar dependências
ou modificar pins. Ele reutiliza os módulos históricos já compilados no
host, em particular `OddSourceBoxes`; não reivindica um bootstrap de todas
as investigações a partir de um clone sem caches. A reprodução desses
módulos anteriores segue os scripts das respectivas pastas de pesquisa.
Os dados, hashes, provas, comandos e logs acompanham a PR.
