# Fonte nativa e fator positivo B*B — testes do kernel completo

**Resultado geral: PARTIAL.** A rota proposta foi formalizada para um fator limitado `B` já fornecido, sem raízes fracionárias. Três escolhas concretas foram confrontadas com a fonte original e excluídas para as identificações especificadas abaixo. A representação Gram positiva canônica em toda ordem permanece aberta. Nenhum desses NO-GOs demonstra impossibilidade de outra realização pela síntese Carry completada.

Base: `aac80d6699009f15de138aa3932b21ab3572ff42`, PR #49. Branch independente: `agent/native-positive-square-kernel`. Repositório consultado do operador: `bfeb10fd2425400fa38139903d12bf0599f02e53`. Os fontes novos ficam somente neste diretório de pesquisa de `geometry-of-numbers`. Não há alteração de fonte física, pesos, câmera, fases, métrica, dressing, completion ou pins. Sem merge automático.

## A — O que já estava demonstrado e foi reutilizado

`MomentGramPositivity.lean` e `ParityMomentGram.lean` já fornecem os consumidores corretos: uma igualdade efetiva entre todos os pareamentos de uma família física e o kernel canônico implica positividade semidefinida; independência legítima acrescenta a estrita. Esses consumidores não constroem a família canônica.

`SymmetricKrylovHankel.symmetricKrylov_inner_add` move potências através do produto interno. `firstColumn_of_symmetric_implies_hankelGram` precisa de uma primeira coluna identificada independentemente. Não tratamos essa hipótese como um resultado já obtido para qualquer operador geométrico.

Há também duas pontes anteriores no operador:

- `PositiveObservableNativeMomentBridge.positiveObservableMoment_eq_native_of_defect_zero` recebe a anulação do defeito de convolução nativo. Sua aplicação exige provar essa anulação para o operador e a fonte concretos.
- `CompletedNativeSignedGeneratorHerglotzGram.completedNativeLogDerivativeHerglotzKernel_eq_signedGeneratorGram` recebe um `CompletedNativeRealHPCarrierCertificate`. Esse certificado contém a representação de kernel desejada; não pode servir como origem incondicional dessa mesma representação.

`NativeCauchyLaguerreResolventDefect.characteristicKernel_sub_parityGram` já preserva dois defeitos diferentes: o da equação vetorial `X-z^2 A X=source` e o da característica `F'+2z*readout*F`. Uma Gram positiva auxiliar não os anula automaticamente. Reutilizamos esse diagnóstico, sem anunciar a identidade condicional antiga como uma solução nova.

Do lado físico foram inspecionados:

1. `c2GlobalGreenAnalysis`, seu Gram original `c2GlobalRestrictedGreenGram` e a cota inferior `1/2` de `c2GlobalGreenAnalysis_norm_sq_bounds`.
2. `physicalCauchyShift`, definido na closure das meias densidades Cauchy originais, e sua isometria/intertwiner `cauchyLaguerreIsometry`. Não é necessário pressupor que essa isometria seja sobrejetiva.
3. O retorno completado `radialReturnTransfer`, o defeito autoadjunto `radialReturnEnergyDefect = I-T* T` e suas duas portas de Jordan já existentes.
4. A fonte original, sua normalização projetiva e o limite polarizado `projectiveChiralDifferenceJet_pairing_tendsto_coefficient`.

As PRs #41/#48/#49 permanecem na linha: os momentos globais antecedem a ortogonalização algébrica, o orçamento completo é `P+Delta`, e a #49 extraiu seu termo de Euler mais o pareamento não linear. Nenhuma dessas identidades pressupõe que todo pivô seja positivo.

## B — O que foi demonstrado agora

### B.1 — A proposta B*B, com ambos os setores e sem raiz fracionária

Para um operador limitado real `B : H → K`, com os produtos internos originais, seja `A=B* B`. A leitura candidata é

\[
\mu_n(v)=\langle v,A^{n+1}v\rangle.
\]

`weightedMoment` apenas nomeia essa leitura de um operador fornecido; não substitui a sequência canônica `h` nem é usado para definir uma fonte geométrica.

`weighted_even_pairing` e `weighted_odd_pairing` provam, para dois índices independentes,

\[
\boxed{\mu_{i+j}(v)=\langle BA^iv,BA^jv\rangle_K,}
\qquad
\boxed{\mu_{i+j+1}(v)=\langle A^{i+1}v,A^{j+1}v\rangle_H.}
\]

Assim `weighted_even_gram` e `weighted_odd_gram` formalizam precisamente os dois setores da proposta, sem precisar construir `A^(1/2)`. As hipóteses locais são completude dos Hilberts reais e limitação de `B`. A demonstração reutiliza a simetria do adjoint square e o teorema Krylov existente. Não se estende automaticamente a operadores não limitados fora de seus domínios.

O passo não fornecido por esse teorema genérico é `h_n=mu_n(v)` para uma escolha física concreta. Os testes seguintes confrontam essa igualdade, em vez de a receber como premissa para anunciar positividade nativa.

### B.2 — Cálculo exato do quadrado do deslocamento físico Cauchy–Laguerre

Seja `B = physicalCauchyShift 1`, com o mesmo carrier físico e a mesma métrica do repositório. Seja `ell` a coordenada zero da isometria Cauchy–Laguerre original. `physical_shift_boundary` prova a identidade polarizada

\[
\boxed{\langle x,y\rangle-\langle Bx,By\rangle
       =\overline{\ell(x)}\ell(y).}
\]

Não foi considerada apenas a diagonal. `physical_shift_square` conclui, como igualdade de operadores,

\[
\boxed{A=B^*B=I-\ell^*\ell.}
\]

A coordenada `ell` é a observação já existente, não uma funcional escolhida para ajustar momentos. Definimos seu vetor de Riesz `e_partial=ell*(1)`, pertencente ao próprio espaço físico. `boundary_readout` prova `ell(e_partial)=||e_partial||^2`.

Escrevendo `a=||e_partial||^2`, `shiftSquare_twice` dá

\[
\boxed{A^2=(2-a)A-(1-a)I.}
\]

Consequentemente, `shift_moment_recurrence` prova para QUALQUER vetor físico `v`, sem calibrar sua massa,

\[
\boxed{\mu_{n+2}(v)=(2-a)\mu_{n+1}(v)-(1-a)\mu_n(v).}
\]

O cálculo não presume completude de uma base Laguerre nova ou um transporte do clock material. O índice do deslocamento aqui é o índice Laguerre do intertwiner existente; não se identifica com profundidade Carry, ordem temporal de jet ou parâmetro espectral.

### B.3 — As portas positivas efetivas da fonte completada

Os dois mapas existentes `radialReturnJordanPositivePort` e `radialReturnJordanNegativePort` são raízes positivas das partes de Jordan do MESMO defeito de retorno. Os aliases `positiveSourceJet` e `negativeSourceJet` aplicam esses mapas ao vetor incidente original, com `nativeSourceChiralJetInput`. Nenhum estado é reconstruído por Cholesky dos momentos desejados.

`source_jordan_budget` prova, com dois argumentos independentes e nos mesmos nós físicos,

\[
\boxed{
2\mathcal Q_k(x,y)=
\langle\Gamma^+_kx,\Gamma^+_ky\rangle-
\langle\Gamma^-_kx,\Gamma^-_ky\rangle.}
\]

O fator dois é o da polarização original. As hipóteses são o strip físico e a não anulação de `E+` nos nós, disponíveis eventualmente em cada dimensão fixa. Não há hipótese de contratividade ou positividade nativa.

`source_jordan_euler` conecta essas portas diretamente à identidade polarizada da #49:

\[
G^+_k(x,y)-G^-_k(x,y)=
2h_0\overline{x_0}y_0+2\mathcal N_k(x,y).
\]

Todos os cruzamentos e os dois pareamentos mistos do companheiro completado permanecem. Esta é uma ponte exata com fatores positivos que já existem, mas o kernel nativo é a DIFERENÇA dos dois Grams. O teorema não declara que a porta negativa seja não nula, nem que ela desapareça em toda ordem.

### B.4 — O que ocorre se elevarmos o defeito completo ao quadrado

No teste de uma fonte, usamos literalmente

\[
u_k=\operatorname{radialIncidentVector}
       (k,1,\operatorname{radialDifferenceSourceCoefficients}(k,1,0)).
\]

Ambos os canais dessa entrada coincidem com o jet projetivo de ordem zero por `radialDifferenceSource_pair`. Não foi alterada sua amplitude.

Denotando o quociente quiral original por `r_k` e `d_k=1-|r_k|^2`, `one_return_apply` e `one_defect_apply` provam

\[
T_ku=r_ku,\qquad D_ku=d_ku,\qquad D_k=I-T_k^*T_k.
\]

`one_storage_scalar` e `one_squared_defect_energy` mantêm a igualdade exata

\[
\langle u_k,D_ku_k\rangle=d_k\|u_k\|^2,\qquad
\boxed{\|D_ku_k\|^2=d_k\langle u_k,D_ku_k\rangle.}
\]

Como `r_k -> -1`, `one_deficit_tendsto_zero` dá `d_k -> 0`. A identidade original de limite fornece, por `one_signed_energy_tendsto`,

\[
\langle u_k,D_ku_k\rangle\longrightarrow2h_0.
\]

Logo `one_squared_energy_tendsto_zero` prova

\[
\boxed{\|D_ku_k\|^2\longrightarrow0.}
\]

A comparação é na MESMA fonte completada, antes de qualquer mudança de pesos ou de escala. O índice `k` é o da regularização radial, não a profundidade vertical Carry.

## C — O que foi refutado, com alcance preciso

### C.1 — Gram do Green bruto como operador A

`weighted_moment_gap` prova a condição necessária, para qualquer operador limitado fornecido,

\[
\|Bx\|^2\ge c\|x\|^2\ \ (\forall x)
\quad\Longrightarrow\quad\mu_2(v)\ge c\mu_1(v).
\]

Para o Green bruto, o teorema geométrico já prova `c=1/2`. As caixas nativas originais, também usadas anteriormente na #36, dão `h1>0` e `h2<h1/16`. `original_green_square_not_canonical` conclui:

**Para todo parâmetro real t e todo vetor v do CoreState, o operador original `c2GlobalRestrictedGreenGram t` não produz a primeira coluna canônica proposta.**

Não basta que esse Gram seja positivo, coercivo e invertível. A contradição é entre sua cota de energia e os coeficientes da mesma fonte nativa. Não foi ajustado um fator de escala para repará-la. O teorema atinge esse operador, não um fator posterior da síntese completada.

### C.2 — Quadrado do deslocamento Cauchy–Laguerre como operador A

`native_no_order_two_recurrence` usa o certificado preexistente `nativeSourceSixBoundaryEnergy_pos`. Uma recorrência de ordem dois anularia os pareamentos do polinômio mônico `X^2-cX-b` contra `1,X,X^2`; seu auto-pareamento também seria zero. A forma canônica real de três coordenadas é estritamente positiva, uma contradição.

`physical_shift_square_not_canonical` combina esse teste com B.2:

**Não existe vetor v no espaço Cauchy físico original para o qual o operador `B*B` desse deslocamento produza todos os momentos canônicos pela leitura proposta.**

A obstrução é ao kernel inteiro `3x3`, não somente à calibração de h0. Ela vale para qualquer massa do vetor e não é o NO-GO do clock logarítmico da #36. O deslocamento continua válido; seu adjoint square possui uma recorrência insuficiente para os pareamentos canônicos.

Os operadores finitos de Jacobi construídos dos momentos nativos permanecem válidos nos seus certificados; esta identificação com o deslocamento é uma obrigação diferente.

O operador `A` é identidade menos posto no máximo um; não afirmamos que A tenha posto um. O original B ainda possui sua ação completa nas colunas físicas. Substituir uma dinâmica por seu adjoint square exige verificar que essa operação conserva a leitura desejada.

### C.3 — Usar D*D para tornar positivo o defeito de retorno

O fator `B=D_k` fornece uma Gram positiva, pois sua energia é `||D_k u||^2`. Mas B.4 prova que, com a normalização original do kernel, a entrada central desse candidato tende a zero, enquanto a canônica é `h0>0`.

`squared_defect_not_canonical_mass` formaliza essa incompatibilidade. O teorema exclui a operação de quadrar o defeito NA MESMA entrada original. Não exclui uma raiz positiva de D quando sua positividade tiver sido demonstrada, nem outro fator obtido independentemente da síntese.

As três obstruções não exibem um pivô canônico negativo. A segunda usa precisamente um prefixo canônico positivo já certificado. Não há NO-GO geral para a geometria Carry ou para a existência de uma realização completada diferente.

Também não confundimos `Delta` da #48, o resto não linear `N` da #49 e a parte negativa de Jordan `D_-`. Um resto `N<0` não prova que a porta de Jordan negativa seja não nula. O orçamento completo pode continuar positivo, como já mostrava o teste da #49.

## D — Kernel, hipóteses e evidências

São 28 teoremas e 11 definições/abreviações novos em cinco módulos: `SquareEnergy`, `ShiftBoundary`, `ShiftMoments`, `SourceSquare` e `NativeTests`. `Audit.lean` registra todas as raízes públicas.

A validação concluiu **33 checks com código de saída zero**. A auditoria verificou **34 raízes estruturais**, com **7.502 constantes transitivas**, e **5 raízes dos testes nativos**, com **6.726 constantes**. Todos os axiomas ficaram restritos aos três fundacionais permitidos.

A auditoria distingue o núcleo estrutural dos testes nativos finitos. O primeiro rejeita dependência dos certificados nomeados de sinal central, positividade das faces de quatro/seis coordenadas, H6/K6, sétimo pivô e contratividade de sete fontes. Os dois grupos também rejeitam o lema que obteria positividade do defeito inteiro recebendo contratividade como premissa. Assim não se esconde essa premissa na construção dos fatores.

Os testes nativos usam explicitamente a desigualdade baixa já certificada por caixas da fonte, a positividade de h0 e a positividade da face de seis coordenadas. Isso é legítimo para REFUTAR a identificação de um candidato; não se usa um prefixo finito para fabricar uma origem positiva em toda ordem.

Os resultados novos são provas Lean, sem dados de zeros, alturas ou uma Hankel-alvo como entrada geométrica. Não se executou uma campanha numérica ou recálculo de momentos. As fontes e a métrica dos operadores originais permaneceram intactas. O procedimento recompila as dependências da #41 e das PRs #46–#49 necessárias aos imports.

```bash
cd /home/thlinux/geometry-of-numbers
git fetch origin ee56930a2c30456cfbd214a29bb31b12d3977204
python3 research/native-positive-square-kernel/validate.py
```

O objeto imutável da #41 é recompilado pelo procedimento herdado; não é mesclado. Comandos, resultados e hashes das fontes compiladas estão em `evidence/checks.json` e `evidence/source-sha256.json`. Os logs vivos ficam fora do checkout até cada comando terminar.

Os checks incluem compilação explícita de cada módulo, `lake build --wfail`, auditorias Foundation/Geometry/Analysis, `#print axioms` com percurso transitivo de tipos/corpos e regressão H6/K6/doze fontes. Os únicos axiomas permitidos são `propext`, `Classical.choice` e `Quot.sound`. Não se reivindica uma validação axiomática de arquivos alheios além dessas raízes e das auditorias executadas.

As branches das PRs anteriores e os dois arquivos não rastreados de usuário no operador são verificados por hashes/refs. Toda alteração pertence a este diretório; não foi criada uma worktree nova. Publicação em PR independente, sem merge automático.

## E — O que falta e próximo passo mínimo

**A síntese nativa ainda não foi identificada com uma única Gram positiva completa dos momentos em toda ordem.** A implicação proposta é correta e seus dois setores foram formalizados para um fator B fornecido. O problema permanece escolher e identificar esse fator a partir da fonte física completa.

Esta investigação acrescenta três restrições concretas à escolha:

1. O Gram do frame Green bruto tem uma cota inferior incompatível com os momentos; não é o operador A procurado.
2. O quadrado do deslocamento físico tem uma recorrência de ordem dois, incompatível com a forma canônica 3x3; nenhum vetor nesse carrier o corrige.
3. Quadrar o defeito de retorno remove a massa canônica central na fonte original; positividade por essa operação não conserva o kernel.

A rota por uma família Gram diretamente sintetizada também permanece aberta; ela não precisa ser a órbita desses operadores limitados. Não há conclusão de impossibilidade para um operador não limitado com domínios devidamente provados.

A alternativa que continua fisicamente alinhada é o fator do DEFEITO ORIGINAL, com seus dois canais preservados. A igualdade de B.3 mostra exatamente o que existe: um kernel nativo como diferença de duas Grams positivas já construídas.

Para a rota das portas de Jordan, o menor avanço independente seria obter da dinâmica completada uma identidade de energia/retorno que faça a contribuição negativa desaparecer ou a realize como um complemento ortogonal legítimo da positiva, preservando os parâmetros variáveis e os dois argumentos. Uma obrigação concreta é construir, antes do sinal dos momentos, um mapa C dos bordos/retornos originais e provar `I-T* T=C* C`, com os mesmos cruzamentos. Definir C como a raiz de D depois de receber sua positividade não descarregaria essa obrigação. Exigir essa identidade como campo de um certificado seria apenas transferi-la; não foi feito aqui. Também seria necessário justificar a coerência/convergência dos estados ao extrair uma família infinita, não somente de cada forma escalar finita.

Para uma rota por operador e resolvente, as obrigações efetivas já estão nomeadas: construir o fator físico e o estado de modo independente, provar a equação vetorial no domínio correto e a identidade division-free com a característica completada. O residual da característica não desaparece só porque A é positivo. No caso ponderado da pergunta, pode-se trabalhar com a fonte induzida Bv e o operador BB* no outro setor, evitando uma raiz fracionária; isso tampouco fornece automaticamente a identificação nativa.

A PR #41 permanece útil depois dessa ponte: a mesma funcional de momentos pode ser ortogonalizada algebricamente sem pressupor sinais. Esta rodada não encontrou uma relação geométrica independente que obrigue todos esses sinais a serem positivos.

**Conclusão: PARTIAL na busca da Gram canônica; NO-GO para as três realizações específicas testadas. Não é um STOP da pesquisa.** O novo cálculo delimita quais operações positivas conservam apenas suas próprias energias e quais ainda precisam ser confrontadas com o kernel original.
