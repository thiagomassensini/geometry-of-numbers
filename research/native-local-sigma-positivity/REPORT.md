# Positividade local dos momentos e curvatura na linha crítica

**Resultado: PARTIAL.** Os resultados são teoremas finitos e locais da resposta completada original. Eles não provam positividade Hankel de todas as ordens, nem uma nova propriedade espectral dos zeros.

## Fonte e variáveis

Com `d = σ − 1/2` e altura `t`, a PR #139 define `completedSigmaResponse d t` a partir da característica completada original e `completedSigmaDensity d t` como sua norma quadrada. As duas quadraturas são recombinadas antes do readout logarítmico `completedSigmaLogJet d n`. Em `d=0` esses jets são identificados com os momentos canônicos originais. Os teoremas aqui dizem respeito às Hankel desses jets; não afirmam uma realização física das doze fontes fora da linha sem transportar a síntese completa.

A paridade em `d` usa o resultado preexistente de reflexão da fonte completada **e a simetria da característica já formalizada**. Não se reivindica que ela foi derivada somente da norma vertical ou apenas da geometria de carry.

A base desta branch é a PR #141, commit `6234e424c8f8c93b42b485aecc006e6acc477a94`, que depende das PRs #139 e #140. Nenhuma dessas PRs foi fundida para este trabalho.

## A — Pivô móvel: paridade e máximo local

Para qualquer setor `s` e ordem `n`, `sigmaSchur_even` prova que o pivô móvel é par para `|d|<1/2`. Caso a matriz anterior no centro seja invertível, `sigmaSchur_differentiable_center` prova diferenciabilidade e `sigmaSchur_deriv_center` prova que sua primeira derivada é zero. Nenhuma dessas declarações exige que o pivô seja positivo.

`sigmaSchur_localMax_of_negative_curvature` combina essa estacionariedade com a segunda derivada negativa e conclui `IsLocalMax`. Este teorema é condicional no sinal de curvatura. `second_even_localMax` descarrega as hipóteses para a segunda direção par com o teorema de sinal da PR #141. O enunciado Lean declara **máximo local não estrito**; não foi formalizado aqui um módulo quantitativo de decaimento.

`second_even_center_positive` estabelece a positividade central reutilizando a desigualdade da fonte da PR #43, `h₀h₂ > 2h₁²`, com `h₀ > 0`. Isso dá o pivô `h₂ − h₁²/h₀ > 0`. `second_even_eventually_positive` mostra que ele permanece positivo para deslocamentos reais suficientemente próximos de zero. A prova não fornece raio numérico.

## B — Uma vizinhança comum para cada par de blocos finitos

`sigmaMatrix_finite_eventually_posDef` prova, para **qualquer setor e qualquer ordem finita N**, a implicação:

> se a matriz canônica no centro é positiva definida, então a matriz dos mesmos jets deslocados de tamanho N permanece positiva definida em alguma vizinhança do centro.

A prova obtém os prefixos positivos por submatrizes, a positividade dos pivôs centrais por Schur, sua persistência por continuidade e recompõe a matriz inteira. Os produtos bilineares e cruzamentos da matriz original não são apagados. O teorema genérico não prova sua hipótese de positividade no centro.

`both_six_sigmaMatrices_eventually_posDef` aplica a implicação aos certificados preexistentes `CarrySixthEven.even_source_six_posDef` e `CarrySixthOdd.odd_source_six_posDef`. Existe assim uma **mesma** vizinhança em que H6 e K6 dos jets deslocados são positivas definidas. O raio depende dos blocos e não foi calculado. Não se pode tomar uma interseção infinita de vizinhanças e concluir que haja raio positivo comum a todas as ordens.

O teorema `exists_positive_noncentral_six_sections` extrai explicitamente um deslocamento `0 < d < 1/2` com ambos os blocos positivos. O resultado demonstra estabilidade local finita: a positividade destes blocos não caracteriza exclusivamente a linha crítica.

Um controle sintético independente, `UniformControl.lean`, explicita por que a passagem a todas as ordens exige mais: `fₙ(d) = 1 − ((n+1)d)²` é par e positiva perto de zero para cada `n`, mas `no_common_positive_neighborhood` prova que não existe uma vizinhança positiva comum para todos. Essa família não representa nem substitui a fonte nativa; é apenas um contraexemplo à inferência lógica de uniformidade.

## C — Leitura theta e limite da generalização

`thetaCurvaturePolynomial_integral` e `sigmaCurvature_eq_thetaIntegral` relacionam a curvatura móvel à leitura theta da redução ponderada da PR #141. O polinômio é obtido das três formas existentes e mantém os termos cruzados. A ponte física às energias originais é o teorema **separado** `CarryCriticalEuler.native_weighted_balance`; a igualdade theta não o invoca transitivamente.

`sigmaCurvature_negative_iff_thetaDominance` expressa a curvatura negativa como dominância de massas **do polinômio da curvatura**. Isso não prova a dominância e não é a dominância do polinômio do pivô central. Nem curvatura negativa nem paridade, sozinhas, obrigam o valor central a ser positivo.

`normalizedThetaFourthExpression_eq_h1` e `normalizedThetaFourthExpression_negative` formalizam a identidade e o sinal da expressão de quarta ordem a partir dos resultados da fonte. Não formalizam uma medida de probabilidade ou não divisibilidade infinita.

## D — Validação e proveniência

Os módulos foram compilados com `-DwarningAsError=true`. `Axioms.lean` audita os novos teoremas com `#print axioms`. A auditoria transitiva separa a lei genérica dos resultados finitos: a primeira proíbe os certificados de sexto pivô; a prova concreta dos blocos seis usa os certificados explicitamente. A regressão da segunda direção par permite os teoremas de sinal da fonte da PR #43, mas não os certificados de sexto pivô. Nenhum resultado all-order de positividade foi usado como hipótese oculta.

Os comandos e logs ficam em `evidence/`: a execução integral consta em `validation.log`; o controle sintético, acrescentado depois, foi compilado separadamente com as mesmas opções e consta em `UniformControl.log` e `Axioms.log`. O roteiro `validate.sh` atualizado inclui esse controle para futuras execuções. O script `compile.sh` usa por padrão a worktree existente `/home/thlinux/geometry-of-numbers-native-critical-euler-balance` e seus caches das dependências; `CARRY_BASE_RESEARCH` permite apontar para uma localização equivalente. A validação focal não é uma reconstrução limpa das dependências do operador.

## E — Próxima obrigação matemática

Encontrar, na fonte completada e antes de descartar os canais, uma cota de orçamento que garanta o sinal do **pivô central** para uma família não limitada de ordens, preservando a direção crítica, retorno, bordo, cruzamentos e cauda. Se a rota usar a curvatura, será preciso relacionar sua desigualdade ao próprio pivô, pois a ponte theta aqui demonstra apenas a primeira. Uma cota em função explícita de ordem e setor, independente do sinal que procura provar, é o alvo concreto; as vizinhanças finitas aqui obtidas não fornecem uma margem uniforme.
