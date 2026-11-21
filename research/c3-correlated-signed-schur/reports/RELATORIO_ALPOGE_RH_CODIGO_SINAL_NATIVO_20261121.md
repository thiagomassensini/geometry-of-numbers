# Auditoria externa Alpöge–Claude (RH/GRH) e efeito no sinal dos momentos nativos

Data: 21/11/2026. Nova pesquisa informada por anúncio de 20/11/2026.
Estado: inspeção parcial do código externo (declarações e módulos ligados ao endpoint), leitura direta de remark.pdf, relatório de verificações independentes do MIT e formalização de uma ponte LÓGICA CONDICIONAL no nosso Lean 4.32. NÃO houve importação nem compilação do acervo externo de 17,4 milhões de linhas nesta VM.

## 1. O resultado anunciado, a verificação independente e sua fronteira

Autor: Levent Alpöge, com Claude.
Anúncio original: https://alpo.ge/remark.pdf
Fonte Lean espelhada, para navegação: https://github.com/CocoSgt/riemann-hypothesis-lean
Auditoria MIT Andrew Sutherland: https://math.mit.edu/~drew/grh/
Origem e versão: Lean 4.33.1, Mathlib 4.33.1. Main.lean usa a definição RiemannHypothesis da própria Mathlib:
  theorem riemannHypothesis : RiemannHypothesis := rhOfAll
O endpoint para Dirichlet L-functions também está codificado.
Em 20/11/2026 a página do MIT relata:
- 175.187 arquivos Lean compilados sem erro;
- apenas axiomas propext, Classical.choice, Quot.sound;
- replay no kernel Lean;
- nanoda, con-leche, lean4lean aprovados;
- con-leche --compare confrontou cinco enunciados com o challenge independente.
Outros testes eram ainda marcados como pendentes. Isso é forte verificação do enunciado *formal*, mas o significado conceitual da prova e sua aceitação institucional ainda estavam sob exame.

Código EXTERNO aberto diretamente via GitHub fetch_file:
1. src/Main.lean
2. src/Statements.lean
3. src/Supplements/Kernels/MainTheorems.lean
4. src/Supplements/Kernels/MainTheoremsAll.lean
5. src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean
6. src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean (imports e árvore extensa)
7. src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean (imports e árvore extensa)
8. src/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean
9. src/Formalism/BehrendSets/BehrendVariance/Select.lean
10. src/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean.

A trilha final real do enunciado é:
  Main.riemannHypothesis
    <- Supplements.Kernels.MainTheorems.rhOfAll
    <- Formalism.VW.rh_of_every allChi
    <- UpperTheory.FinalTheorems.everyCharacter
    <- UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
       + theta lifts / automorphic varieties / Galois etc.

Não confundir src/Main.lean com a prova matemática interna: ele é somente o endpoint de poucos enunciados em uma base muito extensa.

## 2. Onde o AUTOR diz que está o sinal, e o que foi visto no Lean

Anúncio, pp.3-4:
- Stepanov e sua multiplicidade de zeros via determinantes, originalmente sobre corpos finitos.
- A forma W(1_S)>=0 por um determinante; expansão via funções teste e variância.
- Guinand–Weil, soma ponderada de von Mangoldt e uma subtração explícita de termos principais.
- Uso de quadricas e cohomologia média para sinal definido, em contraste com modo principal.
- Iterações de Parseval controlam um resto com precisão de raiz quadrada;
- Cadeias de theta lifts em grupos unitários totalmente definidos, comprimento aproximado sqrt(X), produzem multiplicidade;
- Normas via Chowla–Selberg, Weyl, Siegel mass, inclinação Bost, Iwasawa, seesaw de Rallis e períodos Bessel.

Esses são os mecanismos alegados no ESBOÇO do AUTOR. Não foi demonstrada uma identificação deles com o Green C2, nem é correto afirmar que as linhas de código inspecionadas isoladamente já reproduzem toda essa cadeia de 17 milhões de linhas.

Nos arquivos Lean inspecionados:
- Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanPositiveSemidefinite tem teoremas psd_zero, psd_add, psd_smul, psd_sum para kernels Hermitianos, e composição de fonte positiva.
- Formalism.BehrendSets.BehrendVariance.Select formaliza variância como soma de quadrados com pesos não negativos e sua aplicação em uma seleção de subconjuntos.
- Development.WeilBound.ThetaLifts.Reductions.NormExpSubLe controla uma variação de operador (fase e derivada de lift).
Estes são locais e não autorizam inferir que a nossa forma de retorno esteja automaticamente PSD.

## 3. A identificação original Genuine -> F já está Lean

No nosso CSA:
- NativeScalarGenuineIdentification.lean: primitivo geométrico C2 -> Genuine.
- NativeScalarZetaIdentification.lean: nativeScalar_eq_riemannZeta (na faixa crítica).
- NativeBoundaryArchimedeanDressingSeparation.lean: F(z)=A(z)N(z) mantendo fonte nativa não vestida e Gamma completion separados.
- CompletedNativeRealWeylMoments.lean: os momentos h_n são a resposta logarítmica recursiva de F(z).
- ConditionalCriticalLineConfinement.lean: passagem de coordenadas s=1/2+i z.

Novo teorema Lean, compilado:
  completedNative_zero_height_real_of_RiemannHypothesis
Dada a RiemannHypothesis da Mathlib, se s=operatorHeightParameter z pertence à faixa crítica e F(z)=0, então Im(z)=0.
Prova usa a IDENTIDADE GENUINE/NATIVA e o fator A(z) não nulo na faixa, sem definir outro operador.
Não é um teorema incondicional dentro de nossa branch Lean 4.32: a prova externa v4.33.1 NÃO foi importada. Serve como interface estável para futura integração entre versões.

## 4. Como RH PODERIA fechar o sinal de Hankel por uma rota downstream

Assumindo RH e o produto de Hadamard usual da característica Xi (que é F) em pares de zeros ±gamma positivos reais com multiplicidades m_gamma:
  F(z)/F(0) = prod_gamma (1-z^2/gamma^2)^(m_gamma).
Então formalmente, justificando convergência e extração de coeficientes:
  R(z)=-F'(z)/(2F(z)) = sum_gamma m_gamma*z/(gamma^2-z^2)
e para todo n:
  h_n = sum_gamma m_gamma/gamma^(2n+2).

Portanto para vetor real a de dimensão N e P_a(x)=sum_{j=0}^{N-1} a_j*x^j:
  sum_(i,j) a_i h_(i+j) a_j
     = sum_gamma (m_gamma/gamma^2) * P_a(gamma^-2)^2 >=0.
O Hankel deslocado também fica PSD, inserindo o fator positivo gamma^-2. Se há infinitas alturas positivas distintas, todo polinômio real não nulo tem grau finito, dando estrita positividade.

Isto é um encadeamento ANALÍTICO que RH torna disponível downstream. A ponte COMPLETA do produto infinito de zeros para a sequência h_n (convergência e fatores) AINDA NÃO FOI FORMALIZADA em nosso Lean de C2/CSA nesta rodada. Não declarar que já temos um teorema Lean incondicional de positividade nativa.

No momentos:
  lean/MomentosHankel/MomentHankelPositivity.lean
já formaliza o núcleo finito da construção: momentHankel_posSemidef e momentHankel_posDef para pesos não negativos e suficientes nós reais distintos.
No CSA, AllPrefixPSDNonrecurrence.lean demonstra PSD para todas as ordens + não recorrência => PD. A não recorrência finita para nossos h_n já está em CompletedNativeEntireComparison.lean. São peças disponíveis; a igualdade h_n = soma sobre alturas reais continua a obrigação analítica.

IMPORTANTE: PositiveMeasureHankel.lean no momentos prova POSITIVIDADE theta/cosseno incondicional, mas essa é OUTRA sequência de momentos; não confundir com os h_n da logderivada completada.

## 5. Duas rotas e a questão do sinal físico

ROTA A (consequência usando RH externa): transladar RH em nossa própria F via nativeScalar_eq_riemannZeta e formalizar o produto infinito de Hadamard, obtendo uma medida espectral atômica positiva e TODOS os Hankels h_n PSD/PD. Isto é uma consequência da prova alheia, não uma prova alternativa de RH pela geometria C2.

ROTA B (alternativa independente da geometria): recuperar a PSD sem usar RH, mostrando que a energia da incidência restante domina o retorno na direção de Schur após TFVD/Green/completion, preservando defeitos assinados. Nosso gate existente foi formalizado em PrimeWheelNativeSignedGate.lean. A prova externa NÃO parece fornecer diretamente essa identidade de transporte: o determinante de Weil, multiplicidades por theta lifts e sinal por cohomologia média são mecanismos diferentes. São inspirações metodológicas, não lemas transferíveis automaticamente.

Para uma dedução NOVA realmente geométrica de RH, a ROTA B precisa ser demonstrada sem empregar RH como entrada. Usar RH para provar PSD e depois PSD para RH seria uma cadeia circular se apresentada como prova independente.

## Próximo passo sugerido

1. Formalizar de forma fonte-first e em Lean v4.33.1 a conexão RH externa -> produto Hadamard da F original -> h_n = soma discreta nos zeros -> Gram Hankel PSD; consultar generic MomentHankelPositivity.lean.
2. Em paralelo procurar prova de que o nosso retorno físico é contrativo no subespaço crítico, ou um núcleo Weil equivalente ao nosso Qsource; só assim a rota geométrica independente fecha.
3. Evitar apresentar os kernels de Weil do arquivo externo como o Green C2 sem um intertwiner polarizado explícito e respeitando Gamma.
