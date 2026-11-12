# Certificação cofactorial C3 e compensação quiral

## 1. Proveniência

A fonte é a característica completada original, com genealogia
C2 → Genuine → carta de câmera → escalar nativo → completion → característica
→ resposta logarítmica → momentos. A carta C3 representa a mesma fonte.
Bracket, seed, pesos, amplitudes, fase, completion e retorno são os do
repositório.

- Base solicitada: `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`, merge de #317.
  A lei geral por ordem já está em #316 (`9774ddd42616ad12b9e9a2b9ad93aa89cb7ee796`).
- Base desta continuação: `5f74e8ad1929f402562159d45ff8b72a13b573c9`, merge de
  #323. A branch isolada é `agent/c3-cofactor-canonical-transport-20261112`.
- #318–#322 integraram a aceleração, a identidade cofactorial geral, as caixas
  intermediárias e o limite quiral condicional. #323 integrou as caixas nativas
  e a positividade da matriz cofactorial ímpar. O commit `3e1f6b7` liga
  essa matriz ao pivô canônico e descarrega a condição do limite quiral.
  O commit `bde43be` certifica o setor par e explicita a condição
  $c_0D\ne0$ para o transporte cofactorial.
- A validação usa Lean 4.32.0, mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame
  `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` e o operador no checkout
  `8f15ec76e5a95eb0c61da3a114729363a1d6a477`. Os pins permanecem os do projeto.
  `ThirdSourcePrefix` é a dependência já usada em #146 e #322. O SHA-256 da
  fonte da cópia usada no cache é
  `c3d5e49a945942a92d26776857a721a8d82eff706d13e917ee2a6e88eb4e5b5e`.

## 2. Identidade cofactorial

Em `GeneralCofactorIdentity.lean`, para todo anel comutativo e prefixo
finito simétrico $A$, sejam $D=\det A$, $B=\left(\begin{smallmatrix}A&b\\b^T&d\end{smallmatrix}\right)$,
$v=(u,1)$, $r=Au+b$ e $E(u)=v^TBv$. A prova sem divisão dá

$$
\det B=D E(u)-r^T\operatorname{adj}(A)r.
$$

Para $w=(-\operatorname{adj}(A)b,D)$, a prova dá $Bw=(0,\ldots,0,\det B)$
e $w^TBw=D\det B$. Inclui prefixos vazios e singulares. Em dimensão três,
com entradas $a,b,d,e,f,g$ do bloco simétrico, o determinante se reduz a
$(ad-b^2)g-de^2+2bef-af^2$. `C3Regression.lean` verifica margens positiva
e negativa, prefixo singular, direção não crítica e a fonte sintética
$C(u)=1-u-u^2$. `CofactorIdentity.lean` verifica o vetor cofactorial exato.

## 3. Direções racionais

A direção ímpar é $(14879782871,1692226107996)/10^{14}$ e a par é
$(16943337609,1799554820555)/10^{14}$. São as escolhas diagnósticas propostas
na missão. Entram no cálculo intervalar do residual. A identidade é válida
para qualquer direção e o certificado da direção canônica usa $w$.

## 4. C3 original

`completed_native_head_tail48` decompõe literalmente a característica
completada. A cabeça mantém as 48 células originais e o bordo no endereço
146, com o stencil de 24 amostras até 169. `finite_completed_reference_jet_phase48`
conserva $i^r$ na convolução da cabeça, carta, amplitude e Gamma.
`completed_characteristic_reference_jet_error48` limita a substituição da
Gamma nativa pelas referências racionais verificadas em `GammaThirteen`.

## 5. Representação escolhida

C3/48 usa o polinômio de bordo $B(D)(1+D^{12}/729)$ e o resto
$D^{26}/729^2$. `c3_acceleration48_polynomial` prova a identidade polinomial
com denominador limpo e `c3_acceleration48_cell` vale para toda sequência
complexa. `c3_acceleration48_finite` conserva os dois bordos,
`c3_boundary48_at_infinity` elimina o bordo terminal no limite, e
`c3_twenty_sixth_summable` e `c3_twenty_sixth_series_bound` controlam a
26ª diferença na malha original. `completed_tail48_jet_bound` aplica a
completion e Cauchy, com orçamento
$96\cdot26!\cdot4^r/[729^2(3M-1)^{25}]$ no jato de altura $r$.
A comparação numérica com C3/256 em `compare_c3_heads.py` passa para os
sete coeficientes e é usada como regressão.

## 6. Caixas certificadas

`native_even_source_coefficient_boxes` (PR #323) prova as sete inclusões
na fonte completa. Os centros abaixo são exibidos arredondados. Os centros
racionais exatos estão em `IntervalGate.lean`, em `candidateCoefficientBall`.

| $j$ | Centro exibido | Raio racional |
|---:|---:|---:|
| 0 | 0,49712077818831410991 | $2/10^{12}$ |
| 1 | −0,011485972157572718768 | $2/10^{12}$ |
| 2 | 0,00012345201807031800689 | $1/10^{15}$ |
| 3 | −8,32355481385527072·10⁻⁷ | $1/10^{16}$ |
| 4 | 3,99222655134413717·10⁻⁹ | $1/10^{20}$ |
| 5 | −1,46160257601109609·10⁻¹¹ | $1/10^{20}$ |
| 6 | 4,27454004553684496·10⁻¹⁴ | $1/10^{20}$ |

A avaliação da cabeça preserva o parâmetro comum `log(pi)` em um polinômio
normalizado. Os limites da tabela são racionais e checados pelo kernel Lean.
A soma das magnitudes dos 13 jatos de cabeça que multiplicam a Gamma é
≤ $1/2$. Isso dá erro Gamma ≤ $0,5\cdot10^{-24}$ e a cauda completada
tem erro ≤ $2\cdot10^{-24}$. A inclusão usa a folga provada de
$3\cdot10^{-24}$ em cada caixa, com fase e normalização do jato verificadas.

## 7. Desigualdade principal

`c3_odd_third_cofactor_polynomial_positive` aplica `sourceOddMargin_contains`
e o limite racional estrito
`0 < oddCofactorMarginBall.center - oddCofactorMarginBall.radius`, via
`candidate_source_gate`. Assim $D E(u)-r^T\operatorname{adj}(A)r>0$
para a fonte original. A primeira entrada do prefixo e a cota
$D>9/10^{17}$ também têm certificação C3 em `c3-odd-head-source`.
A especialização par usa as mesmas caixas e operações racionais, com
a direção par. Sua margem é estritamente maior que $3/10^{24}$.

## 8. Resultado canônico

`NativeOddCertificate.lean` identifica a matriz da PR #323 com o bloco
de coeficientes de `sourceKernel nativeC true` usando `odd_three`.
Prova $\det B_{1,3}>0$, $p_{B,1,2}>0$ e $p_{H,1,2}>0$.
A congruência triangular da PR #70 transporta a positividade definida,
e a direção de Hankel com última coordenada 1 lê exatamente o Schur. A
normalização é $p_{B,1,2}=c_0^2p_{H,1,2}$.
`NativeEvenCertificate.lean` usa `even_three` para provar
$\det B_{0,3}>3/10^{24}$ e $p_{H,0,2}>0$.

## 9. Transporte quiral

`CofactorTransport.lean` prova, sob $c_0D\ne0$ e a recorrência da fonte,
que $v_* = T^T w/(c_0D)$ tem última coordenada 1, satisfaz
$H v_*=(0,\ldots,0,p_H)$ e $v_*^T H v_*=p_H$. A especialização ímpar
identifica $v_*$ com `criticalCoefficients 1 2`, que já sintetiza os
estados incidente e retornado. A diferença das energias converge a
$2p_{H,1,2}$. Na escala $(k+1)^{11}$, o déficit relativo converge a
$2p_{H,1,2}/\|\mathrm{criticalLeadingState}(1,2)\|^2>0$. Logo o déficit
relativo é estritamente positivo para $k$ suficientemente grande.

## 10. Auditoria NO-GO

Consulta somente leitura ao catálogo em `6ef3e37413251b0aba2dea5484a8b390f08dbfc2`.
NG-064 e NG-065 exibem testemunhas racionais nas caixas antigas que
violam o sinal novo, respectivamente para cinco integrais e seis fontes.
O domínio é o das tuplas admitidas por aquelas cotas. Aqui as inclusões
novas são de $c_0,\ldots,c_6$ da característica e alimentam uma margem
verificada. Analogamente, `even_schur_data_insufficient` e
`odd_schur_data_insufficient` variam livremente o coeficiente final,
enquanto a prova atual certifica $c_5$ e $c_6$.
A rota usa a congruência do Bézout e a síntese física já formalizada.
As identificações de incidência bruta com Hankel (NG-020/021/022),
reconstrução de Green por readouts coarse (NG-017/057) e identificação
de consumidor fixo com todo o span causal (NG-039/050) ficam fora das
hipóteses. O mesmo vale para o limite cofinal conjunto e a Gram bruta de
duas regularizações (NG-042), o kernel gerador radial em quatro pontos
(NG-062) e as hipóteses conjuntas de atlas seeded finito e Stieltjes
(NG-024/068).

## 11. Auditoria de circularidade

A identidade algébrica usa adjugata, determinante, congruência e Schur.
A identidade geométrica usa o bracket C3, o bordo acelerado e a completion
literal. O controle analítico usa Gamma, chart e caixas da cabeça com a
cauda Cauchy. O sinal é a desigualdade racional estrita. `CertificateAudit.lean`
verifica o fecho transitivo de tipos e corpos de prova. Verifica a presença
da inclusão dos coeficientes, da decomposição literal e do prefixo C3
independente, e exclui os consumidores listados de `PivotBoxes`, de caixas
theta e de teoremas anteriores de sinal. O teste de dependências complementa
a inspeção matemática das hipóteses e das desigualdades efetivamente usadas.

## 12. Validação

Reprodução no ambiente Lean fixado, com os caches das dependências de pesquisa
de #70, #145 e #146 e do operador. O diagnóstico C3/48–C3/256 usa
`mpmath` 1.3.0. O validador imprime os SHAs e compila explicitamente os
módulos de pesquisa com warnings como erros. Inclui a auditoria transitiva,
regressões, os dois diagnósticos racionais e o diagnóstico de cabeça.
O validador integrado terminou com código 0. A auditoria cobriu 17 resultados,
945 teoremas dos módulos da missão e 66.019 declarações na cadeia transitiva.
A nova identidade polinomial também foi compilada isoladamente, com avisos
como erros. O log local `.cache/canonical-validation.log` tem SHA-256
`eea1474169bfa6f88d585ab9da52bf23c32fee29e22e5f0e7a709c93999e70bc`.
O build raiz passou com 8.850 tarefas. As auditorias de fundação,
geometria e análise passaram. O conjunto permitido de axiomas é `propext`, `Classical.choice` e `Quot.sound`.

```sh
bash research/c3-cofactor-chiral-certification/validate.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
git diff --check
```

## 13. Resultado da missão

| Objetivo | Estado |
|---|---|
| Cofator geral e porta polinomial | GREEN |
| Aceleração C3/48 e caixas até $c_6$ | GREEN |
| Terceiro pivô ímpar pela fonte | GREEN |
| Cofator canônico e déficit quiral ímpar na ordem 11 | GREEN |
| Terceiro pivô par pela fonte | GREEN |

## 14. Próximo passo mínimo

O escopo finito especificado está fechado matematicamente. A investigação
opcional da resposta paramétrica das células C2 fica para uma tarefa própria.
