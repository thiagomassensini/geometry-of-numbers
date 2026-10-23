# Transporte Carry–teta: informação, polarização e defeito Green

**Resultado: PARTIAL.** Há um transporte injetivo dos **coeficientes de teste finitos** para os polinômios originais da representação teta, antes da integração. A identidade de Green preserva a leitura bilinear completa, com seus termos mistos e traços. Isso não constrói uma isometria dos estados materiais completados. Dois candidatos concretos de identificação positiva foram refutados no Lean: a fatoração local das densidades `P_(i+j)` e a escolha dos próprios `P_i` como vetores em `L²(Φ)`.

O transporte físico não local proposto pelo usuário permanece aberto. A positividade canônica em toda ordem também permanece aberta.

Data: 23/10/2026. Execução e builds: host `llm`.

## A — O que já estava demonstrado e qual fonte foi inspecionada

### Base e preservação

- Repositório de entrega: `thiagomassensini/geometry-of-numbers`.
- Branch nova: `agent/theta-polarized-green-transport`, criada diretamente de `origin/main`, commit `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Não depende das branches não integradas dos PRs #38–#70. O checkout anterior, branch `agent/tfvd-bezout-schur-residual`, permaneceu em `4103131555dd4b17042a3502aca4e2d78ec62627`, com seu trabalho preexistente preservado.
- Operador consultado sem edições: `/home/thlinux/carry-self-adjoint-operator`, branch `agent/critical-branch-native-audit`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- `origin/main` do operador foi atualizado e conferido em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. Os nove módulos de proveniência listados no manifesto são idênticos nos dois commits. As provas novas foram compiladas no ambiente original desse repositório.
- Nenhuma alteração em fontes nativas, pesos, amplitudes, fases, métricas, dressing, câmeras, pins, arquivos históricos ou PRs anteriores. Nenhum merge automático.

### Declarações atuais reutilizadas

Todos os caminhos desta tabela são relativos a `CarrySelfAdjointOperator/`, no repositório do operador.

| Módulo e declaração | Alcance real |
| --- | --- |
| `CompletedNativeXiCosineTransform.lean`, `XiThetaCosine.completedNative_eq_xiCosineKernel` | Para todo `t : ℝ`, a característica nativa em `(t : ℂ)` é o cast complexo da integral cosseno com o kernel original. Não é uma igualdade de estados materiais. |
| `NativeSourceThetaMomentPolynomials.lean`, `nativeThetaMomentPolynomial_eq` e `nativeThetaMomentPolynomial_integral` | `P_n` é determinado pelos coeficientes da característica e sua integral é exatamente o momento logarítmico canônico, em toda ordem. |
| `NativeSourceSchurThetaIntegral.lean`, `nativeThetaQuadraticPolynomial_integral` | A forma quadrática inteira é preservada pela leitura integral; os cruzamentos não são omitidos. |
| `NativeSourceThetaGreenTransport.lean`, `nativeXiPolynomialIntegral_eq_thetaGreen_integral` | Integração por partes com os dois traços centrais explícitos, para todo polinômio. |
| Mesmo módulo, `nativeSourceMomentQuadratic_eq_thetaGreen_integral` | Os traços da combinação quadrática canônica anulam-se por teorema; não por descarte. |
| `CompletedTfvdGreenAllOrderIntertwining.lean`, `canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort` | Igualdade vetorial já existente entre a porta TFVD completada e a porta Green nativa. Sobrevive aos jets e ao empacotamento Naimark. Não envolve um estado teta. |
| `CompletedNativeTfvdWronskianMoments.lean`, `canonicalC3BracketTfvdMoment_eq_canonical` | Recuperação exata dos momentos pelo Wronskiano TFVD, independente do cutoff. |
| `CompletedNativePolarizedTfvdGreenMomentKernel.lean`, `canonicalNativePolarizedTfvdGreenLedger_identity` | Wronskiano bruto completado = Green finito + proveniência Green + proveniência cruzada + resíduos de leitura + completamento. Hipóteses: `-1 < z.re` e `-1 < w.re`. |
| Mesmo módulo, `canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto` | O defeito converge para Wronskiano menos Green completado; não se afirma que desaparece. Domínio: `0 < z.re < 1` e `0 < w.re`. |
| `CompletedNativeTfvdGreenMomentGramBridge.lean`, `hasCanonicalCompletedNativeGreenMomentJets_iff_defect_zero_of_factors` | Equivalência condicional; recebe as representações Green dos fatores. Não fornece essas representações nem uma Gram canônica incondicional. |

O estado original a preservar não foi substituído pelo par escalar `(F,-F')`. Por exemplo, `CanonicalC3BracketTfvdCompletionState M` mantém `transport`, `valueTail` e `logJetTail`; sua `greenPort` é um vetor em `FiniteC3GreenPortCarrier (M*3)`. O readout escalar é uma projeção desse objeto, não sua definição integral.

O Green causal também já dispõe da reconstrução vetorial `canonicalCompletedC3CausalGreenBoundarySum_state`, incluindo retorno, e da igualdade polarizada `canonicalCompletedC3CausalGreenBoundarySum_inner_eq_nativeState_inner`. Essas identidades nativas não autorizam identificar seu fluxo discreto com o fluxo diferencial teta sem outro transporte demonstrado.

Os no-gos históricos para a densidade ímpar teta e para a primeira densidade Green par já existiam. Eles não são apresentados como descobertas desta rodada. Os resultados abaixo testam adicionalmente os **cruzamentos do setor par** e a **norma integrada do candidato polinomial**.

## B — O que foi demonstrado agora

Convenções: `c_n` são os coeficientes originais da característica completada; `P_n = nativeThetaMomentPolynomial n`; `Φ = completedNativeXiCosineKernel`; `B = XiThetaCosine.thetaTail`. O índice contínuo `u` da representação teta não é profundidade Carry, endereço material nem parâmetro espectral.

### 1. Informação dos coeficientes antes da integração

Em `PolynomialInformation.lean`, definimos somente a combinação de teste

\[
 A_N(x)=\sum_{i<N}x_iP_i.
\]

Os teoremas `thetaInputPolynomial_zero_iff` e `thetaInputPolynomial_injective` provam

\[
 A_N(x)=0\iff x=0.
\]

A prova usa a triangularidade dos graus `2i+2` e seus coeficientes superiores não nulos, derivados da própria recorrência. Não recebe `PosDef`, `PosSemidef`, independência física presumida ou sinais de pivôs.

Além disso, `greenPolynomial_injective` prova que o operador fixo

\[
 \mathscr L P=P''-\tfrac14P
\]

é injetivo em `ℝ[X]`. Portanto, `thetaGreenInput_injective` prova a injetividade de `x ↦ 𝓛(A_N(x))`.

**Limite de interpretação:** esses são coeficientes de teste e polinômios derivados da fonte. Não são o espaço completo dos estados materiais. A injetividade obtida não é uma isometria física e não identifica redundâncias multibase.

### 2. Green em dois argumentos independentes

Em `PolarizedGreen.lean`, `green_product_defect` prova exatamente

\[
 \boxed{\mathscr L(PQ)-P\mathscr LQ-Q\mathscr LP
       =2P'Q'+\tfrac14PQ.}
\]

O termo misto não desaparece. O fluxo original `F_P=PB'-P'B` satisfaz, por `green_flux_product`,

\[
 F_{PQ}=P F_Q+Q F_P-PQB'.
\]

O teorema `green_product_integral` mantém os dois traços:

\[
\begin{aligned}
\int_0^\infty PQ\Phi
={}&\int_0^\infty
 (P''Q+2P'Q'+PQ''-\tfrac14PQ)B\\
 &+\tfrac12P(0)Q(0)
 +(P'(0)Q(0)+P(0)Q'(0))B(0).
\end{aligned}
\]

Para tamanhos finitos independentes `N,M`, qualquer deslocamento `s` e entradas reais independentes `x,y`, `native_bilinear_eq_green_integral` prova

\[
\sum_{i<N,j<M}x_i y_j h_{i+j+s}
=\int_0^\infty
\mathscr L\!\left(\sum_{i<N,j<M}x_i y_jP_{i+j+s}\right)B.
\]

A anulação dos traços dessa combinação é provada separadamente. Isso abrange o setor original e o deslocado. É uma igualdade bilinear de **readouts completos**, não uma igualdade entre energias dos estados materiais.

### 3. Resíduo exato do candidato `e_i ↦ P_i`

Em `ProductResidual.lean`, o diagnóstico usa os mesmos polinômios e a mesma medida:

\[
 E_{ij}=P_{i+j}-P_iP_j.
\]

`canonical_pairing_eq_theta_product_add_green_residual` prova, para quaisquer `i,j`,

\[
 \boxed{h_{i+j}
 =\int_0^\infty P_iP_j\Phi
  +\int_0^\infty \mathscr L(E_{ij})B.}
\]

`thetaProductResidual_green_formula` expõe todos os termos:

\[
\mathscr L(E_{ij})
=\mathscr LP_{i+j}-P_i\mathscr LP_j-P_j\mathscr LP_i
 -2P_i'P_j'-\tfrac14P_iP_j.
\]

Os dois traços centrais de `E_ij` são zero por prova; o fluxo no infinito tem o decaimento já provado para todo polinômio. O resíduo é, assim, uma contribuição de interior explicitamente retida, e não um bordo apagado.

`theta_polynomial_square_integral_nonneg` confirma a positividade da integral de um quadrado contra `Φ`. Não atribui esse sinal ao resíduo. Esta decomposição não é uma nova fonte nem uma nova métrica.

## C — O que foi refutado

### 1. Fatoração local positiva das densidades originais

Em `ThetaCrossObstruction.lean`, os três primeiros polinômios são calculados exatamente:

\[
\begin{aligned}
 P_0(u)&=\frac{u^2}{2c_0},\\
 P_1(u)&=-\frac{u^4}{12c_0}-\frac{c_1u^2}{2c_0^2},\\
 P_2(u)&=\frac{u^6}{240c_0}+\frac{c_1u^4}{12c_0^2}
       +\left(\frac{c_1^2}{2c_0^3}-\frac{c_2}{2c_0^2}\right)u^2.
\end{aligned}
\]

Para o kernel de densidades do setor par, `thetaDensityDeterminant_formula` prova

\[
 \boxed{P_0P_2-P_1^2
 =-\frac{7u^8}{1440c_0^2}
  -\frac{c_1u^6}{24c_0^3}
  -\frac{c_2u^4}{4c_0^3}.}
\]

O coeficiente superior é estritamente negativo usando somente `c_0 ≠ 0`. O determinante tende a `−∞`. Mais precisamente:

- `no_pointwise_theta_density_gram`: não existem dois vetores hilbertianos locais com pareamentos `P_0(u), P_1(u), P_2(u)` para todo `u ≥ 0`.
- `no_ae_weighted_theta_density_gram`: nem mesmo os pareamentos ponderados `Φ(u)P_n(u)` admitem tal fatoração quase em toda parte em `(0,∞)` com a medida de Lebesgue original.
- `even_density_diagonals_pos_but_determinant_neg`: as duas diagonais são eventualmente positivas, enquanto o determinante é negativo. A incompatibilidade está nos cruzamentos, não apenas em alguma diagonal negativa.

A prova usa Cauchy–Schwarz. A falha ocupa uma semirreta, não um conjunto excepcional de medida zero. Não foram usados valores aproximados de momentos.

Isso **não** prova que a matriz das integrais dessas densidades seja indefinida. Integração e fatoração ponto a ponto são condições diferentes.

### 2. Os próprios `P_i` também falham como vetores após integração

Em `IntegratedNormTest.lean`, `theta_first_polynomial_square_integral` prova

\[
 \int_0^\infty P_0(u)^2\Phi(u)\,du
 =\frac{\mu_2}{4c_0^2},\qquad
 \mu_n=\int_0^\infty u^{2n}\Phi(u)\,du.
\]

Já o momento nativo é `h_0 = μ_1/(2c_0)`. Utilizando somente estimativas anteriores da fonte teta, `theta_first_polynomial_square_integral_lt_native` prova a desigualdade estrita

\[
 \boxed{\int_0^\infty P_0^2\Phi<h_0.}
\]

As estimativas reutilizadas são `completedNativeThetaTailMoment_zero_gt`, `completedNativeThetaTailMoment_two_lt`, a não negatividade dos momentos de `B`, e a cota `c_0 ≥ 1/3`. Por elas, `μ_1 > 1/50`, `μ_2 < 1/250`, e `μ_2 < 2c_0 μ_1`. Não se consome um certificado de positividade da Hankel.

Portanto, o candidato específico que identifica o jet nativo de índice `i` com o polinômio `P_i` em `L²(Φ)` tem a norma errada já no índice zero. O teorema `theta_product_residual_zero_zero_integral_pos` também mostra que o resíduo integrado `E_00` é estritamente positivo. Ele não pode ser simplesmente declarado nulo.

**Alcance dos dois no-gos:** excluem essas realizações locais/polinomiais específicas. Não excluem um transporte não local da síntese física completa, nem invalidam os momentos, a representação teta ou a geometria Carry.

## D — O que permanece aberto e o que foi validado

### Ponte física aberta

Não foi construído um operador `𝒰` entre o estado Carry completado original e um estado teta enriquecido que preserve simultaneamente:

1. As portas, as duas pernas reais e seus cruzamentos.
2. As contribuições material, Gamma/dressing e de completamento.
3. Os traços e o retorno físico.
4. A forma polarizada original em duas entradas independentes.

O fluxo `PB'−P'B` pertence à representação diferencial teta. Sua igualdade com um fluxo TFVD nativo não segue da igualdade das integrais ou do uso da palavra Green.

As igualdades provadas nos módulos novos acontecem na representação polinomial downstream da característica **já sintetizada**. Elas não pretendem recuperar o estado físico a partir dos momentos, nem definir retroativamente vetores por Cholesky.

No ledger físico existente, a primeira obrigação continua sendo identificar o destino dos quatro canais do defeito — proveniência Green, cruzamentos, resíduos de readout e completion — sob um transporte vetorial efetivamente definido. O teorema existente do limite não zera esses canais. Receber seu anulamento como hipótese não resolveria a missão.

Os certificados finitos `H6/K6` e suas realizações físicas permanecem resultados distintos dessa ponte em toda ordem. Nenhum deles foi alterado ou usado para fabricar os polinômios ou seus pareamentos.

### Provas, confiança e reprodução

Há **37 teoremas e 4 definições públicos novos**, em cinco módulos de pesquisa, com raízes enumeradas em `public-roots.json`. `Audit.lean` executa `#print axioms` para todas as 41 declarações e percorre os tipos e corpos de suas dependências.

A auditoria registra **5.405 constantes transitivas**. Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos. Os consumidores canônicos de sinais explicitamente bloqueados no script não aparecem nessa dependência. Não há `sorry`, `admit`, `native_decide` ou novos axiomas matemáticos.

O arquivo `evidence/validation.json` contém os comandos, códigos de saída, durações e hashes das fontes. Os logs são preservados. Foram executados:

- Build focado das três fontes originais do operador com `lake build --wfail`.
- Compilação explícita dos cinco módulos novos e da auditoria com `-DwarningAsError=true`.
- `lake build --wfail` do repositório principal.
- Auditorias existentes de Foundation, Geometry e Analysis.
- `git diff --check`, busca de escapes de confiança e verificação de preservação das fontes e dos arquivos preexistentes do operador.

O build raiz, por si só, não inclui esses módulos de pesquisa: sua compilação explícita faz parte do script. Os resultados matemáticos novos são provas Lean, não testes numéricos. Não houve campanha de momentos ou aumento de precisão para esta tarefa.

Para reproduzir no host `llm`, com a branch desta entrega em um checkout de `geometry-of-numbers` e o ambiente original do operador disponível:

```bash
cd /caminho/do/checkout/geometry-of-numbers/research/theta-polarized-green
python3 validate.py
```

`compile_module.sh` usa o ambiente Lake em `/home/thlinux/carry-self-adjoint-operator`, sem alterar suas dependências. `validate.py` verifica também os dois arquivos de pesquisa não rastreados preexistentes no operador; eles não são parte desta entrega.

## E — Próximo passo mínimo

O teste prioritário não é tentar novamente uma raiz quadrada de `P_n` ou anular o resíduo por definição: esses candidatos já falham.

O próximo passo concreto é **definir, a partir do estado TFVD original com suas caudas, o destino de uma porta enriquecida no lado teta**, antes da integral. A porta deve carregar os dois traços e o retorno; o kernel positivo `Φ` sozinho é apenas um peso, não essa porta.

O primeiro teorema a testar deve calcular o pareamento de **duas entradas materiais independentes** e mostrar como cada canal do ledger nativo chega ao interior e ao fluxo teta. O resultado pode ter um defeito, mas esse defeito precisa ser derivado dos canais originais e comparado com o resíduo explícito desta rodada. Começar pela diagonal de ordem zero e pelo cruzamento de ordens zero e um permite refutar cedo um transporte incorreto, sem ajustar constantes.

Ainda não há uma fórmula dessa aplicação vetorial nas declarações inspecionadas. Escrever apenas “existe uma isometria que fornece a Hankel” repetiria o objetivo como hipótese. A busca seguinte precisa fornecer a aplicação e sua identidade de síntese, não apenas o predicado que ela deveria satisfazer.

**Resposta à pergunta central:** foi possível provar preservação de informação dos testes polinomiais e transporte bilinear Green com defeito explícito. Não foi possível deduzir, dessas identidades, uma Gram positiva canônica nem o transporte unitário físico proposto. A obstrução demonstrada incide nas realizações locais/polinomiais testadas; a proposta não local da síntese completa permanece aberta.

Fim do relatório.
