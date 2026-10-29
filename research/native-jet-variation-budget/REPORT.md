# Jets nativos móveis: orçamento da derivada e teste da lei de sinal

**Classificação: PARTIAL.** A derivada do pareamento físico completo recebeu uma cota calculável para qualquer família finita diferenciável e para os próprios stencils nativos. Uma lei de sinal all-order e um orçamento integrado de incrementos para direções críticas arbitrárias continuam abertos. A conversa fornecida é tratada como pista e candidata, não como instrução que altere as fontes.

## A — Resultados já disponíveis

A base é o commit `527c15baa36c6b6d3b301f8b2378b4a9c8920004`, cabeça da PR #131, empilhada sobre a #130. A #131 limita o erro da resposta truncada para uma grade finita arbitrária após a síntese completa. A #130 fornece `native_response_exact_remainder`, `source_remainder_norm_le_one`, `source_remainder_deriv_bound`, além da expansão efetiva para seis fontes e do seu controle de incrementos num caso crítico específico.

Uma correção importante da indicação feita ao final da #131: `materialPair_hasDerivAt`, `scaled_material_hasDerivAt` e `physical_material_derivative` **já valem para N arbitrário**. Não foi necessário redemonstrar a identidade de derivação. `radial_jet_hasDerivAt` identifica a velocidade dos stencils originais; `radial_jet_curve_complete_jet` os identifica com os jets físicos completos na grade, para ordem abaixo do tamanho do prefixo. A #41 distingue ortogonalização algébrica de positividade; nada aqui recebe positividade de Hankel nativa como hipótese.

## B — O que foi demonstrado agora

Em `VariationBudget.lean`, `variation_error_bound` mantém dois vetores complexos independentes e suas duas velocidades. Controla a diferença das variações do pareamento completo por erros distintos ε na resposta e η na sua derivada. `physical_derivative_approximation` conecta essa desigualdade à derivada da fonte física original. O resultado usa a identidade física existente apenas depois da síntese das duas pernas.

Em `RemainderVelocity.lean`, `native_response_derivative_prefix_error` usa o resto completo da resposta logarítmica original, incluindo a derivada desse resto, sem substituir a fonte. `radial_response_derivative_prefix_error` transporta a cota a cada endereço original. Se `z_i=i(i+1)t`, com `i` inicial unidade imaginária, `r_i=|z_i|` e M ordem de truncagem, o erro de velocidade em cada endereço é limitado por

$$\eta_i=\frac{i+1}{2}\bigl((2M+1)r_i^{2M}+4r_i^{2M+1}\bigr).$$

Em `FiniteVelocityBudget.lean`, `physical_derivative_explicit_budget` soma as contribuições de todos os endereços e aplica as cotas ao pareamento da fonte completada. As hipóteses são `t>0`, `N|t|<1/4` e diferenciabilidade dos dois vetores materiais em t; a regularidade dos denominadores e o domínio da fonte são derivados de resultados existentes, sem recebê-los como novas hipóteses. Escrevendo ε para a soma das cotas da #131, η para a soma das `eta_i`, e `X,Y,X',Y'` para as somas dos módulos dos coeficientes e de suas velocidades, o erro entre a derivada física e a variação calculada com a resposta truncada é limitado por

$$\frac2t\,\varepsilon(X'Y+XY')+\frac2{t^2}(t\eta+\varepsilon)XY.$$

A declaração Lean conserva os mesmos fatores como normas complexas, equivalentes aos acima para `t>0`. `native_jets_derivative_explicit_budget` especializa a cota aos stencils fatoriais originais. `native_jet_velocity_size` e `native_jets_ordered_velocity_budget` expõem os fatores exatos de velocidade `m/t` e `n/t`. Isso evidencia a dependência da ordem e da escala; a cota não é uniforme em N ou quando t tende a zero.

Em `RadialExtrapolation.lean`, `quadratic_cancellation` e `extrapolation_error` provam a identidade em duas resoluções e a cota `5 M |h|⁴/12`. `original_radial_step_half` identifica o meio-passo na grade radial original. `six_source_extrapolation_effective` aplica a identidade à expansão completa de seis fontes da #130, com `M=10^20` sob as hipóteses enunciadas de faixa, não anulação e `|u|,|v|≤1`. Não usa orientação da correção. Esta é uma ferramenta de erro, não uma nova prova de sinal. Para `h=10^-10`, o limite aritmético é exatamente `1/240000000000000000000`, cerca de `4,167×10^-21`; ainda não certificamos o valor extrapolado nessa escala.

## C — O que foi refutado ou delimitado

O controle de dois átomos proposto na conversa foi confirmado **em Lean**, sem tratá-lo como outra fonte Carry. Para

$$g_j=(1/100)^{j+1}+(1/1000)(1/10)^{j+1},$$

`two_atom_gram` e `two_atom_positive` demonstram a forma Hankel positiva semidefinida em qualquer dimensão, e `two_atom_majorant` demonstra em toda ordem o majorante `g_j ≤ (22/175)^{j+1}-(1/25)^{j+1}`. Os teoremas `exact_parameter`, `exact_positive_residual` e `exact_negative_correction` verificam exatamente

$$a=1/55,\quad p=81/1100000000>0,\quad C=-3347/12100000000<0.$$

O polinômio de correção é o mesmo padrão de coeficientes da direção crítica de quatro endereços em `CriticalOddTaylor.lean`, aqui avaliado numa sequência de controle. Logo, positividade de Hankel e majorante, mesmo juntos, não forçam esse sinal. Isso não refuta a lei para a fonte nativa.

O teste `check_note.py` conferiu em frações exatas os seis coeficientes propostos, o contraexemplo e a constante de extrapolação. Também calculou diretamente a soma binomial com o denominador de Cauchy original para os 64 pares ímpares `m,n∈{1,3,…,15}`: a camada principal deu `-1` e a seguinte, `-Lambda_{m,n}`. São controles finitos da soma combinatória, preservando os dois índices; ainda não são uma identidade do pareamento físico em toda ordem. **A identidade combinatória proposta para todas as ordens não foi provada** nem conectada em Lean aos stencils gerais. A tabela numérica do anexo e a conjectura sobre o sinal para ordens maiores não foram reproduzidas nem certificadas nesta investigação.

## D — O que permanece aberto

A nova cota é pontual na derivada e preserva todos os cruzamentos. Ainda falta controlar a variação truncada e integrar o orçamento na escala correta entre dois pontos radiais para uma **combinação crítica arbitrária**, com constantes efetivas que levem em conta os coeficientes da direção e o crescimento dos stencils. O controle existente para seis fontes não transporta automaticamente sua margem de sinal a todas as ordens. Também falta uma desigualdade independente da fonte que compare o saldo crítico com a cauda total.

A proposta `Lambda_{m,n}` é uma candidata estrutural promissora, mas sua prova exige extrair a primeira correção do pareamento **dos stencils físicos originais**. `CarryEulerNewtonAll.shifted_falling_address` e `CarryMaterialVariation.jet_kernel_monomial` oferecem uma rota para controlar os pesos de diferenças finitas e o cancelamento da camada principal; não provam a fórmula candidata por si. Nenhuma medida positiva auxiliar, nem a simples convergência de uma cauda, entrega o sinal canônico.

## E — Próximo passo mínimo e reprodução

Para dois jets originais de ordens ímpares arbitrárias, demonstrar primeiro a identidade combinatória concreta que os controles finitos sugerem:

$$\frac1{m!n!}\sum_{i=0}^m\sum_{j=0}^n(-1)^{m+n-i-j}\binom mi\binom nj\frac{(i+1)^{m+n+3}+(j+1)^{m+n+3}}{i+j+2}=-\Lambda_{m,n}.$$

Depois transportar essa identidade ao pareamento físico completo, incluindo fases e normalizações, usando `shifted_falling_address`, a identidade completa de Green e `jet_kernel_monomial`; só então perguntar pelo sinal. Em paralelo matemático, usar a cota de derivada desta investigação para integrar o resto na grade, com coeficientes críticos concretos e sem descartar os termos mistos.

No host `llm`, com a base indicada, o operador original e suas dependências preservados:

```bash
python3 research/native-all-order-radial-tail/restore_verified_cache.py
bash research/native-jet-variation-budget/validate.sh
python3 research/native-jet-variation-budget/check_note.py
```

Validação local no `llm`: cinco módulos matemáticos novos compilados com warnings como erros; `#print axioms` em 23 teoremas; auditoria transitiva de tipos e corpos de 32 declarações, percorrendo 57.625 dependências e bloqueando certificados finitos de positividade; `lake build --wfail` e auditorias Foundation, Geometry e Analysis. Os únicos axiomas detectados foram `propext`, `Classical.choice` e `Quot.sound`. O teste racional dos 64 pares foi executado separadamente.

O restaurador requer o arquivo `.cache/input-cache.tar.gz` dentro de `research/native-all-order-radial-tail`, com SHA256 `d374041b5b017e2541039b6993ed3f53b244f20a1dd8c2e7bb851ba09eca288a`. O pacote de evidências contém o cache de entrada; 200 objetos ancestrais são verificados e reutilizados, e os novos módulos são compilados. As evidências e os comandos estão em `evidence/`. Não se afirma execução da CI externa.

Fim do relatório — orçamento pontual da derivada e controle estrutural negativo certificados; integração de incrementos e lei canônica all-order permanecem abertas.
