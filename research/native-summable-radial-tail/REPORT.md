# Cauda radial somável da família nativa ímpar

**PASS para o gate quantitativo de famílias finitas fixas; a desigualdade de sinal permanece aberta.** Base: geometry-of-numbers main em c66638f05ee432b6bd7d33e4d53737bd9c3d52f6. O resultado vale para cada conjunto finito de ordens ímpares e coeficientes reais fixos; não afirma uma constante uniforme entre famílias nem positividade Hankel em toda ordem.

## A — Objetos e resultados anteriores

A fonte é finiteOddJetSource S c k de OddFiniteEnergy.lean, soma literal dos jets radiais nativos de ordem 2*r+1. Sua síntese completa em dois canais é finite_odd_source_original; o balanço é a fullEnergy existente. O lema finite_odd_source_pairing preserva ambos os cruzamentos ordenados antes da leitura real. As provas anteriores dão o cancelamento de Taylor (odd_pair_taylor_cancellation), a fórmula Lambda em toda ordem e a identidade da primeira correção na fonte completada (#133); o resto e sua derivada têm cotas efetivas a partir da resposta nativa (#130). A PR #131 fornece regularidade para qualquer prefixo finito; #132–#133 tratam a derivada e o integral das combinações originais. A PR #41 separa a ortogonalização algébrica do sinal: não usamos a positividade de um pivô para esta cauda.

## B — Teorema novo e constantes

Para S : Finset ℕ, c : ℕ → ℝ, seja

$$
N=2\sup S+2,\qquad K_0=4N,\qquad t_k=(k+1)^{-1},
\qquad D_k=\operatorname{fullEnergy}(k,\operatorname{finiteOddJetSource}(S,c,k)).
$$

A convenção de Finset.sup dá zero para o conjunto vazio. Para quaisquer K ≥ K₀, [finite_odd_energy_absolute_tail](SummableFamily.lean) prova, no Lean,

$$
\sum_{j=0}^{\infty}|D_{K+j}-D_{K+j+1}|
\leq \frac{B(S,c)}{(K+1)^2}.
$$

O mesmo teorema prova a somabilidade absoluta e que a soma assinada telescopa para D_K - oddCanonicalForm S c; family_budget_tendsto_zero prova que o lado direito tende a zero. family_increment_budget prova cada estimativa de incremento, e family_energy_tendsto identifica o limite. Não há hipótese de sinal, inversibilidade, positividade Hankel ou sinal de Schur. D_k permanece a forma física existente, com retorno, fase, amplitude original e cruzamentos; não é uma nova Gram. Na convenção existente, a diferença das normas quadradas dos dois canais é 2 D_k, como formalizado na regressão de seis fontes.

A constante é finita e explícita. Com M=r+s+3, escreva

$$
f_{rsj}=(-1)^r\,\operatorname{nativeOddBeta}(s,j)\frac{(j+1)!}{(j+2r+3)!},\qquad
W_{rs,p}=\sum_{j=0}^{2s+1}|f_{rsj}|(j+1)^p,
$$

$$
A_{rs}=|\operatorname{spatialCorrection}(2r+1,2s+1)|
 +W_{rs,2M+1}+W_{sr,2M+1}+W_{rs,2M+2}+W_{sr,2M+2},\quad
B(S,c)=\sum_{r,s\in S}|c_rc_s|A_{rs}.
$$

Esses são exatamente oddFilterBudget, pairConstant e familyConstant; os coeficientes dos filtros e spatialCorrection são expressões racionais dos índices, e os coeficientes c são os dados fixos da família. A magnitude do momento na correção foi limitada pelo teorema anterior de decaimento, não por hipótese de sinal. O orçamento é conservador; sua utilidade não requer que seja uma margem positiva. family_constant_nonneg certifica sua não negatividade. Como teste exato, first_pair_constant_value prova A₀₀ = 209/3; six_grid_cutoff_value prova K₀ = 24 para S={0,1,2}.

Os passos formais são:

1. finite_odd_energy_pairing_at_cutoff torna explícito o índice de regularidade, mantendo os dois cruzamentos.
2. effective_response_expansion identifica, no disco certificado, a resposta original com sua parte finita e effectiveResponseRemainder; effective_remainder_norm e effective_remainder_deriv_bound dão limites 1/2 e 2.
3. odd_pair_effective_expansion e normalized_odd_pair_effective_at_regular aplicam os cancelamentos binomiais à síntese existente antes das desigualdades; retêm os dois filtros ordenados. A expressão é h_(r+s+1) - t²*spatialCorrection*h_(r+s+2) + t⁴*R_rs(t).
4. odd_pair_effective_tail_bound e odd_pair_tail_derivative_bound controlam o resto e sua derivada por somas finitas dos endereços. family_curve_derivative_bound obtém |D'_c(t)| ≤ 2*B(S,c)*t no disco; squared_step_scaled integra sem hipótese de sinal.
5. O telescópio físico usa radial_budget_hasSum já existente. Não inferimos positividade a partir da redução absoluta da cauda.

## C — Regressão de seis endereços e limites

[six_input_eq_finite_odd](SixRegression.lean) identifica literalmente S={0,1,2} com os jets 1,3,5 de sixInput; six_physical_eq_twice_finite_energy verifica o fator exato: sixPhysical k = 2 * fullEnergy. O resultado antigo não foi enfraquecido: six_original_absolute_tail_regression transporta a cota da PR #130, e six_anchor_tail_regression mantém K=10^20-1 e cota 10^-40 para o balanço sixPhysical. A positividade do ponto âncora de #130 continua sendo um resultado separado, não utilizado para provar a estimativa geral.

Não foi refutada a positividade global, nem demonstrada uma nova lei de sinal. A constante geral não é apresentada como a constante ótima da PR #130. A derivada limitada e a cauda pequena também não estabelecem, por si mesmas, que o saldo físico é positivo.

## D — Verificação e proveniência

- Todos os módulos novos foram compilados com lean -DwarningAsError=true; a raiz foi compilada com lake build --wfail (8.849 jobs). As auditorias scripts/audit-foundation.sh, audit-geometry.sh e audit-analysis.sh passaram.
- [Audit.lean](Audit.lean) executa #print axioms para os 39 teoremas novos e percorre transitivamente tipos e corpos dos dois teoremas gerais. A execução examinou 57.971 dependências e permitiu apenas propext, Classical.choice e Quot.sound, sem os certificados finitos de positividade e equivalências proibidas pela auditoria. Os teoremas da regressão também tiveram #print axioms; a regressão herda deliberadamente o certificado histórico #130 e não integra essa auditoria de independência do resultado geral. A tentativa de incluí-la no mesmo guard encontrou CarryIntegralCertificate.material_theta_integral_input; isso é registrado como dependência do certificado histórico, não apagado.
- Não foram usados sorry, admit, native_decide nem axiomas novos nos módulos novos. A síntese e os pesos existentes não foram alterados.
- Para as 200 dependências históricas de pesquisa foram reutilizados objetos compilados antes desta execução, do arquivo com SHA-256 d374041b5b017e2541039b6993ed3f53b244f20a1dd8c2e7bb851ba09eca288a. O restaurador verificou hashes de fontes e objetos, ancestralidade, toolchain, manifesto, operador e pacotes, e registrou que tais objetos não foram recompilados nesta execução. Os módulos desta pesquisa e as dependências #131–#133 indicadas no script foram recompilados; isto não equivale a uma recompilação limpa dos 200 módulos históricos. O build raiz foi executado em cache de trabalho isolado.

No servidor de pesquisa, com o checkout e os pacotes nas posições existentes, bash research/native-summable-radial-tail/validate.sh --focused recompila os módulos novos e a auditoria, depois de verificar o arquivo histórico em cache. --full também executa o build raiz e as três auditorias de camada. O arquivo de cache deve existir em research/native-all-order-radial-tail/.cache/input-cache.tar.gz com o hash acima; o caminho local usado nesta execução também está em /tmp/native-effective-radial-budget-verified-cache.tar.gz. A verificação falha fechada se o arquivo, fonte, pins ou estado do operador não coincidirem. Os resultados e hashes constam de evidence/ e SHA256SUMS.

## E — Menor próxima obrigação matemática

Para uma direção crítica original específica c, certificar no mesmo corte (ou em um corte posterior) D_K(c) > B(S,c)/(K+1)^2, sem pressupor o sinal do Schur. A cauda dá então uma cota inferior positiva ao limite; a igualdade física anterior relaciona o limite à forma canônica, e a PR #41 entra para identificar o residual de Schur sob as hipóteses de inversibilidade realmente necessárias. Este gate exige uma estimativa de sinal independente; a prova atual não o fornece.
