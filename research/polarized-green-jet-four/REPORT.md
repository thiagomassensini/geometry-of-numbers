# Extração polarizada Green para J₀, J₂ e J₄

**Classificação: PARTIAL.** Continuação do próximo alvo da PR #87: desenvolver o balanço Green da direção `J₄−u₁J₂−u₀J₀`, preservando dois argumentos independentes, os 25 cruzamentos e o resto analítico. A positividade all-order permanece aberta.

Base imutável: `16caee18d2667dc54ab6fdb37750c136b2366b06`, draft [PR #87](https://github.com/thiagomassensini/geometry-of-numbers/pull/87). Branch: `agent/polarized-green-jet-four`; base de revisão: `agent/critical-green-finite-part`. Sem merge automático. Fonte, métrica, bordos, retorno, completion, pins e trabalhos anteriores preservados.

## A — O que já estava demonstrado

As PRs #81–#87 identificaram os jets físicos originais e sua reconstrução Green completa. Reutilizam-se `physical_jet_original`, `refined_source_green_split`, `residual_basis_all`, `basis_mean`, `basis_contrast`, `source_basis_real` e `physical_column_inner`. Os dois casos excepcionais de bordo continuam na fórmula de `residualFeature`; não são substituídos pelo stencil interior.

`common_even_jets`, da construção anterior de refinamento comum, já fornece limites de pareamentos para ordens pares arbitrárias. Não se apresenta essa identificação qualitativa como descoberta nova. A #87 tinha a expansão com resto para `J₂−aJ₀`; aqui se extrai o balanço polarizado até J₄, com coeficientes explícitos e controle quantitativo do erro.

A [PR #41](https://github.com/thiagomassensini/geometry-of-numbers/pull/41), commit `ee56930a2c30456cfbd214a29bb31b12d3977204`, já provou `NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit`. Sua hipótese é a inversibilidade do prefixo antigo. A nova investigação reutiliza esse teorema diretamente, sem reintroduzir `PosDef` nem duplicar sua prova.

Também se reutilizam a funcional `momentForm`, a construção `coefficientPolynomial` e `momentForm_coefficients` da #41. Cinco fontes antigas inalteradas são recuperadas desse commit e compiladas em cache ignorado, com hashes registrados. Não se altera nem se presume integrada a draft #41.

A analiticidade e os coeficientes da resposta completada são os anteriores: `completedNativeGreenNormalizedResponse_analyticAt`, `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` e o anulamento dos coeficientes pares. Não se usam os certificados de sinal da #43 ou H6/K6 nas provas novas.

## B — O que foi demonstrado agora

### Construção física antes dos coeficientes canônicos

κ=k+1 é a escala radial; δ=i/κ; zⱼ=(j+1)δ. O índice k não é a profundidade Carry, a ordem do jet ou o endereço material. R=−F′/(2F) continua sendo a resposta da característica completada original. Na reconstrução Green, 0<η<1.

A forma física permanece assinada:

\[
 \Phi(x,y)=\tfrac12(\langle x^+,y^+\rangle-\langle x^-,y^-\rangle).
\]

`jetInput` é o stencil anterior, com o mesmo fatorial, passo complexo e pesos binomiais. `jet_input_source` identifica sua síntese com `physicalJet`. Para toda dimensão finita N, `even_polynomial_source` prova a igualdade vetorial

\[
 S_k(c)=\sum_{j<N}c_jJ_{2j}(k).
\]

Este resultado de linearidade não afirma uma lei de sinal em N. Os jets existem antes de escolher os coeficientes c.

O restante da expansão é demonstrado para **dois vetores reais arbitrários** c,d∈ℝ³, correspondentes a polinômios de grau até dois na variável de momentos. `quartic_source_original` identifica

\[
 S_k(c)=c_0J_0(k)+c_1J_2(k)+c_2J_4(k).
\]

Os cinco pesos são forçados pela mesma fonte:

\[
 w(c)=\left(c_0-\frac{c_1\kappa^2}{2}+\frac{c_2\kappa^4}{24},\quad
 c_1\kappa^2-\frac{c_2\kappa^4}{6},\quad
 -\frac{c_1\kappa^2}{2}+\frac{c_2\kappa^4}{4},\quad
 -\frac{c_2\kappa^4}{6},\quad\frac{c_2\kappa^4}{24}\right).
\]

`quartic_input_five` prova a identidade de entradas, antes de aplicar a síntese. Não se ajusta nenhum peso para obter positividade.

### Green completo e 25 cruzamentos

`quartic_full_green` demonstra primeiro a identidade **complexa** em dois argumentos independentes:

\[
 \Phi(S_c,S_d)=\Phi(B_c,B_d)+\Phi(B_c,E_d)+\Phi(E_c,B_d)+\Phi(E_c,E_d).
\]

`quartic_residual_cross_zero` prova EE=0 a partir das duas pernas iguais do residual, preservando o vetor residual e os setores mistos. `quartic_mixed_twenty_five` mantém os 25 pares ordenados e a conjugação dos coeficientes. Não se substitui BE+EB por 2BE para argumentos independentes.

Somente então `quarticBalance` toma a parte real dos três setores restantes. `quartic_balance_twenty_five` a identifica exatamente com

\[
 \mathcal E_k(c,d)=\sum_{i,j=0}^4 w_i(c)w_j(d)
 \frac{\kappa\,[\Im R(z_i)+\Im R(z_j)]}{i+j+2}.
\]

`quartic_balance_five_samples` reúne essa soma em cinco avaliações da resposta, sem apagar nenhum cruzamento. A fórmula integral não é utilizada para criar a fonte ou alterar o produto físico.

As hipóteses locais de não anulação de F e E⁺ nos seis nós do prefixo são descarregadas eventualmente por `five_regular_eventually`. O sexto nó é necessário às diferenças de resposta do residual no quinto endereço; não é uma fonte independente descartada.

### Parte finita e duas correções explícitas

Se p_c(X)=c₀+c₁X+c₂X², a parte finita é

\[
 P(c,d)=\sum_{i,j=0}^2c_id_jh_{i+j}=\mathcal L_h(p_cp_d).
\]

`moment_pairing_original_functional` identifica essa expressão com a **mesma funcional da #41**, em dois argumentos. A interpretação permanece algébrica; não se presume que seja uma norma positiva.

A primeira correção é C(c,d)=cᵀM_Cd, onde

\[
 M_C=-\begin{pmatrix}
 h_1&20h_2&126h_3\\
 20h_2&14h_3&75h_4\\
 126h_3&75h_4&55h_5
 \end{pmatrix}.
\]

A correção seguinte é Q(c,d)=cᵀM_Qd, com

\[
 M_Q=\begin{pmatrix}
 h_2&231h_3&6027h_4\\
 231h_3&147h_4&3102h_5\\
 6027h_4&3102h_5&2002h_6
 \end{pmatrix}.
\]

`readout_fifteenth_remainder` expande a mesma resposta até grau 13 e conserva um resto analítico de ordem 15:

\[
 -iR(it)=\sum_{n=0}^{6}(-1)^nh_nt^{2n+1}+t^{15}\mathcal R(t).
\]

`quartic_exact_expansion` demonstra, para cada c,d e η admissível, eventualmente,

\[
 \boxed{\mathcal E_k(c,d)=P(c,d)+\kappa^{-2}C(c,d)
       +\kappa^{-4}Q(c,d)+\kappa^{-6}U_{\mathcal R}(c,d,\kappa^{-1}).}
\]

A fórmula explícita de U, incluindo todos os termos polinomiais e as cinco avaliações de 𝓡, está em `errorReadout`, `higherPolynomial` e `normalizedMass`. A continuidade do resto é demonstrada. Nenhuma energia renormalizada toma o lugar do balanço original.

`quartic_finite_limit`, `quartic_correction_limit` e `quartic_fourth_limit` provam os três limites correspondentes. `quartic_sixth_error_bound` prova

\[
 \exists M>0,\quad
 |\mathcal E_k-P-\kappa^{-2}C-\kappa^{-4}Q|\le M\kappa^{-6}
 \quad\text{eventualmente}.
\]

M e o limiar podem depender dos coeficientes e da fonte. Não se afirma um cutoff numérico ou uniformidade na ordem.

### Direção de Schur e ortogonalização sem sinal

Para uma sequência m, as definições reutilizam a matriz, os cruzamentos e a inversa originais:

\[
 A=(m_{i+j})_{i,j<2},\quad b=(m_2,m_3)^T,\quad u=A^{-1}b,
 \qquad c_*=(-u_0,-u_1,1).
\]

Sob a hipótese explícita **IsUnit A**, `critical_coefficients_solve` prova Au=b. `critical_moment_pairing` aplica o teorema da #41 e obtém

\[
 P_m(c_*,c_*)=\operatorname{sourceMomentSchur}(m,0,2).
\]

`inverse_schur_source_original` conserva o mesmo estado

\[
 S_k(c_*)=J_4(k)-u_1J_2(k)-u_0J_0(k).
\]

`critical_old_pairing_zero` prova a ortogonalidade algébrica a **todo** o espaço antigo:

\[
 P_m(c_*,(x_0,x_1,0))=0\quad\text{para todo }x\in\mathbb R^2.
\]

Para os momentos canônicos originais, `critical_green_limit` e `critical_green_old_limit_zero` transportam essas identidades ao limite do balanço físico completo. `critical_green_correction_limit` recupera C(c*,c*) como primeira correção ao Schur.

A ortogonalização é uma consequência da equação Au=b e da identificação física do pareamento, sem pressupor o sinal do residual. Isso não fornece positividade da forma assinada ou whitening para a identidade. Os estados físicos são anteriores; a escolha posterior de c* é a leitura algébrica da #41.

### Compatibilidade exata com a PR #87

`PrefixRegression.lean` prova cinco regressões: para c=d=(−a,1,0), a entrada, o balanço Green, a parte finita e as duas correções são exatamente os da #87. São igualdades Lean, não apenas testes numéricos. O novo termo J₄ pode ser zerado sem alterar a normalização ou o estado anterior.

### Validação e reprodução

**PASS nas 17 verificações sequenciais**, no host canônico llm, Lean `v4.32.0`: proveniência, geração da auditoria, build nativo focado com `--wfail`, seis módulos novos e `Audit.lean` com avisos tratados como erros, diagnóstico 80/120 dígitos, build raiz com `--wfail`, auditorias Foundation/Geometry/Analysis, preservação da base e `git diff --check`.

Há **38 teoremas e 20 definições**, totalizando 58 raízes públicas no namespace `CarryPolarizedFour`.

| Grupo | Raízes | Constantes únicas em tipos/corpos | Controle |
| --- | ---: | ---: | --- |
| Construção física | 27 | 5919 | Nenhuma definição de estado por momentos canônicos; bloqueio dos consumidores posteriores listados. |
| Extração, Schur e regressões | 31 | 6579 | Sem certificados finitos de sinal ou polinômios theta como dependências listadas no guard. |
| União | 58 | 6645 | Somente `propext`, `Classical.choice`, `Quot.sound`. |

Os **37 módulos ancestrais** e as **cinco fontes antigas inalteradas da #41** foram recompilados e registrados por hash. Não há `sorry`, `admit`, `native_decide` ou novos axiomas nas fontes novas. Os dois arquivos não rastreados preexistentes no operador tiveram seus hashes conferidos; fontes nativas, pins, módulos históricos e main foram preservados. A validação é local em Lean, sem afirmação sobre CI remoto.

Comandos, logs e SHA das fontes novas estão em `evidence/validation.json`; o audit também imprime os axiomas do lema antigo da #41 efetivamente reutilizado.

Os módulos de pesquisa são compilados explicitamente, pois o build raiz não os importa automaticamente. Auditoria transitiva de tipos e corpos, incluindo constantes privadas, e `#print axioms` para cada raiz pública. Construção física auditada sem momentos como entradas; identificação analítica auditada sem os certificados finitos de sinal listados no guard.

Reprodução no host canônico llm, em checkout desta branch e com as dependências anteriores preservadas:

```bash
cd research/polarized-green-jet-four
mkdir -p evidence
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 build_pr41.py > evidence/pr41-build.log 2>&1
python3 validate.py
```

`build_pr41.py` lê as fontes exatas da draft #41 do commit registrado; não altera módulos históricos. Se necessário, buscar antes o objeto Git da PR. `record_provenance.py` compara os hashes das fontes e artefatos dos ancestrais e registra os módulos nativos e os pins. Nenhuma dependência é atualizada.

O diagnóstico Python usa a característica original via sua identificação downstream já provada com xi. Não fornece zeros, alturas ou tabelas de momentos, e não reexecuta toda a síntese material TFVD. Extrai sete momentos pela recorrência `2FR=−F′`, verifica os 25 cruzamentos físicos, BE e EB separadamente, a recomposição completa e os limites escalados para argumentos independentes e para a direção crítica. Os valores diagnósticos na direção crítica foram:

| Quantidade | Valor aproximado | Estatuto |
| --- | ---: | --- |
| P(c*,c*) | 1,11464160449679×10⁻¹³ | Numérico; a identificação exata com Schur é provada sob IsUnit A. |
| C(c*,c*) | +1,07475689246236×10⁻¹² | Sinal somente numérico nesta investigação. |
| Q(c*,c*) | −2,59108195253221×10⁻¹³ | Sinal somente numérico nesta investigação. |

A primeira correção observada tem sinal oposto ao da direção anterior da #87. Isso orienta a próxima investigação, mas não constitui aqui um contraexemplo formal a uma lei universal de sinal. As provas extraem os coeficientes sem receber seus sinais.

No nó correspondente a s=0, a avaliação usa Γ(1+s/2)=(s/2)Γ(s/2), removendo o polo artificial da expressão não simplificada; a característica não é alterada. Aritmética 80/120 dígitos é evidência numérica, não uma prova de sinal ou de propriedade infinita.

## C — O que não foi demonstrado ou pode ser confundido

Não se demonstrou uma nova impossibilidade da geometria. O anulamento do residual na forma assinada não significa vetor nulo, redundância ou permissão para descartar cruzamentos.

A identidade P=𝓛_h(pq) não é uma representação de Hilbert positiva. As matrizes M_C e M_Q são coeficientes de uma expansão, não novas métricas nem operadores de alturas.

Não se inferiu o sinal de C(c*,c*) ou de Q(c*,c*) dos sinais de suas entradas ou das normas de cada canal. A condição IsUnit A é necessária à utilização da inversa como solução da equação antiga; não foi apresentada como condição equivalente ao sinal do próximo pivô.

## D — O que permanece aberto

A expansão polarizada é provada para o espaço gerado por J₀,J₂,J₄. A identidade vetorial linear é geral em dimensão finita; a expansão quantitativa e a estimativa não foram anunciadas em ordem arbitrária.

O transporte de Schur e a ortogonalidade crítica recebem inversibilidade do prefixo antigo. Não se provou aqui essa condição para todos os prefixos, nem uma desigualdade independente da fonte que force todo Schur seguinte a ser não negativo. H6/K6 e certificados finitos anteriores não são usados como premissas dos resultados novos.

O objetivo global permanece OPEN: falta uma lei de sinal para o balanço completo ou uma realização positiva que identifique exatamente o kernel canônico, conservando os termos de bordo, cruzamentos e cauda.

## E — Próximo passo mínimo

Demonstrar a fórmula em dois índices arbitrários para a primeira correção, diretamente dos pesos binomiais dos jets e do kernel Cauchy anterior. A candidata concreta é

\[
 B_n=\frac{(n+1)(n+2)}2,\qquad
 A_n=\frac{(n+1)(n+2)(n+3)(3n+4)}{24},\qquad
 d_{ij}=A_{2i}+A_{2j}-B_{2i}B_{2j}.
\]

Ela recupera os pesos 1,20,126,14,75,55 do bloco provado. `derive_coefficients.py` confere por soma binomial racional exata os 25 pares 0≤i,j≤4, **sem momentos como entradas**. O resultado está em `evidence/symbolic-coefficients.json`; é um teste finito da próxima obrigação, não uma prova Lean all-order.

O teorema a atacar deve identificar essa lei com o coeficiente de κ⁻² do mesmo pareamento físico em ordens arbitrárias, mantendo os dois argumentos e o resto. A escolha do ponto inicial dos stencils é a original; B e A não são pesos novos da fonte nem uma nova métrica.

Essa fórmula deve distinguir o viés da discretização radial do residual de Schur. Se uma desigualdade geométrica independente puder orientar o termo finito, demonstrá-la com o mesmo balanço. Uma regra sobre a primeira correção, sozinha, não prova positividade do pivô. Não extrapolar os sinais dos testes finitos para uma lei all-order.

FIM DO RELATÓRIO — POLARIZED_GREEN_JET_FOUR
