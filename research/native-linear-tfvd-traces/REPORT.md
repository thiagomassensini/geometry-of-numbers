# TFVD linear com suporte finito arbitrário e os dois traços

**Classificação: PARTIAL para a positividade canônica em toda ordem. A obrigação
do numerador, isolada na PR #97, está demonstrada.** Também foram provados seu
transporte polarizado pelo Green físico, uma cota com o cruzamento de bordo
explícito e um contraexemplo a uma positividade irrestrita desse coeficiente.

Base exata: `9e01b6a8f591046c3478e1faf80af692062a95d4`, PR #97,
branch `agent/native-quartic-boundary-sign`. Esta continuação está na branch
`agent/native-linear-tfvd-traces`, com destino à PR #97, sem merge automático.
Main foi conferida em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
O operador consultado permanece em `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

O espaço é o carrier Cauchy físico original. Escrevemos

\[
\phi_j=\texttt{completedNativeChiralCauchyFeature}\ j,\quad
S=\texttt{physicalCauchySynthesis},\quad M=\texttt{physicalRadialAdvance},
\]

\[
R_\eta=(I-\eta M)^{-1},\qquad G_\eta=\eta M R_\eta^2.
\]

Os nomes Lean são `physicalGreenResolvent` e `physicalGreenOperator`.
Para o Green limitado, usamos `0<η<1`. O multiplicador M é autoadjunto e
contrativo no espaço original. Não se introduz sua inversa.

Reutilizamos:

- `NativeCompletedFiniteGreenResidual.lean`: `coefficientShift`,
  `finiteTfvdBulk_succ`, `finiteCoefficientValve_two_traces`.
- PR #92, `CoefficientPorts.lean`: `coefficient_tower_synthesis`,
  `coefficient_real_bracket`, `coefficient_imag_bracket` e
  `physical_finite_reconstruction`. O coeficiente complexo reúne as duas
  quadraturas das torres reais existentes.
- PR #92, `CompletionCommutator.lean`: `completionCommutator`,
  `completion_commutator_zero` e `completion_commutator_succ`.
- PR #95, `ResponseTaylor.lean`: a definição original
  `monomialWeight 1 j = j+1`, denotada abaixo por p₁.
- PR #96, `ComplementNorm.lean` e `CurvatureKernel.lean`: autoadjunção,
  comutação do resolvente e `resolvent_norm_lower`.
- PR #94, `GreenSeed.lean`: `green_seed_cross` e
  `green_seed_cross_re_pos`, na mesma métrica física.

A PR #97 já demonstrou o sinal do bordo quártico e do coeficiente espacial
completo dessa ordem. Esta continuação conserva esses resultados e não altera
seus módulos. A prova geral do numerador não usa a positividade quártica.

## B — O que foi demonstrado agora

### B.1 — Identidade finitamente suportada, antes da síntese

Para qualquer `c : ℕ →₀ ℂ`, denote
`Cηc = completionCommutator eta (monomialWeight 1) c` e por σ o shift
unilateral `coefficientShift`. O comutador literal satisfaz

\[
(C_\eta c)_0=0,\qquad
(C_\eta c)_{j+1}=\eta^{-1}c_{j+2}-\eta c_j.
\]

`linear_commutator_succ` identifica essa fórmula com o peso nativo p₁.
`linear_commutator_shift_numerator` prova a igualdade de coeficientes inteira:

\[
\boxed{
\sigma C_\eta c
=\eta^{-1}(c-c_0e_0-c_1e_1)-\eta\sigma^2c.
}
\]

Não há cutoff fixado nem hipótese de sinal. A identidade algébrica vale para
todo η real, com a convenção de inversão total do Lean; a interpretação pelo
Green abaixo mantém explicitamente `0<η<1`.

Reutilizando o theorem TFVD existente dos dois traços,
`linear_commutator_tfvd_numerator` também prova

\[
\boxed{
\sigma C_\eta c
=\sigma B_\eta c+2\sigma c-2\eta\sigma^2c-2c_0e_1,
}
\]

onde `Bηc = finiteTfvdBulk eta c`. O termo central `−2c₀e₁` permanece;
não foi absorvido numa redefinição do bulk.

### B.2 — A obrigação física da PR #97

`synthesis_shift` prova `Sσc=MSc` a partir das colunas físicas originais.
Isso é um intertwining para a síntese existente, não uma afirmação de isometria.
Defina somente o readout vetorial dos dois coeficientes iniciais:

\[
T_c=c_0\phi_0+c_1\phi_1
\quad(\texttt{physicalTrace}).
\]

`physical_linear_numerator` resolve exatamente a obrigação proposta:

\[
\boxed{
MS(C_\eta c)=\eta^{-1}(Sc-T_c)-\eta M^2Sc.
}
\]

`physical_linear_tfvd_numerator` transporta também a fórmula em termos do
bulk, conservando `−2c₀φ₁`. As duas são igualdades vetoriais no domínio físico.
Não houve escalarização intermediária ou inversão de M.

### B.3 — Pareamento completo em dois argumentos independentes

Para `0<η<1`, `green_inner_right_numerator` e
`double_advance_pairing` transportam o Green usando somente comutação e
autoadjunção dos multiplicadores limitados originais.

`green_linear_polarized_factor` prova, para quaisquer c e d complexos e
finitamente suportados, com `f_c=Sc`:

\[
\boxed{
\begin{aligned}
\langle f_c,G_\eta S(C_\eta d)\rangle
={}&\langle R_\eta f_c,R_\eta f_d\rangle
-\langle R_\eta f_c,R_\eta T_d\rangle\\
&-\eta^2\langle R_\eta Mf_c,R_\eta Mf_d\rangle.
\end{aligned}
}
\]

Os dois argumentos são independentes. O termo de bordo mantém ambos os
coeficientes iniciais de d e seu cruzamento com toda a entrada c. Só depois
se toma a diagonal real, em `green_linear_diagonal_factor`:

\[
U_\eta(c)=\|R_\eta f_c\|^2
-\Re\langle R_\eta f_c,R_\eta T_c\rangle
-\eta^2\|R_\eta Mf_c\|^2.
\]

Essa U é o pareamento espacial do comutador da resposta linear p₁. Não é
um novo momento, pivô canônico ou substituto do balanço quiral completado.

### B.4 — Uma cota com o bordo original explícito

Da contratividade de M, `advance_contracts` e `green_linear_lower` deduzem

\[
\boxed{
U_\eta(c)\ge(1-\eta^2)\|R_\eta Sc\|^2
-\Re\langle R_\eta Sc,R_\eta T_c\rangle.
}
\]

O cruzamento de bordo não recebeu sinal por hipótese. No subespaço determinado
pelas condições geométricas explícitas `c₀=c₁=0`, ele se anula, e
`green_linear_zero_traces_lower` prova

\[
U_\eta(c)\ge(1-\eta^2)\|Sc\|^2.
\]

`green_linear_zero_traces_pos` conclui sinal estrito quando `Sc≠0`. Essa
condição de não degenerescência está exposta; não se presume injetividade
global da síntese. O subespaço não é imposto à fonte canônica para fabricar
seu sinal. Por exemplo, o stencil quártico anterior tem `c₀=1/24` e `c₁=−1/6`;
a direção quadrática anterior tem `c₀=−1/2` e `c₁=1`. Nenhuma pertence a ele.

## C — O que foi refutado

`green_linear_seed_negative` prova, na fonte-semente original `c=e₀`,

\[
\boxed{U_\eta(e_0)<0\qquad(0<\eta<1).}
\]

De fato, o mesmo comutador dá `Cηe₀=−ηe₁`; o pareamento é
`−η Re⟨φ₀,Gηφ₁⟩`, estritamente negativo pelo theorem físico anterior.
Isso refuta a positividade do coeficiente linear para todas as entradas
finitas e a tentativa de descartar seus traços. Não refuta o sinal das direções
críticas canônicas, o balanço completado, a geometria ou as Hankel canônicas.

Também não se pode aplicar a cota sem bordo aos stencils originais apenas
porque foram produzidos por diferenças: seus coeficientes iniciais não são zero.
A PR #97 já mostrava por que a contribuição quártica concreta precisa ser
conservada. A identidade geral explica agora onde os dois dados entram.

## D — Alcance, dependências e validação

Há quinze teoremas e uma definição públicos em três módulos novos:
`FiniteTraces.lean`, `PhysicalNumerator.lean` e `GreenPairing.lean`.
`Audit.lean` faz `#print axioms` e percorre tipos e corpos das dezesseis raízes.
A compilação explícita auditou 5.051 dependências transitivas, usando somente
`propext`, `Classical.choice` e `Quot.sound`. O guard de ausência da sequência
canônica e da característica completada passou para todos os resultados novos.

Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos novos. Fontes,
amplitudes, fases, pesos, métrica, pins e arquivos históricos são preservados.
As duas quadraturas estão reunidas pelos adaptadores físicos existentes; os
pareamentos conservam cruzamentos antes da diagonal real. O resolvente
limitado completo é mantido: não se fez truncamento de sua cauda.

O suporte de entrada é finito mas arbitrário. Isso não afirma um domínio
all-input do peso não limitado p₁, nem um transporte do operador infinito
completado. Tampouco identifica esta U linear com todo o residual finito.
A fonte não linear, as outras potências da resposta e os cancelamentos entre
setores continuam sendo obrigações distintas. Os certificados finitos
canônicos anteriores permanecem válidos.

`validate.py` recompila os dezoito ancestrais de pesquisa efetivamente
importados, compara os hashes com a base, compila os quatro módulos de prova
e auditoria explicitamente com warnings como erros, roda `lake build --wfail`
e as auditorias Foundation/Geometry/Analysis. Os comandos e códigos de saída
ficam em `evidence/validation.json`. A raiz Lake sozinha não inclui estes
módulos de pesquisa. O manifesto da entrega permite conferir cada arquivo.
Nesta execução, **os 14 comandos passaram com código de saída zero**;
`evidence/preservation.json` registra a preservação das fontes, pins,
main e trabalho anterior. `MANIFEST.sha256` permite conferir a entrega com
`sha256sum -c MANIFEST.sha256`.

## E — Próximo passo mínimo

O numerador geral está fechado. A próxima obrigação é calibrar os pesos
binomiais e fatoriais **já existentes** de cada diferença, incluindo sua fase,
antes de tentar deduzir seu sinal:

\[
Sc_m=(c_m)_0 C^m\phi_0,\qquad
(c_m)_1=-m(c_m)_0,\qquad C=I-M.
\]

Aqui cₘ deve ser a entrada original do jet; não é autorizada sua definição
retroativa por essas igualdades. O escalar é seu coeficiente inicial efetivo
da construção, não um parâmetro escolhido por ajuste.

Com essa identificação, a fórmula do numerador determina o bordo, em vez de
postulá-lo. Para m≥2, confrontar no mesmo espaço físico a família P da PR #97:

\[
M^2P_{m-2}(C)\phi_0
\stackrel{?}=
C^m\phi_0-\phi_0+mM\phi_0-M^2C^{m-2}\phi_0.
\]

A identidade escalar correspondente já está provada. Sua calibração
operatorial e o transporte dos pesos originais em toda ordem ainda não fazem
parte desta entrega. O caso m=4 precisa reproduzir literalmente o bordo
`5φ₁/24−φ₂/12` e o sinal da PR #97. Depois será possível procurar o controle
do cruzamento de bordo para essa família específica, sem eliminar os traços.

Mesmo uma lei para todos esses coeficientes lineares não provaria o sinal de
todo residual canônico: a etapa posterior deve conservar a resposta não linear
original e o balanço entre setores, como nas PRs #41, #95 e #96.

Para recriar a worktree após sua remoção, no servidor `llm`:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-linear-tfvd-traces \
  agent/native-linear-tfvd-traces
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-linear-tfvd-traces/.lake
```

Reprodução na pasta `research/native-linear-tfvd-traces` dessa worktree:

```bash
python3 validate.py
```

Entrega em PR draft sobre a PR #97, sem merge automático. Relatório completo,
logs e manifesto acompanham as fontes. A limpeza se limita à worktree
temporária própria, depois de commit, push e cópia local verificada.

**Fim do relatório.**
