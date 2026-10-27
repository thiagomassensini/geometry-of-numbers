# Taylor nativo de ordem 11 e cancelamento completo da família quártica

**PARTIAL para positividade canônica all-order. A obrigação E da PR #102
foi fechada.** O Taylor original foi transportado ao suporte com halo de seis
endereços, seu resto foi controlado nos dois setores e a mesma fonte
`J₄−aJ₂−bJ₀` foi reunida antes da parte finita.

Base exata: `114c220b4e187f80e6645f354fd0de7e08444768`, PR #102,
branch `agent/native-cubic-seed-crosses`. Branch desta rodada:
`agent/native-quartic-response-taylor`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

A resposta é a existente `responseReadout`, construída a partir da
característica completada e de seu companion de bordo. Seus coeficientes
são os momentos canônicos originais h, identificados pela recorrência da
derivada logarítmica. Não se define outra resposta, fonte ou sequência.

Reutilizamos concretamente:

- `ResponseTaylor.lean`: `response_readout_analytic`,
  `response_coefficient_derivative`, `response_coefficient_even`,
  `response_coefficient_odd`, `response_radial_readout`,
  `radial_step_tendsto`.
- `PhysicalKernels.lean`: `stencil_congr`, linearidade dos campos e kernels
  em pesos e entradas, com os dois setores originais.
- `ResponseFlux.lean`: `full_response_flux`, `mixed_response_flux`,
  `full_split`, com a síntese completa de duas pernas.
- `CriticalFamily.lean`: `criticalFamily`,
  `critical_family_original_source`, `critical_family_support`,
  `critical_family_explicit`, preservando fases e fatoriais.
- `FourthBoundaryDefect.lean`: `fourthShape` e `fourth_shape_explicit`.
- `inner_completedNativeChiralCauchyFeature`: a métrica Cauchy literal,
  `⟨φ_i,φ_j⟩=1/(i+j+2)`.

As PRs #101 e #102 já calibraram o termo espacial cúbico e seus cruzamentos.
Eles não são o balanço completado e não serão usados como sua substituição.

Também foi conferida a declaração atual
`nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto`, em
`CompletedNativeChiralBoundaryJetTransport.lean`. O transporte assinado
all-order já existe. A novidade demonstrada aqui é a resolução do Taylor,
dos cancelamentos e do resto **nos setores desta mesma família**; não é
anunciar novamente a mera existência daquele limite.

## B — O que foi demonstrado agora

### B.1 — Taylor da mesma resposta, antes de qualquer novo sinal

`response_eleventh_remainder` prova a existência de R analítico no centro:

\[
q(t)=h_0t-h_1t^3+h_2t^5-h_3t^7+h_4t^9+t^{11}R(t).
\]

Aqui q é somente a notação para `responseReadout`. A igualdade é eventual
numa vizinhança complexa de zero. Não recebe sinais de h como hipóteses.

Com `δ_k=(k+1)⁻¹`, `p_r(j)=(j+1)^r` e
`ℛ_k(j)=(j+1)¹¹ R((j+1)δ_k)`, os teoremas
`response_weight_taylor11_prefix` e `response_weight_taylor11_six` dão

\[
\rho_k(j)=i[h_0\delta_kp_1(j)-h_1\delta_k^3p_3(j)
+h_2\delta_k^5p_5(j)-h_3\delta_k^7p_7(j)
+h_4\delta_k^9p_9(j)+\delta_k^{11}\mathcal R_k(j)].
\]

Um único R serve para **todo prefixo finito**. A ordem dos quantificadores é
`∃ R, ∀ N, eventualmente em k, ∀ j : Fin N`.
O limiar em k pode depender de N. Isso não fornece uma vizinhança uniforme
para todos os endereços infinitos, nem aumenta automaticamente a ordem dos
jets. A especialização `Fin 6` inclui o endereço exterior 5.

`response_field_kernel_taylor11` transporta primeiro o campo complexo
inteiro, tanto no setor completo (`false`) quanto no Green-comutador
(`true`), para qualquer entrada finita com suporte em `range N`.
Só depois o pareia com uma entrada esquerda independente. O mesmo R,
os cruzamentos, o halo e o Green original são conservados.

### B.2 — A família radial é a mesma, com todos os fatores explícitos

Seja `d₄=(1,−4,6,−4,1)/24`, `q₂=(−1/2,1,−1/2)` e `e₀=(1,0,…)`.
Defina apenas o perfil algébrico

\[
v_{a,b}(t)=d_4-at^2q_2-bt^4e_0.
\]

`critical_family_profile` prova a igualdade de coeficientes da fonte antiga:

\[
\boxed{\operatorname{criticalFamily}(k,a,b)
=(k+1)^4v_{a,b}(\delta_k).}
\]

A fase da ordem dois, o 4!, a semente positiva com coeficiente −b e ambos
os fatores radiais são demonstrados, sem trocar pesos ou métrica. a,b aqui
são os parâmetros radiais livres, e não os parâmetros de perfil mantidos
fixos na PR #102. k radial, endereço material e profundidade Carry continuam
distintos.

`full_five_pairing` prova o pareamento Cauchy completo em **dois conjuntos
independentes de cinco coeficientes complexos**. Só depois entram as
especializações reais. `kernel_three_input_expansion` conserva os nove
pareamentos ordenados para qualquer peso e para ambos os setores.

### B.3 — Cancelamento geométrico exato, sem momentos como premissa

Escreva `B_p(t)=Re K_false[p](v(t),v(t))`. `full_profile_weights` prova:

| Peso | Pareamento completo exato |
| --- | --- |
| p₁ | b²t⁸/2 |
| p₃ | −abt⁶+b²t⁸/2 |
| p₅ | a²t⁴/2−20abt⁶+b²t⁸/2−bt⁴ |
| p₇ | 7a²t⁴−231abt⁶+at²+b²t⁸/2−126bt⁴ |
| p₉ | 147a²t⁴/2−2290abt⁶+75at²+b²t⁸/2−6027bt⁴+1/2 |

`full_weight_cancellation` usa cinco escalares reais **arbitrários** m₀,…,m₄:

\[
2[m_0B_1-m_1t^2B_3+m_2t^4B_5-m_3t^6B_7+m_4t^8B_9]
=t^8[Q_m(a,b)+t^2P_m(a,b,t)],
\]

onde

\[
Q_m=m_4-2am_3+(a^2-2b)m_2+2abm_1+b^2m_0,
\]

e o polinômio exato restante é

\[
\begin{aligned}
P_m={}&-14a^2m_3-40abm_2+150am_4-b^2m_1+252bm_3\\
&+t^2(147a^2m_4+462abm_3+b^2m_2-12054bm_4)\\
&+t^4(-4580abm_4-b^2m_3)+b^2m_4t^6.
\end{aligned}
\]

O fator t⁸ elimina exatamente as quatro possíveis ordens divergentes,
antes de qualquer desigualdade. A prova é da fonte Cauchy original com
seus coeficientes; não recebe os momentos canônicos nem sua positividade.

### B.4 — Resto controlado e recomposição dos setores físicos

`remainder_five_field_continuous` conserva os seis endereços na parte mista.
`remainder_profile_kernel_continuous` prova continuidade do pareamento do
resto, com ambos os argumentos do perfil variando. Não substitui o resto
por zero. A propriedade do Green é a do operador limitado original, com
sua cauda exata.

Escreva `Q=Q_h` e

\[
E(t)=P_h(a,b,t)+2\Re K_{false}[\mathcal R(t)](v(t),v(t)).
\]

`quartic_complete_expansion` chega à **mesma fonte física completada**:

\[
\boxed{\operatorname{fullEnergy}_k=Q(a,b)+\delta_k^2E(\delta_k).}
\]

Mais precisamente, se Lₖ é o `quarticLeadingFlux true`, a identidade mantém

\[
\begin{aligned}
\operatorname{mixedEnergy}_k&=L_k+2\delta_k^2K^{re}_{R,true},\\
\operatorname{bulkBoundaryEnergy}_k
&=Q-L_k+\delta_k^2(E-2K^{re}_{R,true}).
\end{aligned}
\]

Assim o termo misto e seu oposto de bulk/bordo se cancelam **na soma
demonstrada**, e os dois restos continuam presentes até essa recomposição.
Não se atribui sinal individual a Lₖ nem se descarta qualquer setor.

`quartic_full_energy_limit` conclui `fullEnergy → Q`.
`quartic_full_second_order_bound` prova, para η,a,b fixos, a existência de
M>0 tal que, eventualmente,

\[
|\operatorname{fullEnergy}_k-Q(a,b)|\le M\delta_k^2.
\]

Não se afirma uma constante uniforme na dimensão, em η ou nas direções.

### B.5 — A normalização original da energia

`full_energy_norm_difference` demonstra

\[
2\operatorname{fullEnergy}_k=\|I_k\|^2-\|R_k\|^2.
\]

Portanto `quartic_norm_difference_limit` fornece limite **2Q** para a
diferença das energias, enquanto o limite de `fullEnergy` é **Q**.
O fator 2 da candidata no relatório da PR #102 corresponde à diferença
das normas, não à definição `fullEnergy`. Não se alterou a forma assinada
ou sua métrica para ajustar esse fator.

## C — O que não foi demonstrado

Os cancelamentos determinam a parte finita; não determinam seu sinal.
Q é a forma canônica no vetor (−b,−a,1), mas a realização aqui usa uma
forma **assinada**, não a norma de um único vetor em um espaço de Hilbert.
O limite de uma diferença de energias não é automaticamente não negativo.

Não foram demonstradas positividade Hankel all-order, contratividade do
retorno em todas as direções, margem relativa fixa ou independência linear
de uma família infinita positiva. Os resultados finitos anteriores e a
obstrução cúbica da PR #102 permanecem intactos.

O teorema all-order antigo de transporte de energia também não descarrega
o sinal. Esta investigação fornece uma resolução e uma taxa concretas da
mesma fonte nesta ordem, e não uma nova prova de positividade global.

## D — Auditoria e reprodução

São **32 teoremas e nove definições** novos em `Taylor11.lean`,
`QuarticKernel.lean`, `QuarticRemainder.lean` e `QuarticFlux.lean`.
A auditoria gerada `Audit.lean` passou para **41 raízes públicas**:
16 espaciais, com 5.083 dependências transitivas, e 25 de proveniência,
com 5.748 dependências de tipos/corpos.
O grupo espacial é auditado sem característica ou momentos canônicos como
dependências. O grupo de proveniência pode usar a característica e os
momentos para suas identidades, mas rejeita os consumidores de sinal
selecionados. Ambos rejeitam axiomas além de `propext`, `Classical.choice`
e `Quot.sound`. Não há escapes de confiança ou hipóteses de positividade.

`build_upstream.py` lista os 30 ancestrais realmente importados. A
reprodução normal recompila todos; a validação final pode conferir os
hashes de fontes e `.olean` produzidos no bootstrap desta mesma rodada com
`--reuse-upstream`. Os módulos novos são sempre compilados explicitamente.

Os **15 checks locais passaram com código de saída zero**, incluindo
as compilações explícitas, o build raiz com `--wfail` e as três auditorias.
`preservation.json` confirma fontes, pins, main e trabalho antigo intactos.
Os detalhes do bootstrap estão em `evidence/upstream-bootstrap.json`.
A aprovação local não é uma afirmação sobre CI externo.

Na máquina `llm`, recriar a worktree após a entrega:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-quartic-response-taylor \
  agent/native-quartic-response-taylor
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-quartic-response-taylor/.lake
cd /home/thlinux/geometry-of-numbers-native-quartic-response-taylor/research/native-quartic-response-taylor
python3 validate.py
```

O validador executa os alvos explícitos com warnings como erros,
`lake build --wfail`, auditorias Foundation/Geometry/Analysis e preservação
de fontes, pins e trabalhos antigos. `evidence/validation.json` registra os
comandos e códigos de saída; os logs e o manifesto SHA-256 acompanham a
entrega. Conferir o manifesto antes de regenerar os logs:

```bash
sha256sum -c MANIFEST.sha256
```

## E — Próximo passo mínimo

Extrair o primeiro coeficiente da correção completa, em vez de inferir seu
sinal da cota absoluta O(δ²). As duas menores identidades ainda a formalizar
são `R(0)=−h₅`, para o resto desta expansão, e o pareamento espacial
`Re K_false[p₁₁](d₄,d₄)=55/2`. A primeira propriedade deve ser
fortalecida em `response_eleventh_remainder` e transportada com o mesmo R
pelos campos e setores, sem escolher outro resto posteriormente.

Elas levam à candidata para a primeira correção:

\[
E(0)\stackrel{?}=-55h_5+150ah_4-14a^2h_3
+252bh_3-40abh_2-b^2h_1.
\]

Essa fórmula explícita é **próxima obrigação**, não resultado Lean desta
entrega. O valor 55/2 foi apenas conferido por cálculo racional finito
independente; não é uma premissa dos teoremas novos.

Depois se deve especializar a,b na direção crítica do bloco antigo,
reutilizando a ortogonalização algébrica e o Schur da PR #41 sob a
inversibilidade apropriada. Encontrar uma desigualdade independente da
fonte que determine o sinal continua sendo uma obrigação adicional.

Entrega em PR draft sobre a PR #102, sem merge automático. Main, fontes,
pesos, amplitudes, métrica, pins e trabalhos alheios são preservados.

**Fim do relatório.**
