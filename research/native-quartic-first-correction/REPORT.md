# Primeira correção completa da família quártica nativa

**PARTIAL para positividade canônica all-order. O alvo E da PR #103 foi
fechado.** O valor do mesmo resto no centro, o pareamento de peso 11 e o
coeficiente completo da primeira correção foram provados em Lean. A direção
crítica foi especializada sob inversibilidade do bloco antigo, sem receber
positividade como hipótese.

Base exata: `78d74b06b06ad9250fbf2718f580b3beb030a568`, PR #103,
branch `agent/native-quartic-response-taylor`. Branch desta rodada:
`agent/native-quartic-first-correction`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

A sequência h continua sendo a canônica original, extraída da resposta
completada por sua recorrência logarítmica. A família física é a mesma
`criticalFamily k a b`, identificada com `J₄−aJ₂−bJ₀` nos dois canais,
incluindo as fases, 4!, amplitudes, semente e normalização originais.

A PR #103 já provou o Taylor até grau 9 com resto de ordem 11, a calibração
do perfil radial, os cancelamentos completos e uma cota O((k+1)⁻²).
Também fixou a identidade original `2*fullEnergy=‖I‖²−‖R‖²`.
Faltavam o valor do resto no centro e o coeficiente dessa correção.

Reutilização concreta:

- `ResponseTaylor.lean`: `response_readout_analytic`,
  `response_coefficient_derivative`, `response_coefficient_even`,
  `response_coefficient_odd`, `response_radial_readout`.
- PR #103, `Taylor11.lean`: `taylorWeight9`, `remainderWeight11`.
- PR #103, `QuarticKernel.lean`: `full_five_pairing`,
  `profile_support`, `critical_family_profile`, `kernel_scale_both`.
- PR #103, `QuarticRemainder.lean`: `field_congr_prefix`, continuidade
  dos campos e pareamentos do resto, incluindo o halo de seis endereços.
- PR #103, `QuarticFlux.lean`: `quartic_full_flux_exact`,
  `quartic_full_error_continuous`, `full_energy_norm_difference`.
- `ResponseFlux.lean`: `full_response_flux`, `mixed_response_flux`,
  `full_split` da fonte completada original.
- `NativeSourceAllOrderSchur.lean`: definições originais de matriz,
  cruzamentos, complemento de Schur e formas quadráticas de momentos.

A separação lógica da PR #41 é mantida: ortogonalização algébrica e
identificação do residual não determinam, por si, o sinal desse residual.

## B — O que foi demonstrado agora

### B.1 — O resto é identificado na resposta complexa original

`response_remainder11_with_value` usa o Taylor analítico original até
ordem 13 para construir um resto de ordem 11 com valor determinado:

\[
R(z)=-h_5+z^2S(z),\qquad S\text{ analítico no centro}.
\]

Logo R é analítico, `R(0)=−h₅` e, perto de zero,

\[
q(z)=h_0z-h_1z^3+h_2z^5-h_3z^7+h_4z^9+z^{11}R(z).
\]

Essa construção agrupa os coeficientes do Taylor da mesma função q.
Não escolhe um termo para ajustar uma energia nem altera a fonte.

`nativeRemainder11` nomeia essa testemunha. Os teoremas
`native_remainder_analytic`, `native_remainder_value` e
`native_response_taylor11` mantêm suas três propriedades juntas.
`remainder_value_of_response_identity` prova ainda que qualquer outro
resto analítico que satisfaça **essa mesma identidade complexa da resposta**
tem o mesmo valor no centro. Não se afirma igualdade global dos restos fora
da vizinhança onde a expansão é válida.

`native_response_weight_prefix` transporta a mesma testemunha a qualquer
prefixo finito de endereços. `native_response_field_kernel_prefix`
transporta primeiro os campos complexos completos dos dois setores e só
depois os pareia com uma entrada esquerda independente.
O índice eventual depende do prefixo; não se reivindica uniformidade sobre
todos os endereços infinitos.

### B.2 — O coeficiente espacial 55/2 é certificado no kernel

O stencil quártico permanece `d₄=(1,−4,6,−4,1)/24` e a métrica física
continua `⟨φ_i,φ_j⟩=1/(i+j+2)`. O peso é o original `p₁₁(j)=(j+1)¹¹`.

`full_quartic_weight11_complex` demonstra

\[
\boxed{K_{false}[p_{11}](d_4,d_4)=55/2\quad\text{em }\mathbb C.}
\]

O resultado real vem depois, em `full_quartic_weight11_real`.
`zero_remainder_kernel` prova, para qualquer função complexa R,

\[
K_{false}[\mathcal R(0)](v_{a,b}(0),v_{a,b}(0))=(55/2)R(0).
\]

A igualdade complexa antecede a parte real. A prova reutiliza o pareamento
anterior de dois conjuntos independentes de cinco coeficientes; não usa
apenas uma identificação entre normas diagonais.

### B.3 — A mesma testemunha chega aos setores e à energia completa

`native_sector_expansion` mantém o mesmo `nativeRemainder11` nos setores
completo e Green-comutador. `native_complete_expansion` preserva o termo
misto, seu oposto de bulk/bordo e ambos os restos até a recomposição.
Nenhuma contribuição é removida para obter um sinal.

Com `δ_k=(k+1)⁻¹`, o resultado reutiliza a identidade da PR #103:

\[
\operatorname{fullEnergy}_k=Q(a,b)+\delta_k^2E(\delta_k),
\]

\[
Q(a,b)=h_4-2ah_3+(a^2-2b)h_2+2abh_1+b^2h_0.
\]

Agora `native_full_error_zero` identifica exatamente

\[
\boxed{E(0)=C(a,b)=-55h_5+150ah_4-14a^2h_3
+252bh_3-40abh_2-b^2h_1.}
\]

Todos os seis termos permanecem. a,b são parâmetros reais livres da família
radial, e não coeficientes de perfil mantidos fixos em todas as escalas.
Não foram escolhidos por um sinal do pivô ou por valores espectrais.

`native_scaled_error_limit` fornece o primeiro coeficiente não cancelado:

\[
\boxed{(k+1)^2\bigl(\operatorname{fullEnergy}_k-Q(a,b)\bigr)
\longrightarrow C(a,b).}
\]

Equivalentemente, `fullEnergy=Q+Cδ²+o(δ²)` para η,a,b fixos. A normalização
original é preservada: `native_scaled_norm_difference_limit` fornece

\[
(k+1)^2(\|I_k\|^2-\|R_k\|^2-2Q)\longrightarrow2C.
\]

`native_eventually_below` e `native_eventually_above` mostram a orientação
eventual **condicional ao sinal de C**. Se C<0, a energia fica abaixo de Q;
se C>0, fica acima. Não se prova monotonicidade, nem se recebe esse sinal
como premissa da expansão ou do limite incondicionais.

### B.4 — Especialização de Schur sem PosDef

Defina o sistema antigo original

\[
A=(h_{i+j})_{i,j<2},\qquad b_{old}=(h_2,h_3)^T,\qquad
u=A^{-1}b_{old},\quad a_*=u_1,\ b_*=u_0.
\]

`quartic_schur_identity` é genérico em uma sequência real m e exige somente
`IsUnit (sourceMomentMatrix m 0 2)`. Usando `Au=b_old`, demonstra a igualdade
entre Q na direção (−u₀,−u₁,1) e o Schur, sem PosDef ou sinal do novo pivô.
`critical_quartic_schur` especializa a sequência canônica original:

\[
Q(a_*,b_*)=\operatorname{sourceMomentSchur}(h,0,2).
\]

Sob a mesma hipótese de inversibilidade antiga,
`critical_scaled_error_limit` e `critical_scaled_norm_difference_limit`
identificam a primeira correção do residual físico crítico com C(a*,b*)
e 2C(a*,b*), respectivamente. Trata-se da terceira direção par (n=2).

A família física foi construída com parâmetros livres antes dessa
especialização. Escolher sua direção crítica por ortogonalização algébrica
não é usado como origem de uma nova métrica ou de uma Gram positiva.

## C — Alcance e obstruções

As duas identidades que eram candidatas na PR #103 agora estão no kernel.
O sinal de C(a*,b*) e o sinal do Schur não foram demonstrados nesta rodada.
Uma aproximação por baixo não implica, por si, que seu limite seja positivo.

Também não se deduz positividade de Hankel all-order, contratividade em
todas as direções ou uma margem relativa fixa entre os dois canais.
A energia continua sendo uma forma assinada após a síntese completa.
Não se altera esse objeto para aplicar Hilbert, Gram ou Cholesky.

### C.1 — Pista all-order, separada dos resultados Lean

Em paralelo, `spatial_correction_canary.py` testa uma fórmula para os
coeficientes espaciais em **dois índices independentes**. Usa somente os
stencils pares originais, incluindo fase e fatorial,

\[
q_r(j)=(-1)^{r+j}\binom{2r}{j}/(2r)!,\qquad 0\le j\le2r,
\]

e a métrica Cauchy literal. Não usa momentos canônicos, theta, zeros ou
alturas como entradas. Para m=2r, n=2s, defina

\[
s_m=(m+1)(m+2)/2,\qquad
t_m=(m+1)(m+2)(m+3)(3m+4)/24,
\quad A_{m,n}=t_m+t_n-s_ms_n.
\]

A **candidata ainda não formalizada em Lean** é

\[
\Re\bigl(K_{false}[p_{m+n+3}](q_r,q_s)
+K_{false}[p_{m+n+3}](q_s,q_r)\bigr)
=(-1)^{r+s}A_{m,n}.
\]

Os 25 pares 0≤r,s≤4 passaram com aritmética racional exata. O script
conserva e registra separadamente os dois pareamentos ordenados, testa
também o coeficiente principal e os cancelamentos ímpares inferiores.
O estado do artefato é `PASS_FINITE_RATIONAL_ONLY`; isso não prova a fórmula
em toda ordem. Não há campanha de novos momentos ou aumento de precisão.

Nos índices 0,1,2, a candidata organiza os seis coeficientes já provados de C:

\[
(A_{2r,2s})_{r,s=0}^2=
\begin{pmatrix}1&20&126\\20&14&75\\126&75&55\end{pmatrix}.
\]

Esse quadro é uma tabela de coeficientes, **não uma nova métrica**. Mesmo
suas entradas positivas não autorizam um argumento de Gram: seu menor
2×2 tem determinante 14−400=−386. Portanto, uma eventual prova all-order
dessa lei espacial ainda exigirá uma propriedade adicional da fonte para
determinar o sinal da correção canônica.

## D — Validação e reprodução

São 22 teoremas e cinco definições em `RemainderValue.lean`,
`WeightEleven.lean`, `CompleteCorrection.lean` e `CriticalSchur.lean`.
A auditoria cobre 27 raízes públicas: cinco espaciais, com 5.483
dependências transitivas, e 22 de proveniência, com 6.030 dependências.

O grupo espacial não depende dos momentos canônicos ou da característica.
O grupo de proveniência pode usar a resposta e os momentos originais, mas
rejeita os consumidores de sinal selecionados pelo guard. Somente
`propext`, `Classical.choice` e `Quot.sound` são permitidos. Não há novos
axiomas matemáticos ou escapes de confiança.

Os 34 ancestrais foram compilados de sua base exata. A validação final
confere seus hashes de fontes e `.olean` antes dos módulos novos; uma
reprodução normal recompila os ancestrais. O canário racional é um check
separado da compilação e da auditoria Lean.

Os **16 checks locais passaram com código de saída zero**, incluindo
`lake build --wfail`, compilações explícitas, auditorias das três camadas e
o canário racional. O canário não substitui prova Lean. `preservation.json`
registra fontes, pins, main e trabalhos antigos intactos. A aprovação local
não é uma afirmação sobre CI externo.

Na máquina `llm`, recriar a worktree após a entrega:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-quartic-first-correction \
  agent/native-quartic-first-correction
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-quartic-first-correction/.lake
cd /home/thlinux/geometry-of-numbers-native-quartic-first-correction/research/native-quartic-first-correction
python3 validate.py
```

`validate.py` compila os módulos novos explicitamente com warnings como
erros, executa `lake build --wfail`, auditorias Foundation/Geometry/Analysis
e preservação de fontes, pins e trabalhos antigos. Comandos e saídas estão
em `evidence/validation.json` e nos logs. Conferir o manifesto antes de
regenerar os logs:

```bash
sha256sum -c MANIFEST.sha256
```

## E — Próximo alvo mínimo

A correção da família quártica e sua especialização crítica estão agora
identificadas. Para a generalização geométrica, o próximo alvo concreto é
formalizar a lei de dois índices da seção C.1 nos stencils nativos de ordem
arbitrária, preservando os dois pareamentos ordenados. Uma rota a testar é
diferenças finitas de ordens m,n, como iterações da segunda diferença
nos dois argumentos, aplicadas ao quociente polinomial
`(x^p+y^p)/(x+y)`, para p ímpar, sem qualquer hipótese sobre h.

Isso substituiria tabelas finitas por uma identidade espacial all-order;
não substituiria a obrigação de sinal. Depois será necessário transportar
a mesma lei pela resposta completada e obter uma desigualdade independente
da fonte para C na direção crítica, sem pressupor o pivô ou a positividade
Hankel que se deseja concluir.

Entrega em PR draft sobre a PR #103, sem merge automático. Main, fontes,
amplitudes, pesos, métrica, pins e trabalhos anteriores são preservados.

**Fim do relatório.**
