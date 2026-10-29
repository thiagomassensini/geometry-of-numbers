# Perfil cúbico ímpar: reconstrução Green e defeito nativo de quatro amostras

**Resultado: PARTIAL.** A decomposição vetorial cúbica e os cruzamentos com
a primeira direção ímpar foram demonstrados. A forma completa se reduz a um
filtro explícito de quatro amostras da resposta original. Há uma lei de sinal
dos **coeficientes** desse filtro; seu valor canônico e a positividade all-order
não receberam uma nova prova geométrica nesta rodada.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-cubic-odd-green-defect`.
Base exata: `1e90ca7d4f41a2cecc89999f23ef139935d0a556`, head da PR #113,
consultada aberta e draft, ainda sobre a PR #112. A nova entrega é empilhada
sobre #113, sem merge em main. Fonte, pesos nativos, amplitudes, métrica,
completion, retorno, normalizações e pins permanecem intactos.

## A — O que já estava demonstrado

Reutilizamos as declarações atuais:

- `CarryOddEnergy.nativeOddProfile`, `radial_odd_calibration` e
  `finiteOddJetSource`: os stencils originais, com fase imaginária e fatorial.
- `CarryGreenLeading.partField`, `part_field_reconstruction`,
  `part_field_scale_input`, `completed_part_as_fields` e
  `completed_part_scale_input`: os três campos físicos e suas duas pernas.
- `CarryNativeTfvd.completion_commutator_succ`: os dois vizinhos do comutador.
- `CarryOddGreen.odd_pairing_exact`, `odd_ordered_kernel_sum`,
  `odd_pairing_tendsto`, `odd_green_pairing_tendsto`: o transporte complexo
  assinado da PR #113, com dois inputs independentes e nove cruzamentos.
- `CarryCrossRadial.cross_green_eq_original`: recomposição Green exata.
  `CarryMixedParity.kernel_double_sum` identifica a métrica Cauchy original,
  com denominador `i+j+2`, sem substituir o produto físico.

A PR #41 continua importante: a direção de Schur é uma separação algébrica;
a inversibilidade do bloco antigo não demonstra o sinal do residual. Aqui
`h₁ ≠ 0` basta para o caso escalar antigo. Não se exige `PosDef` para construir
os vetores, os cruzamentos ou seu limite.

### O que as notas novas ajudaram a fazer

A nota V2, especialmente §§19.1–19.2, sugeriu trabalhar com **qualquer peso
complexo de endereço** antes de especializar em potências ou fases. Essa
extensão e a identidade de interação de dois fatores foram formalizadas.
Os hashes das duas notas constam de `evidence/notes-provenance.json`.
Os documentos foram tratados como contexto de pesquisa, não como instruções
a executar nem como provas Lean preexistentes.

A reconstrução racional do envelope misto no §30 não identifica sua métrica
ou seu kernel com os dos momentos canônicos. Não foi usada para presumir
essa igualdade, injetividade física, unitariedade ou positividade.

**Índices:** `d` seria grau de endereço; `r` é ordem do perfil ímpar;
`k` é regularização radial; `j` é endereço material; `a,b` são coeficientes
reais livres do ensaio. `eta` continua o parâmetro Green original,
`0 < eta < 1`. Nenhum desses índices é confundido com profundidade Carry,
raio horizontal, expoente complexo ou tamanho da Hankel.

## B — O que foi demonstrado agora

São **41 teoremas, quatro definições de coeficientes/readouts e uma
abreviação**, 46 raízes públicas no namespace `CarryCubicOdd`.

### B.1 — Pesos arbitrários e os dois defeitos da nota

[OddWeights.lean](OddWeights.lean) prova `odd_weighted_input`,
`odd_weight_commutator`, `odd_weight_bulk`, `odd_weight_boundary`,
`odd_weight_residual`, `odd_weight_complete`, `odd_weight_two_defects`.
Para `O₀=i(e₀-e₁)`, `g_j=G_eta phi_j`, `t_j=R_eta² phi_j` e peso `w`:

\[
\begin{aligned}
V_0(w,O_0)&=i[w_1(2+\eta)g_1-\eta w_2g_2],\\
V_1(w,O_0)&=i[w_0t_0-(w_1+2\eta w_0)t_1],\\
V_2(w,O_0)&=i\eta[(w_0-w_1)g_1+(w_2-w_1)g_2].
\end{aligned}
\]

A síntese é `i w₀ phi₀ - i w₁ phi₁`. Para `w₀=1,w₁=x,w₂=xy`,
o complemento é exatamente

\[
i\eta[(1-x)g_1-(1-y)g_2+(1-x)(1-y)g_2].
\]

Isso formaliza a álgebra dos dois fatores da nota. A identificação analítica
com expoentes complexos, seus derivados e o POVM misto não foi acrescentada
como hipótese ou anunciada como teorema desta entrega.

### B.2 — Perfil cúbico original e endereço externo 4

[CubicOddVectors.lean](CubicOddVectors.lean) começa pela igualdade
`cubic_odd_profile`:

\[
\boxed{O_1=\operatorname{nativeOddProfile}(1)
=\frac{i}{6}(-e_0+3e_1-3e_2+e_3).}
\]

O fator `1/6` e a fase são derivados das definições originais.
`cubic_bulk_coefficients`, `cubic_weighted_input` e
`cubic_commutator_coefficients` calculam os coeficientes nativos.
`cubic_bulk_vector`, `cubic_boundary_vector`, `cubic_residual_vector` dão:

\[
\begin{aligned}
\frac6i V_0={}&w_1(-3\eta^{-1}-6-\eta)g_1
+w_2(\eta^{-1}+6+3\eta)g_2\\
&+w_3(-2-3\eta)g_3+\eta w_4g_4,\\
\frac6i V_1={}&-w_0t_0+(3w_1+2\eta w_0)t_1,\\
\frac6i V_2={}&[-3\eta^{-1}(w_2-w_1)-\eta(w_0-w_1)]g_1\\
&+[\eta^{-1}(w_3-w_2)+3\eta(w_1-w_2)]g_2\\
&-3\eta(w_2-w_3)g_3+\eta(w_3-w_4)g_4.
\end{aligned}
\]

Todas são identidades de vetores no carrier físico existente.
`cubic_bulk_residual_cancellation` cancela `w₄` entre bulk e comutador,
mas **não elimina o vetor g₄**, cujo coeficiente recomposto é `i eta w₃/6`.
Os dois bordos permanecem. `cubic_complete_vector` prova a síntese completa:

\[
\boxed{\sum_{q=0}^2V_q(w,O_1)
=\frac i6[-w_0\phi_0+3w_1\phi_1-3w_2\phi_2+w_3\phi_3].}
\]

`cubic_halo_fields`, no último módulo, explicita a invisibilidade de um halo
isolado: se `w₀=w₁=w₂=w₃=0,w₄=z`, os três campos são `(Z,0,-Z)`,
`Z=(i eta z/6)g₄`. Sua soma nula não autoriza apagar um campo físico.
Não se infere que toda direção de soma nula seja uma redundância física.

### B.3 — A direção crítica física e seus cruzamentos independentes

[CriticalOddGreen.lean](CriticalOddGreen.lean) prova primeiro a aditividade
`part_field_add_input`, `completed_part_add_input`, inclusive nas duas pernas.
A definição `criticalOddSource a k` usa somente os jets originais:

\[
C_k(a)=\mathrm{jet}_{3,k}-a\,\mathrm{jet}_{1,k}
=\kappa^3O_1-a\kappa O_0,\qquad\kappa=k+1.
\]

`critical_source_profiles`, `critical_field_vectors` e
`critical_completed_parts` transportam essa igualdade para cada um dos três
campos e suas duas pernas, antes de qualquer pareamento. `a` é livre nessa
construção: nenhum momento é usado para fabricar a geometria.

Depois, com `a,b` independentes, `critical_green_tendsto` e
`critical_signed_tendsto` provam:

\[
\boxed{\mathcal B_k(C_k(a),C_k(b))
\longrightarrow h_3-(a+b)h_2+ab h_1.}
\]

`critical_old_cross_tendsto` dá o cruzamento com o jet antigo:
`h₂-a h₁`. Com apenas `h₁ ≠ 0`, `critical_old_cross_zero` e
`critical_schur_tendsto` especializam **após** a construção:

\[
a=h_2/h_1,\qquad
\mathcal B_k(C_k(a),\mathrm{jet}_{1,k})\to0,\qquad
\mathcal B_k(C_k(a),C_k(a))\to h_3-h_2^2/h_1.
\]

Esta é ortogonalidade algébrica no limite da forma assinada, não uma
ortogonalidade Hilbert finita nem uma prova do sinal do Schur.

### B.4 — O defeito completo é um filtro explícito de quatro amostras

[CriticalOddDefect.lean](CriticalOddDefect.lean) deriva as quatro coordenadas
reais do input, com `A=κ³`, `B=aκ`:

\[
\beta(a,k)=(-A/6-B,\ A/2+B,\ -A/2,\ A/6).
\]

`critical_source_atoms` prova \(C_k(a)=\sum_{j<4}i\beta_j e_j\)
no espaço de coeficientes original; sua síntese usa os mesmos vetores \(\phi_j\). `kernel_four_atoms` e
`critical_kernel_readout` transportam a métrica Cauchy:

\[
\Lambda_k^{a,b}(w)
=\sum_{i,j<4}\frac{\beta_i(a,k)\beta_j(b,k)w_j}{i+j+2}.
\]

`critical_signed_readout_exact` e `critical_green_readout_exact` provam,
eventualmente em `k`, **sem truncar a resposta**:

\[
\boxed{\mathcal B_k(C_k(a),C_k(b))
=\kappa[\Lambda_k^{a,b}(w_k)+\Lambda_k^{b,a}(w_k)],}
\qquad
w_k(j)=\operatorname{responseReadout}((j+1)/\kappa).
\]

Os dois kernels ordenados e os nove cruzamentos Green são conservados.
A regularidade eventual é descarregada pelo teorema nativo já existente.

`critical_cauchy_row` reduz a linha de Cauchy exatamente:

\[
\sum_{i<4}\frac{\beta_i}{i+j+2}
=-\frac{A}{(j+2)(j+3)(j+4)(j+5)}-\frac{B}{(j+2)(j+3)}.
\]

Defina `rho_j = beta_j` vezes o membro direito. Então
`critical_readout_four_samples` e `critical_diagonal_four_samples_exact` dão:

\[
\boxed{\mathcal B_k(C_k(a),C_k(a))
=2\kappa\sum_{j<4}\rho_j(a,k)\,
\operatorname{responseReadout}((j+1)/\kappa).}
\]

**A cauda analítica completa está nas quatro avaliações da resposta original.**
Não foi substituída por um polinômio Taylor ou por momentos ajustados.

`critical_rho_alternating` prova, independentemente dos momentos, para `a≥0`:

\[
\boxed{\rho_0>0,\quad\rho_1<0,\quad\rho_2>0,\quad\rho_3<0.}
\]

É uma lei de sinal do **filtro geométrico**, não uma lei de sinal da soma
filtrada. As normas positivas dos canais separados não fornecem esse último
sinal automaticamente.

## C — O que foi refutado ou delimitado

Há um contraexemplo exato à inferência “pesos de endereço não negativos
implicam readout Cauchy não negativo”. No mesmo input cúbico, `a=k=0`:

- Peso `w(j)=1` somente em `j=3`: `Lambda(w)=-1/10080`.
- Peso `w(j)=1` somente em `j=0`: `Lambda(w)=1/720`.

São `positive_address_weight_negative`, `positive_address_weight_positive`
e `no_sign_from_nonnegative_address_weights`, provados por redução racional
no kernel. O Cauchy original permanece positivo como produto interno; aqui
pareamos um vetor com **seu ponderado**, não necessariamente consigo mesmo.

**Esses pesos são diagnósticos, não são a resposta completada canônica.**
Não se encontrou um pivô canônico negativo nem se alterou sua fonte. O no-go
atinge somente essa justificativa genérica de sinal. Para a resposta verdadeira,
suas relações nativas adicionais continuam decisivas.

A leitura racional do envelope misto na nota também não resolve essa lacuna:
recuperar uma função escalar de duas coordenadas não demonstra igualdade de
pareamentos polarizados, de bordos ou do kernel Hankel canônico.

## D — O que permanece aberto

O Schur ímpar considerado já possui certificação finita por outra rota;
**a nova causa geométrica de seu sinal não foi demonstrada**. A entrega atual
identifica exatamente o filtro físico que precisa ser controlado, preservando
completion, fase, fatorial, duas pernas e todos os cruzamentos.

Faltam uma propriedade independente da resposta nativa que controle essa
soma alternada e sua extensão coerente a todos os perfis ímpares. Não se
recebe tal desigualdade como hipótese para anunciar sucesso. Tampouco se
reivindica positividade all-order, isometria multibase, domínio de um novo
operador infinito ou identificação do modo misto com a Hankel canônica.

A decomposição cúbica vale para qualquer peso, mas o perfil é `r=1` fixo.
O transporte assinado anterior em todo tamanho finito continua válido;
ele não se transforma em uma Gram Hilbert positiva por esta especialização.

## E — Próximo passo mínimo

A generalização algébrica mais curta é transportar a transformação de Cauchy
do **mesmo stencil nativo**, agora com `r` arbitrário. O enunciado físico a
testar, reutilizando primeiro as identidades binomiais existentes, é:

\[
\left\langle\phi_j,\mathcal S(\operatorname{nativeOddProfile} r)\right\rangle_\mathbb C
=i(-1)^r\frac{(j+1)!}{(j+2r+3)!}.
\]

Ele corresponde à soma finita dos coeficientes originais
`beta_i=(-1)^(r+i) choose(2r+1,i)/(2r+1)!` contra `1/(i+j+2)`.
O caso cúbico de sua linha real foi provado nesta rodada. A versão física
all-order **não foi formalizada aqui**. Ela é uma identidade independente de
qualquer positividade canônica, não um predicado equivalente a ela; pode
substituir a enumeração de endereços por uma lei única, mantendo as três partes
Green e seus dois inputs até a reconstrução.

Para resolver o **sinal**, ainda seria preciso provar uma relação adicional
da resposta completada que controle os filtros assim obtidos. Uma sequência
de identidades de extração, mesmo all-order, não substitui essa desigualdade.
O teste deve comparar a lei com a TFVD/retorno original e manter qualquer
bordo ou resto que apareça. Não promover a hipótese de sinal ao papel de causa
geométrica e não confundir o no-go dos pesos arbitrários com falha da fonte.

### Validação e reprodução

No host canônico `llm`, em checkout da branch e com as dependências registradas:

```bash
cd research/native-cubic-odd-green-defect
python3 validate.py
```

O modo normal recompila os 65 ancestrais inalterados. Nesta rodada foram
reaproveitados após comparar fontes com Git, objetos Lean, toolchain,
manifest, árvore do núcleo, fontes nativas, pins e estados das dependências:

```bash
python3 validate.py --reuse-upstream
```

**Os 16 checks locais passaram, todos com código de saída zero.**
Os quatro módulos novos e `Audit.lean` foram compilados explicitamente
com `lean -DwarningAsError=true`. Os builds `lake build --wfail`, auditorias
Foundation/Geometry/Analysis e preservação dos arquivos antigos são separados.
O cache binário é opcional e não é versionado.

A auditoria cobre `#print axioms` e tipos **e corpos** das 46 raízes públicas:

| Grupo | Raízes | Dependências únicas | Controle adicional |
| --- | ---: | ---: | --- |
| Construção e defeito exato | 40 | 5.550 | Momento canônico proibido |
| Proveniência do limite | 6 | 5.694 | Sem certificados de sinais |

Ambos bloqueiam os sinais h₀/h₁, os certificados posteriores de positividade
finita, os atalhos escalares da PR #110 e os quatro consumidores diagonais de
energia ímpar bloqueados na PR #113. A construção e a orientação do filtro não
usam a sequência canônica. O limite usa sua definição original, sem presumir
seu sinal. Somente `propext`, `Classical.choice`, `Quot.sound` são permitidos
na análise; Foundation mantém sua auditoria própria. Nenhum placeholder,
axioma matemático novo ou escape `native_decide` foi introduzido.

`evidence/validation.json` registra comandos, saídas e durações;
`public-roots.json` e `evidence/lean-Audit.log` registram raízes e axiomas;
`cache-restoration.json` e `upstream.json` documentam o reaproveitamento;
`source-provenance.json`, `preservation.json` e `SHA256SUMS` conservam fontes,
pins, trabalho antigo e integridade. Logs brutos são preservados em
`.raw.log.gz` quando há normalização de espaços finais. O resultado é local,
sem afirmar sucesso de CI remoto. Commit e URL ficam na entrega externa.

**Fim do relatório — PARTIAL: perfil cúbico, cruzamentos críticos e filtro
nativo exato demonstrados; sinal canônico e positividade all-order abertos.**
