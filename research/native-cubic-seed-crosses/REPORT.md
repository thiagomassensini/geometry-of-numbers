# Quatro cruzamentos cúbicos com a semente nativa

**PARTIAL para o residual canônico e para positividade all-order.**
A obrigação E da PR #101 foi fechada: os quatro cruzamentos ordenados
com a semente positiva foram calibrados separadamente, e os nove
pareamentos da família original foram incorporados. Os resultados Lean efetivamente compilados
e os comandos de validação são registrados na seção D.

Base: `02c14efb8f5b3bc7197293e6beafb29853b26813`, head da PR #101,
`agent/native-cubic-quartic-factor`. Branch desta investigação:
`agent/native-cubic-seed-crosses`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

O espaço é o carrier Cauchy nativo, com o produto interno complexo original.
Continuamos a usar

\[
M=\texttt{physicalRadialAdvance},\quad C=I-M,\quad
R_\eta=(I-\eta M)^{-1},\quad G_\eta=\eta MR_\eta^2,
\quad 0<\eta<1.
\]

A semente desta rodada é `e₀=Finsupp.single 0 1`, com síntese φ₀.
Ela é o negativo do antigo `seedInput`. Os demais perfis são

\[
q=(-1/2,1,-1/2),\qquad d_4=(1,-4,6,-4,1)/24.
\]

O kernel mantido literalmente é

\[
K_3(c,d)=\langle Sc,G_\eta S(C_\eta[p_3]d)\rangle,
\qquad p_3(j)=(j+1)^3.
\]

É o `cubicKernel` da PR #100, alias do `sectorKernel true` anterior.
Não é suposto Hermitiano. A ordem dos argumentos é material nesta rodada.

Para dois argumentos físicos independentes, escrevemos

\[
r_f=R_\eta Mf,\quad v_f=Cr_f,\quad w_f=C^2r_f,
\quad H_2=19I-\eta^2B_2,\quad H_4=A_4-\eta^2B_4,
\]

com os mesmos polinômios anteriores:

\[
\begin{aligned}
B_2&=7I-38M+37M^2,\\
A_4&=27I+26C+61C^2,\\
B_4&=C^2(36I-120C+91C^2).
\end{aligned}
\]

Reutilização concreta:

- `CurvatureKernel.lean`: `green_inner_transport`,
  `curvature_resolvent_advance`, `gradient_pairing`.
- `ComplementNorm.lean`: `physical_complement_contracts`.
- `NativeCoefficient.lean`: `native_curvature`,
  `native_gradient_norm_lower`, com `‖vφ₀‖²≥1/60`.
- `BoundaryFactor.lean`: `quartic_resolvent_advance`,
  `quartic_base_pairing`, `quartic_gradient_as_complement`.
- `QuarticCoefficient.lean`: `native_quartic_vector`,
  `native_quartic_gradient_lower`, com `‖wφ₀‖²≥1/280`.
- PR #100: `cubic_native_tangent`, `cubic_tangent_resolvent`,
  `cubic_multiplier_inner_upper`, `cubic_three_input_expansion`.
- PR #101: `quartic_cubic_tangent_native`,
  `quartic_cubic_tangent_resolvent`, `quartic_margin_inner_lower`,
  `two_jet_expansion` e `two_jet_cone_lower`.

As cotas `B₂≼7I` e `H₄≽27I` vêm dos símbolos originais no
intervalo físico. A cota `H₂≽12I` é deduzida explicitamente agora dessas
propriedades anteriores; não é hipótese sobre momentos. As cotas de norma são
da Gram Cauchy literal. Não se importam caixas theta para descarregar sinais.

## B — O que foi demonstrado agora

### B.1 — Calibração da semente antes do pareamento

`positive_seed_eq_neg_seedInput` distingue os dois sinais da semente.
`positive_seed_cubic_commutator` identifica o vetor inteiro:

\[
\boxed{C_\eta[p_3]e_0=-7\eta e_1.}
\]

Logo `seed_cubic_tangent_native` identifica a expressão física limitada

\[
t_{0,\eta}(f)=-7\eta Mf
\]

com a síntese desse comutador em f=φ₀. Não há inversa não limitada de M,
substituição de fonte, alteração da métrica ou descarte de bordo.

### B.2 — Os quatro pareamentos complexos independentes

As versões polarizadas são os teoremas
`quadratic_seed_polarized`, `seed_quadratic_polarized`,
`quartic_seed_polarized` e `seed_quartic_polarized`:

\[
\begin{aligned}
\langle -C^2f/2,G_\eta t_0(g)\rangle
 &=\frac{7\eta^2}{2}\langle v_f,v_g\rangle,\\
\langle f,G_\eta t_2(g)\rangle
 &=-\frac12\langle r_f,H_2r_g\rangle,\\
\langle C^4f/24,G_\eta t_0(g)\rangle
 &=-\frac{7\eta^2}{24}\langle w_f,w_g\rangle,\\
\langle f,G_\eta t_4(g)\rangle
 &=\frac1{24}\langle r_f,H_4r_g\rangle.
\end{aligned}
\]

Aqui t₂ é o `cubicTangent` antigo no perfil quadrático, não uma nova fonte
de ordem dois; t₄ é `quarticCubicTangent`. As identificações nativas são
demonstradas em φ₀ antes da parte real. Não se presume que esses mapas
comutem com uma troca arbitrária do endereço material.

`seed_seed_polarized` conserva também a diagonal da semente:

\[
\langle f,G_\eta t_0(g)\rangle=-7\eta^2\langle r_f,r_g\rangle.
\]

### B.3 — Sinais das quatro entradas, sem momentos como premissas

Os teoremas `native_*_complex` fazem a calibração no kernel antigo.
Só depois os teoremas `native_quadratic_seed`, `native_seed_quadratic`,
`native_quartic_seed`, `native_seed_quartic` e `native_seed_seed`
tomam a parte real diagonal. Com r=rφ₀, v=vφ₀ e w=wφ₀:

| Entrada ordenada | Identidade real exata | Cota provada da fonte |
| --- | --- | --- |
| Re K₃(q,e₀) | 7η²‖v‖²/2 | ≥7η²/120>0 |
| Re K₃(e₀,q) | −Re⟨r,H₂r⟩/2 | ≤−1/10<0 |
| Re K₃(d₄,e₀) | −7η²‖w‖²/24 | ≤−η²/960<0 |
| Re K₃(e₀,d₄) | Re⟨r,H₄r⟩/24 | ≥3/160>0 |
| Re K₃(e₀,e₀) | −7η²‖r‖² | ≤−7η²/60<0 |

As constantes são cotas conservadoras. `native_base_gradient_lower`
deduz `‖r‖²≥1/60` de `‖v‖²≥1/60` e `‖Cr‖≤‖r‖`; não é um ajuste de norma.

Os dois termos de cada par são conservados também nas somas:

\[
S_{20}:=\Re(K_3(q,e_0)+K_3(e_0,q))\le-1/24,
\qquad
S_{40}:=\Re(K_3(d_4,e_0)+K_3(e_0,d_4))\ge1/72.
\]

São `native_quadratic_seed_sum_upper` e
`native_quartic_seed_sum_lower`. As provas usam `H₂≽12I`, `H₄≽27I`
e as contrações C e C², sem apagar os termos de sinais opostos.

### B.4 — Os nove pareamentos da família com a semente

Os nomes novos abreviam somente leituras do mesmo kernel:

\[
\begin{aligned}
A(a)&=\Re K_3(d_4-aq,d_4-aq),\\
P(a)&=S_{40}-aS_{20},\\
E(a,b)&=\Re K_3(d_4-aq-be_0,d_4-aq-be_0).
\end{aligned}
\]

`native_family_exact` dá a identidade sem hipótese de sinal de a ou b:

\[
\boxed{E(a,b)=A(a)-bP(a)-7\eta^2\|r\|^2b^2.}
\]

Ela conserva os nove pareamentos ordenados da expansão anterior; não
substitui a parte mista por uma norma ou por uma média simetrizada.
Para a≥0, as propriedades físicas já derivadas fornecem

\[
A(a)\ge3/17920+a^2/20+23a/2240>0,
\quad P(a)\ge1/72+a/24>0.
\]

`native_family_strict_decrease` testa uma consequência concreta: para a≥0,
E(a,b) é estritamente decrescente em b≥0. `native_family_positive_iff`
isola o que ainda precisaria ser controlado para os coeficientes efetivos:

\[
bP(a)+7\eta^2\|r\|^2b^2<A(a).
\]

Essa equivalência é apenas o residual da identidade física demonstrada.
Não é anunciada como uma lei que descarrega a própria desigualdade.

## C — O que a rota refuta e o que ela não refuta

`native_family_negative_witness` fornece um teste negativo na mesma família:

\[
b=72(A(a)+1)>0\quad\Longrightarrow\quad E(a,b)\le-1
\qquad(a\ge0).
\]

Esse b é usado somente como contraexemplo à positividade para coeficientes
livres. Não é escolhido como parâmetro canônico, ajuste de fonte ou origem
de um operador positivo. `exists_positive_seed_negative_family` registra a
existência de uma fonte negativa. Logo, a positividade da família sem
semente não pode ser estendida a todos os b≥0 por um argumento de norma.

O NO-GO é específico do coeficiente espacial cúbico com parâmetros livres.
Ele não é um NO-GO da fonte completada, da geometria Carry, de Hankel ou
da investigação all-order. O peso cúbico entra na resposta completa com
seu coeficiente original e junto aos demais pesos; E não é o balanço físico
total nem um pivô de Schur.

A calibração radial da PR #100 permanece explícita:
`J₄−a_rad J₂−b_rad J₀` tem perfil
`(k+1)⁴[d₄−a_rad/(k+1)² q−b_rad/(k+1)⁴ e₀]`.
Assim a,b deste relatório são coordenadas do perfil, não os mesmos números
em todas as escalas radiais. Não se confunde k radial com profundidade Carry,
endereço material ou parâmetro de câmera.

## D — Lean, auditoria e reprodução

São **39 teoremas e quatro definições** novos em `SeedFactors.lean`,
`SeedSigns.lean` e `SeedFamily.lean`, todos compilados com warnings como
erros. A auditoria transitiva passou para **43 raízes públicas e 5.163
dependências de tipos/corpos**, sem momentos ou característica como
dependências.

`Audit.lean` imprime axiomas de todas as raízes novas e percorre seus tipos e
corpos, rejeitando momentos canônicos, característica completada e os
consumidores de sinal selecionados pelo guard. Só são permitidos os axiomas
fundacionais padrão `propext`, `Classical.choice` e `Quot.sound`.

Nenhuma conclusão desta rodada recebe positividade de Hankel ou sinal de
pivô como hipótese. Não há fonte theta, zeros ou alturas como entradas.
Fontes, pesos, fases, amplitudes, 4!, Green, retorno, métrica e pins são
preservados. A igualdade de cada expressão com a fonte literal antecede
a leitura real e suas estimativas.

Os 39 ancestrais importados são recompilados de sua base exata por
`build_upstream.py`. Na validação final, `--reuse-upstream` permite conferir
os mesmos hashes de fontes e `.olean` já compilados nesta rodada, sem repetir
essa compilação. Na reprodução a partir de uma worktree nova, usar o comando
sem essa opção.

Os **14 checks locais passaram com código de saída zero**, incluindo
`lake build --wfail`, os módulos explícitos e as auditorias de Foundation,
Geometry e Analysis. `preservation.json` confirma fontes, pins, main e
trabalhos preexistentes intactos. O build inicial dos 39 ancestrais também
passou; seu comando está em `evidence/upstream-bootstrap.json`.

Na máquina `llm`, a worktree pode ser recriada após a entrega:

```bash
git -C /home/thlinux/geometry-of-numbers worktree add \
  /home/thlinux/geometry-of-numbers-native-cubic-seed-crosses \
  agent/native-cubic-seed-crosses
ln -s /home/thlinux/geometry-of-numbers/.lake \
  /home/thlinux/geometry-of-numbers-native-cubic-seed-crosses/.lake
cd /home/thlinux/geometry-of-numbers-native-cubic-seed-crosses/research/native-cubic-seed-crosses
python3 validate.py
```

Para conferir os arquivos entregues antes de regenerar os logs:

```bash
sha256sum -c MANIFEST.sha256
```

O validador compila explicitamente os módulos de pesquisa com warnings como
erros, executa o build raiz `lake build --wfail`, as auditorias de Foundation,
Geometry e Analysis, e verifica preservação da base, pins e trabalhos antigos.
A raiz Lake sozinha não inclui esses módulos de pesquisa.
Comandos, saídas e tempos ficam em `evidence/validation.json` e nos logs.
A auditoria local não representa aprovação de CI externo.

## E — Menor próximo alvo

O sinal dos quatro cruzamentos já pode ser confrontado no mesmo kernel, mas
o coeficiente cúbico sozinho não decide o sinal da fonte completada.
O próximo alvo analítico concreto é ampliar o Taylor original da resposta
ao suporte com halo `j : Fin 6`, até grau 9 com resto analítico de ordem 11:

\[
\rho_k(j)=i\big[h_0\delta p_1(j)-h_1\delta^3p_3(j)
+h_2\delta^5p_5(j)-h_3\delta^7p_7(j)+h_4\delta^9p_9(j)
+\delta^{11}\mathcal R_k(j)\big],\quad \delta=(k+1)^{-1}.
\]

Aqui `ℛ_k(j)=(j+1)¹¹ R((j+1)δ)`, com R analítico no centro.

Essa fórmula de ordem 11 é uma **próxima obrigação**, não um novo teorema
desta rodada. O resultado existente `response_weight_taylor` está escrito
em `Fin 4`, até grau 5 e resto de ordem 7. Deve-se reutilizar a analiticidade
e os coeficientes originais, sem criar uma nova resposta.

Depois será necessário inserir a mesma família radial em todos os setores,
conservar os nove pareamentos, cancelar os polos completos e controlar o
resto antes da parte finita. A candidata de limite a confrontar é

\[
2[h_4-2a_{rad}h_3+(a_{rad}^2-2b_{rad})h_2
+2a_{rad}b_{rad}h_1+b_{rad}^2h_0].
\]

Também é apenas alvo futuro desta entrega. A PR #41 continua sendo o elo
para interpretar a parte finita na direção crítica como Schur sob a
inversibilidade apropriada. Nenhuma das identidades cúbicas desta rodada
prova o sinal desse limite ou permite pressupô-lo.

Entrega em PR draft sobre a PR #101, sem merge automático.
Main, PRs anteriores e trabalhos alheios permanecem preservados.

**Fim do relatório.**
