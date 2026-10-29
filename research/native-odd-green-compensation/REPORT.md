# Transporte da fonte ímpar original para a Hankel deslocada

**Classificação: PARTIAL.** O transporte solicitado foi demonstrado para a
forma complexa assinada completa, em toda ordem finita fixa. A compensação
vetorial do primeiro input ímpar foi demonstrada para todo grau de endereço.
A positividade all-order da Hankel canônica permanece aberta.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-odd-green-compensation`.
Base exata: `608ada10b07d33d6b691e4685b062bcc59a8a7a4`, head da PR #112,
`agent/native-cross-radial-green-cubic`, consultada aberta, draft e sem merge.
A nova PR é empilhada sobre essa branch; não pressupõe integração em main.
Nenhuma PR anterior, definição de fonte, métrica, amplitude, retorno ou pin foi alterado.

## A — O que já estava demonstrado

As declarações atuais, e não somente os relatórios anteriores, são reutilizadas:

- `CarryOddEnergy.nativeOddProfile`, `finiteOddJetSource`,
  `finite_odd_source_profile`, `finite_odd_source_support` e
  `odd_coefficients_imaginary` são os perfis e as fontes ímpares originais.
- `CarryOddEnergy.normalized_odd_pair_expansion` e
  `odd_pair_remainder_continuous` fornecem a expansão exata do par ordenado
  ímpar, incluindo a correção e o resto analítico. O trabalho anterior também
  possui consumidores diagonais de energia; eles não são usados aqui para
  inferir a identidade com dois inputs independentes.
- `CarryMixedParity.complete_complex_pair` reconstrói a forma complexa
  completa da mesma fonte; `response_samples_real` controla a conjugação.
- `CarryCrossRadial.cross_green_eq_original` identifica os nove pareamentos
  Green/bordo/complemento com a forma original. Seu caso de duas escalas
  radiais diferentes não é substituído por uma falsa isometria.
- `CarryGreenLeading.partField`, `part_field_reconstruction` e
  `completed_part_scale_input` são os operadores físicos já existentes.
- A PR #112 demonstrou extração Taylor e recomposição cúbica vetorial.
  Seu próximo teste era o input ímpar original com os fatores `2^d`, `3^d`,
  os dois bordos e o comutador. Esse teste é resolvido abaixo.
- `GeometryOfNumbers.Analysis.shiftedHankel` e `sourceMomentMatrix h 1 N`
  já são as definições da mesma Hankel deslocada. A nova identificação entre
  elas é literalmente `rfl`; não se introduz uma sequência substituta.

O mecanismo de ortogonalização algébrica da PR #41 continua separado da
interpretação positiva: inversibilidade permite separar o Schur, mas não
fornece seu sinal. Os certificados H6/K6 e das doze fontes permanecem
resultados finitos anteriores; não são premissas destas novas provas.

**Índices distintos:** `d` é grau do peso de endereço; `r,s` são ordens dos
jets ímpares; `k` é a regularização radial; `N` é a ordem finita da matriz.
Nenhum deles é identificado com profundidade vertical Carry. `eta` é o
parâmetro do Green já definido, com `0 < eta < 1`; não é ajustado aos momentos.

## B — O que foi demonstrado agora

Todos os nomes novos abaixo pertencem ao namespace `CarryOddGreen`.
São 27 teoremas, duas definições de readout e duas abreviações de vetores
preexistentes, distribuídos em quatro módulos Lean.

### B.1 — Compensação vetorial ímpar para todo grau de endereço

Escreva `O = nativeOddProfile 0 = i(e₀-e₁)`, `w_d(j)=(j+1)^d`,
`phi_j = completedNativeChiralCauchyFeature j`,
`g_j = physicalGreenOperator eta phi_j` e
`t_j = (physicalGreenResolvent eta)^2 phi_j`.
As abreviações `greenColumn`, `traceColumn` nomeiam exatamente esses vetores.

Em [OddVectors.lean](OddVectors.lean), sem produtos internos ou projeções:

\[
\begin{aligned}
V_0(w_d,O)&=i\,2^d(2+\eta)g_1-i\eta3^d g_2,\\
V_1(w_d,O)&=i\,[t_0-(2^d+2\eta)t_1],\\
V_2(w_d,O)&=i\eta[(1-2^d)g_1+(3^d-2^d)g_2].
\end{aligned}
\]

São `odd_bulk_vector`, `odd_boundary_vector`, `odd_residual_vector`.
As identidades dos coeficientes são `odd_bulk_coefficients`,
`odd_weighted_coefficients`, `odd_commutator_coefficients`.
Os dois bordos aparecem em `V_1`; o endereço externo `2` continua presente
em `V_0` e `V_2`. Não se descartou um termo por ser invisível a uma diagonal.

Em [OddCompensation.lean](OddCompensation.lean), para **todo** `d : Nat`:

\[
\boxed{V_0+V_2=i[(2^{d+1}+\eta)g_1-\eta2^d g_2].}
\]

`odd_bulk_residual_cancellation` prova o cancelamento exato de `3^d`
entre bulk e comutador, como vetores. O complemento não é zero.
A síntese completa, `odd_complete_vector_reconstruction` e a versão
inteiramente expandida `odd_three_vector_identity`, prova:

\[
\boxed{V_0+V_1+V_2=i\phi_0-i2^d\phi_1.}
\]

Esta é a síntese do input original ponderado, não uma escolha de norma.
`odd_profile_radial_jet` calibra o primeiro jet original:
`radialJetCoefficients k 1 = (k+1) • O`.
`odd_physical_jet_calibration` transporta essa igualdade para cada uma das
três partes da fonte **com as duas pernas**, antes do pareamento assinado.

As regressões exatas `odd_linear_residual`, `odd_cubic_residual` são:

\[
V_2(w_1,O)=i\eta(-g_1+g_2),\qquad
V_2(w_3,O)=i\eta(-7g_1+19g_2).
\]

### B.2 — Dois inputs independentes, sem partir somente da diagonal

Em [OddHankelTransport.lean](OddHankelTransport.lean), sejam `S,T` suportes
finitos independentes, `c,d : Nat → Real` coeficientes independentes, e
`C_k=finiteOddJetSource S c k`, `D_k=finiteOddJetSource T d k`.
A nova definição `oddPairing` é somente a forma original:

\[
\operatorname{oddPairing}_k(C,D)
=\frac12(\langle I_k(C),I_k(D)\rangle_\mathbb C
         -\langle R_k(C),R_k(D)\rangle_\mathbb C).
\]

Não é um novo produto interno positivo. A fonte completada, suas fases,
ambas as quadraturas e seu retorno são os anteriores.

`kernel_imaginary_imaginary` prova a realidade do kernel com os dois inputs
puramente imaginários e pesos reais. Não recebe simetria nem positividade.
`odd_ordered_kernel_sum` mantém as **duas ordens** do kernel. Depois,
`odd_pairing_exact` prova, eventualmente na regularização original:

\[
\operatorname{oddPairing}_k(C,D)
=\sum_{r\in S}\sum_{s\in T}c_r d_s\,
   \operatorname{normalizedOddPair}(r,s,k).
\]

O prefixo de regularidade inclui o halo dos endereços de ambos os inputs.
A condição eventual de não anulação da característica é descarregada pelo
teorema original de regularidade radial, não recebida como hipótese nova.

`normalized_odd_pair_tendsto` usa a expansão anterior com seu resto contínuo
para provar `normalizedOddPair r s → h(r+s+1)`.
Com somas finitas e sem hipóteses de sinal, `odd_pairing_tendsto` conclui:

\[
\boxed{\operatorname{oddPairing}_k(C,D)
\longrightarrow\sum_{r\in S,s\in T}c_r d_s h_{r+s+1}.}
\]

`odd_green_pairing_tendsto` prova o mesmo limite com `crossGreenPair`,
isto é, com **todos os nove cruzamentos** das partes Green/bordo/comutador.
Primeiro ocorre a reconstrução vetorial completa; somente depois, o readout.

### B.3 — Transporte explícito para a nossa matriz ímpar

Em [OddRegressions.lean](OddRegressions.lean), para cada `N` fixo:

\[
K_N(i,j)=h_{i+j+1},\qquad
\boxed{\operatorname{oddPairing}_k(x,y)\longrightarrow x^TK_Ny.}
\]

`odd_bilinear_eq_matrix` faz a reindexação das somas para `Fin N`.
`odd_matrix_bilinear_tendsto` e `odd_matrix_green_bilinear_tendsto`
provam a fórmula para **quaisquer dois vetores reais finitos**, não apenas
para `x=y`. `odd_matrix_entry_tendsto` e
`odd_matrix_green_entry_tendsto` dão cada entrada a partir dos jets ímpares
originais. `odd_matrix_entry_real_tendsto` aplica a projeção real somente
após a síntese complexa e a prova de seu limite.

`shifted_hankel_eq_source` preserva a igualdade das duas definições atuais.
`odd_bilinear_diagonal_eq` verifica a compatibilidade com `oddCanonicalForm`
preexistente; essa compatibilidade não é usada como origem do transporte.

O resultado vale para todo `N`, com `k → ∞` para cada `N` fixo. Não se
reivindica uniformidade em `N`, troca de limites ou identidade isométrica
entre regularizações radiais diferentes.

## C — O que foi refutado ou delimitado

Não surgiu um novo no-go da geometria. Foram resolvidas as fórmulas exatas
do candidato ímpar indicado pela PR #112.

As identidades impedem três leituras incorretas:

1. Apagar o complemento por um cancelamento de seu autopareamento perderia
   os termos `1-2^d` e `3^d-2^d`, necessários à reconstrução.
2. Apagar os bordos perderia `t₀-(2^d+2eta)t₁`. O cancelamento de `3^d`
   não autoriza essa remoção.
3. Identificar `oddPairing` com uma Gram positiva omitiria a subtração do
   canal retornado. A igualdade do kernel canônico com esta **forma assinada**
   não demonstra sua positividade.

Os no-gos anteriores de mistura de escalas radiais continuam intactos.
Aqui ambos os inputs usam o mesmo `k`, embora suportes, ordens e coeficientes
sejam independentes. Não foram usados zeros, alturas, Cholesky dos momentos
ou uma nova métrica para fabricar vetores.

## D — O que permanece aberto

**O transporte assinado para K_N está provado. A representação positiva
all-order permanece aberta.** Na diagonal, obtemos exatamente

\[
x^TK_Nx=\lim_k\frac12(\|I_k(x)\|^2-\|R_k(x)\|^2).
\]

A positividade das duas normas separadas não determina a diferença.
Não foi demonstrada contratividade do retorno em todas as direções ímpares,
nem uma realização Hilbert positiva equivalente, nem independência linear
all-order. Nenhum desses itens foi inserido como hipótese.

A compensação explícita de B.1 é all-degree para **O₀**. Ela não deve ser
anunciada como a fórmula explícita de cada `nativeOddProfile r`. Já B.2–B.3
tratam efetivamente todas as combinações finitas de jets ímpares pelo kernel
completo, sem inferir o sinal de suas parcelas.

## E — Próximo passo mínimo

Agora é possível atacar um defeito geométrico concreto, mantendo os dois
argumentos. O primeiro teste não trivial do sinal ímpar é a combinação
original de jets `jet₃ - a jet₁`, sem mudar fonte, fases ou pesos, com
`a=h₂/h₁` e `h₁>0` já conhecido. O transporte aqui demonstrado identifica
seu limite assinado com

\[
h_3-2a h_2+a^2h_1=h_3-h_2^2/h_1.
\]

O próximo teorema útil é uma **decomposição vetorial explícita** das partes
do perfil cúbico `nativeOddProfile 1`, pareadas com as de `nativeOddProfile 0`,
que exponha o defeito completo dessa combinação antes do readout. As fórmulas
locais do comutador e os nove pareamentos já existentes permitem testá-la
sem recalcular momentos. O objetivo é identificar uma propriedade independente
do transporte que controle seu sinal; não receber esse Schur positivo como
entrada. Uma mera reescrita do sinal, ou mais um consumidor do certificado
theta finito, não fecharia a explicação geométrica.

Se a decomposição exibir parte positiva mais defeito sem sinal, deve-se
registrar exatamente o defeito. Se o sinal vier somente do limite que se
pretende provar, a rota é circular. Mesmo que esse primeiro caso feche,
a generalização precisa conservar todos os perfis e a cauda; não se extrapola
a positividade all-order do sucesso finito.

### Validação, proveniência e reprodução

No host canônico `llm`, em checkout da branch e com as dependências registradas:

```bash
cd research/native-odd-green-compensation
python3 validate.py
```

O modo normal recompila os 61 módulos ancestrais inalterados da base.
**Nesta rodada eles foram reaproveitados**, após verificar os hashes das
fontes contra Git, dos 61 objetos Lean, da toolchain, manifest, árvore do
núcleo, fontes nativas, pins e estados das dependências.
`restore_verified_cache.py` documenta essas verificações; a variante
`--verify-only` não extrai nem altera o cache. A compilação desta rodada usa:

```bash
python3 validate.py --reuse-upstream
```

**Os 16 checks locais passaram, todos com código de saída zero.**
Os quatro módulos novos e `Audit.lean` foram compilados explicitamente com
`lean -DwarningAsError=true`. Os builds `lake build --wfail` e as auditorias
Foundation/Geometry/Analysis são executados separadamente. O cache binário
não é versionado; sem ele, o modo normal recompila os ancestrais.

A auditoria registra `#print axioms` para as 31 raízes públicas e percorre
tipos **e corpos**, em dois grupos:

| Grupo | Raízes | Dependências únicas | Restrição adicional |
| --- | ---: | ---: | --- |
| Construção vetorial/exata | 19 | 5.520 | Momento canônico proibido |
| Proveniência do limite/matriz | 12 | 5.719 | Sem certificados de sinais |

Ambos bloqueiam os consumidores posteriores de positividade finita,
os certificados de sinal h₀/h₁, os atalhos escalares da PR #110 e os
quatro consumidores diagonais `finite_odd_source_pairing`,
`finite_odd_energy_pairing`, `finite_odd_energy_correction_tendsto`,
`finite_odd_green_correction_tendsto`. A identidade de dois inputs não é
apresentada como consequência de uma prova escalar diagonal omitida.
Somente `propext`, `Classical.choice`, `Quot.sound` são admitidos nesta
camada de análise; Foundation conserva sua auditoria própria.

Os comandos e saídas ficam em `evidence/validation.json`; as raízes em
`public-roots.json`; a auditoria em `evidence/lean-Audit.log`;
a restauração em `evidence/cache-restoration.json`; fontes, pins e trabalho
antigo protegido em `source-provenance.json` e `preservation.json`.
`SHA256SUMS` registra a integridade. Logs brutos com espaços finais são
conservados em `.raw.log.gz` quando necessário. O resultado é local,
sem reivindicação de CI remoto. O commit e a URL da PR ficam na entrega
externa, evitando referência circular do próprio arquivo ao seu commit.

**Fim do relatório — PARTIAL: transporte polarizado completo para a matriz
ímpar demonstrado; positividade all-order continua aberta.**
