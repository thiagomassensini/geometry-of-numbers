# Primeira correção da energia nativa em ordem finita arbitrária

**PARTIAL para a positividade canônica all-order; alvo E da PR #105
concluído.** O transporte da lei espacial chega agora à mesma energia
completada para qualquer conjunto finito de jets pares originais. As
condições locais de regularidade são descarregadas eventualmente na própria
fonte. Não há hipótese de sinal, inversibilidade de Hankel ou whitening.

Base exata: `7cbbe245b912325aa4f651aa460010fc1623d3c8`, PR #105,
branch `agent/native-all-order-spatial-correction`. Nova branch:
`agent/native-all-order-energy-correction`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Entrega em PR draft empilhada sobre #105, sem merge automático.

## A — O que já estava demonstrado

A PR #41 separou eliminação algébrica e sinal: um residual de Schur pode
ser identificado sob inversibilidade sem que sua positividade decorra
dessa operação. Aqui não se constrói sequer um inverso: os coeficientes da
fonte são livres. A especialização a uma direção crítica continua sendo
uma operação posterior, com suas hipóteses próprias.

A PR #105 provou o pareamento complexo dos stencils em dois índices
arbitrários. Para q_r=(-1)^r staticStencil(2r), m=2r,n=2s, sejam

\[
s_m=\frac{(m+1)(m+2)}2,\quad
 t_m=\frac{(m+1)(m+2)(m+3)(3m+4)}{24},\quad
 A_{m,n}=t_m+t_n-s_ms_n.
\]

A soma dos dois kernels ordenados no peso m+n+1 é (-1)^(r+s), no
peso m+n+3 é (-1)^(r+s)A_{m,n}, e os pesos ímpares inferiores cancelam.
Foram reutilizados `native_below`, `native_leading`,
`native_first_correction` e `radial_even_calibration`.

Outras declarações reutilizadas:

- `response_readout_analytic`, `response_coefficient_derivative`,
  `response_coefficient_even`, `response_coefficient_odd` e
  `response_radial_readout`, de `ResponseTaylor.lean`.
- `fullEnergy`, `full_response_flux`, `full_split`,
  `bulkBoundaryEnergy` e `mixedEnergy`, de `ResponseFlux.lean`.
- `radial_jet_original_source`, de `Stencil.lean`.
- `canonicalCompletedNativeRadialProjectiveChiral_eventually_regular`
  e `radial_weight_difference`: a regularidade eventual dos nós físicos.
- As operações originais de síntese e `coefficientWeight`, sua linearidade
  finita e a métrica Cauchy literal.

Também foram consultados os antecedentes
`all-order-binomial-green/CanonicalExtraction.lean`,
`GeneralCorrectionForm.lean` e `MomentSeparation.lean`.
Já possuíam extração formal de coeficientes em toda ordem, a identidade
`correction_bilinear_three_pairings` e a separação algébrica entre correção
e Schur. **Não se reivindica descobrir essas identidades nesta rodada.**
O alvo novo é o limite da correção reescalada do consumidor concreto
`CarryCriticalTfvd.fullEnergy`, com suporte arbitrário, resto e
regularidade efetiva. Os antecedentes consultados não são novas
hipóteses nem dependências formais dos módulos desta entrega.

## B — O que foi demonstrado agora

Todos os nomes novos estão em `CarryEnergyCorrection`.

### B.1 — Taylor da mesma resposta, em qualquer truncamento

`response_taylor_polynomial` separa os coeficientes pares nulos e os
ímpares da resposta nativa. `response_odd_remainder` prova, para cada N,

\[
q(z)=\sum_{j<N}(-1)^j h_j z^{2j+1}+z^{2N+1}R_N(z),
\qquad R_N\text{ analítico em }0.
\]

`nativeRemainder` escolhe uma testemunha dessa identidade da mesma função;
não escolhe um erro para ajustar uma energia. A fonte continua determinando
h, q e o Taylor. Não se supõe o sinal de nenhum coeficiente.

`response_samples_prefix` conserva o mesmo R_N em todo prefixo finito de
endereços. `response_synthesis_expansion` transporta a igualdade para a
**síntese complexa inteira** dos coeficientes ponderados, antes de parear
com uma entrada esquerda independente. Não há limite de suporte infinito
nem índice eventual uniforme em todos os prefixos.

### B.2 — Dois inputs físicos e o resto de quarta ordem

Defina apenas como notação K_w(c,d)=⟨S(c),S(wd)⟩ para o kernel existente,
e Ψ_rs(z)=K_{q((j+1)z)}(q_r,q_s)+K_{q((j+1)z)}(q_s,q_r).
Ambos os pareamentos ordenados são mantidos.

`kernel` é uma abreviação de `sectorKernel false`; seu corpo não depende
do parâmetro eta. O valor 1/2 na abreviação instancia esse parâmetro inerte,
não ajusta fonte, amplitude ou métrica. A recomposição Green abaixo aceita
qualquer 0<eta<1.

Com l=r+s, a lei espacial cancela todos os termos abaixo de 2l+1.
`pair_taylor_cancellation` retém exatamente os dois termos seguintes.
`pair_response_expansion` prova, numa vizinhança do centro,

\[
\boxed{
\Psi_{rs}(z)=z^{2l+1}
 \left(h_l-z^2A_{2r,2s}h_{l+1}+z^4T_{rs}(z)\right).
}
\]

Aqui T_rs(z) é explicitamente a soma dos mesmos dois kernels ordenados,
com peso

\[
 (j+1)^{2l+5}R_{l+2}((j+1)z).
\]

Não foi descartado. `weighted_synthesis_sum`,
`weighted_synthesis_continuous` e `pair_remainder_continuous` demonstram
sua continuidade a partir da síntese finita original. Para cada truncamento
usa-se R_N da mesma resposta; pares com o mesmo l usam a mesma testemunha.
Não se afirma uma única cota uniforme para todos os N.

A fase original q_r e a alternância dos coeficientes da resposta se
cancelam nas duas contribuições retidas; esse cancelamento é provado.
A parte real é tomada somente após as identidades complexas.

### B.3 — Mesma fonte completada, com suporte finito arbitrário

Para S um conjunto FINITO de ordens, c_r reais e k radial, define-se

\[
f_k=\sum_{r\in S}c_r\operatorname{radialJetCoefficients}(k,2r).
\]

É `finiteJetSource`: soma literal dos inputs existentes.
`finite_source_original` prova a igualdade vetorial nos dois canais:

\[
\operatorname{physicalCompletedFiniteSource}(k,f_k)
 =\sum_{r\in S}c_r J_{2r}(k).
\]

`finite_source_support` deriva o suporte do stencil original, contido em
0,...,2 max(S). `finite_source_pairing` preserva todos os cruzamentos e
usa apenas uma reindexação exata da soma dupla para reunir os pares
ordenados. Não presume que cada kernel ponderado seja Hermitiano.

Escreva κ_k=k+1, δ_k=κ_k⁻¹ e

\[
 Q_S(c)=\sum_{r,s\in S}c_rc_s h_{r+s},\qquad
 C_S(c)=-\sum_{r,s\in S}c_rc_s A_{2r,2s}h_{r+s+1}.
\]

`normalized_pair_expansion` conserva o resto δ_k⁴T_rs(δ_k) e
`normalized_pair_correction_tendsto` prova seu limite após a reescala.
`finite_energy_pairing` descarrega a regularidade no prefixo físico e
identifica a energia completa com a soma desses pareamentos normalizados.

O teorema principal é `finite_energy_correction_tendsto`:

\[
\boxed{
\kappa_k^2\bigl(\operatorname{fullEnergy}(k,f_k)-Q_S(c)\bigr)
\longrightarrow C_S(c).
}
\]

Vale para qualquer S finito fixo e quaisquer coeficientes reais fixos,
inclusive a fonte zero. Em Lean, C usa a parte real de `spatialCorrection`;
esses coeficientes são os polinômios reais A acima.

Não se recebem `PosDef`, `PosSemidef`, `IsUnit`, independência linear,
contração de retorno, alturas ou um sinal de pivô. O enunciado não é
condicional à identidade Gram que queremos descobrir.

### B.4 — Green, bordo, retorno e normalização original

`finite_source_green_recomposition` conserva a identidade

\[
 \operatorname{fullEnergy}
 =\operatorname{bulkBoundaryEnergy}+\operatorname{mixedEnergy}.
\]

O prefixo de regularidade inclui o endereço exterior adicional do
comutador. `finite_green_correction_tendsto` prova o MESMO limite C_S
para essa soma, sem zerar o termo misto ou descartar correções de bordo.

`original_norm_difference` conserva o fator 1/2 da forma nativa:

\[
 2\operatorname{fullEnergy}(k,f_k)=\|I_k\|^2-\|R_k\|^2.
\]

`finite_norm_difference_correction` transporta a expansão ao balanço
incidência−retorno, com limite 2C_S. Não há alteração da métrica.

### B.5 — Regressão quártica e certificação

Para S={0,1,2}, c=(−b,−a,1), `finite_quartic_source` recupera exatamente
J4−aJ2−bJ0. `finite_quartic_form` recupera Q da PR #104, e
`finite_quartic_correction` recupera

\[
 -55h_5+150ah_4-14a^2h_3+252bh_3-40abh_2-b^2h_1.
\]

`quartic_correction_regression` obtém o limite anterior como corolário do
teorema geral, sem depender do certificado quártico para prová-lo.

São 39 teoremas, dez definições e duas abreviações em quatro módulos de
prova. A auditoria cobre 51 raízes públicas: 15 espaciais, com 5.082
dependências transitivas, e 36 de proveniência, com 5.762 dependências.
O grupo espacial proíbe momentos e característica; o grupo de proveniência
pode usar a resposta e os momentos originais, mas proíbe os consumidores
de sinais selecionados pelo guard. Somente `propext`, `Classical.choice`
e `Quot.sound` são permitidos. Não há novas admissões ou axiomas matemáticos.

## C — O que foi refutado ou não pode ser inferido

Esta rodada não introduz um novo contraexemplo à fonte canônica.
Mantém os controles anteriores:

- A tabela A não é uma Gram positiva: sua direção (20,−1) tem valor −386,
  formalizado na PR #105. A nova identidade não apaga essa obstrução.
- A correção usa o momento seguinte ao prefixo que determina um Schur.
  `arbitrary_correction_with_fixed_schur`, no antecedente
  `MomentSeparation.lean`, separa as duas quantidades para funcionais
  arbitrárias. Esse controle não modifica a fonte canônica.
- Assim, provar o sinal de C não basta, por si só, para concluir o sinal de Q
  ou de todos os pivôs. Não se transforma uma taxa de aproximação em uma
  prova de positividade do limite.

## D — O que permanece aberto

A positividade all-order de H e K e uma Gram Hilbert exata dos momentos
canônicos continuam abertas. A energia analisada permanece uma forma
assinada dos mesmos canais físicos, não uma norma positiva disfarçada.

O teorema quantifica todos os suportes finitos fixos. Não prova controle
uniforme na ordem, limite conjunto k,d→∞, domínio de um operador infinito
ou desaparecimento de uma cauda material infinita.

Também não fornece um sinal universal para C_S. Não escolhe o lado de
aproximação sem uma desigualdade adicional da fonte específica. As
identidades theta e os certificados H6/K6 não são premissas dessa prova.

O transporte desta entrega usa jets pares. A lei de coeficientes com
paridade arbitrária já existe em `all-order-binomial-green`; isso não
substitui automaticamente o novo limite físico reescalado no setor ímpar.

## E — Próximo passo mínimo

Transportar a mesma expansão ao setor ímpar, usando os coeficientes de
paridade já provados, sem refazer a lei binomial. Conservar o fator −i
proveniente do passo imaginário, sua conjugação e a fonte completa

\[
 f_k^{\mathrm{odd}}=\sum_{r\in S}c_r
 \operatorname{radialJetCoefficients}(k,2r+1).
\]

O alvo concreto a testar e demonstrar, ainda não provado aqui, é

\[
\kappa_k^2\left(\operatorname{fullEnergy}(k,f_k^{\mathrm{odd}})
 -\sum_{r,s\in S}c_rc_s h_{r+s+1}\right)
\longrightarrow
-\sum_{r,s\in S}c_rc_s A_{2r+1,2s+1}h_{r+s+2}.
\]

Reutilizar `same_parity_first_correction`,
`original_quotient_same_parity` e `native_same_parity_first_correction`
dos módulos históricos consultados; conferir as normalizações nos dois
canais e o halo do comutador. Isso estende o controle ao setor deslocado K,
sem reivindicar que a extensão resolva seu sinal.

A obrigação de sinal permanece separada: exige uma propriedade
independente do transporte completado. Não repetir
`correction_bilinear_three_pairings` como se fosse uma nova prova de sinal,
nem interpretar a correção negativa como prova da positividade de Q.

### Reprodução e evidências

No ambiente original do servidor `llm`, em worktree desta branch com
`.lake` ligado ao cache canônico:

```bash
cd research/native-all-order-energy-correction
python3 validate.py
```

O comando normal recompila os 31 ancestrais das fontes na base exata.
`--reuse-upstream` verifica todos os hashes de fontes e `.olean` do
bootstrap registrado. Os quatro módulos novos e `Audit.lean` são sempre
compilados explicitamente com warnings como erros.
Os **15 checks locais passaram com código de saída zero**.
A validação inclui `lake build --wfail` raiz e dos alvos pertinentes do
operador, auditorias
Foundation/Geometry/Analysis, base, fontes, pins e trabalhos preexistentes.
Logs, comandos e códigos de saída constam de `evidence/validation.json`.
`public-roots.json`, `evidence/lean-Audit.log`, `evidence/upstream.json`,
`evidence/source-provenance.json` e `evidence/preservation.json` registram
as dependências e a preservação. O manifesto SHA256 cobre a entrega.
Os checks são locais no servidor; não constituem uma afirmação de CI remoto.

**Fim do relatório — PARTIAL para positividade; transporte da primeira
correção da energia completada provado em qualquer suporte finito par.**
