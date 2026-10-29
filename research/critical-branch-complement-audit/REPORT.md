# Auditoria do complemento crítico C2 até a fonte Green completada

## Conclusão

**PARTIAL no transporte até Parseval; OPEN na ponte principal até a forma quiral nativa.** Há dois NO-GOs específicos já demonstrados: identificar o estado bruto unitário com o vetor do momento zero; anular todo o residual do jet Taylor complexo radial. Não são obstruções a toda realização possível da fonte completada.

Nesta rodada foram acrescentadas provas de compressão **polarizada**, transporte isométrico do mesmo complemento, síntese finita com todos os cruzamentos, defeito do frame Green bruto e testes nativos de baixa ordem. Nenhuma positividade Hankel all-order foi assumida ou tentada.

## Proveniência e escopo

Execução canônica por `ssh llm`, Lean 4.32.0. Bases:

| Repositório | Base | Branch desta auditoria |
| --- | --- | --- |
| geometry-of-numbers | `59e53d863f4ef0ad998b0eb19fd3891c9839cc35` | `agent/critical-branch-complement-audit` |
| carry-self-adjoint-operator | `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` | `agent/critical-branch-native-audit` |

Os branches anteriores `agent/seventh-even-centered-source` e `agent/material-boundary-source-sewing` foram preservados. Esta auditoria parte das respectivas `origin/main`, sem incorporar os PRs abertos #34 e #107. Nenhum worktree foi criado ou removido. A ponte principal permanece aberta: não fazer merge automático.

Pins, fontes históricas, amplitudes, métricas, câmeras, completion e coeficientes originais permanecem intactos. Os dois arquivos de usuário `C2OddTfvdTransport.lean` e `C2OddTfvdTransportAudit.lean` foram preservados, com hashes conferidos pelo verificador.

Os módulos Green/relógio existem em ambos os repositórios, em namespaces distintos. Em geometry usam `GeometryOfNumbers.Analysis.*`; no operador, as portas locais usam `CarrySelfAdjointOperator.*`. O pacote geometry pinado pelo operador permanece em `d7cc54f5c485320f1fada33118e9e6101488819a`. Não se usou uma troca silenciosa de `LEAN_PATH` ou de pin para misturar ambientes.

## A. Geometria, operadores e domínios concretos

| Objeto existente | Domínio → codomínio / papel |
| --- | --- |
| `realCriticalBranchIsometry t` | `RealPlaneHilbert →ₗᵢ[ℝ] C2BranchCarrier`; plano real → ℓ² das duas pernas e profundidades `j+2` |
| `criticalPhysicalCoreFiber m t` | correção física de fase aplicada ao ramo puro existente |
| `globalCriticalPhysicalBranch t` | `CoreState →ₗᵢ[ℝ] GlobalC2BranchCarrier`; soma Hilbert dos núcleos ímpares positivos |
| `globalBranchIncidenceIsometry` | equivalência isométrica real `GlobalC2BranchCarrier ≃ₗᵢ[ℝ] OddMaterialState` |
| `globalCriticalPhysicalBranchIsometry t` | `CoreState →ₗᵢ[ℝ] OddMaterialState` |
| `oddMaterialToGreenState` | `OddMaterialState →ₗᵢ[ℝ] State`; duas quadraturas empacotadas e extensão por zero |
| `c2GlobalGreenInputIsometry t` | `CoreState →ₗᵢ[ℝ] State`; composição literal das duas portas anteriores |
| `greenStateMaterialLogGenerator` | operador parcial complexo sobre `State`, com domínio maximal do relógio material |
| `greenParsevalMaterialLogOperator` | operador parcial no espaço de análise; relógio transportado na imagem Parseval fechada, zero no complemento ortogonal dessa imagem |

`State` é o carrier ℓ² complexo dos inteiros materiais positivos; `CoreState` é ℓ² dos núcleos ímpares positivos com fibra real de duas coordenadas. O produto interno utilizado na compressão é **real**, inclusive depois do empacotamento complexo. Seu adjunto é o adjunto real.

A fórmula pontual existente, `globalCriticalPhysicalBranchIsometry_pointwise` / `c2GlobalGreenInput_apply`, mantém

\[
n=2^d m\pm1,\quad d=j+2,\quad 2^{-d/2}\,R(-t\log n)v_m.
\]

`globalC2_provenance_roundtrip` recupera núcleo, perna e profundidade. A fase do ramo puro `−d t log 2` só se torna `−t log n` pela correção física já existente. Não identificamos profundidade, endereço material e ordem de jet.

O domínio exato, por `c2Source_log_domain_iff`, é

\[
Uv\in\operatorname{Dom}L\iff
\sum_{n\ge1}(\log n)^2 |(U_0v)(n)|^2<\infty.
\]

Os novos teoremas recebem essa condição explicitamente para **cada** entrada. Valem para fontes de suporte finito nos núcleos que pertençam ao domínio e, mais geralmente, para toda fonte nesse domínio. Esta auditoria não acrescentou um teorema de pertencimento automático para toda fonte de suporte finito nos núcleos: esse suporte ainda deixa uma cauda infinita em profundidade. Não há aplicação implícita de `L²`.

### Identidade exata nova

Namespace `GeometryOfNumbers.Analysis.CriticalBranchComplement`:

\[
C_U=I-UU^*,\qquad
\langle C_Uz,C_Uw\rangle_\mathbb R
=\langle z,w\rangle_\mathbb R-\langle U^*z,U^*w\rangle_\mathbb R.
\]

- `complement_pairing`: identidade para duas entradas independentes.
- `compression_energy`: a diagonal pedida, para qualquer `z`, portanto para `z=LUv` quando definido.
- `c2_clock_compression_energy`: especialização literal ao relógio e input C2 existentes.
- `compression_energy_nonneg`: sinal não negativo.
- `compression_energy_pos_iff`: sinal estrito **se e somente se** `C_Uz ≠ 0`. A isometria sozinha não fornece a não degenerescência.
- `complement_synthesis_pairing`: síntese finita completa antes do produto interno, com todos os cruzamentos ordenados, inclusive entre famílias de tamanhos diferentes.

Não foi criado outro relógio. `complement` é a expressão `I−UU*`, não uma mudança de fonte ou métrica.

### Transporte exato até Parseval

Para uma segunda isometria real `P`,

\[
C_{PU}Pz=P C_Uz.
\]

`complement_isometric_transport` prova a igualdade vetorial; `complement_isometric_pairing` prova a conservação polarizada. Elas se aplicam à incidência material e à inclusão Green existentes.

`realParseval` apenas empacota a restrição real da análise Parseval canônica já existente. Com o intertwining de `greenParsevalMaterialLogOperator_c2Source_intertwining`, o novo `c2_clock_complement_parseval_pairing` identifica, para duas fontes em seus domínios, o complemento calculado **depois** do relógio Parseval com o complemento do mesmo relógio material **antes** da análise.

A projeção `I−(PU)(PU)*` relativa à fonte C2 não deve ser confundida com o complemento ortogonal da imagem de `P` usado para estender o relógio por zero. São subespaços diferentes.

### Defeito exato do Green bruto

Se `T` é `canonicalRawGreenAnalysis`, o novo `rawGreen_complement_pairing` prova

\[
\langle TC_Uz,TC_Uw\rangle
=\langle C_Uz,C_Uw\rangle+\delta_T(z,w),\quad
\delta_T(z,w)=\langle(T^*T-I)C_Uz,C_Uw\rangle.
\]

É um residual real bilinear simétrico; depende do frame canônico e das duas entradas complementares. Seu sinal não foi determinado neste subespaço. Os bounds existentes do frame implicam, na diagonal,

\[
-\tfrac12\|C_Uz\|^2\le\delta_T(z,z)\le
\mathrm{greenBesselConstant}\,\|C_Uz\|^2.
\]

Esta última desigualdade é uma consequência matemática dos bounds existentes; não recebeu um novo nome Lean nesta rodada. Não se deduz daqui nem anulação nem sinal positivo. O testemunho existente `canonicalRawGreenAnalysis_not_isometry` impede tratar `T` globalmente como isometria; ele não prova não anulamento especificamente em toda imagem de `C_U`.

A fatoração original `c2GlobalRestrictedGreenGram_source_factors` continua sendo `W* J* T* T J W`. Sua positividade é a positividade desse Gram bruto, não uma identificação com a forma quiral.

## B. Fonte quiral, polarização e correções

A fonte de chegada existente é `nativeSourceProjectiveBoundaryJetSynthesis n k x`, com carrier
`CanonicalCompletedNativeChiralCauchyCarrier × CanonicalCompletedNativeChiralCauchyCarrier` e forma original

\[
B_{\rm chir}(a,b)=\tfrac12(\langle a_+,b_+\rangle_\mathbb C-
\langle a_-,b_-\rangle_\mathbb C).
\]

`nativeSourceProjectiveBoundaryJetSynthesis_pairing` retém todos os cruzamentos de duas sínteses independentes. `..._pairing_tendsto` identifica seu limite com os dois blocos de momentos, com fases herdadas `(-1)^i`, e só então elimina os setores mistos pelo limite demonstrado. `..._energy_tendsto` prova

\[
2(\|S_k(x)_+\|^2-\|S_k(x)_-\|^2)
\longrightarrow\operatorname{nativeSourceFiniteBoundaryEnergy}(2n,x).
\]

É uma diferença assinada. A soma dos dois quadrados não é a energia original. O teorema `nativeSourceEvenBoundary_positive_iff_stieltjes` é uma equivalência exata, não uma prova independente do sinal.

As correções não desaparecem por positividade individual. As identidades existentes, verificadas na auditoria de axiomas, são:

- `RealFirstNative.resolvedCorrection_escape_four_crosses`: cancelamento dos quatro termos Gamma/correção no canal escape, nas formas métrica e associada à rotação real.
- `RealFirstNative.nativeDefect_real_components`: para `g=⟨response(z),response(w)⟩ℝ`, `ω=⟨J response(z),response(w)⟩ℝ`, `s=w−conj z` e Wronskiano `W(w,z)`, o defeito original satisfaz `D.re=s.re*g−s.im*ω−W.re` e `D.im=s.re*ω+s.im*g−W.im`, sob as hipóteses de faixa declaradas.
- `ChiralReturn.polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance`: balanço completo `= 2⟨Gamma(c),Gamma(d)⟩ + 2i rawGammaWronskianBalance(c,d)` com os pesos originais.
- `ChiralReturn.storage_re_eq_gammaEnergy_sub_rawGammaBalance`: diagonal `storage.re = 2‖Gamma(c)‖² − 2 Im(rawGammaWronskianBalance(c,c))`, com domínio e não anulamento dos denominadores explícitos.

O sinal do termo Gamma residual completo é aberto em toda ordem; estimativas de uma seção finita não o tornam não negativo em todas as direções.

**Não foi encontrada/provada uma aplicação física que identifique `C_U L Uv` com essa síntese quiral completada.** As identidades anteriores controlam suas respectivas fontes existentes. Não justificam colar os carriers pelo nome Green, pela isometria ou por igualdade diagonal isolada. Por isso ainda não há um defeito branch→chiral efetivamente calculado: primeiro falta a aplicação que torne essa comparação da mesma fonte bem tipada. O residual do frame e o residual Gamma acima são explícitos; não os declaramos iguais entre si.

## C. Obstruções e baixa ordem

Namespace novo no operador: `CarrySelfAdjointOperator.CriticalBranchNativeAudit`.

### Massa bruta e recorrência nativa — NO-GO específico

Reutilizados `canonicalCompletedNativeLogDerivativeMoment_zero_pos`, `..._zero_lt_sixteenth` e a recorrência real da característica completada, com `c₀>0`. Para os momentos de um observável positivo existente, o novo `convolutionDefect_eq_moment_errors` demonstra

\[
D_n=c_0(q_n-h_n)+\sum_{k<n}(q_k-h_k)c_{n-k}.
\]

Em particular `convolutionDefect_zero_eq_mass_error` dá

\[
D_0=c_0(\|u\|^2-h_0).
\]

Se `‖u‖=1`, então `unit_source_zero_defect_gt` prova `D₀ > 15 c₀/16 > 0`. Especializações:

- `raw_critical_branch_zero_defect_pos`;
- `raw_global_physical_branch_zero_defect_pos`;
- `raw_green_input_zero_defect_pos`;
- `raw_global_physical_branch_not_native`.

Esses enunciados usam o observável **limitado** da API `positiveObservableMoment`. A obstrução já está na massa de sua fonte, independentemente do observável. Não identificamos esse observável com o relógio material parcial. E não atribuímos massa 1 ao vetor `C_U L Uv`: a obstrução do estado bruto não refuta o complemento físico.

### Primeiro cruzamento — NO-GO da atribuição literal a núcleos distintos

`raw_distinct_cores_even_cross_not_native` demonstra que dois vetores brutos provenientes de núcleos distintos têm produto interno zero, por `globalCriticalPhysicalBranch_core_orthogonal`, enquanto a primeira entrada fora da diagonal da Hankel par é `h₁≠0`. Portanto essa atribuição literal de jets pares a núcleos brutos distintos também falha na polarização. O enunciado não é uma afirmação sobre toda família corrigida de jets ou sobre o complemento clocked.

### Primeira face da energia original

`native_boundary_two` prova, com a escala herdada e sem ajuste,

\[
E_2(x)=4(h_0|x_0|^2+h_1|x_1|^2).
\]

A massa `h₀` do kernel de momentos e o fator `4h₀` da face de bordo original são comparações diferentes. Nenhum fator foi removido para compatibilizar o ramo unitário.

### Green/Taylor — NO-GO específico já existente

`canonicalCompletedNativeGreenForwardDifferenceGramResidual_odd_zero_eq_moment_one` prova, **sob a hipótese explicitamente recebida `hkernel`**, que o residual na primeira diagonal ímpar é `(h₁ : ℂ)`. A fonte theta/cosseno já fornece `h₁≠0`. `not_forall_canonicalCompletedNativeGreenForwardDifferenceGramResidual_eq_zero_unconditional` elimina a premissa adicional `h₁≠0`, mas ainda recebe `hkernel`; seu nome não transforma essa hipótese em uma construção física.

Logo não se deve tentar anular o residual de todos os jets Taylor complexos dessa realização radial. Isso não refuta o carrier TFVD real/enriquecido nem toda realização Green possível.

## D. Menor obrigação restante

Antes de qualquer nova prova Hankel all-order, construir a aplicação **determinada pela fonte** dos coeficientes originais da síntese quiral para as fontes C2 no domínio do relógio. Ela deve preservar as duas quadraturas, pernas, endereço, cauda, completion e correções, com igualdade vetorial/readout efetiva — sem escolher vetores por fatoração do Gram alvo.

O próximo teste mínimo é a face de dois coeficientes: produzir as imagens das duas direções originais, provar os domínios e comparar os dois diagonais e o cruzamento (incluindo a forma associada a `J`, quando se reconstrói o pairing complexo). Com a escala de `E₂`, as diagonais exigidas são `4h₀` e `4h₁`; o cruzamento de paridades tem de coincidir com o zero já demonstrado na fonte. Para uma representação com complemento residual, esse residual deve sair da síntese existente com fórmula e sinal próprios, não ser postulado como campo de um certificado.

Depois desse teste, a obrigação completa é a igualdade polarizada para cada ordem e para duas famílias independentes de coeficientes. Se o residual se anular, a energia complementar fornece não negatividade; para obter positividade estrita ainda será necessária a não degenerescência da aplicação de escape, conforme `compression_energy_pos_iff`. Se o residual não se anular, seu controle de sinal terá de ser provado antes de qualquer consequência Stieltjes.

## Relação com o resultado finito K₆ / doze fontes

A afirmação anterior sobre K₆ refere-se à seção finita: `CarrySixthOdd.sixth_ordered_odd_pivot_pos`, `twelve_boundary_positive`, `canonical_twelve_physical_realization` e `twelve_complete_source_comparison` estão nas fontes de `research/sixth-odd-twelve-sources/`. A realização de doze fontes começa **depois** da positividade dos dois blocos 6×6, conforme `OddPhysicalTwelve.lean`. Ela não é uma prova independente de que o complemento do ramo C2 fornece os sinais em toda ordem. Nesta auditoria esses arquivos foram consultados; seu certificado numérico/theta não foi recalculado nem alterado.

## Validação e entrega

Novos módulos: `CriticalBranchComplementTransport.lean` e `CriticalBranchComplementAudit.lean` em geometry; `CriticalBranchNativeObstructions.lean` e `CriticalBranchNativeAudit.lean` no operador. Inventário exato e raízes em `INVENTORY.md`.

`validate.py` registra comandos, códigos de saída, logs e SHA256 em `evidence/validation.json`. `check_sources.py` verifica todos os nomes públicos novos, registros, ausência de atalhos no código de prova novo, preservação de todos os módulos matemáticos antigos e dos pins e hashes dos arquivos do usuário. As auditorias Lean percorrem os tipos e corpos transitivos e permitem apenas `propext`, `Classical.choice`, `Quot.sound`; não há hipótese axiomática nova.

Executados builds focados e de raiz com `lake build --wfail`, auditorias públicas, e os scripts requeridos do repositório. Resultados finais e contagens estão em `VALIDATION.md`, gerado dos logs. Um erro inicial de posição do import em `Analysis.lean` foi corrigido antes da validação final; o log dessa tentativa foi retido separadamente. Não é uma falha matemática.

A publicação é em branches/PRs identificados, sem merge. Commits finais e URLs são registrados no arquivo de entrega local `DELIVERY.json`.
