# Porta material–teta: TFVD, atlas, Mellin e correções Green

**Resultado: PARTIAL, com uma ponte vetorial concreta nova.** A porta Green finita já existente foi recuperada, célula por célula, pela Mellin de uma porta gaussiana original, com sua fase e seu fator Gamma. A igualdade foi transportada ao campo `greenPort` do estado TFVD completado e ao pareamento de duas entradas materiais independentes nas duas pernas.

O transporte do **registro completado inteiro** e sua identificação com o kernel canônico dos momentos permanecem abertos. Não foi demonstrada uma isometria física infinita, nem positividade Hankel em toda ordem.

Data: 23/10/2026. Provas e builds executados em `llm`.

## A — O que já estava demonstrado e foi preservado

### Base e fontes

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch nova: `agent/material-theta-tfvd-port`.
- Base: `b43fcfe133ad4560291542dd43cbaf4f213efa8e`, branch da PR #71, aberta e em draft. Esta entrega é uma continuação empilhada para revisão; nenhum arquivo da PR #71 foi editado.
- `main` consultada e preservada: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Operador consultado sem alterações: HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`; `origin/main` conferida em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Ambiente CPFormal efetivamente usado: commit `65d50f6db1208708e109982ba97e1d51d3039956`.
- NativeCarryC3Crosswalk: `150cfc7fb08da96bf8117f15869cc2b819d593c2`.
- NativeCarrySpectralWeyl: `298d83c9351e308a5213b9f5ac32e44087f98a9f`.

Não se alteraram fonte, pesos, amplitudes, fases, métricas, câmera, normalizações, dressing, pins ou dependências. Os arquivos de pesquisa preexistentes não rastreados foram preservados. Não houve merge automático.

### Declarações reutilizadas

| Fonte | Declaração e alcance |
| --- | --- |
| CPFormal, `CpNativeCarryFiniteCameraAlgebra.lean` | `nativeCarryFiniteSaturatedChart_odd_normal_form` e `nativeCarryFiniteSaturatedChart_odd_cross_identity`: prefixo menos centros e composição de câmeras ímpares com os cutoffs exatos, sem primalidade. |
| CPFormal, `CpCarryAmplitudeIdentification.lean` | `primeCarryAmplitudeRatio_eq_criticalAmplitude_one`: a razão usada no TFVD já é a amplitude Carry. O prefixo histórico `prime` não acrescenta uma hipótese de primalidade a essa identidade. |
| CPFormal, `CpCarryWeightedVerticalTfvdFinite.lean` | `carryWeightedScalarReconstruction`: reconstrução finita com Green e dois dados iniciais. |
| Operador, `CompletedNativeXiCosineTransform.lean` | `thetaTailMode`, `thetaTailModeFirst`, suas derivadas e somabilidade; `thetaTail_eq_two_mul_tsum`. São os modos originais, não polinômios definidos por momentos. |
| Mathlib, `MellinEqDirichlet.lean` | `hasSum_mellin_pi_mul_sq`: transformação Mellin dos modos gaussianos em amostras de Dirichlet, com o fator `Complex.Gammaℝ` original. |
| NativeCarryC3Crosswalk, `FinitePackaging.lean` | `packaged_nativeState_eq_dirichletValue_nativeLine`: identifica a amostra complexa com as duas quadraturas materiais nativas. |
| NativeCarryC3Crosswalk, `GenuineBracketGreenIdentity.lean` | `finiteC3GenuineBracketGreenBoundaryPair`: porta física finita existente, com duas pernas e células preservadas. Sua primeira coordenada vem do gradiente Genuine resolvido. |
| Operador, `CompletedC3BracketTfvdGreenFactorization.lean` | `canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket`: identifica o campo `greenPort` do registro TFVD original. Os campos `valueTail` e `logJetTail` permanecem distintos desse campo. |
| Operador, `CompletedNativeCameraUniversality.lean` | Universabilidade dos readouts normalizados e dos momentos entre câmeras. Não foi usada como se fornecesse uma isometria de estados. |

O contexto enviado ajudou a separar dois assuntos: as relações do atlas não são restritas à C3; o adaptador físico concreto disponível já possui um carrier C3. Generalizar as leis vetoriais do atlas e calibrar esse adaptador são passos compatíveis, não afirmações de que todas as energias brutas sejam iguais.

## B — O que foi demonstrado agora

### 1. Porta antes da integração e da leitura dos momentos

Para endereço positivo `n`, usamos literalmente

\[
\theta_n(u)=e^{u/2}e^{-\pi n^2e^{2u}}.
\]

`addressMode_succ` e `addressModeFirst_succ` identificam esses termos com os modos originais já formalizados. A porta é

\[
J_n(a;u)=\bigl(a\theta_n(u),\ a\log(n)\theta_n(u),\ a\theta_n'(u)\bigr).
\]

Os três canais são distintos: valor, gerador logarítmico material e derivada na coordenada teta. O coeficiente `a : ℂ` retém ambas as quadraturas reais.

`resolvedThetaLift_injective` preserva os coeficientes finitos por endereço. `resolvedLabeledThetaLift_injective` mantém também um rótulo independente de perna/câmera: esse rótulo não é codificado como outro endereço aritmético.

O tipo da porta é apenas um produto de canais. Não foi declarada uma nova métrica física nesse produto, nem se definiu a porta por uma Hankel ou por seus pivôs.

### 2. Dilatação aritmética e amplitude Carry

Se `b > 0`, seja a razão já existente

\[
\eta_b=\texttt{primeCarryAmplitudeRatio}\ b=b^{-1/2}.
\]

`materialThetaMode_dilation` prova

\[
\boxed{J_{bn}(a;u)=\eta_b\,
T_{\log b}J_n(a;u+\log b),}
\qquad
T_c(v,\ell,d)=(v,\ell+cv,d).
\]

A amplitude é a anterior da geometria; não foi escolhida para ajustar esta fórmula. A transformação do canal logarítmico tem um termo de mistura real. O canal derivado em `u` não recebe esse mesmo termo.

`real_shear_preserves_green` e `theta_mode_log_green_dilation` mostram que essa mistura preserva a forma Green existente e que a dilatação acrescenta o fator `η_b²`. Isso é covariância de Green; não é uma declaração de isometria das energias físicas.

Essas leis de dilatação valem para bases positivas, incluindo bases compostas. A fórmula finita da câmera ímpar, separadamente, conserva suas hipóteses `Odd b` e `1 < b`; não foi aplicada indevidamente à câmera C2 alinhada.

### 3. TFVD com retorno e duas entradas

`thetaLift_firstDifference`, `thetaLift_secondDifference`, `thetaLift_return` e `thetaLift_green` provam que o lift concreto comuta com as operações finitas já existentes. `port_tfvd` é a reconstrução coordenada dos três canais, usando `carryWeightedScalarReconstruction`.

`address_tower_step` aplica a lei à torre aritmética `b^k n`, com os índices separados. `address_tower_tfvd` prova a reconstrução dessa família concreta com a amplitude `η_b`. São identidades em qualquer profundidade finita; não afirmam extensão isométrica a um operador infinito.

Para entradas independentes, `tfvd_log_green_four_crosses` conserva

\[
G(X,Y)=G(G_X,G_Y)+G(G_X,R_Y)+G(R_X,G_Y)+G(R_X,R_Y).
\]

O retorno mantém valor e primeira diferença ponderada iniciais. Nenhum dos quatro cruzamentos é descartado.

### 4. Atlas e completamento teta com caudas reais

`odd_camera_port_normal_form` e `odd_atlas_port_cross_identity` aplicam as leis nativas ao vetor inteiro de três canais. Os ajustes de cutoff e as dilatações da câmera produto são os originais, inclusive para câmeras compostas como 9.

`completedThetaPort_components` identifica a síntese infinita:

\[
\mathbf B(u)=\left(B(u),\ 2\sum_{n\ge1}\log(n)\theta_n(u),\ B'(u)\right).
\]

A somabilidade do novo canal logarítmico foi provada a partir dos modos e da derivada já existentes. `thetaPortTail` soma os modos omitidos; não é uma variável residual fornecida independentemente. `completedThetaPort_head_tail` é uma igualdade vetorial exata.

`completed_theta_green_four_crosses` conserva HH, HT, TH e TT para cutoffs e parâmetros independentes, tanto na projeção logarítmica quanto na projeção derivada.

No lado gaussiano, o prefixo menos centros completado satisfaz, por `completed_camera_shift_formula`,

\[
\mathbf C_b^\theta(u)=\mathbf B(u)
-b\eta_b\,T_{\log b}\mathbf B(u+\log b).
\]

`completed_camera_head_tail` mantém separadamente os cutoffs do prefixo e dos centros, cada qual com sua cauda original. Isso não é uma identificação automática desse vetor com todos os campos do registro TFVD nativo.

### 5. Calibração material e dressing original

Para coeficientes complexos arbitrários,

\[
H_a(x)=\sum_{n=1}^{N}a_n e^{-\pi n^2x}.
\]

`finite_heat_mellin` prova, para `Re(s)>0`,

\[
\boxed{\mathcal M H_a(s/2)=\Gamma_{\mathbb R}(s)
\sum_{n=1}^{N}a_n n^{-s}.}
\]

`finite_heat_mellin_native` identifica as amostras do lado direito com os estados reais nativos empacotados. Não entram zeros, alturas ou momentos prescritos.

Se `D(s)=Σ a_n n^{-s}` e `L(s)=Σ a_n log(n)n^{-s}`, então `D'=-L`. `finite_heat_mellin_hasDerivAt` mantém a correção

\[
(\Gamma_{\mathbb R}D)'=\Gamma_{\mathbb R}'D-\Gamma_{\mathbb R}L.
\]

`native_height_gamma_trace` conserva ainda o fator `i` da mudança original `s=1/2+iz`. Não se confundem derivada no expoente, derivada em altura e derivada em `u`.

`native_completion_eq_gammaR` identifica precisamente o dressing original:

\[
\texttt{nativeXiCompletionFactor}(z)
=\tfrac12s(s-1)\Gamma_{\mathbb R}(s).
\]

O termo polinomial não foi retirado. A calibração de valor com esse fator é `original_completed_finite_value_mellin`.

### 6. Pareamento polarizado com correção Gamma

Para uma porta `p=(v,ℓ)`, a porta completada em expoente é

\[
\mathcal D_s p=(\Gamma_s v,\ \Gamma_s\ell-\Gamma_s'v).
\]

`gammaDress_green_defect` prova, para parâmetros e entradas independentes,

\[
\boxed{
G(\mathcal D_s p,\mathcal D_t q)
=\overline{\Gamma_s}\Gamma_t G(p,q)
+(\overline{\Gamma_s}\Gamma_t'
-\overline{\Gamma_s'}\Gamma_t)\langle v,w\rangle.}
\]

O termo valor–valor adicional está explícito. Não foi declarado zero nem positivo. Essa fórmula usa o expoente complexo; a fase `i` da altura foi demonstrada separadamente.

### 7. Ligação com a porta física já existente

`NativePortCalibration.lean` reutiliza **o próprio** `FiniteC3GreenPortCarrier M`, sem substituir seu espaço ou sua métrica. A porta gaussiana tem, por célula, a diferença dos endereços `3(n+2),3(n+1)` na primeira perna e `n+2,n+1` na segunda, com `cpPhaseNormalizer 3 s` preservado.

`native_green_port_mellin` prova

\[
\boxed{\mathcal M_s^{\rm células}\Theta_{M,s}
=\Gamma_{\mathbb R}(s)\,
\texttt{finiteC3GenuineBracketGreenBoundaryPair}(M,s).}
\]

`original_tfvd_green_projection_mellin` liga essa igualdade diretamente ao campo `greenPort` de `canonicalC3BracketTfvdCompletionState`. A integração é feita por coordenada; nenhuma soma grosseira das células define o resultado.

`weighted_native_two_input_green` acrescenta duas entradas materiais independentes, cada uma com coeficientes complexos independentes nas duas pernas. O pareamento é a **forma Green original**, aplicada aos vetores finitos completos, e o fator é exatamente `conj(Γ_s)Γ_t`. Os coeficientes são sondas de entrada; não alteram os pesos da fonte canônica nem a métrica.

A fase radial dependente de `Im(s)` foi mantida como parâmetro nesse adaptador. Ela não foi diferenciada como se fosse holomorfa. As provas de derivação Gamma anteriores operam antes dessa fase.

## C — O que foi refutado ou limitado por teste exato

`material_log_green_modes` e `theta_derivative_green_modes` dão os dois kernels modais, com o mesmo fator `conj(a)d θ_n θ_m`:

\[
\begin{aligned}
G_{\log}&:\quad \log n-\log m,\\
G_{\partial_u}&:\quad 2\pi(m^2-n^2)e^{2u}.
\end{aligned}
\]

`raw_modal_fluxes_have_opposite_sign` prova, nos endereços 1 e 2 e coeficientes unitários, que o primeiro fluxo é negativo e o segundo positivo, para todo `u`. Portanto, não podemos simplesmente substituir o canal logarítmico pelo canal derivado teta. O resultado não exclui um transporte que mantenha a mistura, Gamma, bordos e retorno.

`nonzero_mode_with_zero_self_green` mostra também um estado não nulo com fluxo Green próprio zero. Esse fluxo não pode ser chamado de norma positiva do estado.

`raw_critical_material_sum_not_summable` prova a divergência da soma positiva bruta `Σ n^(-1/2)`. A calibração Mellin finita, sozinha, não permite trocar soma e integral no limite crítico infinito. A câmera e suas compensações precisam ser sintetizadas primeiro. Isso não refuta a fonte completada, cuja convergência possui mecanismos adicionais.

Não foi demonstrado que a massa dos centros seja o resíduo `D_ij` da PR #71. Tampouco se usou a independência dos polinômios teta para fabricar estados físicos retroativamente.

## D — O que permanece aberto e como foi validado

A ponte fecha **a projeção Green finita** do registro original e o transporte TFVD finito de entradas endereçadas. Não transporta ainda o registro inteiro. Em particular, falta uma realização proveniente da mesma fonte para os campos `valueTail` e `logJetTail`, com seus cruzamentos e a normalização própria da câmera.

As caudas gaussianas desta entrega são demonstradas como séries dos modos originais. Sua igualdade vetorial com as caudas analíticas nativas não foi presumida. A igualdade já conhecida de características escalares não descarrega essa obrigação.

Também não foi provada uma isometria entre a síntese teta e a métrica física nativa completa. A identidade Mellin com fator Gamma é uma calibração de vetores/readouts, não uma identidade de normas em `L²(Φ)`.

O defeito físico em `canonicalNativePolarizedTfvdGreenLedger_identity` continua contendo proveniência Green, cruzamentos, resíduos de leitura e completamento. A projeção `greenPort` calibrada é apenas uma parte desse balanço. Os certificados finitos H6/K6 permanecem distintos dessa questão.

Os módulos novos são enumerados por `generate_audit.py`; `Audit.lean` executa `#print axioms` de todas as declarações públicas e percorre tipos e corpos transitivamente. O audit rejeita, inclusive, dependências de `canonicalCompletedNativeLogDerivativeMoment`, dos polinômios de momentos teta e dos resultados da PR #71. Assim, o lift novo não recebe a sequência desejada como entrada.

A entrega contém **64 teoremas e 35 definições/abreviações públicos** em oito módulos. As 99 raízes têm auditoria de **5.337 constantes transitivas**, permitindo somente `propext`, `Classical.choice` e `Quot.sound`.

`evidence/validation.json` registra builds explícitos dos módulos novos, builds das fontes importadas, `lake build --wfail`, auditorias Foundation/Geometry/Analysis, busca de escapes de confiança, hashes e preservação dos arquivos anteriores. Os logs são reproduzíveis. Não há novos axiomas matemáticos, `sorry`, `admit` ou `native_decide`.

Reprodução no host `llm`, com esta branch em um checkout:

```bash
cd /caminho/do/checkout/geometry-of-numbers/research/material-theta-tfvd-port
python3 validate.py
```

O script compila no ambiente original de `/home/thlinux/carry-self-adjoint-operator`, sem alterar pins. A compilação raiz não inclui automaticamente os módulos de pesquisa; eles são compilados explicitamente.

## E — Próximo passo mínimo

Usar `original_tfvd_green_projection_mellin` para transportar **os canais restantes do ledger**, sem voltar a provar apenas a igualdade escalar `F=teta`.

O primeiro alvo concreto é construir as imagens dos mesmos `valueTail` e `logJetTail` como somas dos termos de câmera omitidos, junto com seus traços, e calcular os termos cabeça–cauda e cauda–cabeça para duas sondas independentes. A comparação deve manter os fatores de câmera, o termo polinomial do dressing e a correção Gamma demonstrada aqui.

Uma estimativa operacional a testar é o erro de cauda Mellin ponderado por `x^(Re(s)/2-1)(1+|log x|)` **depois do cancelamento da câmera**. Ela permitiria transportar valor e primeiro jet ao limite. Essa estimativa, mesmo provada, não seria automaticamente uma representação Gram: ainda será necessário comparar o pareamento físico completo com o kernel canônico, mantendo o defeito original.

Somente então faz sentido confrontar a imagem do ledger com `E_ij=P_(i+j)-P_iP_j` da PR #71. Não se igualará essa imagem à massa dos centros por definição e não se escolherá uma métrica para apagar o desajuste.

**Resposta:** o destino teta agora tem uma porta construtiva endereçada, um transporte TFVD e uma calibração vetorial à projeção física finita existente. O transporte completado de todos os campos, a preservação da energia física inteira e a positividade canônica em toda ordem continuam abertos.

Fim do relatório.
