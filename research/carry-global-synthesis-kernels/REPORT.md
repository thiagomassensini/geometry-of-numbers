# Síntese geométrica: redundância de coeficientes, informação física e orçamento multibase

**Resultado: PARTIAL.** Foi identificada uma síntese positiva concreta no frame Green já existente, com seu núcleo exato e seu transporte de domínio. Foi demonstrado que esse núcleo difere da informação física perdida ao comprimir para um ramo. Também foram formalizadas obstruções à soma bruta de observações multibase e à extensão de uma extração finita do total comum. **Não foi demonstrada uma representação Gram dos momentos canônicos em todas as ordens.**

Base da branch independente `agent/carry-global-synthesis-kernels`: **`349740eaff8f154c444c918757b608e6efb210a4`**, cabeça conferida da PR #39. Sua base transitiva na `main` é `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. As PRs #38 e #39 estavam abertas e fora da `main`; nenhuma foi alterada. A dependência #38 foi consultada e recompilada pelo commit congelado `16de0ef478afb1c95c16edfe8153ac80dc035b71`, em cache isolado, sem trocar checkout ou pins. Todos os arquivos novos ficam em `research/carry-global-synthesis-kernels/`.

O operador foi consultado no commit `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem alterações; seus dois arquivos de usuário não rastreados foram preservados. Nenhum worktree foi criado ou removido. Sem merge automático.

## A — O que já estava demonstrado

**Geometria e síntese física.** `carryMaterialRealSample_eq_depthState` identifica a amplitude nativa e a fase material prescrita. `carryMaterial_camera_amplitude_factorization` conserva a contribuição horizontal na decomposição do endereço. `carryMaterialCamera_general_transport`, `carryMaterialTower_general_transport` e `carryMaterialCamera_general_pairing_transport` conservam as correções de raio e os dois cruzamentos entre câmeras. Raio, profundidade e endereço material permanecem índices distintos.

**TFVD, retorno e completamento.** `carryMaterialProjective_reconstruct` e os capstones R2 já encerram a reconstrução correspondente, sem redefinir uma norma. `carryValveReturnGreen_physical_ledger` e `carryValveReturnGreen_tail_ledger` conservam o Green escondido e os quatro termos de prefixo/cauda. O estado material efetivo é `baseTwoCompletedBoundaryHilbertState`, no carrier seed ⊕ (gradiente ⊕ retorno). Seu dressing e seu companheiro produzem o par físico `carryMaterialCompanionValuePair`, cuja leitura é `(-F′,2F)`.

**Frame Green concreto.** `c2GlobalGreenInputIsometry` e `globalCriticalPhysicalBranchIsometry` preservam o produto interno real, as duas pernas, a amplitude `2^(-k/2)`, a fase `-t log n` e o endereço aritmético. O Green bruto não é uma isometria: `canonicalRawGreenAnalysis_not_isometry` e `canonicalRawGreen_frameOperator_ne_identity` fornecem a separação exata. A normalização Parseval já construída satisfaz `canonicalGreenAnalysis_gram_identity` e `canonicalGreenAnalysis_isometry`. Os bounds utilizados são os já provados para o frame concreto, não novas hipóteses.

**Domínios.** `greenParsevalMaterialLogOperator_P_mem_domain_iff` e `greenParsevalMaterialLogOperator_intertwining` transportam o domínio original do gerador material. Esse gerador não foi identificado com Jacobi ou com o operador de alturas. O clock do carrier material completado é outro objeto tipado; não se identificam os dois domínios por analogia.

**PR #39.** Foram preservados `finite_camera_separation`, `all_cameras_finite_injective`, `camera_two_four_distance`, `carryMaterialReadoutProjection_boundary_defect` e os demais resultados. A distância entre as sondas 2 e 4 permanece exatamente 8. O defeito da projeção ambiente de readout permanece exatamente metade do readout. O verificador original da PR #39 foi executado, conferindo também os hashes dos arquivos anteriores.

**PR #38.** Foram reutilizadas as leis originais de escala, inclusive `native_log_moments_constant_amplitude`, `native_two_mass_actions_same_jacobi` e `native_geometric_mass_not_response_dilation`. Os quatro módulos da biblioteca e `NativeScaleSeam.lean` foram recompilados a partir dos objetos Git originais, em um overlay de build isolado. Não se presumiu que estejam na `main`.

**Síntese nativa entre câmeras.** A auditoria também recuperou `canonicalC3CameraResolvedCorrectedGreenKernel_fixedAtlas_sum_eq_correctedBoundary`: a fronteira corrigida é uma soma dupla sobre um atlas material finito independente dos parâmetros. Os cruzamentos entre câmeras já estão explícitos. Esse atlas de contribuições por fatorização não é a família de observações `profile b n` da PR #39, nem um teorema de positividade da soma Green. `CanonicalCompletedNativeTfvdCameraParsevalIncidenceTransport` contém uma condição métrica como campo; não foi usado como se fornecesse sua realização concreta.

**Limite conhecido.** `material_pair_corrected_green` e `material_clock_canonical_residual_ledger`, da comparação material, dão a igualdade assinada com a resposta canônica completada. O resultado `physical_forcing_schur` da PR #37 identifica o forcing negativo com a subtração central de Schur. Nenhum desses resultados fornece ainda o sinal de todas as formas finitas.

## B — O que foi demonstrado agora

### B.1 — A síntese existente e os dois núcleos diferentes

Foi reutilizado o mapa Parseval concreto, escrito `P` após simples restrição a escalares reais. A síntese `S=P*` é seu adjunto existente. Para um coeficiente Green `z`, e para o ramo físico original `U_t`, defina somente os estados derivados

\[
y=Sz,\quad v=U_t^*y,\quad
\chi=y-U_tv,\quad \eta=z-Py.
\]

Não se fornece uma matriz de momentos a essas definições. Não há nova fonte, métrica, gerador ou estado escolhido por Cholesky.

`synthesis_parseval`, `synthesis_frame_null` e `coefficient_kernel_exact` provam

\[
SP=I,\qquad S\eta=0,\qquad
Sz=0\iff\eta=z.
\]

`raw_canonical_same_coefficient_kernel` dá uma identificação importante:

\[
\boxed{\ker S=\ker A^*,}
\]

onde `A=canonicalRawGreenAnalysis` é o Green bruto original. A prova utiliza a normalização já demonstrada `B(A*A)B=I` para `B=(A*A)^(-1/2)`. Logo, a normalização canônica do frame **não transforma uma direção material independente em redundância**: o núcleo de coeficientes continua sendo o original.

Para dois argumentos independentes, `complete_polarized_split` prova

\[
\boxed{\langle z,w\rangle_{\mathbb R}
=\langle v_z,v_w\rangle_{\mathbb R}
+\langle\chi_z,\chi_w\rangle_{\mathbb R}
+\langle\eta_z,\eta_w\rangle_{\mathbb R}.}
\]

As duas pernas e ambas as quadraturas já estão nos mapas físicos; a identidade é aplicada ao vetor inteiro. Nenhum cruzamento entre fontes foi apagado. Na diagonal,

\[
\|z\|^2=\|v\|^2+\|\chi\|^2+\|\eta\|^2,
\qquad
\boxed{\|Sz\|^2=\|v\|^2+\|\chi\|^2.}
\]

O quociente correto de coeficientes elimina `η`, não `χ`. `same_physical_state_iff` identifica as classes que sintetizam o mesmo estado. `quotient_energy_minimum` prova que `PSz` minimiza a norma ambiente entre os representantes dessa classe.

`reconstructed_domain_iff` e `reconstructed_clock_intertwines` preservam o domínio do gerador material sobre esse representante. A hipótese exata do último é `Sz ∈ greenStateMaterialLogGenerator.domain`; não se aplica um operador não limitado fora de seu domínio, nem se pressupõe que todos os estados tenham todos os momentos logarítmicos.

**Alcance:** esta é uma síntese positiva verdadeira do frame concreto já construído. Não foi demonstrado que ela seja a síntese multibase completada exigida para identificar os momentos canônicos. `branch_choice_preserves_total` é invariância da energia completa sob a escolha do ramo parametrizado por `t`; não foi anunciado como invariância entre todas as câmeras.

### B.2 — Informação comum repetida pelas câmeras

Para a mesma observação da PR #39,

\[
O_b(a)=\sum_n a_n\,\operatorname{profile}_b(n),\qquad
T(a)=\sum_n a_n,
\]

com `a : ℕ →₀ ℂ` e `a(0)=0`, `large_camera_total` prova que todas as câmeras suficientemente grandes dão exatamente `T(a)`.

Disso decorre o resultado global sobre o orçamento desta família:

\[
\boxed{\sum_{j\ge0}|O_{j+2}(a)|^2\text{ é somável}\iff T(a)=0.}
\]

Nome: `camera_energy_summable_iff`. É uma equivalência para todos os dados de suporte finito, sem hipótese de positividade Hankel.

As observações centradas `O_b(a)-T(a)` têm suporte finito em câmeras (`centered_observations_finite`). Guardar `T(a)` uma única vez **junto** de todas elas continua injetivo (`total_and_centered_injective`). `camera_polarized_total_split` conserva os quatro termos ordenados: total/total, total/centrado, centrado/total e centrado/centrado.

Essa é uma separação algébrica de informação comum em dados finitos. Não foi atribuída uma nova métrica a essa codificação, nem se afirmou que sua norma seja a forma canônica.

### B.3 — O total bruto da fonte original não admite essa passagem automática ao infinito

Foi avaliada a própria fonte prescrita, sem alterar amplitudes ou fases. No tempo zero,

\[
T_N^{\rm nativo}=\sum_{n=1}^{N}\operatorname{Re}f_0(n)
=\sum_{n=1}^{N}\frac1{\sqrt n}.
\]

`native_total_square_lower` prova

\[
\boxed{T_{k^2}^{\rm nativo}\ge k\quad(k\ge1).}
\]

`native_total_unbounded` conclui que, para todo real `C`, algum prefixo tem total maior que `C`. Assim, extrair um total escalar comum funciona nos dados finitos, mas não produz automaticamente um escalar finito para esta fonte infinita.

Essa soma **não é** a característica completada. Não se declarou divergente o estado material completado, sua resposta ou sua energia. O resultado impede substituir o balanço completado, com seus retornos, por uma soma bruta que omite os mecanismos de cancelamento.

### B.4 — Compatibilidade exata com a PR #38

`synthesis_homogeneous_energy` prova, na métrica original,

\[
\|S(\beta z)\|^2=\beta^2\|Sz\|^2.
\]

O teorema original da PR #38, reutilizado por `native_log_amplitude_invariant`, prova que multiplicar todos os coeficientes da característica completada por uma constante não nula deixa os momentos logarítmicos invariantes.

Como `h₀>0` já foi certificado pela fonte theta, `no_universal_unnormalized_linear_gram` demonstra que nenhuma regra que use **esses vetores não normalizados, a mesma síntese linear e todas as amplitudes constantes** pode identificar sua energia com esses momentos. Basta confrontar as amplitudes 1 e 2. Não se modifica a amplitude nativa escolhida; refuta-se uma lei universal de identificação entre operações diferentes.

`jacobi_blindness_not_source_equality` reúne os dois resultados originais da PR #38: as ações de massa `q⁻¹` e `q` podem dar o mesmo Jacobi, embora as sequências de momentos sejam diferentes quando `q>0` e `q≠1`. A perda desse parâmetro em Jacobi não é prova de redundância física upstream.

## C — O que foi refutado

1. **Tratar todo núcleo da compressão a um ramo como redundância de frame.** `physical_seed_not_redundant` usa o vetor material original `e₁`. Para `z=P e₁`, demonstra `η=0`, `v=0`, `χ=e₁` e `‖z‖²=1`, em todo tempo de ramo. A compressão apaga uma direção física não nula que não é redundância de coeficientes. O vetor `e₁` é uma sonda física, não uma identificação postulada com o jet canônico de ordem zero.

2. **Empilhar todas as observações escalares da PR #39 em uma ℓ² sem tratar a informação comum.** Para o seed finito `a=δ₁`, `seed_camera_observation` dá `O_b(a)=1` em toda câmera admissível. `seed_camera_energy_prefix` dá energia exatamente `M` nas primeiras `M` câmeras e `seed_camera_energy_not_summable` exclui somabilidade. Esta obstrução é da agregação bruta de observações, não do frame Green concreto ou de qualquer síntese multibase possível.

3. **Promover a separação finita do total comum a uma decomposição escalar infinita da fonte nativa.** O total bruto dessa fonte é ilimitado. A conservação finita de informação não fornece o domínio ou a continuidade de uma extensão completada. Não se acrescentou uma renormalização para contornar esse fato.

4. **Confundir a homogeneidade de uma energia linear com a invariância da derivada logarítmica.** A lei universal não normalizada foi refutada. Isso não refuta uma construção na amplitude nativa fixa, nem uma normalização projetiva efetivamente derivada da fonte; tais construções ainda precisam demonstrar seus pareamentos exatos.

As obstruções da PR #39 — distância 8 entre sondas e defeito de bordo `ℓ(y)/2` — continuam intactas. **Não foi refutada a positividade dos momentos canônicos nem a existência geral da síntese procurada.**

## D — O que permanece aberto

O primeiro passo não demonstrado para o objetivo principal é a igualdade entre **o kernel positivo de uma síntese física completada apropriada** e o kernel dos momentos canônicos. O adjunto Parseval agora auditado reconstrói o estado Green de seu próprio frame; não identifica esse estado com o jet completado que produziria `h_(i+j)` ou `h_(i+j+1)`.

Os mapas de transporte entre câmeras com correções horizontais estão disponíveis. As somas Green entre câmeras com atlas fixo também estão disponíveis. Sua existência não permite substituir a forma Green assinada por uma soma diagonal de normas. A distância 8 lembra que as sondas de duas câmeras não são automaticamente o mesmo estado em duas bases; o defeito `ℓ/2` lembra que uma projeção ambiente pode não preservar o retorno físico.

Na fonte completada continuam presentes o centro, o gradiente, o retorno, o dressing, o completion e os cruzamentos. Nenhuma nova igualdade elimina os canais assinados. Em particular, não foi demonstrada a não negatividade do restante físico depois de descontar o forcing. Nenhum `IsMomentGramRepresentation` ou transporte métrico com a conclusão desejada foi fornecido como hipótese livre.

O resultado não demonstra a norma global canônica determinada exclusivamente pelas relações entre todas as câmeras, a independência de câmera dessa norma, uma família Gram canônica em todas as ordens ou positividade estrita. Os certificados H6/K6 e a realização finita de doze fontes foram preservados, sem serem usados para fabricar os novos estados.

## E — Próximo passo mínimo

O alvo concreto continua sendo a dominância no mesmo ledger físico da PR #37. Escreva `a=h₀>0`, `v(t)` para o forcing físico já construído e `𝓡(t,u)` para o coeficiente restante dos canais central/central, compressed/compressed, ambos os cruzamentos compressed/forcing e o complemento escondido. É necessário **demonstrar da fonte**, não acrescentar como hipótese,

\[
\boxed{\operatorname{Re}\sum_{i,j}\overline{c_i}\mathcal R(t_i,t_j)c_j
\ \ge\ h_0\left\|\sum_i c_i v(t_i)\right\|^2.}
\]

A igualdade de Schur anterior identifica exatamente o que essa desigualdade descontaria. Nesta rodada não foi demonstrada uma desigualdade mais fraca que a substitua. Uma prova útil deve produzir uma identidade Green/Bessel ou uma fatoração relativa para **esses mesmos canais completados**, inclusive nas direções que anulam a soma do forcing.

Os novos resultados dão três testes prévios para essa tentativa: eliminar somente o núcleo verdadeiro de coeficientes; conservar o complemento físico independente; e não usar uma extração escalar cuja somabilidade falhe na fonte original. O transporte de domínio pelo Parseval já existente pode ser usado onde seu estado de origem esteja identificado, sem trocar esse estado pelo alvo de Hankel.

**Formalização e reprodução.** São 31 teoremas públicos novos e sete definições/abreviações de estados derivados. As 38 raízes novas e três regressões da PR #39 passaram por `#print axioms` e por percurso transitivo de tipos e corpos: 6.814 declarações, permitindo somente `propext`, `Classical.choice`, `Quot.sound`. Os módulos não introduzem `sorry`, `admit`, `native_decide`, axiomas matemáticos ou definições opacas.

Os três módulos novos são `GreenSynthesis.lean`, `CameraBudget.lean` e `ScaleCompatibility.lean`; `Audit.lean` registra raízes e regressões. As provas são compiladas explicitamente com warnings como erros, além do build de raiz com `lake build --wfail` e das auditorias Foundation/Geometry/Analysis. Não há alterações em módulos históricos, na Foundation, nas métricas ou nos pins.

```bash
git fetch origin agent/carry-scale-covariance
python3 research/carry-global-synthesis-kernels/check_sources.py
python3 research/carry-global-synthesis-kernels/validate.py
python3 research/carry-global-synthesis-kernels/verify_evidence.py
```

O roteiro recompila os módulos necessários da PR #39, verifica suas evidências, prepara os cinco arquivos congelados da PR #38 em cache isolado, compila as provas novas e sua auditoria, executa o build `--wfail` e as três auditorias do repositório. Os quatorze comandos e os hashes dos logs ficam em `evidence/validation.json`. O manifesto registra os arquivos anteriores preservados, os objetos Git da PR #38 e os arquivos Lean novos. Não houve campanha numérica nem recálculo de momentos.

O `fetch` acima apenas disponibiliza o objeto da PR #38 em um clone que ainda não o possua. A compilação fixa o SHA documentado, sem depender de movimentos posteriores da branch. Os dois arquivos de usuário não rastreados registrados no manifesto são verificações de preservação específicas deste host, não dependências dos teoremas.

Para revisão sem duplicar os commits anteriores, o PR de continuação usa como base a branch da PR #39, explicitamente ainda não integrada. A branch #39 permanece em seu commit original. Nenhuma integração automática à `main` foi realizada.
