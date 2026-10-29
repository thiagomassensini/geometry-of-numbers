# Transporte Mellin das caudas originais da câmera C3

**Classificação: PARTIAL.** Foram transportados os dois campos originais `valueTail` e `logJetTail`, com convergência integral, correção Gamma e cruzamentos. A igualdade com uma Gram de Hilbert da Hankel canônica continua aberta.

Esta entrega continua a PR #72. Não altera a fonte, amplitudes, fases, métrica, câmeras, completion, pins ou arquivos históricos. Não usa momentos, zeros, alturas ou certificados Hankel como entrada da construção.

## A — O que já estava demonstrado

### Base e proveniência

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch: `agent/native-camera-tail-mellin`.
- Base efetiva: `a0b025507f709b00fbfe294dfdfcd6d0f1da4230`, branch da PR #72, `agent/material-theta-tfvd-port`.
- `origin/main`: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35` na verificação desta entrega. As PRs #71 e #72 ainda estavam abertas. Esta continuação é empilhada sobre a #72; não pressupõe merge dessas branches em `main`.
- Ambiente Lean original: `/home/thlinux/carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Execução no host `llm`. Não foram modificados o checkout principal, as worktrees anteriores nem os dois módulos C2 não rastreados do operador.

Os SHAs dos pacotes e das fontes originais estão em `evidence/source-provenance.json`. Os snapshots atuais das PRs #41 e #72 estão em `evidence/pr-41.json` e `evidence/pr-72.json`.

### Definições originais recuperadas

Em `CPFormal/Analytic/CpGenuineFirstCutoffTail.lean`:

\[
\operatorname{realCpBracketCutoffTail}(3,M;s)
=\sum_{k\geq0}\operatorname{realCpSaturatedBracket}(3,k+M;s).
\]

Em `CompletedEnrichedTfvdBoundaryCompanion.lean`:

\[
\operatorname{canonicalC3LogJetCutoffTail}(M;s)
=\sum_{k\geq0}\operatorname{canonicalLogBracketBlock}(k+M;s).
\]

`hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail` já demonstra que a segunda série é a derivada negativa da primeira no domínio nativo. Não se trata de uma cauda nova fornecida externamente.

`CanonicalC3BracketTfvdCompletionState` mantém os campos `transport`, `valueTail` e `logJetTail` separados. `canonicalC3BracketTfvdCompletionState_transport_components` identifica os readouts finitos e o Green port do mesmo registro. A #72 demonstrou `original_tfvd_green_projection_mellin`, mas deixou os dois campos de cauda sem imagem integral calibrada.

O ledger original, em `CompletedNativePolarizedTfvdGreenMomentKernel.lean`, mantém:

\[
W=G_{\rm finito}+\Delta_{\rm green}+\Delta_{\rm cruzamentos}
+\Delta_{\rm readout}+\Delta_{\rm completion}.
\]

O teorema `canonicalNativePolarizedTfvdGreenLedger_identity` é uma identidade assinada. Não demonstra que o defeito seja zero ou positivo.

### Como a PR #41 ajuda

A #41 foi conferida no commit `ee56930a2c30456cfbd214a29bb31b12d3977204`. Em `research/native-moment-orthogonalization-audit/SchurLogic.lean`:

- `sourceMomentSchur_sewing_of_isUnit` exige apenas a inversibilidade do bloco anterior.
- `sourceMomentSchur_critical_direction_of_isUnit` identifica a direção crítica com o mesmo complemento de Schur, sem inserir seu sinal.
- `native_inverseSchur_boundary_energy` identifica a energia assinada do bordo original com quatro vezes o pivô, nos coeficientes originais.

Portanto, **transportar o residual e demonstrar seu sinal são obrigações distintas**. Esta continuação segue essa separação. Não importa a branch da #41 nem sua funcional de momentos para definir os estados gaussianos; a auditoria desta entrega proíbe dependência da definição dos momentos canônicos. A #41 orienta a interpretação e o consumidor posterior, preservado para quando a identidade física completa estiver disponível.

## B — O que foi demonstrado agora

Todos os nomes abaixo estão no namespace `CarryCameraTail`. Os módulos são novos, em `research/native-camera-tail-mellin/`.

### 1. Mesmos endereços e coeficientes, antes da integral

`CameraHeatTail.lean` define o modo original

\[
E_n(x)=e^{-\pi n^2x}
\]

e a célula literal da câmera:

\[
C_m(x)=E_{3m+2}(x)-2E_{3m+3}(x)+E_{3m+4}(x).
\]

`cameraHeatTail M x` é a soma dos mesmos blocos com `m=k+M`. `cameraHeatHead M x` conserva a semente `E_1` e os blocos anteriores a `M`. Os coeficientes `1,-2,1` e todos os três endereços são mantidos antes de Mellin ou pareamento. Não se introduz um espaço com métrica ajustada ao resultado.

Para `x>0`, `camera_block_norm_le` demonstra:

\[
|C_m(x)|\leq E_{3m+2}(x)-E_{3(m+1)+2}(x).
\]

A prova usa a monotonicidade dos modos em seu endereço, depois de reunir a célula completa. A estimativa telescopa entre células. `camera_prefix_norm_le` e `camera_tail_norm_le` dão:

\[
\left|\sum_{k<L}C_{k+M}(x)\right|\leq E_{3M+2}(x),
\qquad |\mathcal T_M(x)|\leq E_{3M+2}(x),
\]

onde `𝒯_M = cameraHeatTail M`. `summable_camera_blocks` prova a somabilidade; `camera_heat_head_tail` prova a recomposição exata da fonte gaussiana, inclusive a semente, antes do pareamento.

### 2. Integral Mellin da cauda verdadeira

Escreva

\[
\mathcal M_s[f]=\int_0^\infty x^{s/2-1}f(x)\,dx,
\qquad \Gamma_s=\Gamma_{\mathbb R}(s).
\]

Para **todo `s` com `0 < s.re`**, `camera_tail_mellin_convergent` prova a integrabilidade, e `camera_tail_mellin` prova:

\[
\boxed{\mathcal M_s[\mathcal T_M]
=\Gamma_s\,\operatorname{realCpBracketCutoffTail}(3,M;s).}
\]

`camera_prefix_mellin_tendsto` demonstra a passagem ao limite das próprias integrais por convergência dominada. Não se trata apenas da convergência dos valores fechados de uma fórmula finita. A linha crítica `s=1/2+it` está inteiramente nesse domínio.

### 3. O jet logarítmico e sua correção Gamma

`bounded_heat_mellin_hasDerivAt` controla uma fonte mensurável limitada por um múltiplo de um modo gaussiano. Demonstra a convergência da integral com `log x` e sua identificação com a derivada de Mellin.

Aplicando isso à mesma cauda, `camera_tail_log_mellin` prova:

\[
\boxed{
\Gamma_s\,\operatorname{canonicalC3LogJetCutoffTail}(M;s)
=\Gamma'_s\,\operatorname{realCpBracketCutoffTail}(3,M;s)
-\frac12\mathcal M_s[\log x\,\mathcal T_M].}
\]

O fator `1/2` vem do expoente `s/2`. O termo `Γ'_s` não foi omitido. Essa identidade não confunde o jet material com a derivada na coordenada teta, nem diferencia holomorficamente a fase radial do Green port finito.

O par complexo é construído pelas integrais da fonte:

\[
\mathcal J_s[f]=\left(\mathcal M_s[f],-\frac12\mathcal M_s[\log x\,f]\right).
\]

`original_stored_tail_trace` identifica esse par com `gammaDress s` aplicado aos dois campos originais. A transformação é a já demonstrada na #72:

\[
\mathcal D_s(v,\ell)=(\Gamma_sv,\Gamma_s\ell-\Gamma'_sv).
\]

`gammaUndress_gammaDress` e `gammaDress_gammaUndress` verificam sua inversa para `Re(s)>0`, usando a não anulação original de Gamma. Isso é reversibilidade desses dois canais de traço, não uma isometria de todos os estados materiais.

### 4. Erro integral de valor e primeiro jet

`TailControl.lean` demonstra `weighted_camera_tail_error_tendsto_zero`:

\[
\boxed{
\int_0^\infty x^{\operatorname{Re}(s)/2-1}
(1+|\log x|)|\mathcal T_M(x)|\,dx\longrightarrow0.}
\]

O majorante comum vem de `E_2` e de sua versão ponderada por `|log x|`. A prova preserva o cancelamento da câmera antes da integração. É precisamente o controle operacional de cauda sugerido no final do relatório da #72. Não usa qualquer pivô positivo.

### 5. Cabeça, cauda e todos os cruzamentos

`camera_head_trace_calibration` transporta a cabeça original com sua semente. `original_record_projections_mellin` identifica simultaneamente:

1. O Green port finito já calibrado na #72.
2. Os dois readouts da cabeça do registro original.
3. Os dois campos originais de cauda.

`completed_heat_trace_calibration` reúne cabeça e cauda somente depois dessas identificações. `completed_heat_green_four_crosses` conserva os quatro termos ordenados `HH`, `HT`, `TH` e `TT`, com parâmetros e cortes independentes.

`completed_heat_green_gamma_defect` mantém também o defeito exato:

\[
G(\mathcal D_sp,\mathcal D_tq)
=\overline{\Gamma_s}\Gamma_t G(p,q)
+(\overline{\Gamma_s}\Gamma'_t-\overline{\Gamma'_s}\Gamma_t)
\langle p_1,q_1\rangle.
\]

O termo valor–valor não recebeu sinal nem foi suprimido.

### 6. Campo completion e dressing originais

`mellin_completion_eq_original_ledger` identifica os seis termos da correção cabeça–cauda com o campo `completion` do ledger existente. Os dois argumentos complexos permanecem independentes, com a conjugação original.

`native_ledger_with_mellin_completion` substitui apenas esse campo por sua expressão integral comprovada. Os outros três campos permanecem literalmente na identidade.

`native_completed_trace_from_mellin` recupera o par original `canonicalC3BracketTfvdCompletedTracePair`, com:

- O mesmo `cpChartFactor 3 s` e sua derivada.
- A mesma substituição `s = operatorHeightParameter z` e o fator `I` do jet de altura.
- O mesmo `nativeXiCompletionFactor` e seu companion de produto.

`original_completed_trace_head_tail` recompõe esse par. `completed_native_green_four_crosses` conserva os cruzamentos depois do dressing e do quociente, inclusive para coeficientes complexos independentes aplicados às cabeças e caudas. Não são coeficientes arbitrários por modo infinito; essa extensão não é reivindicada.

## C — O que foi refutado ou evitado

Não foi demonstrado um novo NO-GO nesta entrega. As obstruções anteriores não foram reempacotadas como novidade.

O transporte não autoriza:

- Substituir o jet material por uma derivada teta sem o termo Gamma.
- Somar separadamente a série material bruta `Σ n^(-1/2)` para passar ao limite; a célula compensada é reunida primeiro.
- Chamar o Green assinado de norma positiva.
- Declarar que a reversibilidade do par de traços recupera todo o estado material, suas pernas e os canais invisíveis ao readout.
- Usar a identificação do residual da #41 como prova do sinal desse residual.

A norma utilizada na estimativa integral é o módulo complexo dos blocos analíticos, não uma nova métrica física para os momentos.

## D — O que continua aberto e como foi validado

### Alcance exato

A lacuna dos **dois campos armazenados de cauda**, no semiplano `Re(s)>0`, foi fechada por integrais da mesma fonte. O domínio original de alguns resultados nativos é maior, `Re(s)>-1`; esta entrega não estende o transporte integral a todo esse domínio.

O registro enriquecido contém mais informação do que suas projeções Green e de traço. Não foi demonstrada uma isometria entre esse registro completo e uma realização teta. Também não foram transportadas individualmente todas as pernas das três correções estruturais do ledger.

Em particular, não foi demonstrado que:

\[
h_{i+j}=\langle V_i,V_j\rangle,
\qquad h_{i+j+1}=\langle W_i,W_j\rangle
\]

para estados físicos independentes dos momentos. A Hankel canônica all-order permanece aberta. As certificações H6/K6 e a interpretação inversa-Schur da #41 continuam válidas no seu alcance anterior; nenhuma é entrada destas provas novas.

### Validação reproduzível

São **51 teoremas e 16 definições públicas**, em seis módulos. `Audit.lean` imprime os axiomas das **67 raízes públicas** e percorre **5.225 constantes transitivas**, nos tipos e nos corpos. Apenas `propext`, `Classical.choice` e `Quot.sound` são permitidos na Analysis.

O guard rejeita a definição dos momentos canônicos, os polinômios de momentos teta, consumidores de sinais canônicos e o namespace de pesquisa `CarryThetaPolarized`. Nenhuma família foi construída a partir da Hankel desejada.

`evidence/validation.json` registra **23 comandos, todos com código de saída zero**: recompilação das dependências de pesquisa da #72, builds das fontes originais com `lake build --wfail`, compilação explícita dos módulos novos com warnings como erros, auditoria de axiomas, build raiz, auditorias Foundation/Geometry/Analysis e verificações de preservação. Não há `sorry`, `admit`, `native_decide` ou novos axiomas matemáticos.

Reprodução no host `llm`, em checkout desta branch:

```bash
cd /caminho/do/checkout/geometry-of-numbers/research/native-camera-tail-mellin
python3 validate.py
```

O script usa o ambiente original do operador e não modifica seus pins. O build raiz sozinho não inclui módulos de pesquisa; a compilação explícita desses módulos está registrada separadamente. Os logs brutos e hashes permitem conferir cada alegação. As evidências locais não são apresentadas como resultado do CI externo.

## E — Próximo passo mínimo

O próximo canal a transportar é `readoutResidual`, sem reduzi-lo antecipadamente à soma escalar. Seu módulo original já separa quatro fatores:

- `mixedBoundaryLeftResidual`.
- `mixedBoundaryRightResidual`.
- `mixedBoundaryJetLeftResidual`.
- `mixedBoundaryJetRightResidual`.

O alvo concreto é construir suas imagens **a partir das quatro pernas originais de `ReflectedBoundarySynthesisData`** e provar a comutação com o transporte Mellin/Gamma. Começar em `M=1`, com dois parâmetros independentes e os endereços materiais preservados, fornece um teste exato antes de generalizar o corte. Depois recompor `mixedBoundaryResidualCorrection` e conferir a identidade com o campo `readoutResidual` do mesmo ledger.

Isso deve conservar a fase radial como coeficiente de sua própria porta, o jet analítico correto e as correções já transportadas. Definir a imagem do residual apenas como diferença entre valores desejados não descarrega a proveniência das quatro pernas.

Somente depois da identificação dos canais estruturais completos cabe investigar o sinal de seu kernel e aplicar o consumidor residual da #41. Nenhuma etapa atual permite apagar `greenProvenance`, `crossProvenance` ou `readoutResidual` para obter uma Gram positiva.

**Conclusão:** o transporte solicitado avançou da porta Green finita para as duas caudas integrais originais, com controle do primeiro jet, completion, dressing e todos os cruzamentos de cabeça e cauda. O sinal e a preservação da energia física completa continuam sendo obrigações distintas.

Fim do relatório.
