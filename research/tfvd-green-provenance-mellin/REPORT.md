# Proveniência Green: transporte Mellin de todas as células e do ledger

**Resultado: PARTIAL.** O próximo alvo da PR #74 foi fechado: `greenProvenance` foi transportado célula por célula, com igualdade do registro completo antes da soma. Isso completa a identificação dos quatro campos do ledger TFVD/Green com expressões integrais da mesma fonte, em todo cutoff finito. A realização como Gram positiva dos momentos canônicos continua aberta.

## A — O que já estava demonstrado

### Base, domínio e preservação

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch: `agent/tfvd-green-provenance-mellin`.
- Base: `6b0926527be8e2c27bd3aac8297070292a880e89`, branch `agent/tfvd-four-leg-mellin`, PR #74.
- A PR #74 foi conferida aberta, draft e sem merge. Esta entrega é empilhada sobre ela; não pressupõe integração à `main`.
- `origin/main` conferido: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Fontes do operador: `/home/thlinux/carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Execução e compilação no host `llm`, em worktree isolada. Somente arquivos novos deste diretório de pesquisa pertencem à mudança.

Foram preservados fontes, endereços, amplitude, fase, métrica, câmeras, retornos, Gamma, dressing, completion, pins e arquivos históricos. O diretório preexistente `research/entrywise-moment-square/` do checkout principal e os dois módulos C2 não rastreados do operador não foram alterados.

### Resultados reutilizados

Da PR #72, namespace `CarryMaterialTheta`:

- `nativeHeatGreenPort`: porta gaussiana literal, com os endereços materiais e o normalizador radial originais.
- `cellwiseMellinPort`: integral coordenada por coordenada nas duas pernas do carrier finito existente.
- `native_green_port_mellin`: imagem integral igual a `Gammaℝ(s)` vezes a porta Genuine/Green original.

Da PR #73, namespace `CarryCameraTail`:

- `gammaUndress`: remoção do fator Gamma, incluindo sua derivada no jet.
- `mellin_completion_eq_original_ledger`: identificação exata da correção independente de cabeça/cauda.
- `nativeCompletionTrace`, `native_completed_trace_from_mellin`, `completed_native_green_four_crosses`: completion original e seus cruzamentos, sem afirmar isometria.

Da PR #74, namespace `CarryFourLeg`:

- `mixed_value_decode`, `mixed_log_decode`: decodificação aritmética efetiva dos três resíduos.
- `heat_mixed_legs_calibration`, `original_four_legs_mellin`: igualdade das quatro pernas, antes do pareamento.
- `heat_crosses_eq_original_ledger`, `heat_readout_eq_original_ledger`: identificação dos cruzamentos ordenados e da correção de readout.

Das fontes originais:

- `NativeCarryC3Crosswalk.finiteC3EnrichedTfvdValueGreenPort_canonical`.
- `NativeCarryC3Crosswalk.finiteC3EnrichedTfvdBlockGreenProvenance`.
- `NativeCarryC3Crosswalk.tfvdPairGreenLegChannels`.
- `NativeCarryC3Crosswalk.greenForm_eq_sum_finiteC3GreenPortEdge`.
- `CPFormal.Analytic.Cp.phaseNormalizedCpBlockGradient_eq_radial_mul`.
- `CarrySelfAdjointOperator.canonicalNativePolarizedTfvdGreenLedger_identity`.
- `CarrySelfAdjointOperator.canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto`.
- `CarrySelfAdjointOperator.canonicalC3MixedTailCompletionDefect_tendsto_zero`.

A PR #41 continua sendo um consumidor lógico posterior: a ortogonalização algébrica e a costura Schur usam inversibilidade do bloco antigo; não fornecem automaticamente um sinal. Nenhum momento ou fator de Cholesky da Hankel-alvo define as fontes desta entrega.

## B — O que foi demonstrado agora

Os novos nomes pertencem ao namespace `CarryGreenProvenance`, em cinco módulos. O manifesto completo está em `public-roots.json`; as provas e seus fechos transitivos são auditados em `Audit.lean`.

### 1. As duas portas originais, incluindo a refletida

Definimos a imagem integral material, em cada coordenada do carrier existente:

\[
P_N(s)=\Gamma_{\mathbb R}(s)^{-1}
  \mathcal M_{s/2}[\operatorname{nativeHeatGreenPort}_N(s)].
\]

`material_green_port_eq` demonstra que `P_N(s)` é exatamente `finiteC3GenuineBracketGreenBoundaryPair N s`, quando `Re(s)>0`. A inversa Gamma remove o fator analítico previamente demonstrado e não nulo nesse domínio. Não é um ajuste de norma nem uma normalização escolhida para acertar momentos.

`mixed_direct_green_port` confirma que a porta direta do par misto depende do valor em `w`, enquanto o jet continua em `z`. `direct_port_mellin` e `reflected_port_mellin` calibram os dois campos efetivos da fonte original.

A reflexão é a original:

\[
z^\#=1-\overline z.
\]

Logo a calibração conjunta usa

\[
0<\Re z<1,\qquad \Re w>0.
\]

O limite superior em `z` é necessário para a integral da porta refletida. Ele não é uma nova hipótese de positividade, nem uma restrição da identidade algébrica original, que vale em domínio maior.

As fases radiais permanecem dentro das duas portas. Não se toma derivada holomorfa do normalizador dependente da parte imaginária. Os jets de `heatMixedLegs` continuam com a correção Gamma já demonstrada na #74.

### 2. Os oito transportes e a compensação dormente

Em cada bloco `m : Fin M`, há duas células de bordo, rotuladas por `r : Fin 2`, e três resíduos Green, rotulados por `Fin 3`. O endereço do resíduo permanece `finProdFinEquiv (m,r)`; nenhuma soma substitui esses rótulos.

Para uma célula, sejam `l,r,jl,jr` suas quatro pernas originais e `d,e` as portas direta e refletida. `heatCellProvenance` aplica o construtor original, conservando os quatro campos:

\[
\begin{aligned}
T_R&=(r-\overline{d_h})\,jl,\\
T_{JL}&=\overline{d_h}(jl-e_r),\\
T_L&=-(l-\overline{d_r})\,jr,\\
T_{JR}&=-\overline{d_r}(jr-e_h).
\end{aligned}
\]

`heatBlockProvenance` mantém as duas células e o terceiro resíduo como

\[
-G_{\mathrm{edge}}(d,e;m,2).
\]

O objeto não é definido como diferença entre totais globais. Cada campo é construído das pernas e portas integrais antes do pareamento total.

O teorema central é:

```lean
block_provenance_mellin (M : ℕ) (m : Fin M)
  (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
  heatBlockProvenance M z w m = originalBlockProvenance M z w m
```

É uma igualdade do registro `TfvdSameSGreenProvenanceChannels`, contendo dois registros de quatro campos e a compensação dormente. Não é apenas igualdade de `.total`. `originalBlockProvenance` é uma especialização literal de `finiteC3EnrichedTfvdBlockGreenProvenance` ao par misto original.

As projeções `visible_legs_mellin`, `dormant_legs_mellin` e `dormant_compensation_mellin` registram as identificações separadas. Só depois é formada a soma sobre `m`, em `heatGreenProvenance`.

`heat_green_eq_original_ledger` fecha o alvo indicado pela PR #74:

\[
\operatorname{heatGreenProvenance}_M(z,w)
=\operatorname{ledger}_M(z,w).\mathrm{greenProvenance}.
\]

As hipóteses são apenas as condições analíticas de domínio expostas acima. `M` é arbitrário, incluindo zero; uma célula individual exige naturalmente um elemento de `Fin M`.

### 3. O ledger com seus quatro campos

`heatLedger` reúne quatro expressões construídas independentemente:

1. `heatGreenProvenance`;
2. os cruzamentos ordenados das quatro pernas integrais;
3. `heatReadoutCorrection`;
4. `mellinCompletionDefect`.

`full_ledger_mellin` demonstra igualdade do registro inteiro com `canonicalNativePolarizedTfvdGreenLedger`. `native_wronskian_full_mellin` transporta a identidade original completa:

\[
W(z,w)=G(P_{3M}(w),P_{3M}(z^\#))
+L_G+L_\times+L_R+L_C.
\]

O Wronskiano continua o original `canonicalCompletedC3RawMixedWronskian`. Os cruzamentos, os quatro residuais lineares de readout e os seis termos de completion permanecem nas expressões originais das PRs #73–74.

Essa igualdade vale para todo corte finito e dois parâmetros independentes. Ela transporta uma identidade assinada; não prova preservação da norma física do estado completo.

### 4. O que a fase radial faz ao Green

`material_port_coordinates` recupera, coordenada por coordenada, a forma original

\[
P_N(s)_n=(\rho(s)g_n(s),g_n(s)),\qquad
\rho(s)=3^{-\operatorname{criticalDisplacement}(\Re s)}
=3^{1/2-\Re s}.
\]

`green_edge_radial` conserva os dois parâmetros:

\[
G_{\mathrm{edge}}(P_N(s),P_N(t);n)
=(\rho(t)-\rho(s))\,\overline{g_n(s)}g_n(t).
\]

`dormant_compensation_radial` dá a fórmula orientada do terceiro resíduo, com coeficiente

\[
-\bigl(3^{\operatorname{criticalDisplacement}(\Re z)}
-3^{-\operatorname{criticalDisplacement}(\Re w)}\bigr).
\]

O sinal não foi imposto. A fórmula evidencia por que não se pode apagar a fase radial ou substituir essa contribuição por uma norma.

Se `Re z = Re w = 1/2`, então `rho=1`. Os teoremas `critical_port_legs_equal`, `critical_green_edge_zero` e `critical_green_form_zero` demonstram que as pernas coincidem e o Green entre essas portas se anula, inclusive para parâmetros imaginários independentes.

`critical_dormant_compensation_zero` demonstra o cancelamento do terceiro resíduo **nesse domínio**, após a fórmula completa ter sido preservada. Não se descarta a compensação fora dele.

`critical_wronskian_in_ledger` conclui:

\[
W(z,w)=L_G+L_\times+L_R+L_C
\quad\text{na linha crítica em ambos os argumentos}.
\]

Não se conclui que as portas sejam vetores nulos. A forma Green usada aqui é sesquilinear anti-Hermitiana, não um produto interno positivo. Também não se conclui que cada correção individual seja nula.

### 5. A cauda e o limite continuam explícitos

Após a calibração de todos os registros, `heatLedgerTotal` aplica a leitura escalar total. `heat_ledger_total_eq_native_defect` a identifica com o defeito nativo original.

`heat_ledger_total_tendsto` transporta o limite já demonstrado na fonte:

\[
\operatorname{heatLedgerTotal}_M(z,w)\longrightarrow
W(z,w)-K_{\mathrm{Green,radial}}(z,w).
\]

O kernel à direita é exatamente `canonicalCompletedC3MixedRadialGreenKernel`, com os mesmos parâmetros e hipóteses de domínio. Não se declara que esse limite é zero.

`heat_completion_tendsto_zero` transporta o desaparecimento da correção de cauda. Isso não elimina automaticamente os outros três campos. Na linha crítica, `critical_ledger_total_cutoff_independent` demonstra que o **total** já coincide com o Wronskiano em todo cutoff, embora suas parcelas possam depender de `M`.

Não há troca não justificada de uma soma material infinita bruta por uma integral. As calibrações de portas são finitas; a completion e o limite usam as caudas e os teoremas de convergência originais.

## C — O que foi refutado ou delimitado

Não foi demonstrada uma impossibilidade global da geometria, nem um novo contraexemplo à positividade canônica.

A prova radial delimita precisamente o uso desta porta: seu Green finito se anula no produto das linhas críticas. Assim, a identidade transportada mantém o Wronskiano nos campos de correção; a simples calibração Mellin da porta Green não fornece uma Gram positiva para esse Wronskiano.

Não foi provado aqui que o Wronskiano seja não nulo em todo par, nem que alguma correção tenha sinal universal. A conclusão formal é a identidade completa, com os cancelamentos exatamente indicados.

Já existe nas fontes o controle `c3RawToCenteredMixedCoefficientDefect_quarter_limit_ne_zero`, em `CompletedC3MixedGreenWronskianDefect.lean`. Ele impede tratar indiscriminadamente o coeficiente radial bruto como o coeficiente centrado completado. Esse é um resultado **preexistente**, não uma nova prova desta entrega; não foi usado como hipótese de positividade.

As seguintes inferências continuam sem autorização matemática:

- igualdade de imagens integrais implica isometria do estado físico completo;
- desaparecimento da cauda implica desaparecimento da proveniência finita;
- Green nulo implica estado nulo;
- a soma de termos assinados é positiva porque as portas vivem em um Hilbert;
- uma igualdade de Wronskianos brutos identifica automaticamente os jets de uma Gram com `h_(i+j+s)`.

## D — O que permanece aberto e certificação

### A lacuna matemática

O ledger bruto completo agora está identificado. Falta demonstrar uma identidade positiva para a **síntese completada e normalizada que produz os momentos**, mantendo o mesmo objeto e os mesmos coeficientes.

Em particular, esta entrega não fornece:

- uma isometria física global entre estados nativos e estados integrais;
- uma costura C2–C3 global coerente em todos os blocos e caudas;
- uma realização `h_(i+j+s) = inner(V_i,V_j)` para a sequência canônica original;
- sinais all-order dos pivôs ou contração do retorno em toda direção crítica.

O termo residual aberto não foi renomeado como hipótese resolvida. A implicação Gram → Hankel positiva já existe; o conteúdo faltante continua sendo a identificação física efetiva do kernel completado, com seus termos assinados.

### Validação reprodutível

```bash
cd research/tfvd-green-provenance-mellin
python3 validate.py
```

O script compila explicitamente os módulos de pesquisa anteriores e novos; esses módulos não são automaticamente cobertos pelo build raiz. Executa também os builds focados do operador e da geometria, `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e as verificações de preservação.

`Audit.lean` executa `#print axioms` para todas as novas raízes públicas e percorre tipos e corpos transitivos. A lista permitida é `propext`, `Classical.choice`, `Quot.sound`. Há bloqueio explícito dos construtores de momentos canônicos, polinômios de momentos theta, certificados finitos de sinal posteriores e dependências `CarryThetaPolarized.*`.

O resultado final das verificações, contagens, comandos, tempos e hashes está em `evidence/validation.json` e nos logs correspondentes. `evidence/source-provenance.json` registra os commits e os arquivos originais consultados. Não se reivindica sucesso de CI externo com base nesses logs locais.

Resultado executado: **35 comandos, todos com código de saída zero**. Há **29 teoremas e 7 definições novas**, totalizando **36 raízes públicas**. A auditoria percorreu **5.307 constantes transitivas de tipos e corpos** e encontrou somente os três axiomas fundacionais permitidos. As varreduras de escapes de confiança e as verificações de preservação passaram. Foundation e Geometry continuam sujeitas às próprias políticas de axiomas de seus scripts.

## E — Próximo passo mínimo

O próximo alvo deve ser o **pareamento completado em dois argumentos**, usando `nativeCompletionTrace`, a igualdade vetorial `native_completed_trace_from_mellin` e o ledger integral agora completo. A aplicação da completion original inclui o quociente da câmera, sua derivada, o fator `I` da coordenada de altura, o dressing e seu companion. Sua ação no pareamento precisa ser calculada com todos os termos mistos, sem tratá-la como isometria.

A obrigação concreta é obter uma fórmula independente do cutoff para esse pareamento completado, exibindo separadamente a parcela transportada do ledger e o termo adicional produzido pela completion. Confrontar o resultado com o kernel nativo que gera os momentos, em **dois argumentos independentes**, antes de fixar um deles no centro ou extrair coeficientes.

O teste inicial deve usar o primeiro coeficiente diagonal e um cruzamento. Se a igualdade falhar, registrar o defeito exato; não substituí-lo por zero nem ajustar o kernel. Se houver correspondência efetiva, procurar uma fatoração ou uma desigualdade independente para a **soma completa**, incluindo o termo adicional. A simples fórmula do quociente logarítmico não oferece essa desigualdade.

Os teoremas preexistentes de `CompletedNativeTfvdWronskianMoments.lean` identificam o readout centrado com a resposta normalizada e seus momentos em toda ordem. Eles devem ser usados como consumidores da síntese completada, não como definição retroativa de vetores. A PR #41 deve entrar somente depois da identidade de pareamento, para interpretar o residual de ortogonalização, mantendo inversibilidade separada de sinal.

**Conclusão:** o alvo local `greenProvenance` está fechado e o ledger inteiro foi transportado com sua proveniência. A passagem desse balanço assinado à Gram positiva canônica permanece PARTIAL. Nenhum merge automático foi realizado.

Fim do relatório.
