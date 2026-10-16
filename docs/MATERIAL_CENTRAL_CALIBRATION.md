# Carry — calibração central da fonte material e do Green canônico

Data: 2026-10-16. Repositório de implementação: `thiagomassensini/geometry-of-numbers`.

**Resultado:** a resposta escalar completada da fonte material é exatamente a característica canônica em todo parâmetro real. Entretanto, o estado literal `Z(t)=D(t)Y_t`, no Hilbert original e com a normalização canônica, não realiza seu kernel Green: já na origem o defeito é estritamente maior que `3/16`. Trata-se de uma obstrução dessa candidata, sem conclusão de impossibilidade para outras aplicações geométricas derivadas da fonte.

## 1. Proveniência e interfaces efetivas

Bases conferidas:

| Repositório | Commit consultado | Função nesta investigação |
| --- | --- | --- |
| geometry-of-numbers | `9e5f9ce93ce2f421b0b65bd7a3ffc5351e213f02` | PRs 1–3: incidências, mesma fonte, transporte material e reconstrução TFVD |
| carry-self-adjoint-operator | `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` | PRs 105/106 e contratos canônicos atuais |
| momentos | `a54f267365d5d8c965376734b17b10ae89ed3f74` | Auditoria histórica de coeficientes, somente leitura |

Os hashes dos arquivos, commits de última alteração, merges dos PRs e nomes completos das 29 novas declarações estão em [provenance.json](../research/material-central-calibration/provenance.json).

Nos nomes abaixo, `A = GeometryOfNumbers.Analysis`, `B = A.BaseTwoCompletion` e `C = CarrySelfAdjointOperator`; as abreviações são apenas deste relatório.

| Objeto / declaração original | Tipo, origem e normalização |
| --- | --- |
| `B.criticalMaterialSample` / `BaseTwoExactHeadTailCompletion.lean` | `ℝ → ℕ → ℂ`; para `n>0`, `f_t(n)=n^(-1/2) exp(-it log n)` |
| `B.criticalMaterialGradient` / `BaseTwoCompletedGradientSignalLift.lean` | `g_t(j)=f_t(j+2)-f_t(j+1)`; índice material, sem identificação com profundidade |
| `B.baseTwoCompletedMaterialGradientL2` | O gradiente efetivo pertence a `MaterialEdgeL2`; a sequência bruta `f_t` não foi colocada em ℓ² |
| `B.baseTwoCompletedBoundaryValue` / `BaseTwoCompletedBoundaryLimit.lean` | `β_t=∑'_k(g_t(rightEdge k)-g_t(leftEdge k))`, convergência de retornos de células completas; não é dado livre nem traço vertical TFVD |
| `B.BaseTwoCompletedBoundaryHilbertCarrier` / `BaseTwoCompletedBoundaryHilbert.lean` | `WithLp 2 (ℂ × WithLp 2 (MaterialEdgeL2 × ℂ))`; norma L² original |
| `B.baseTwoCompletedBoundaryHilbertState` | `Y_t=(f_t(1),g_t,β_t)`, fonte já construída |
| `B.baseTwoCompletedBoundaryHilbertReadout` | Mapa linear contínuo complexo `ℓ(a,g,β)=a+β`; ignora o interior, embora este permaneça no estado e na norma |
| `B.baseTwoCriticalCompleteSignal` | `S_t=f_t(1)+∑'_k cell_t(k)=ℓ(Y_t)`; células históricas de centro `4(k+1)` e passo 1 |
| `B.baseTwoCanonicalDressingScalar` / `BaseTwoCompletedVectorLiftGate.lean` | `D_t=A_t/C_t`, completion arquimediana dividida pelo fator C2; não nulo para todo `t:ℝ` |
| `B.baseTwoVectorDressing` | Para qualquer carrier normado complexo, mapa linear contínuo `y ↦ D_t • y`; não é assumido isométrico |
| `B.baseTwoCanonicalResponse` / `BaseTwoCanonicalDressingMoments.lean` | `A_t*(S_t*C_t⁻¹)=D_t*S_t`, resposta completada integral |
| `A.carryMaterialTfvdGreenReadout`, `A.carryMaterialTfvdReturnReadout` | Mapas `MaterialEdgeL2 →L[ℝ] ℝ`; endereços `GlobalC2BranchAddress`, quadratura `Fin 2`; retorno requer `0<eta<1` |
| `C.completedNativeOperatorCharacteristic` | `F:ℂ→ℂ`, completion arquimediana vezes `nativeScalar(1/2+iz)` |
| `C.completedNativeOperatorBoundaryCompanion` | `F_comp(z)=-deriv F z` |
| `C.normalizedCompletedGreenState` | `Z(z)/(sqrt(2)*F(z))`, como multiplicação escalar no carrier; não normaliza pela norma de Z |
| `C.completedGreenNormalizedResponse` | `q(z)=F_comp(z)/(2F(z))` |
| `C.completedGreenTaylorJet` | Coeficiente `(n!)⁻¹ • iteratedDeriv n state 0`, derivada complexa para `state:ℂ→E` |
| `C.HasCompletedNativeRealAxisNormalizedGreenKernel` | Gram complexo com dois parâmetros reais independentes, igual a `dslope q x u`, sob `F(x),F(u)≠0` |
| `C.HasCanonicalCompletedNativeTfvdGreenCenterLegReadout` | Identifica coeficiente Green polarizado com produtos dos mesmos jets TFVD, retendo incidência centro–perna; é obrigação, não existência de aplicação |
| `C.CompletedNativeRealHPCarrierCertificate` | Gram canônico em Hilbert real e independência das duas famílias de paridade; não foi preenchido por esta investigação |

A massa/profundidade relacional e a meia escala mantêm sua proveniência anterior. A fase logarítmica é a prescrita na fonte histórica; não foi deduzida apenas da divisibilidade. Nenhum pin, fonte, peso, produto interno ou operador foi alterado.

## 2. Norma completa na origem: prova na biblioteca padrão

O módulo novo [CarryMaterialCentralCalibration.lean](../GeometryOfNumbers/Analysis/CarryMaterialCentralCalibration.lean) prova 14 teoremas, registrados na auditoria `Analysis/Audit.lean`.

Para todo tempo real:

\[
\|Y_t\|^2=1+\|g_t\|^2+|\beta_t|^2.
\]

Na origem, com `P` a realização física C2 existente e `Q` a projeção residual existente:

\[
\boxed{\|Y_0\|^2=1+\|Pg_0\|^2+\|Qg_0\|^2+|\beta_0|^2.}
\]

São `A.carryMaterial_source_norm_sq` e `A.carryMaterial_origin_norm_physical_residual`. A decomposição utiliza a identidade polarizada anterior `A.carryMaterial_physical_residual_pairing`, não uma ortogonalização escolhida agora. O retorno global foi preservado.

A nova identidade de paralelogramo para o readout original é

\[
2\|y\|^2-|\ell(y)|^2=2\|g\|^2+|a-\beta|^2,
\qquad y=(a,g,\beta).
\]

`A.carryMaterial_readout_norm_gap` vale no carrier original. Especializando à fonte:

\[
2\|Y_0\|^2-|S_0|^2=2\|g_0\|^2+|1-\beta_0|^2.
\]

O quadrado `|1-β_0|²` mantém a interferência semente–retorno. Não é lícito substituí-lo por `1+|β_0|²`.

Também foram provados: `β_0=S_0-1`, `Im β_0=0`, `S_0≠0` e `‖g_0‖>0`. Para esta última, basta a coordenada material efetiva `g_0(0)=1/sqrt(2)-1`, sem estimativa numérica.

### Green, traço e residual

Reutiliza-se, sem reprova, `A.carryMaterialTfvd_edge_pairing` do PR #3. Para endereços físicos independentes `e,f`, os dois gradientes reconstruídos satisfazem

\[
\overline{g_e}h_f=\overline{G_e}G_f+\overline{G_e}R_f+
\overline{R_e}G_f+\overline{R_e}R_f.
\]

`R` nessa fórmula é retorno de traço vertical; `β` é retorno global de células completas. A expressão da norma pode ser refinada coordenada a coordenada com os quatro termos, mas esta investigação não provou uma nova identidade de soma global de energias Green. O setor residual e `β` não desaparecem porque uma leitura finita os ignore.

## 3. Identificação escalar efetiva entre os repositórios

O verificador [CanonicalComparison.lean](../research/material-central-calibration/CanonicalComparison.lean) contém 15 teoremas no namespace `CarryMaterialCanonicalComparison`.

A aplicação explícita de parâmetros é a inclusão `t:ℝ ↦ (t:ℂ)`. As definições dão

\[
s_{material}(t)=\tfrac12+it=operatorHeightParameter(t),
\]

com a comutação `t*i=i*t` verificada. Em seguida foram identificados os dois lados a partir das fontes:

1. `material_sample`: amostra material = `dirichletValue(nativeLine t) n`, para `n>0`.
2. `material_cell`: a mesma célula C2, com centro e pernas iguais.
3. `material_signal`: igualdade das sínteses completas, inclusive soma infinita.
4. `material_camera_factor` e `material_completion_factor`: mesmos fatores originais.
5. **`material_response`: `baseTwoCanonicalResponse t = completedNativeOperatorCharacteristic (t:ℂ)`, para todo t real.**

A divisão usa a não anulação do fator da câmera já provada; a linha tem parte real 1/2 e está no domínio `-1<Re(s)<1` requerido pelo teorema de `nativeScalar`.

Isto prova uma identificação escalar, não uma conjugação entre relógio material e operador das alturas. Também não transforma a derivada real de um vetor em derivada holomorfa. O verificador externo não acrescenta dependência ao Lake: combina os oleans já compilados, sob pins compartilhados idênticos, e fixa o commit do operador. Os 15 resultados são checados pelo kernel, mas ficam fora do build padrão da biblioteca para preservar seus pins.

## 4. Teste da candidata literal e defeito exato

Agora os escalares podem ser legitimamente comparados: `F(t)=D(t)S_t`. A candidata testada é somente `Z(t)=D(t)Y_t`. Na origem `D_0`, `S_0` e `F(0)` são não nulos. O cancelamento é algébrico, sem ajuste de constantes:

\[
M_0:=\left\|\frac{D_0Y_0}{\sqrt2 F(0)}\right\|^2
=\frac{1+\|g_0\|^2+|\beta_0|^2}{2|S_0|^2}.
\]

O outro lado é o valor diagonal literal do contrato:

\[
K_{can}(0,0)=dslope(q)(0,0)=q'(0)=h_0=-\frac{c_1}{c_0},
\quad c_n=\operatorname{Re}\frac{F^{(2n)}(0)}{(2n)!}.
\]

`canonical_kernel_at_origin` usa `C.completedNativeGreenNormalizedResponse_hasDerivAt_h0`. Não há divisão por `u-x` na diagonal: `dslope_same` fornece a derivada já demonstrada. A ordem zero do jet normalizado é a avaliação na origem por `normalized_jet_order_zero`; não se generaliza esse fato aos demais jets.

O defeito exato, provado com o verdadeiro h0, é

\[
\boxed{
\mathcal E_0=M_0-h_0=
\left(\frac14-h_0\right)+
\frac{2\|Pg_0\|^2+2\|Qg_0\|^2+|1-\beta_0|^2}{4|S_0|^2}.
}
\]

Aparecem a contribuição física, o residual e o desbalanço semente–retorno. O dressing é o correto e cancela; não há constante de completion a calibrar. O excesso vem de comparar a energia do carrier original com a derivada logarítmica do seu readout escalar.

`C.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` já prova `h0<1/16` por identidades theta/cosseno e limite analítico da cauda. Com `‖g_0‖>0`, esta investigação prova

\[
M_0>\frac14,\qquad \boxed{\mathcal E_0>\frac3{16}}.
\]

Não se trata de teste de ponto flutuante. Os novos teoremas são `material_canonical_central_mass_gt_quarter`, `material_canonical_central_defect_exact`, `material_canonical_central_defect_physical` e `material_canonical_central_defect_gt_three_sixteenths`.

Finalmente, `no_normalized_kernel_with_literal_material_origin` prova: **nenhuma função `state:ℂ→BaseTwoCompletedBoundaryHilbertCarrier` cujo valor na origem seja exatamente `D_0Y_0` satisfaz `HasCompletedNativeRealAxisNormalizedGreenKernel`.** A prova exige apenas esse valor, não continuidade ou holomorfia da extensão. Não exclui todo transporte para outro carrier, nem todo estado derivado geometricamente da fonte.

## 5. Primeiro cruzamento: convenção recuperada, investigação interrompida na calibração

Como a candidata falha já na ordem zero, não se afirmou sua identificação em ordens superiores.

A convenção literal evita um erro de índices: para jets Taylor indexados por ordens naturais, o coeficiente requerido é `polarizedGreenMomentCoefficient h p q`, dependente de `p+q`. Assim, `(p,q)=(0,1)` exige **zero**, e o primeiro h1 aparece em `(0,2)`, `(1,1)` ou `(2,0)`. Na família intercalada, `inl n` é ordem `2n`, `inr n` é ordem `2n+1`: h1 surge entre os dois primeiros jets pares, ou na norma do primeiro jet ímpar. Isso não corresponde a escolher profundidades verticais 0 e 1.

O valor genuíno recuperado no operador é

\[
h_1=\frac{c_1^2-2c_0c_2}{c_0^2},
\]

por `C.canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant`. O estudo arquivado em `momentos` registra aproximadamente `h0=0.023104993115418970788933810430339014…` e `h1=0.000037172599285269686164866262471740…`; estes números são apenas diagnóstico anterior, não utilizados nas provas, e nenhuma nova campanha numérica foi executada.

Os relógios fortes do gradiente e readouts TFVD existentes continuam disponíveis. Nenhum desses teoremas identifica automaticamente o estado global com jets holomorfos no carrier canônico.

## 6. Rota real corrigida e primeira ponte restante

O PR #106 conserva as duas quadraturas: `C.RealQuadrature.J`, suas formas métricas e de rotação, o empacotamento fiel (`C.RealQuadrature.pack_inner`, `C.RealQuadrature.pack_J` em `NativeRealFirstQuadratureNaturality.lean`), o complemento prime-carry (`C.RealFirstNative.towerComplement_eq_original_quadratures`) e observado/halo/escape. Essas realizações não identificam carriers diferentes só por semelhança de fórmulas.

Na diagonal a energia real e a norma complexa do mesmo estado coincidem. A obstrução acima não pode ser removida por uma mera reescrita das duas quadraturas. Não foi aplicada a forma complementar de outro carrier ao Y material sem um mapa tipado que o justificasse.

**Diagnóstico solicitado:**

| Etapa | Situação exata |
| --- | --- |
| Fonte disponível | `Y_t=(1,g_t,β_t)`, com fonte, fase, endereços C2 e residual prescritos |
| Transformações existentes | Projeção física/residual; reconstrução real TFVD por Green + retorno de traço; dressing escalar; readout `ℓ(Y_t)=S_t` |
| Objeto de destino | Estado/jets de `CanonicalCompletedTfvdGreenHilbertCarrier` com pareamento canônico, depois a interface real HP |
| Igualdade escalar | **Provada:** `D_t ℓ(Y_t)=F(t)` |
| Igualdade vetorial tentada | **Refutada para a candidata literal:** `‖D_0Y_0/(sqrt2 F(0))‖²=h0` |
| Primeira construção ainda ausente | Uma aplicação da fonte e de seus dados Green/traço/retorno ao estado canônico, derivada das relações e com ação explicitamente determinada na origem |
| Primeira propriedade que essa aplicação deve demonstrar | Sua energia central normalizada é `h0`; depois, o pareamento de dois parâmetros e os coeficientes genuínos. Essa propriedade não pode ser suprida pelo mesmo vetor literal com norma preservada |

Não há uma hipótese de isometria artificial preenchendo a lacuna. Uma nova ponte terá de explicar matematicamente por que seu estado central é diferente do lift literal testado, preservando a proveniência, e então verificar o kernel completo. Não se autoriza modificar a métrica para apagar o excesso. O certificado complexo anterior obstruído pelo primeiro jet ímpar não foi reutilizado.

## 7. Status e reprodução

| Status | Resultado |
| --- | --- |
| **PROVADO em Lean — biblioteca** | 14 identidades da norma completa, retorno, cancelamento e excesso central da candidata |
| **PROVADO em Lean — verificação externa** | 15 teoremas: identificação da fonte escalar, parâmetro explícito, defeito contra h0 e no-go estreito |
| **PROVADO anteriormente / reutilizado** | Reconstrução TFVD + traço, quatro cruzamentos, duas quadraturas e limite h0<1/16 |
| **CONDICIONAL — interface existente** | Aplicar certificados HP quando seu Gram e independências forem demonstrados; não preenchidos nesta rodada |
| **OBSTRUÍDO** | Kernel normalizado para qualquer extensão com valor literal `D_0Y_0` na origem, no carrier original |
| **ABERTO** | Aplicação física canônica que identifique pareamentos; genuíno primeiro cruzamento dessa aplicação |

Comandos executados em `llm`, no checkout isolado baseado no commit acima:

```bash
lake build GeometryOfNumbers.Analysis.CarryMaterialCentralCalibration --wfail
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
lake env lean -DwarningAsError=true research/material-central-calibration/Regression.lean
bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator
```

Build completo: **8825 jobs**, sem warnings. Guardas transitivos por `collectAxioms` inspecionam tipos e corpos; os 29 resultados permitem somente `propext`, `Classical.choice`, `Quot.sound`. A Foundation conserva footprint vazio; Geometry mantém seu guard próprio. Sem `sorry`, `admit`, novos axiomas ou mudanças de pins. O verificador cruzado requer módulos do operador previamente compilados no commit fixado e pins Lean/Mathlib/GreenFrame idênticos; ele não altera fontes ou manifests do outro repositório.

[Evidência de validação](../research/material-central-calibration/validation.json), [footprints novos](../research/material-central-calibration/footprints.json) e logs comprimidos na mesma pasta. As regressões conservam o canário 72, os nove cruzamentos, endereços TFVD, relógio e obstruções anteriores. O módulo de comparação externo também audita suas 15 declarações em toda execução.
