# Carry — do estado material completo ao primeiro canal normalizado

Data: 2026-10-16. Implementação em `geometry-of-numbers`, base `0b5f841663e3790fb7a89566b8f189337d49cdb1` (PR #4). Operador consultado, sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.

**Avanço:** foi construída a companheira vetorial da fonte material no domínio do relógio existente. Seu readout é exatamente a companheira canônica `-F'`. Isso fornece a resposta normalizada correta e uma identificação local com a extração do primeiro canal da fonte de quatro setores. A energia central desse canal é exatamente h0, e uma identidade de dois parâmetros conserva o kernel residual.

**Limite:** este canal é um observável extraído por quocientes e derivadas da fonte completa. Não é uma identificação isométrica do estado material inteiro com o estado canônico. O no-go do lift literal `D(t)Y_t` do PR #4 permanece válido.

## 1. Fonte, domínio e transformações reutilizados

Mantêm-se os objetos existentes:

\[
Y_t=(1,g_t,\beta_t),\quad
S_t=\ell(Y_t),\quad
\ell(a,g,\beta)=a+\beta,\quad F(t)=D(t)S_t.
\]

O retorno β foi construído pela soma de células completas. A componente gradiente pertence a ℓ²; a fonte bruta `n^(-1/2) exp(-it log n)` não foi colocada em ℓ². O dressing D é o original, sem nova constante.

O relógio material K é `BaseTwoCompletion.completedBoundaryTransportedClock`, um **mapa linear parcial** no Hilbert original. Seu domínio já impõe:

1. a coordenada β é a soma efetiva dos retornos de células;
2. as coordenadas do relógio pertencem a ℓ²;
3. o retorno global do relógio é somável.

`baseTwoCompletedBoundaryHilbertState_mem_clockDomain` fornece o domínio para todo t real. `completedBoundaryState_hasDerivAt_clock` fornece a derivada forte real de todo o estado:

\[
\dot Y_t=-iK Y_t.
\]

Não foi postulado um relógio diagonal, um novo domínio ou holomorfia de Y. A conexão material `log(j+2)-log(j+1)` continua nas coordenadas triangulares do K existente.

## 2. Companheira construída antes do readout

O módulo novo [CarryMaterialNormalizedResponse.lean](../GeometryOfNumbers/Analysis/CarryMaterialNormalizedResponse.lean) define, para cada t real, um mapa linear complexo **no domínio existente**:

\[
\boxed{\mathcal C_t(y)=-\bigl[D(t)(-iKy)+D'(t)y\bigr].}
\]

É `GeometryOfNumbers.Analysis.carryMaterialDressedCompanion`. Nenhuma continuidade desse mapa parcial ou extensão a todo o Hilbert é presumida. O termo D' atua sobre o estado inteiro. Semente, gradiente e retorno permanecem no carrier antes da observação escalar.

`carryMaterialDressedSource_hasDerivAt` prova

\[
\frac{d}{dt}\bigl(D(t)Y_t\bigr)=-\mathcal C_t(Y_t).
\]

Se B(y) é `baseTwoCompletedBoundaryClockReturn y`, o readout exato é

\[
\boxed{\ell(\mathcal C_t(y))=iD(t)B(y)-D'(t)\ell(y).}
\]

São `carryMaterialClock_readout` e `carryMaterialDressedCompanion_readout`. B é o **retorno global do relógio**; não é β nem o retorno de traço de cada fibra TFVD. Esses dados não foram identificados entre si.

Aplicando a derivada forte ao readout contínuo já existente, prova-se

\[
\ell(\mathcal C_t(Y_t))=-\frac{d}{dt}\,baseTwoCanonicalResponse(t).
\]

Não se diferenciou uma série escalar informalmente nem se apagou o termo derivativo da completação.

## 3. Comparação real com o par canônico

O verificador [CanonicalComparison.lean](../research/material-central-calibration/CanonicalComparison.lean) foi estendido no namespace `CarryMaterialResponseComparison`. Reutiliza a identidade escalar do PR #4:

\[
baseTwoCanonicalResponse(t)=completedNativeOperatorCharacteristic(t:\mathbb C).
\]

O teorema novo `material_characteristic_hasDerivAt` restringe ao eixo real a derivada da **característica escalar**, cuja analiticidade no domínio já está provada. Isso não identifica uma derivada real de Y com um jet holomorfo vetorial.

Resultam as identificações efetivas:

\[
\boxed{\bigl(\ell(\mathcal C_t(Y_t)),\ell(D(t)Y_t)\bigr)
=\bigl(F_{comp}(t),F(t)\bigr)=\bigl(-F'(t),F(t)\bigr).}
\]

São `material_companion` e `material_boundary_pair`. A ordem companheira/valor é a da definição original `canonicalCompletedC3ScalarBoundaryPair`.

A aplicação seguinte é um readout **não linear**, definido a partir desse mesmo domínio e dessa mesma fonte:

\[
r_{mat}(t)=\frac{\ell(\mathcal C_t(Y_t))}{2\ell(D(t)Y_t)}.
\]

`material_normalized_response` prova, em todos os parâmetros reais com as definições totais do código, `r_mat(t)=(-F'(t))/(2F(t))`. Para interpretar a divisão usual exige-se F(t)≠0; a regressão verifica a não anulação na origem, que persiste em uma vizinhança por continuidade. Nenhuma interpretação de quociente usual é feita nos zeros de F.

Quando S(t)≠0, `carryMaterialNormalizedResponse_connection` dá a expansão que revela a proveniência:

\[
\boxed{r_{mat}(t)=\frac{iB(Y_t)}{2S_t}-\frac{D'(t)}{2D(t)}.}
\]

O segundo termo é a conexão da completação. O termo B contém o relógio com a reconstrução material e seus retornos. A resposta não foi obtida reescalando a norma de Y para caber em h0.

## 4. A escala e o primeiro canal vêm dessa resposta

Definem-se sobre o parâmetro **real**:

\[
a_{mat}(t)=dslope(r_{mat})(0,t),\qquad
\alpha_{mat}=\operatorname{Re}a_{mat}(0),\qquad
\phi_{mat}(t)=\frac{a_{mat}(t)}{\sqrt{\alpha_{mat}}}.
\]

As três definições pertencem à biblioteca Geometry; não recebem h0 como entrada. Em t=0, dslope é a derivada, não a divisão total 0/0.

O verificador compara a resposta física com `SourcePositiveReduction.sourceResponse`, reutilizando o germen já provado em `NativeCompletedSourcePositiveReductionJet`. Resultados:

- `material_normalized_response_zero`: r_mat(0)=0.
- `material_normalized_response_hasDerivAt_zero`: r_mat'(0)=h0.
- `material_axis_eventually_eq`: os eixos material e da fonte de quatro setores coincidem localmente no eixo real, incluindo o valor removível na origem.
- `material_scale_eq` e `material_scale_pos`: α_mat=h0>0.
- `material_feature_eventually_eq`: o canal material coincide localmente com `SourcePositiveReduction.positiveFeature`.

Isso fecha as calibrações novas:

\[
\boxed{\|\phi_{mat}(0)\|^2=h_0,}\qquad
\boxed{\langle\phi_{mat}(0),\phi_{mat}(t)\rangle=a_{mat}(t)}
\]

para a linha central local. São `material_feature_center_energy` e `material_feature_center_row`. A origem é o readout do estado e de sua companheira; a escala só depois é identificada com o momento já certificado.

`material_feature_pairing_local` testa dois parâmetros reais independentes em uma vizinhança aberta de 0 e prova a igualdade dos produtos internos desse canal com os do canal existente. A notação complexa conserva as duas quadraturas já utilizadas nas fontes; não foi construído um novo carrier para alterar sua métrica.

## 5. O residual foi transportado, não eliminado

Se r1 é `SourcePositiveReduction.reducedResponse`, construído anteriormente pela redução da mesma resposta sintetizada, existe uma vizinhança real U de 0 onde

\[
\boxed{\begin{aligned}
r_{mat}(u)-\overline{r_{mat}(t)}
={}&(u-\bar t)\langle\phi_{mat}(t),\phi_{mat}(u)\rangle\\
&+\overline{r_{mat}(t)}r_{mat}(u)
\bigl(r_1(u)-\overline{r_1(t)}\bigr).
\end{aligned}}
\]

É `material_kernel_numerator_split_local`, válido inclusive nos pontos de colisão: não divide por u−t. A prova transporta `sourceKernel_numerator_split` existente; não o reimplementa para um campo livre.

Para t,u∈U com u≠t, `material_kernel_split_local` permite a divisão legítima:

\[
\frac{r_{mat}(u)-\overline{r_{mat}(t)}}{u-\bar t}
=\langle\phi_{mat}(t),\phi_{mat}(u)\rangle+
\overline{r_{mat}(t)}r_{mat}(u)K_{r_1}(t,u).
\]

O fator do residual permanece com sua ordem de conjugação original. As hipóteses de não anulação dos eixos da redução são obtidas localmente do teorema existente, não introduzidas como certificado opaco de igualdade de kernels.

**Limite da diagonal:** a calibração e a linha central usam o valor removível correto. A identidade do numerador também é válida na diagonal. Não se anunciou nesta rodada uma extensão removível do kernel residual em todas as demais diagonais reais. A fórmula antiga de energia finita que exige `z_j ≠ conj(z_i)` não foi aplicada indevidamente a uma família de pontos reais, onde os pares i=j violariam essa hipótese.

## 6. O que fechou e o que ainda falta

| Status | Resultado |
| --- | --- |
| **PROVADO — biblioteca** | Companheira linear no domínio correto, derivada forte do estado vestido, readout com retorno do relógio e conexão D', fórmula da resposta material |
| **PROVADO — verificador entre repositórios** | Par canônico (-F',F), resposta normalizada correta, escala α=h0>0, energia e linha central do primeiro canal, pareamento local em duas entradas e residual exato |
| **REUTILIZADO** | Fonte de quatro setores, redução positiva de primeiro canal, positividade central h0, relógio forte e síntese/readout material anteriores |
| **ABERTO** | Realização Hilbert do residual completo e igualdade do Gram físico completo com o kernel canônico; extensão removível residual em todas as diagonais reais |
| **NO-GO ANTERIOR PRESERVADO** | A norma do lift literal D Y com normalização sqrt(2) F continua diferente de h0 |

A cadeia demonstrada nesta rodada é

**estado material completo → companheira no domínio do relógio → readout (-F',F) → resposta normalizada → primeiro canal e residual.**

Não se provou

**norma do estado material completo = kernel canônico**, nem **kernel residual positivo em todas as ordens**.

A diferença é matemática: a construção nova usa a companheira, a conexão e o quociente removível da resposta. Ela não é uma isometria de Y, um whitening definido pelo Hankel ou uma constante ajustada à calibração. O próximo dado necessário é uma realização do residual compatível com a fonte e com o pareamento real completo.

## 7. Validação e proveniência

Há **6 novas definições e 8 novos teoremas** na biblioteca e **17 novos teoremas** no verificador externo. As definições também foram incluídas nas guardas de axiomas da biblioteca. Os 17 teoremas do verificador anterior são preservados e auditados novamente.

Comandos executados em `llm`:

```bash
lake build GeometryOfNumbers.Analysis.CarryMaterialNormalizedResponse --wfail
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
lake env lean -DwarningAsError=true research/material-response-transport/Regression.lean
bash scripts/audit-material-central-comparison.sh /home/thlinux/carry-self-adjoint-operator
```

Build focado: **8787 jobs**; completo: **8826 jobs**. Os guardas transitivos por `collectAxioms` inspecionam tipos e corpos, com `#print axioms` explícito. Os novos resultados usam somente `propext`, `Classical.choice`, `Quot.sound`; a Foundation conserva sua auditoria vazia. Não há `sorry`, `admit`, novos axiomas ou alterações de pins.

Regressões: canário 72, nove cruzamentos, endereços e retorno TFVD, residual físico, conexão do relógio, não anulação central, domínio de todo o estado e contribuição derivativa da semente na companheira.

[Proveniência por arquivo e commit](../research/material-response-transport/provenance.json), [novas declarações](../research/material-response-transport/new-roots.json), [footprints](../research/material-response-transport/footprints.json) e [validação](../research/material-response-transport/validation.json). Logs comprimidos na mesma pasta.

O verificador externo preserva os manifests: usa os módulos compilados dos dois repositórios, com Lean/Mathlib/GreenFrame compartilhados e o commit do operador fixado. A implementação não altera `carry-self-adjoint-operator`, `momentos` ou os trabalhos preexistentes.
