# Proveniência inteira e ledger de incidências Carry

Investigação em `llm`, 15/10/2026. Base de `geometry-of-numbers`: `e1084b43533255b399b82dc307b536d7dfdca07f`. Fonte consultada do autoadjunto: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, após PRs #105/#106. A formalização nova está somente na geometria; nenhum pin ou fonte de outro repositório foi alterado.

**Obtivemos A, B e C:** proveniência comum de câmeras pela torre residual original, compatibilidade exata das incidências e um ledger quadrático finito com defeito polarizado. O contramodelo de 72 prova que incidências e energias locais não bastam para determinar a energia da síntese. **D permanece aberto:** não construímos o mapa físico desse ledger para o carrier TFVD/Green do PR #106.

## 1. Proveniência existente, antes das provas novas

Os nomes da tabela são relativos aos namespaces completos indicados. As fontes, hashes e commits de última alteração estão no índice de proveniência que acompanha este relatório.

| Camada e namespace | Declarações conferidas | Hipóteses e limite |
|---|---|---|
| `GeometryOfNumbers.Foundation` — primeiro retorno | `existsUnique_emergentLocalCapacity`, `emergentLocalCapacity_gt_one_of_first_step_changes` | Trajetória unitária, observação local com passo autônomo e injetivo, apresentação finita explícita. Passo inicial alterado dá capacidade maior que um. Não se deduz tudo isso do inteiro isolado. Sem Hilbert ou norma. |
| Mesmo namespace — torre | `emergentResidualTower_value`, `residualTower_eq_canonical`, `emergentResidualTower_expansion`, `emergentResidualTower_truncate` | Para `b>0`, reconstrução `n=prefixo+cauda*b^k`, unicidade entre torres limitadas e coerência de truncamentos. A cauda não é descartada. Sem Hilbert. |
| `GeometryOfNumbers.Geometry` — centro/pernas | `balancedCarry_spec`, `emergentCapacity_balancedCarry_spec`, `balancedCarry_positive_depth_iff` | O balanceamento recebe capacidade ímpar explicitamente; não recebe primalidade. A torre caracteriza o offset profundo. Não escolher arbitrariamente o antipodal C2. Os novos pares escalados abaixo usam a geometria inteira geral, sem resolver esse problema de balanceamento. |
| Mesmo namespace — profundidade | `hasCarryDepthAtLeast_eq_scaled_tail`, `hasCarryDepthAtLeast_iff_dvd_pow` | `HasCarryDepthAtLeast` foi definido por zeros sucessivos da torre. Divisibilidade por `b^k` é um teorema posterior, para `b>0`. Zero sobrevive a todos os níveis; base um também. Não há redefinição por valuation. |
| `GeometryOfNumbers.Analysis` — crosswalk primo | `primeResidualDepth_iff_le_factorization`, `primeResidualDepth_factorization_characterized`, `primeResidualDepth_quantity_ext` | Primo `p`, quantidade não nula. A fatoração representa os thresholds já construídos. Os thresholds em todas as bases primas determinam a quantidade. Mathlib entra aqui; não há uso matemático de Hilbert nessas identidades. |
| `GeometryOfNumbers.Foundation` — massa/metade | `canonicalResidualDepthMass_eq_radixShare`, `canonicalResidualDepthMass_quadraticCompatibility_iff_half`, `foundational_half_scaling_capstone` | Contagem prefixal e compatibilidade quadrática explícita; para rigidez, `b>1`, `k>0`, denominador formal positivo. Metade já estava selecionada. Axiomas vazios, sem norma/Hilbert. |
| `GeometryOfNumbers.Analysis` — realização quadrática | `realDepthMass_eq_one_div_pow`, `realCriticalAmplitude_sq_eq_realDepthMass`, `realCriticalDepthState_energy`, `rotateRealPlane_energy` | Massa local, amplitude e energia coordenada `x²+y²` são objetos distintos, ligados pelos respectivos teoremas. Ângulo livre. Não determinam uma energia global independente da câmera. |
| Mesmo namespace — atlas | `atlasResolvedEnergy_eq_input`, `centerLegAtlasEnergy_common_partition_independent` | Recebem `AdmissibleAtlasPartition`, cuja soma unitária é uma entrada semântica. As identidades não constroem uma partição canônica de incidências inteiras. |
| Mesmo namespace — observação vertical | `completeVerticalObservabilityGram_posDef`, `completeVerticalObservabilityGram_not_hankel` | Já usa Hilbert. A família observada é independente, mas seu Gram não é Hankel: `G02=1`, `G11=4+eta²+eta⁻²`, para `eta≠0`. |
| `GeometryOfNumbers.Analysis.CanonicalGreenMomentSeam` | `greenParseval_iteratedDeriv`, `baseTwoCanonicalGreenFirstColumnResidual_eq_material` | Já usa Hilbert/Parseval. Transportar jets e seus pareamentos conserva o residual de calibração anterior; não o anula. |

As declarações dos PRs #105/#106, em `CarrySelfAdjointOperator`, foram lidas separadamente:

- `RealQuadrature.double_domainJ`, `RealQuadrature.double_realAdjoint_pairing` e `RealQuadrature.pack_inner`: Hilberts reais já dados; preservação de domínio, adjunto e duas formas polarizadas.
- `RealQuadrature.materialLogClock_edge_connection`: mantém a conexão material `log(n+2)-log(n+1)`.
- `RealFirstNative.towerComplement_coercive`: forma complementar da torre já dada, com orçamento `1/12`; não constrói seu estado físico.
- `RealFirstNative.pr105_full_pairing_comparison`: comparação do pareamento total dos três setores. `RealFirstNative.response` é o desempacotamento da resposta completada já existente.
- `GammaMaterialSewing.nativeCompletedGlobalEscape_fourTerms_zero` e `GammaMaterialSewing.nativeCompletedWronskianDefect_eq_twoSectorBoundary`: dependem da fonte completada e conservam correções e cruzamentos ordenados.
- `CompletedNativeRealHPCarrierCertificate` e `HasCanonicalCompletedNativeTfvdGreenCenterLegReadout`: interface real corrigida e identidade física ainda necessária. `not_completedNativeGreenWeylReducedHeightCertificate` já refuta a antiga entrada Taylor complexa radial.

Uma peça relevante continua fora da `main` do outro repositório: o [PR #15 de native-carry-spectral-weyl](https://github.com/thiagomassensini/native-carry-spectral-weyl/pull/15), aberto na conferência desta rodada. No commit científico `f83ad1ab388ad627595eec20dbd393d2cc300f4e`, `NativeCarrySpectralWeyl.Finite.Relational.divisibility_inner` e `gramKernel_finsupp` realizam o Gram nativo por contagem de divisibilidade e `1/lcm(d,e)`, preservando multiplicidades. O checkout consultado estava em `871217099a069083791738578b2e44005b31986e`; a `main` remota em `248249ce098491f4194209d8e698dc5965f1405d` não contém o arquivo. Essa construção não foi reimplementada, importada ou integrada nesta tarefa. Seu módulo importa Naimark, embora a contagem aritmética seja uma etapa identificável; seu Gram nativo não foi identificado com o kernel Green canônico.

## 2. Resultado A: o inteiro comum e a profundidade na outra câmera

Em `Geometry/IntegerCameraIncidence.lean`, `IntegerCameraCell` contém apenas base, profundidade e core. Seu raio é `b^k`; seu centro é `b^k*m`; os três pontos usam `leftLeg`, centro e `rightLeg` preexistentes. Câmera e papel permanecem como rótulos da incidência. Não há primalidade, métrica ou máximo na definição.

`integerCameraTowerCell b n k` lê o core como **cauda da torre original**. De `HasCarryDepthAtLeast b n k`, o teorema novo `integerCameraTowerCell_reconstruction` obtém

\[
b^k\,\operatorname{tail}_{b,k}(n)=n.
\]

`integerCamera_common_integer` aplica essa reconstrução em duas bases positivas. É um teorema geral sem axiomas; não identifica coordenadas de câmeras diferentes.

Em `Analysis/PrimeCameraProvenance.lean`, reutilizamos a equivalência prima anterior:

\[
\bigl(\mathrm{Depth}_p(n,k)\land\neg\mathrm{Depth}_p(n,k+1)\bigr)
\iff k=n.\mathrm{factorization}(p),\qquad p\text{ primo},\ n\ne0.
\]

`primeCamera_common_maximal_presentations` constrói simultaneamente as duas apresentações maximais a partir das torres. A equivalência caracteriza sua profundidade única. A reconstrução fixa também o core, pois o fator `p^k` é positivo.

O resultado relacional mais útil é `integerCamera_other_depth_iff`. Para bases positivas coprimas e qualquer nível `l`,

\[
\boxed{\mathrm{Depth}_q(n,l)
\iff\mathrm{Depth}_q\!\left(\operatorname{tail}_{b,k}(n),l\right)}
\]

sempre que `Depth_b(n,k)` vale. A remoção da escala `b^k` conserva **todos** os thresholds da outra câmera. A versão `primeCamera_other_depth_iff` recebe primos distintos. Não exige que os cores de uma câmera sejam rasos nas demais.

O canário verifica exatamente `72=2³*9=3²*8`; o core `9` tem profundidade `2` na câmera 3, e o core `8` tem profundidade `3` na câmera 2. Outro canário prova que `8=4¹*2` tem profundidade máxima 1 na base composta 4 e core não coprimo a 4. Não acrescentamos a hipótese indevida de coprimalidade nesse caso.

## 3. Resultado B: a sobreposição conserva o centro, não as pernas

`integerCamera_same_center_leg_displacement` prova, para centro comum e raios `r_a,r_b`,

\[
L_a-L_b=r_b-r_a,\qquad R_a-R_b=r_a-r_b.
\]

`integerCamera_same_center_overlap` prova algo mais forte: se os raios são positivos e distintos, dois pontos das células coincidem **se e somente se ambos são o centro**. Não se inventa uma bijeção entre pernas.

No canário, as células são exatamente `(64,72,80)` e `(63,72,81)`. Elas representam o mesmo inteiro central, mas observam relações aditivas diferentes. Igualdade de quantidade não é igualdade desses dois observáveis.

As massas locais também permanecem distintas, por teorema novo que apenas especializa a API anterior:

\[
\mu_2(3)=1/8\ne1/9=\mu_3(2).
\]

Isso não é um defeito da meia escala: cada massa pertence a uma resolução local diferente. Nenhum teorema novo iguala essas massas, soma pesos escolhidos ou deduz um produto interno global delas.

## 4. Resultado C: ledger real de incidências com defeito explícito

`Analysis/IntegerIncidenceEnergy.lean` começa pelos pontos inteiros efetivos. O stencil de uma célula é o dado finitamente suportado

\[
A_a=\delta_{L_a}-2\delta_{c_a}+\delta_{R_a}.
\]

Para uma lista finita de células e coeficientes declarados, `integerIncidenceLedger` soma esses stencils **com suas multiplicidades assinadas**. `integerIncidenceLedger_synthesis` prova que a leitura no campo real `v: Int→ℝ²` coincide com a síntese dos readouts das células. O campo é entrada explícita; não foi escolhido de um Hankel.

O ledger da soma das duas células de 72 tem coeficiente `−4` no centro compartilhado. Mesclar o endereço inteiro não apaga sua multiplicidade. Apagar uma cópia do centro alteraria a observação. As pernas diferentes continuam com seus endereços distintos.

`integerIncidenceSynthesis_ext_iff` prova que duas apresentações têm a mesma síntese para **todo** campo de observação se e somente se seus ledgers inteiros coincidem. A prova testa cada inteiro por uma observação delta; não recebe uma isometria como hipótese.

Para comparar apresentações `A,B`, definimos apenas o defeito calculável `D=B−A`. Se `X_A(v)` é a síntese e `delta(v)=X_D(v)`, a reconstrução exata é

\[
X_B(v)=X_A(v)+\delta(v).
\]

Usamos a energia coordenada preexistente `E(x,y)=x²+y²`. Sua polarização é `P(u,v)=u₁v₁+u₂v₂`; `integerObservationPair_polarization` verifica que ela é a polarização dessa mesma energia, sem introduzir outra métrica.

`integerIncidence_pairing_transport` mantém dois campos independentes e os três termos de correção:

\[
\begin{aligned}
P(X_B(v),X_B(w))-P(X_A(v),X_A(w))={}&
P(X_A(v),\delta(w))\\
&+P(\delta(v),X_A(w))+P(\delta(v),\delta(w)).
\end{aligned}
\]

Na diagonal, `integerIncidence_energy_transport` fornece

\[
\boxed{E(X_B)-E(X_A)=2P(X_A,\delta)+E(\delta).}
\]

`integerIncidence_energy_conservation_iff` identifica a condição adicional exata: o lado direito precisa ser zero. Não se impõe seu sinal. Igualdade dos ledgers é suficiente para conservar a síntese em todos os campos; conservação de uma energia isolada pode ocorrer mesmo com ledger diferente. Não afirmamos a recíproca mais forte.

### Contramodelo finito auditado

O campo `v_+` vale `(1,0)` nos pontos 63 e 64 e zero nos demais. `v_-` muda apenas o valor em 63 para `(-1,0)`. Assim:

- As incidências são as mesmas, inclusive o centro compartilhado 72.
- As energias em **todos os pontos** são iguais nos dois campos.
- A energia de cada readout individual das duas células é 1 em ambos.
- Os readouts são `(1,0),(1,0)` em `v_+` e `(1,0),(-1,0)` em `v_-`.
- A energia da síntese das duas células é **4** no primeiro caso e **0** no segundo.

Esses fatos estão em `integerCamera72_local_energy_does_not_determine_synthesis`. Com amplitudes arbitrárias fixas `a,b`, `integerCamera72_weighted_energy_gap` prova exatamente

\[
\boxed{E(aX_2(v_+)+bX_3(v_+))-E(aX_2(v_-)+bX_3(v_-))=4ab.}
\]

Logo fixar amplitudes ou energias locais não elimina o cruzamento faltante. O resultado refuta somente a determinação da energia sintetizada por esses dados locais. Não refuta uma lei adicional da fonte canônica que fixe as relações entre os campos. A soma das energias locais é conservada nesse exemplo; ela é um observável distinto da energia da síntese, conforme a disciplina anterior do repositório.

## 5. Qual dado falta para a próxima identificação?

O primeiro dado ainda não construído é **a leitura vetorial física da estrutura inteira completa, com suas relações de fase e retorno**, que selecione os pareamentos cruzados entre as incidências compartilhadas e as pernas distintas. Inteiro comum, massas locais e energias locais não o determinam pelas hipóteses examinadas.

Para um campo efetivamente derivado da fonte, o defeito acima já tem endereço: `B−A` e sua síntese. A próxima conservação exigirá uma identidade desse campo que anule `2P(X_A,delta)+E(delta)`, ou outra lei de comparação que mantenha explicitamente seu valor. A condição foi identificada, não preenchida.

Não há nesta rodada um crosswalk tipado dessas observações para `NativeGpreTowerHilbert` ou para o carrier TFVD/Green. Portanto não aplicamos o orçamento `1/12` ao ledger como se esse mapa existisse. A conexão material do PR #106 permanece intacta; parâmetros de tempo não foram introduzidos no ledger. A completação, seus termos derivativos, cabeça/cauda e os quatro canais Green continuam no repositório consultado, sem renomeá-los como o defeito inteiro `B−A`.

O domínio físico também precisa ser demonstrado: uma célula inteira pode ter perna zero (por exemplo, core unitário), de modo que sua existência aritmética não autoriza automaticamente aplicar um relógio logarítmico de pontos positivos.

Depois de construir esse mapa físico, ainda será necessário demonstrar o pareamento normalizado que alimenta `HasCanonicalCompletedNativeTfvdGreenCenterLegReadout` e `CompletedNativeRealHPCarrierCertificate`. Não identificamos profundidade com jet, câmera com índice material, relógio de fase com altura ou Gram de observação com Hankel.

## 6. Estado formal e validação

**Provado no Lean:** todos os resultados A/B/C descritos, os canários de 72 e base composta, a reconstrução do ledger, sua extensionalidade e as identidades de defeito e contramodelo. São teoremas gerais ou cálculos exatos conferidos pelo kernel; não experimentos de ponto flutuante.

**Apenas análise em texto:** a indicação de quais dados de fase/retorno precisariam determinar os cruzamentos e a comparação conceitual com o PR #106. Nenhuma existência de transporte físico foi inferida disso.

**Aberto:** escolha física do campo completo, compatibilidade dinâmica, transporte para a torre prima e identificação TFVD/Green canônica. Não houve campanha de positividade ou reconstrução do operador.

Os três módulos novos e os imports/audits centrais passaram em `lake build --wfail` (8.820 jobs). Os scripts oficiais de Foundation, Geometry e Analysis também passaram. Os 47 roots públicos novos têm `#print axioms` e guards transitivos de tipos/corpos: definições discretas sem axiomas, teoremas de Geometry somente `propext`/`Quot.sound`, Analysis somente os três axiomas padrão. Foundation e sua cadeia de seleção não foram alteradas. Não foram usados placeholders, axiomas novos ou escapes de confiança.

Os nomes completos, comandos, footprints, hashes e logs comprimidos acompanham a publicação. Foram preservados os pins e o trabalho preexistente dos outros repositórios. A integração e a remoção da worktree da tarefa são registradas na confirmação de publicação.
