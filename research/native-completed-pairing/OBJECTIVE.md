# Carry — Ponte quadrática canônica sem escolha de câmera

**Especificação de formalização para a próxima PR (após #75).** 23/10/2026.

## 0. O problema correto

Não construir outra característica, outro operador ou uma norma conveniente. O alvo é derivar, da **síntese completada original** da geometria Carry, a positividade da **forma de Hankel dos momentos canônicos existentes**. A escolha de base/câmera é uma coordenada de representação: a quantidade sintetizada deve ser independente dela. A ortogonalização é posterior aos momentos e à Hankel; é feita por whitening/Jacobi, não por ortogonalizar câmeras.

As profundidades verticais em câmeras primas reconstruem o dado aritmético:

\[
  n=\prod_{p\mid n}p^{v_p(n)},\qquad
  \log n=\sum_{p\mid n}v_p(n)\log p.
\]

A compatibilidade quadrática nativa força a amplitude \(b^{-k/2}\). **Esses dois fatos não constituem, isoladamente, uma prova de positividade da forma de Hankel**. A ligação não trivial é a conservação do pareamento quadrático após a síntese completada — incluindo Green, pernas, bordos, retornos, cruzamentos, fator de câmera, log-jets, Gamma e completion.

## 1. Objetos existentes e dependências reais

- `GeometryOfNumbers/Foundation/FoundationalHalfScalingCapstone.lean`: `foundational_half_scaling_capstone`, escala crítica derivada, sem nova métrica.
- `primos/CPFormal/Analytic/CpPrimeTowerCarryMangoldtBridge.lean`: `sum_primeVerticalScale_primeFactors_eq_log`, leitura vertical prima = logaritmo da quantidade.
- `primos/CPFormal/Analytic/CpPrimeDepthLogWaveBridge.lean`: `primeDepthLogCoordinate_eq_log`, `nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm`, `finiteChart_primeDepthWave_eq_dirichlet`.
- `CarrySelfAdjointOperator/LogarithmicMomentHankel.lean`: `IsLogDerivativeMomentSequence.unique`, `hankelGram`, `shiftedHankel`.
- `GeometryOfNumbers/Analysis/MomentGramPositivity.lean`: `IsMomentGramRepresentation`, `IsShiftedMomentGramRepresentation`, `hankelGram_posSemidef_of_gramRepresentation`, `hankelGram_posDef_of_gramRepresentation`.
- `GeometryOfNumbers/Analysis/FiniteJacobiTransport.lean`: `finiteJacobiSection`, `finiteGramWhitening_identity` e `J = B K Bᵀ`.
- `GeometryOfNumbers/Analysis/CanonicalFiniteHeight.lean`: `canonicalFiniteHeightOperator`, `canonicalFiniteHeightOperator_isSymm` e polinômio característico, todos consumidores posteriores das hipóteses necessárias.
- `carry-self-adjoint-operator/CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean`: `sourceMomentMatrix_all_posDef_iff_schur`, `nativeSourceBoundary_all_pos_iff_sourceSchur`, que identificam o critério exato do sinal.
- PR #41 de `geometry-of-numbers`: energia do bordo residual = `4 *` pivô de Schur, **identidade assinada**, sem positividade presumida.
- PRs #71–#75 de `geometry-of-numbers`: transporte para theta/Mellin com auditoria de no-gos locais, caudas, quatro pernas, proveniências, residual e completion. PR #75 prova `full_ledger_mellin`, `native_wronskian_full_mellin`, `critical_wronskian_in_ledger` para cada cutoff finito, não uma Gram positiva.

**Estado das branches em 23/10:** #75 é draft empilhada sobre #74 → #73 → #72 → #71; #41 é draft independente a partir de main. Não chamar teorema de #41 como se estivesse importável na branch de #75 sem resolver explicitamente integração/stack. Não alterar módulos históricos para forçar compilação.

## 2. Primeiro objetivo: completed pairing, dois parâmetros independentes

Tomar a porta material e a fonte **originais** da PR #75; aplicar o completamento original no nível de **vetores e pareamentos**, não somente em identidades escalares. Expandir a ação de câmera/quociente, derivada, fator de altura, dressing, companion e todos os termos mistos. O alvo deve ser uma igualdade de dois argumentos, antes de diagonalizar, tomar limite ou extrair momentos:

\[
  \mathcal K_{\mathrm{completed}}(z,w)
    = \text{pareamento completado da fonte integral original}.
\]

A expressão do lado direito deve nascer das pernas/canais transportados antes dos momentos. O registro da PR #75 não pode ser condensado apagando canais que se anulam apenas sob hipóteses especiais. O Green radial crítico igual a zero não é uma identidade de norma positiva.

**Aceitação parcial A:** provar que as duas maneiras de calcular o pareamento completado (fonte nativa e transporte theta/Mellin) coincidem, para todos os cutoffs finitos e parâmetros no domínio original. Identificar separadamente o defeito de completion, sem ajustá-lo ad hoc. Se houver um termo que permaneça, preservá-lo na equação com sua proveniência.

## 3. Segundo objetivo: identificar o kernel de momentos canônicos

Extrair os jets do pareamento completado e compará-los, sem alterar normalizações, com a sequência concreta

`canonicalCompletedNativeLogDerivativeMoment : ℕ → ℝ`.

Os primeiros testes são `h₀` (diagonal), `h₁` (cruzamento) e `h₂` (segundo momento); reusar a leitura centrada/normalizada original, não o Wronskiano bruto quando diferirem. Identificar todos os coeficientes, não só a soma numérica.

**Enunciado final desejado** (esquema de tipos, NÃO código compilado; `completedCarryFeature` ainda precisa ser definido da fonte original):

```lean
-- OBJETIVO, não um teorema existente.
-- A feature nasce exclusivamente da síntese original, nunca dos h_n.
-- E = Hilbert carrier físico completado adequado, com norma da fonte.

theorem canonical_moment_eq_original_completed_gram
    (i j : ℕ) :
    canonicalCompletedNativeLogDerivativeMoment (i + j) =
      Matrix.gram ℝ completedCarryFeature i j := by
  -- Desenvolver a igualdade polarizada da fonte PR #75,
  -- aplicar o completamento original, e extrair os jets.
  ...
```

**Não aceitar prova circular:** não definir `completedCarryFeature` usando Cholesky, a matriz Hankel, a sequência de momentos, alturas conhecidas, raízes de zeta, nem `PosDef`; não escolher por decreto um novo produto interno que faça o resultado verdadeiro. Pode ser que a forma assinada exija um passo adicional para isolar um carrier positivo: se não fechar, registrar o defeito exato em vez de postulá-lo zero.

## 4. Terceiro objetivo: positividade como CONSEQUÊNCIA

A partir da igualdade anterior, reusar sem duplicar provas:

```lean
-- Esquema da aplicação de um teorema JÁ EXISTENTE
hankelGram_posSemidef_of_gramRepresentation
  (moments := canonicalCompletedNativeLogDerivativeMoment)
  (feature := completedCarryFeature)
  (by
    intro i j
    exact canonical_moment_eq_original_completed_gram i j)
  N
```

(Os argumentos implícitos/namespaces exatos devem ser ajustados ao compilador da branch integrada.)

Para `PosDef`, provar adicionalmente a independência linear de todo prefixo da família `completedCarryFeature`; daí aplicar `hankelGram_posDef_of_gramRepresentation`. A transformação para Jacobi e o operador finito são **consumidores** desses certificados, não parte da sua demonstração.

## 5. Rota paralela para localizar precisamente o sinal: residual/Schur

Da PR #41, temos identidade assinada no residual:

\[
  E_{2(n+1)}(\mathrm{nativeResidualBoundary}_{s,n})=4d_{s,n}.
\]

No operador, `nativeSourceBoundary_all_pos_iff_sourceSchur` e `sourceMomentMatrix_all_posDef_iff_schur` já localizam as condições de sinal em toda ordem. Portanto, outra maneira de fechar o problema é mostrar positividade estrita da **energia do bordo completado original**, na direção residual correta, para todos `s ∈ {0,1}`, `n`, sem modificar a energia e sem confundi-la com a soma de normas positivas das pernas.

Não usar `PosDef` da Hankel-alvo como premissa nesse canal; isso seria circular. Os certificados finitos existentes (#69/#70) servem como canários, não como extrapolação silenciosa.

## 6. O que o primeiro PR seguinte deve entregar

**Título sugerido:** `Derivar o pareamento completado da fonte e testar o kernel canônico em dois argumentos`.

1. Importar exatamente o stack da PR #75 e os objetos de completamento genuínos.
2. Obter igualdade vetorial/polarizada de duas entradas antes da escalarização.
3. Calcular termos mistos de quociente, derivada, Gamma, readout e companion, conservando quatro campos do ledger.
4. Testar identidade dos jets `(0,0)`, `(0,1)`, `(1,1)`, comparando com `h0`, `h1`, `h2` nativos.
5. Se falhar, fornecer contraexpressão EXATA do defeito, não um simples `PARTIAL`; inspecionar especificamente termos de sobreposição C2–C3 da #74.
6. Se fechar, generalizar a todos os jets `(i,j)` e tentar fatoração quadrática na energia ORIGINAL em R².
7. Só depois importar os consumidores genéricos `MomentGramPositivity` e os resultados de #41 para propagar o sinal à Jacobi e ao operador existente.
8. Auditar `#print axioms`, dependências transitivas, `lake build --wfail`, controles para fonte assinada; não usar `sorry`, `admit`, novos axiomas, simplificação sem equivalência ou hipóteses de positividade disfarçadas.

**Classificação atual honesta:** reconstrução aritmética vertical **PROVADA**; compatibilidade de massa crítica **PROVADA sob hipóteses explícitas**; operador e resultados espectrais condicionais **CONSTRUÍDOS/FORMALIZADOS**; ledger Mellin finito **TRANSPORTADO**; identidade positiva de todos os momentos com uma única síntese física **ABERTA**.

## 7. Referências

- https://github.com/thiagomassensini/geometry-of-numbers/pull/41
- https://github.com/thiagomassensini/geometry-of-numbers/pull/74
- https://github.com/thiagomassensini/geometry-of-numbers/pull/75
- https://github.com/thiagomassensini/geometry-of-numbers/blob/main/GeometryOfNumbers/Analysis/MomentGramPositivity.lean
- https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean
- https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpPrimeDepthLogWaveBridge.lean