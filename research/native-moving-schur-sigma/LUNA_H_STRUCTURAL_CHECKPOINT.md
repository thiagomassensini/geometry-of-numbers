# Luna H — checkpoint estrutural (14/11/2026)

## Base e escopo

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch isolada: `codex/luna-h-sigma-schur-quartic-sign-20261114`.
- Base: `main` em `ca621765d4a4c1c1254a7df282d95926f29d362f`.
- A PR #331 permanece aberta, mas esta entrega não a importa nem depende dela. A compilação usa a fonte Carry fixada em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Nenhum checkout ou branch preexistente foi alterado.

Esta entrega conclui a etapa estrutural obrigatória antes de qualquer cálculo intervalar pesado. Ela trabalha com `sigmaSchur` e `canonicalCriticalVector` originais, sem trocar a fonte ou normalização.

## Resultados Lean novos

Módulo: `SigmaSchurQuarticRemainder.lean`.

1. `sigmaSchur_fixed_direction_exact`: para todo `d` em que a matriz de prefixo original é invertível, o pivô móvel é a forma quadrática da direção central crítica fixa menos a energia da direção antiga reacoplada. A direção fixa é literalmente `canonicalCriticalVector`.
2. `sigmaResidualCoupling_eq_matrix_mul_reacoupled`: o residual completo de acoplamento é exatamente `A(d) r(d)`.
3. `sigmaSchur_fixed_direction_residual_form`: identidade equivalente à fórmula solicitada,
   `p(d) = v₀ᵀ H(d) v₀ − w(d)ᵀ A(d)⁻¹ w(d)`.
   Todos os acoplamentos antigos/novos permanecem no termo `w`; nenhum termo cruzado foi removido.
4. `sigmaSchur_le_fixed_direction_of_posDef`: sob invertibilidade e positividade definida do prefixo, a correção é não negativa e o pivô móvel fica abaixo da forma da direção fixa.
5. `sigmaSchur_analyticAt_of_prefix`: a analiticidade local do pivô é derivada dos jets originais e da fórmula por determinante/cofatores da inversa matricial, sem uma hipótese de regularidade adicional.
6. `sigmaSchur_third_deriv_center_eq_zero`: a terceira derivada transversal central zera pela paridade já formalizada.
7. `exists_sigmaSchur_quartic_remainder`: para cada setor `s` e ordem `n` com prefixo central invertível, existem `δ > 0` e `B ≥ 0`, com `δ < 1/2`, tais que
   `|p(d) − p(0) + 𝒜[s,n] d²| ≤ B d⁴` para todo `|d| ≤ δ`.

A amplitude `sigmaSchurCurvatureAmplitude` é a soma original de curvatura de `moving_schur_curvature_expanded`; o teorema legado fornece `p''(0) = -2 𝒜[s,n]`. Nenhum sinal de `𝒜[s,n]` é assumido ou concluído.

O resto quartico vem do teorema de Taylor em intervalo compacto aplicado ao pivô analítico local. O raio e a constante são existenciais, sem estimativa numérica efetiva nesta etapa.

## Dependências reutilizadas

- `moving_schur_curvature_expanded` e `sigmaSchur_even`.
- `exists_sigma_prefix_neighborhood` e `sigma_matrix_symm`.
- `sourceMomentSchur_sewing_of_isUnit`.
- `sigma_log_jet_analytic_center` e `sigma_log_jet_center_eq_canonical`.
- Taylor com resto de ordem quatro do Mathlib.

A auditoria Lean das quatro declarações centrais reporta apenas `[propext, Classical.choice, Quot.sound]`. Não foi introduzido axioma, `sorry` ou `admit`.

## Compilação

Compilado com `-DwarningAsError=true` usando `compile_sigma_pade.sh SigmaSchurQuarticRemainder`, a fonte Carry fixada acima e os caches de pesquisa necessários. A compilação terminou sem warnings ou erros. A compilação C1 anterior da cadeia de origem também terminou com `warningAsError` habilitado.

## Limites desta entrega

- Ainda não existem caixas racionais/intervalares Lean para os jets, pivôs ou prefixos 6×6 em `d ≠ 0`.
- Os valores do pacote Python para `n=6`, `s=0,1`, inclusive os limiares aproximados `4.98526775×10⁻⁴` e `1.25172592×10⁻⁴`, permanecem apenas comparações experimentais.
- Portanto, não há nesta etapa certificado de sinal para os blocos 7×7, intervalo formal de cruzamento, unicidade de cruzamento ou afirmação sobre a primeira dimensão que perde semidefinição positiva.
- A ponte Carry/C2/Jordan usada no centro não foi transportada para `d ≠ 0`.

## Próximo passo

Construir um gate de sinal quantitativo a partir da direção crítica fixa e do termo de reacoplamento, depois descarregar as caixas para `s=0,1`, `n=6` nos intervalos racionais propostos. Primeiro verificar positividade do prefixo 6×6 durante o intervalo; para a extremidade negativa, testar `p(d) ≤ v₀ᵀH(d)v₀` antes de limitar o reacoplamento.
