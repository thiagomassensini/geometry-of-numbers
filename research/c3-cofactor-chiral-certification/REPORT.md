# Certificação cofactorial C3 e compensação quiral

**Classificação:** PARTIAL. A identidade cofactorial e a porta condicional de sinal estão formalizadas. A inclusão dos coeficientes nativos completos nas caixas estreitas ainda não foi provada; portanto, não há uma certificação GREEN do terceiro pivô.

## A. Origem e proveniência

- Repositório: `thiagomassensini/geometry-of-numbers`; esta continuação está na branch `agent/c3-cofactor-chiral-certification-20261112-next`.
- Esta etapa parte de `origin/main` em `e4f5de51cad523963a327c8295067f88fc7855fa` (PR #321 integrada), preservando os trabalhos anteriores de #316–#320.
- Pins não alterados: Lean 4.32.0, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- PRs #316 e #317 já estavam integradas. As definições da completion, Gamma, chart, fonte e stencil C3 original são reutilizadas; pesos e fatores não foram modificados.
- A validação direta usa as dependências Lean já compiladas dos dois repositórios locais. A árvore de trabalho original, que tinha mudanças preexistentes, permaneceu intocada.
- O transporte quiral importa `CompletedHeadEight`, cuja dependência `ThirdSourcePrefix` vem do cache de #146; o SHA-256 da fonte `research/c3-tilt-prime/ThirdSourcePrefix.lean` coincide com a cópia da branch de #146 usada para compilar esse cache (`c3d5e49a945942a92d26776857a721a8d82eff706d13e917ee2a6e88eb4e5b5e`).

## B. Resultados demonstrados em Lean

- `GeneralCofactorIdentity.lean` prova para todo anel comutativo e todo tamanho finito a identidade do determinante bordeado, incluindo prefixos singulares e o caso de prefixo vazio. Para prefixo simétrico, `border_quadratic_eq_directionalEnergy` identifica a energia definida pelos coeficientes com `vᵀBv`, e `border_directional_identity` prova `det B=D E(u)-rᵀadj(A)r` para toda direção `u`, sem inversa. O módulo também prova `B*w = (0,…,0,det B)` e `wᵀBw = det(A)*det(B)` para `w=(-adj(A)b,det A)`, sem hipótese de positividade.
- `border_det_three_by_three` e `cofactorVector_three_by_three` recuperam, respectivamente, `D*g-d*e²+2*b*e*f-a*f²` e o vetor explícito `[b*f-d*e,b*e-a*f,D]` da fórmula geral.
- `odd_third_prefix_isUnit_from_completed_c3` reutiliza a certificação da fonte C3 completada para provar a invertibilidade do prefixo ímpar 2×2. A prova depende do head C3 e dos coeficientes de ordem baixa, não do sinal do terceiro pivô.
- `odd_third_critical_balance_tendsto` e `odd_third_scaled_relative_deficit_tendsto` especializam o transporte quiral ao bloco ímpar de ordem 11 sem hipótese adicional de invertibilidade do prefixo. `odd_third_gap_coefficient_pos_iff` identifica o sinal do coeficiente de déficit com o sinal do Schur; `odd_third_relative_deficit_eventually_pos` continua condicional a esse sinal.
- `odd_third_cofactor_identity`: determinante do bloco simétrico 3×3 igual ao determinante do prefixo vezes a energia residual menos o termo da adjugata. Não requer que o prefixo seja invertível.
- `odd_third_cofactor_vector_identity` e `odd_third_cofactor_vector_quadratic`: identidades exatas para o vetor cofactorial.
- O módulo `SchurGate.lean` prova que a margem cofactorial positiva implica positividade definida do bloco 3×3 sob as hipóteses explícitas de prefixo positivo e determinante do prefixo positivo.
- `candidate_cofactor_margin_lower_positive` prova a porta para as caixas racionais candidatas já existentes. A inclusão dos coeficientes da fonte C3 nessas caixas não foi demonstrada; a porta, isoladamente, não certifica a fonte.
- `completed_tail48_jet_error_through_twelve`: a contribuição da cauda da completion original em `M=48` tem norma de jato até ordem 12 limitada por `10⁻²⁰`.
- `head48_reference_contains` e `native_gamma_thirteen_boxes` certificam, separadamente, as caixas do head C3/48 e os jatos Gamma até ordem 12.
- `completed_jet_box_exact48` propaga por operações intervalares racionais exatas as caixas dos fatores originais, do head e dos centros Gamma de referência, até os jatos completados finitos de ordem 12. A prova não arredonda os intervalos entre operações. Ela ainda não inclui o erro de substituir os centros Gamma pela Gamma nativa.
- `GammaHeadCrosswalk.lean` demonstra a fase exata do head completado, o erro da substituição pela Gamma nativa como uma soma finita ponderada pelos jatos reais do head, e o transporte desse erro junto com a cauda `M=48` para os jatos da característica completada original. O único bound Gamma usado é `native_gamma_thirteen_boxes`.

## C. Identidade e porta cofactorial

Em dimensão arbitrária, para `A : Matrix (Fin n) (Fin n) R`, `b : Fin n → R` e o bloco simétrico bordeado

\[
B=\begin{pmatrix}A&b\\b^{\mathsf T}&d\end{pmatrix},\qquad D=\det A,
\]

o novo módulo estabelece a identidade sem divisão

\[
\det B=Dd-\sum_i b_i(\operatorname{adj}(A)b)_i.
\]

Ela vale mesmo para `D=0`; a prova usa expansão de Laplace e uma permutação cíclica dos menores para Cramer. Para qualquer `u`, com `v=(u,1)` e `r=Au+b`, também prova `det B=D(vᵀBv)-rᵀadj(A)r`, identificando `vᵀBv` com `directionalEnergy`. Para `w=(-adj(A)b,D)`, vale `B w=(0,…,0,det B)` e `w^{\mathsf T}Bw=D\det B`. São identidades algébricas, não desigualdades de sinal.

Para

\[
B=\begin{pmatrix}a&b&e\\b&d&f\\e&f&g\end{pmatrix},\quad
D=ad-b^2,
\]

e a direção crítica `(x,y)`, o arquivo prova a igualdade exata

\[
\det B=D\,\mathcal E-\mathcal R_{\rm adj},
\]

onde `\mathcal E` é a energia quadrática deslocada e `\mathcal R_adj` é o resíduo da adjugata definido em `CofactorIdentity.lean`. A identidade vale também quando `D=0`. O teorema de positividade usa uma desigualdade estrita independente para a margem; nenhuma equivalência de sinal é tratada como prova do sinal.

O controle sintético negativo continua ativo: a fonte algébrica negativa já existente tem bloco não positivo. As provas novas não promovem positividade para fontes arbitrárias.

## D. Fonte C3, head e cauda

A construção conserva a fonte C3 original e sua completion. O head usa 48 células e o stencil exato de 24 pontos de bordo; a decomposição cabeça/cauda é literal. O controle da cauda mantém os fatores originais e é válido até a ordem 12.

O transporte de `completed_jet_box_exact48` cobre o head finito convolvido com os centros racionais Gamma. `completed_native_jet_reference_error48` fecha a ligação algébrica e quantitativa restante: ele controla a troca pela Gamma nativa por uma soma explícita de `|leftRealJet48 j|` vezes `10⁻²⁴`, e então acrescenta a cota original de cauda `10⁻²⁰`. `finite_completed_reference_jet_phase48` conserva a fase `i^r`, e o teorema final compara diretamente com `sourceJet r completedNativeOperatorCharacteristic`. O cálculo intervalar exato reproduzível usa as caixas Lean de `leftRealJet48` para majorar essa soma.

## E. Terceiro pivô C3

**Setor par (`s=0,n=2`): PARTIAL.** A identidade cofactorial e os controles anteriores estão disponíveis; uma nova margem geométrica não foi certificada.

**Setor ímpar (`s=1,n=2`): PARTIAL.** A porta cofactorial condicional está provada, mas as caixas nativas completas ainda não foram transportadas até ela.

O script `diagnose_completed_boxes48.py` refaz com `fractions.Fraction` a propagação exata das caixas racionais do head e dos centros Gamma, acrescentando tanto o erro Gamma fornecido por `completed_native_jet_reference_error48` quanto a cauda já provada. A permissão Gamma mais larga, até a ordem 12, é aproximadamente `4.7787520913 × 10⁻²⁵`; a cauda `10⁻²⁰` continua dominando. O cálculo reporta para a margem ímpar aproximadamente

\[
[-9.10708079037569\times10^{-32},\;1.00488624771212\times10^{-31}],
\]

que contém zero. A inclusão do jato nativo completo na vizinhança de erro é provada em Lean; a avaliação final da margem é um diagnóstico racional reproduzível, não um teorema Lean de positividade. Para concluir será necessária uma inclusão mais estreita que preserve dependências entre jatos de ordem baixa e coeficientes Gamma de ordem alta, ou uma estimativa direta da margem.

## F. Contraexemplos e limitações

- A identidade da adjugata é algébrica e não força sinal.
- As caixas candidatas de `IntervalGate.lean` implicam uma margem positiva apenas sob a hipótese de que os coeficientes estão nessas caixas. Essa hipótese de inclusão segue aberta para a fonte C3 nativa.
- O intervalo diagnóstico que cruza zero não refuta positividade da fonte: ele mostra apenas que as caixas e o cálculo intervalar atuais não a certificam.
- Não se reivindica positividade all-order, equivalência com uma Gram física positiva, ou uma prova independente via theta.

## G. Obrigações ainda abertas

- Certificar uma margem cofactorial ímpar estritamente positiva pela fonte original; a faixa rigorosa existente ainda contém zero.
- O transporte quiral de ordem 11 está formalizado; eventual positividade do déficit continua dependente da desigualdade de sinal do Schur, que não foi demonstrada.

## H. Validação

- `GammaThirteen.lean`: compilado com `lean -DwarningAsError=true`; auditoria de axiomas reportou apenas `propext`, `Classical.choice` e `Quot.sound`.
- `CompletedBoxes48.lean`: compilado com `lean -DwarningAsError=true`; `chart_jet_box_exact`, `reciprocal_jet_box_exact`, `left_jet_box_exact48` e `completed_jet_box_exact48` usam apenas `propext`, `Classical.choice` e `Quot.sound`.
- `GammaHeadCrosswalk.lean`: compilado com `lean -DwarningAsError=true`; os quatro teoremas públicos usam apenas `propext`, `Classical.choice` e `Quot.sound`.
- `GeneralCofactorIdentity.lean`: compilado diretamente com warnings como erros; a auditoria dos dez teoremas públicos reportou apenas `propext`, `Classical.choice` e `Quot.sound`.
- `ChiralOrder11.lean`: compilado diretamente com warnings como erros; os cinco teoremas públicos usam apenas `propext`, `Classical.choice` e `Quot.sound`.
- `bash research/c3-cofactor-chiral-certification/validate.sh`: passou explicitamente pelos 20 módulos, com warnings como erros, impressão dos axiomas públicos, regressões e diagnóstico racional. Os resultados públicos novos dependem apenas de `propext`, `Classical.choice` e `Quot.sound`.
- `bash research/c3-odd-head-source/validate.sh`: passou nos oito módulos que sustentam o prefixo ímpar C3, incluindo `CompletedHeadEight.lean`; não encontrou atalhos de prova nem axiomas novos.
- `lake build --wfail`: passou em todos os 8.850 alvos.
- `bash scripts/audit-foundation.sh`, `bash scripts/audit-geometry.sh` e `bash scripts/audit-analysis.sh`: passaram. Fundação não encontrou axiomas; geometria respeitou seu conjunto permitido; análise permitiu apenas os axiomas padrão.
- `git diff --check` e a varredura de `sorry`, `admit`, `native_decide` e declarações `axiom` nos módulos da missão passaram.
- Commit novo `1b1b05a` (`feat(c3): add directional cofactor and odd order-11 transport`) foi validado e enviado para a branch da PR.
- `diagnose_completed_boxes48.py`: aritmética racional exata, reproduzível com Python padrão; combina caixas de jatos do head validadas em Lean, a cota Gamma transportada em Lean e a cota original da cauda. Sua saída diagnóstica não afirma positividade.
- Commit de retomada: `18da645 feat(c3): propagate exact completed head coefficient boxes` (enviado à branch remota).
- PR #318 foi mesclada em `main` em 2026-11-12; SHA do merge: `21c24415de48b184f5ad0498f9ac28e7c64a8195`. A PR continha os commits `18da645` e `64a6169` e manteve a classificação PARTIAL.
- PR #319, apenas de proveniência, foi mesclada em `main` no SHA `d4df30eb426653121c42cfe1bcfed68d3ce9bfed`.
- Commit do crosswalk Gamma/cauda: `f93a34a2eaa9ee6162758231b7a7171160009556`, enviado à branch `agent/c3-completed-crosswalk-20261112`.
- PR #320 foi mesclada em `main` em 2026-11-12; SHA do merge: `f5b403f31cc63a1f1a4af069180b0516f88841f1`. Ela incluiu o crosswalk, o relatório atualizado e o diagnóstico exato, mantendo PARTIAL.
- Não foram usados `sorry`, `admit`, `native_decide` ou axiomas novos.
- Continuação desta branch: `GeneralCofactorIdentity.lean` formaliza a identidade direcional geral; `ChiralOrder11.lean` transporta o limite quiral usando o prefixo C3 já certificado. A certificação do terceiro pivô segue PARTIAL, sem novo resultado de sinal.

## I. Próxima missão mínima

Preservar as dependências entre os jatos da cabeça C3 e os coeficientes Gamma de ordem alta ao avaliar a margem cofactorial ímpar; a faixa rigorosa atual ainda contém zero.
