# Certificação cofactorial C3 e compensação quiral

**Classificação:** PARTIAL. A identidade cofactorial e a porta condicional de sinal estão formalizadas. A inclusão dos coeficientes nativos completos nas caixas estreitas ainda não foi provada; portanto, não há uma certificação GREEN do terceiro pivô.

## A. Origem e proveniência

- Repositório: `thiagomassensini/geometry-of-numbers`; branch `agent/c3-cofactor-chiral-certification-20261112`.
- Base da branch: `origin/main` em `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`.
- Pins não alterados: Lean 4.32.0, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- PRs #316 e #317 já estavam integradas. As definições da completion, Gamma, chart, fonte e stencil C3 original são reutilizadas; pesos e fatores não foram modificados.
- A validação direta usa as dependências Lean já compiladas dos dois repositórios locais. A árvore de trabalho original, que tinha mudanças preexistentes, permaneceu intocada.

## B. Resultados demonstrados em Lean

- `odd_third_cofactor_identity`: determinante do bloco simétrico 3×3 igual ao determinante do prefixo vezes a energia residual menos o termo da adjugata. Não requer que o prefixo seja invertível.
- `odd_third_cofactor_vector_identity` e `odd_third_cofactor_vector_quadratic`: identidades exatas para o vetor cofactorial.
- O módulo `SchurGate.lean` prova que a margem cofactorial positiva implica positividade definida do bloco 3×3 sob as hipóteses explícitas de prefixo positivo e determinante do prefixo positivo.
- `candidate_cofactor_margin_lower_positive` prova a porta para as caixas racionais candidatas já existentes. A inclusão dos coeficientes da fonte C3 nessas caixas não foi demonstrada; a porta, isoladamente, não certifica a fonte.
- `completed_tail48_jet_error_through_twelve`: a contribuição da cauda da completion original em `M=48` tem norma de jato até ordem 12 limitada por `10⁻²⁰`.
- `head48_reference_contains` e `native_gamma_thirteen_boxes` certificam, separadamente, as caixas do head C3/48 e os jatos Gamma até ordem 12.
- `completed_jet_box_exact48` propaga por operações intervalares racionais exatas as caixas dos fatores originais, do head e dos centros Gamma de referência, até os jatos completados finitos de ordem 12. A prova não arredonda os intervalos entre operações. Ela ainda não inclui o erro de substituir os centros Gamma pela Gamma nativa.

## C. Identidade e porta cofactorial

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

O transporte de `completed_jet_box_exact48` cobre o head finito convolvido com os centros racionais Gamma. Faltam duas ligações antes de obter caixas dos coeficientes nativos `c₀,…,c₆`: o erro da Gamma nativa multiplicada pelo head e a passagem dos jatos da completion completa para os coeficientes da fonte com a fase normalizada. A cota de cauda existente pode então ser incorporada com seu erro original.

## E. Terceiro pivô C3

**Setor par (`s=0,n=2`): PARTIAL.** A identidade cofactorial e os controles anteriores estão disponíveis; uma nova margem geométrica não foi certificada.

**Setor ímpar (`s=1,n=2`): PARTIAL.** A porta cofactorial condicional está provada, mas as caixas nativas completas ainda não foram transportadas até ela.

O script `diagnose_completed_boxes48.py` refaz com `fractions.Fraction` a propagação exata das caixas racionais do head e dos centros Gamma, acrescentando a margem de cauda já provada. Ele reporta para a margem ímpar aproximadamente

\[
[-9.10708079037569\times10^{-32},\;1.00488624771212\times10^{-31}],
\]

que contém zero. Este cálculo não inclui a substituição dos centros pela Gamma nativa e não é uma prova Lean nem uma afirmação sobre o sinal da fonte completa. Ele mostra que a propagação intervalar independente atual não fecha a porta; para concluir será necessária uma inclusão mais estreita ou uma estimativa que preserve correlações entre coeficientes.

## F. Contraexemplos e limitações

- A identidade da adjugata é algébrica e não força sinal.
- As caixas candidatas de `IntervalGate.lean` implicam uma margem positiva apenas sob a hipótese de que os coeficientes estão nessas caixas. Essa hipótese de inclusão segue aberta para a fonte C3 nativa.
- O intervalo diagnóstico que cruza zero não refuta positividade da fonte: ele mostra apenas que as caixas e o cálculo intervalar atuais não a certificam.
- Não se reivindica positividade all-order, equivalência com uma Gram física positiva, ou uma prova independente via theta.

## G. Obrigações ainda abertas

- Provar o crosswalk entre `completedHead48` e os jatos reais convolvidos com a Gamma nativa, com uma cota quantitativa útil para o erro Gamma.
- Incorporar a cauda `M=48` às caixas dos coeficientes nativos e provar a inclusão desses coeficientes no Lean.
- Fechar a margem cofactorial odd com uma desigualdade independente. A propagação de caixas independentes atual não basta.
- Fazer o transporte chiral de ordem 11, que não foi concluído nesta branch.

## H. Validação

- `GammaThirteen.lean`: compilado com `lean -DwarningAsError=true`; auditoria de axiomas reportou apenas `propext`, `Classical.choice` e `Quot.sound`.
- `CompletedBoxes48.lean`: compilado com `lean -DwarningAsError=true`; `chart_jet_box_exact`, `reciprocal_jet_box_exact`, `left_jet_box_exact48` e `completed_jet_box_exact48` usam apenas `propext`, `Classical.choice` e `Quot.sound`.
- `validate.sh`: recompilou os 18 módulos da pesquisa com warnings como erros, auditou axiomas, não encontrou placeholders proibidos e executou o diagnóstico racional.
- `lake build --wfail`: sucesso em todos os 8.857 alvos do projeto.
- `bash scripts/audit-foundation.sh`, `bash scripts/audit-geometry.sh` e `bash scripts/audit-analysis.sh`: todos passaram. Fundação não encontrou axiomas; geometria respeitou seu conjunto permitido; análise respeitou os axiomas padrão.
- `git diff --check` e a varredura de `sorry`, `admit` e `native_decide` passaram.
- `diagnose_completed_boxes48.py`: aritmética racional exata, reproduzível com Python padrão; sua saída é diagnóstica e não substitui a prova Lean de inclusão da fonte completa.
- Commit de retomada: `18da645 feat(c3): propagate exact completed head coefficient boxes` (enviado à branch remota).
- PR #318 foi mesclada em `main` em 2026-11-12; SHA do merge: `21c24415de48b184f5ad0498f9ac28e7c64a8195`. A PR continha os commits `18da645` e `64a6169` e manteve a classificação PARTIAL.
- Não foram usados `sorry`, `admit`, `native_decide` ou axiomas novos.

## I. Próxima missão mínima

Formalizar um único crosswalk quantitativo de `sourceJet r completedHead48` para a convolução de `leftRealJet48` com os jatos Gamma nativos, e então combinar esse erro com o limite de cauda já provado para verificar em Lean se as caixas resultantes separam a margem cofactorial de zero.
