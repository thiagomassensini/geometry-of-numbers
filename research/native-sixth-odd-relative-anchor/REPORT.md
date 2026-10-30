# Margem radial relativa da sexta direção ímpar

**Resultado: certificado finito para a direção crítica de seis jets ímpares; PARTIAL para a investigação all-order.** A prova usa a fonte física completada e conserva seus 36 cruzamentos. Para índices radiais suficientemente grandes, o desconto variacional e as duas caudas somados são inferiores a 2% da energia física da direção racional experimental. A direção crítica original domina então sua própria cauda.

## A — Base e dependências

Base: `geometry-of-numbers`, commit `86fd2191a601672e8a96cea5dffd889a7dd41c57`, PR #137, empilhada sobre #136, #135 e #134. Os resultados anteriores de `finite_odd_critical_anchor_of_relative_budget` e da PR #41 fornecem, respectivamente, o critério relativo e a identificação da direção crítica com o Schur e com o bordo. O prefixo ímpar antigo de tamanho cinco é positivo definido pelo teorema anterior `CarryThetaPattern.odd_source_five_posDef`; sua inversibilidade é usada explicitamente.

A testemunha racional de seis colunas e as caixas theta dos momentos até \(h_{11}\) vêm da investigação histórica `research/sixth-odd-twelve-sources`. Seus coeficientes de teste são dados racionais não confiados, e a inclusão das caixas é provada na fonte original. O cálculo usa a coluna de teste, as caixas dos pareamentos e os resultados de intervalo, não os antigos teoremas de positividade do sexto pivô. A auditoria transitiva bloqueia explicitamente esses teoremas, inclusive os pivôs transformados e a positividade prévia do bloco de seis.

A fonte e a métrica física não foram alteradas. A representação theta fornece certificados analíticos de entrada; esta não é uma prova de que a geometria sozinha determina o sinal sem essa certificação.

## B — Margem experimental e correção variacional

A direção experimental \(c\) é a sexta coluna da matriz racional histórica dividida por \(10^{18}\), com última coordenada igual a 1. `twelve_trial_form_lower` prova

\[
 Q(c)>10^{-36}.
\]

A forma \(Q\) inclui todos os pares ordenados \((i,j)\) dos seis jets: são 36 cruzamentos, inclusive os antigos–novos. Essa desigualdade por si só não garante que o pivô de Schur seja positivo.

`oldCoordinate` usa o bloco inicial de cinco colunas da mesma testemunha para conferir o prefixo antigo. `transformedOld_entry` prova que seu bloco é precisamente a congruência da matriz original, e `oldCoordinate_isUnit` prova que a mudança de coordenadas é invertível. Nas caixas do bloco transformado, cada diagonal é pelo menos \(1/4\) e cada cruzamento fora da diagonal tem módulo no máximo \(1/100\). Preservando os 20 cruzamentos fora da diagonal, `transformed_old_coercive` estabelece

\[
 y^T B y\ge \tfrac15 y^T y.
\]

`congruence_inverse_residual` prova a invariância exata de \(r^TA^{-1}r\). Os cinco componentes do resíduo transformado são identificados com os cruzamentos originais entre o prefixo e a sexta coluna, sem truncá-los. Com suas caixas, `original_inverse_correction_upper` conclui

\[
 r^TA^{-1}r\le10^{-38}.
\]

Essa cota é independente do sinal do novo pivô; a positividade do prefixo já estabelecido não deve ser confundida com a positividade do bloco ampliado.

## C — Balanço físico e bordo

`finite_energy_direct_error` mantém a fonte original e controla a diferença entre sua energia de uma escala e \(Q\). As duas caudas radiais tendem a zero. Os teoremas novos demonstram que, eventualmente,

\[
 D_k(c)>9\cdot10^{-37},\qquad
 r^TA^{-1}r+E_k(c)+2E_k(c_*)<\tfrac1{50}D_k(c),
\]

onde \(c_*\) é a direção crítica por inverso do bloco antigo e cada \(E_k\) é a cota radial completa da própria fonte correspondente. Assim `twelve_critical_anchor_eventually` prova \(E_k(c_*)<D_k(c_*)\) para todo \(k\) suficientemente grande. O teorema é existencial quanto ao limiar: **não se afirma um índice numérico explícito para esta ordem**.

`twelve_critical_form_positive_from_anchor` deduz a positividade do limite pela âncora física. `sixth_odd_schur_positive_via_relative_source` transporta-a ao sexto pivô ímpar, e `twelve_original_boundary_positive_via_relative_source` à energia de bordo original, com o fator quatro da PR #41. Esse sinal já era conhecido historicamente; a contribuição desta rodada é uma nova rota pela margem relativa da fonte completa, com uma cota explícita para o desconto e sem o sinal novo como premissa.

O percentual de 2% mede o orçamento de transporte em relação à energia experimental. Não é uma contração uniforme dos canais incidente e retornado nem uma constante válida para todas as ordens.

## D — Estado geral, validação e proveniência

A investigação não prova uma lei all-order. O critério relativo funciona em ordem arbitrária como implicação, mas ainda falta obter suas hipóteses independentemente para uma família de ordens. Também não se estabeleceu aqui o análogo do orçamento radial para o setor par, nem uma identificação global com espectro ou alturas.

Usa-se Lean `v4.32.0` e o operador em `bfeb10fd2425400fa38139903d12bf0599f02e53`. `validate.sh` recompila os módulos novos com avisos como erros, executa `Audit.lean` e `lake build --wfail`, e busca `sorry`, `admit`, `native_decide` e novas declarações `axiom`. São reutilizados compilados de pesquisa anteriores; não é uma reconstrução histórica a partir de clone vazio. A auditoria permite positividade dos momentos iniciais e do prefixo antigo, mas veta resultados de positividade do sexto pivô e do bloco de seis como entradas. A recompilação dos oito módulos de pesquisa e `lake build --wfail` passaram (8.849 tarefas). A auditoria das sete raízes percorreu 65.468 dependências e encontrou apenas `propext`, `Classical.choice` e `Quot.sound`. Não foram encontrados atalhos ou novos axiomas. O manifesto comparou 253 objetos compilados com a worktree anterior, sem divergências. Logs e hashes ficam em `evidence/`.

## E — Próxima obrigação mínima

Determinar uma cota racional para o orçamento das duas caudas desta direção crítica, de modo a trocar o limiar eventual por um índice inteiro verificável. Para a lei geral, buscar um controle da coercividade e do resíduo transformados que seja obtido da fonte, dependa explicitamente da ordem e não receba a positividade do pivô novo por outro nome. A cota sem sinal para famílias finitas da PR #137 é uma ferramenta para essa busca, não a conclusão.
