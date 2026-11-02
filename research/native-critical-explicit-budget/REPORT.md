# Orçamento radial explícito da direção crítica ímpar

**Classificação: PARTIAL para o problema all-order; certificado explícito para a família finita já tratada.** A PR #136 obteve uma âncora física para a quinta direção ímpar a partir de um índice dependente de um orçamento real da fonte. Este trabalho limita esse orçamento por uma constante racional e produz um índice natural explícito.

## A — O que já existia

A base é o commit `330588425269895c55389eec067885ec4d75d05c` da PR #136, empilhada sobre as PRs #135 e #134. O teorema `finite_critical_transfer` liga a energia física experimental à energia da direção crítica, mantendo a correção \(r^TA^{-1}r\) e as duas caudas. A matriz antiga de ordem quatro é invertível a partir de um certificado anterior; o sinal do novo pivô não é hipótese. A PR #41 fornece a identificação exata com a direção crítica e o transporte para o bordo nativo.

A entrada analítica continua sendo a mesma da PR #136: caixas theta dos momentos originais. Elas são usadas como certificados de intervalos, sem modificar a fonte nem supor que a representação theta seja a origem da geometria. Os compilados históricos foram reaproveitados; a prova não é uma reconstrução limpa de toda a cadeia histórica.

## B — Novo corte e comparação relativa

Para a família de cinco jets ímpares, a direção racional \(c\) tem \(D_k(c)>6\cdot10^{-30}\) a partir de \(k_0=10^{22}-1\). Aqui \(D_k\) é a parte real do pareamento quiral da fonte física completa, na normalização preexistente. Não se trata de postular que uma diferença de energias tenha sinal positivo.

`scaled_inverse_apply` prova a mudança de coordenadas do solve do bloco antigo. As 16 entradas de sua adjunta, o determinante e todos os quatro resíduos são controlados pelas mesmas caixas já existentes. `correction_bounded` e `critical_coefficient_bounded` provam que os cinco coeficientes da direção crítica original têm módulo no máximo 2. A mudança diagonal serve apenas à verificação dos intervalos.

`critical_family_budget_rational` e `critical_error_at_numeric_cutoff` deduzem

\[
 C_*\le 25\cdot2^2\cdot10^{10}=10^{12},\qquad
 E_k(c_*)\le10^{-32}\quad(k\ge k_0).
\]

Como a expansão da fonte usa o passo \(1/(k+1)\), a cota é aplicada sem apagar cruzamentos. `critical_anchor_after_numeric_cutoff` prova para todo \(k\ge k_0\) que \(E_k(c_*)<D_k(c_*)\), com um índice natural explícito. A fonte é exatamente a direção crítica original, e não a direção racional experimental. Além disso, `critical_energy_lower_after_numeric_cutoff` prova \(D_k(c_*)>5\cdot10^{-30}\) nessa faixa.

`ten_relative_budget_after_numeric_cutoff` certifica ainda, para todo \(k\ge k_0\),

\[
 r^TA^{-1}r+E_k(c)+2E_k(c_*)<\tfrac1{100}D_k(c).
\]

O fator 1% compara os custos de transporte com a energia física experimental. Ele **não** é uma margem fixa entre as energias incidente e retornada; não contradiz o no-go anterior para esse outro tipo de contração.

## C — O que se estende a ordens finitas

`finite_family_budget_bound` vale para qualquer família finita de jets ímpares: se os coeficientes têm módulo no máximo \(L\) e cada uma das constantes dos pares fica abaixo de \(M\), então

\[
 C(S,c)\le |S|^2L^2M.
\]

`finite_family_direct_budget_bound` transporta essa cota para o erro radial da fonte completa. Todos os pares ordenados são incluídos antes da estimativa em valor absoluto; \(L\) e \(M\) podem depender da família e da ordem. A cota é absoluta e não determina o sinal.

`finite_odd_critical_anchor_of_relative_budget` registra um critério suficiente em qualquer ordem ímpar finita: quando o prefixo antigo é invertível, a energia experimental é positiva e o conjunto de correção e caudas é inferior a uma fração \(\rho<1\) da energia experimental, a âncora crítica supera sua cauda. `ten_anchor_via_relative_budget` aplica o critério ao caso concreto com \(\rho=1/100\).

Essa hipótese relativa é uma obrigação matemática, não uma propriedade provada para toda ordem. A identificação de uma família física que a satisfaça uniformemente ou com margens controladas por ordem continua aberta. Não há aqui um teorema correspondente para o setor par.

## D — Verificações e proveniência

Os módulos novos usam Lean `v4.32.0` e o `carry-self-adjoint-operator` em `bfeb10fd2425400fa38139903d12bf0599f02e53`. O script `validate.sh` recompila os módulos novos com avisos como erro, executa `lake build --wfail`, executa `Audit.lean` e procura `sorry`, `admit`, `native_decide` e novas declarações `axiom`. O script pressupõe os caches de pesquisa da cadeia anterior e o ambiente do operador; não é uma prova de reconstrução a partir de clone vazio.

A recompilação dos seis módulos de pesquisa e o `lake build --wfail` passaram (8.849 tarefas). A auditoria transitiva de seis raízes percorreu 84.167 dependências, rejeitou os certificados anteriores do quinto pivô e encontrou somente os axiomas fundacionais `propext`, `Classical.choice` e `Quot.sound`. Não há `sorry`, `admit`, `native_decide` nem novas declarações `axiom`. Um manifesto comparou 245 objetos compilados com a worktree anterior, sem divergências. Os registros e hashes estão em `evidence/`. A prova não fornece positividade all-order, autovalores ou alturas.

## E — Próxima obrigação mínima

Para cada nova ordem ímpar, obter uma direção física experimental, uma cota para sua energia e uma estimativa relativa efetiva que inclua correção variacional e as duas caudas. O teorema geral mostra exatamente como essas peças se combinam, mas não as fornece automaticamente. Investigar também um análogo tipado da estimativa radial para o setor par antes de afirmar uma lei envolvendo ambos os setores.
