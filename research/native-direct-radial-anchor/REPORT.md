# Âncora radial direta para a quinta direção ímpar

**Resultado: PARTIAL para o programa all-order; certificado finito para a quinta direção ímpar.** A fonte física completa de dez jets ímpares tem, na direção crítica original e a partir de um índice definido abaixo, energia maior que a cota explícita de sua cauda radial. Isso fornece outra demonstração finita do sinal do quinto Schur ímpar. Esse sinal já havia sido certificado por outra via: o avanço aqui é o transporte por uma âncora física finita e uma estimativa variacional, e não um novo resultado all-order.

## A — Base e resultados anteriores

Base: `geometry-of-numbers` commit `202dba8a60591159fa0d6da058f146719516ffc1`, ponta da PR #135, empilhada sobre a PR #134. A execução usou `carry-self-adjoint-operator` em `bfeb10fd2425400fa38139903d12bf0599f02e53` e Lean `v4.32.0`. As duas permaneciam abertas durante a execução. O prefixo ímpar antigo de ordem quatro é positivo definido por `CarryCriticalSource.sourceMatrices_through_four_posDef`; empregamos sua inversibilidade. Não se usa como hipótese o sinal do quinto pivô.

A PR #134 fornece a síntese finita original, sua expressão polarizada completa e o orçamento somável radial. A PR #41 fornece `sourceMomentSchur_critical_direction_of_isUnit` e `native_inverseSchur_boundary_energy`. A identidade variacional de `CarryVariationalSchur.sourceTrialEnergy_eq_schur_add_residual_of_isUnit` é válida com o bloco antigo invertível, sem hipótese sobre o novo sinal. Os intervalos de entrada vêm de `CarryThetaPattern.mem_thetaTwentyBox` e da recorrência original; theta é aqui uma certificação analítica dos mesmos momentos, não uma alegação de origem geométrica da positividade.

## B — O que foi demonstrado agora

Em `DirectBound.lean`, `finite_energy_direct_error` controla a energia física completa, numa única escala radial, por

\[
 |D_k(c)-Q(c)|\leq E_k(c):=t_k^2 C(c),\qquad t_k=(k+1)^{-1}.
\]

`D_k` é `fullEnergy`, a parte real do pareamento quiral da fonte física completa na normalização existente; trata-se de um balanço assinado. A família finita é sintetizada antes da leitura; a soma inclui todos os pares ordenados de direções. Para cinco direções há 25 cruzamentos. Não é um limite que apaga os termos físicos.

`TenTrial.lean` certifica a forma da direção racional experimental

\[
 c=(3909825757/10^{21},-940486631/(5\cdot10^{16}),
 1101622369/(5\cdot10^{13}),-1085933731/(125\cdot10^9),1)
\]

com `rational_trial_head_lower`: \(Q(c)>7\cdot10^{-30}\). Em `TenTrialEverywhere.lean`, para todo \(k\ge 10^{22}-1\), a energia da mesma fonte satisfaz \(D_k(c)>6\cdot10^{-30}\) e seu orçamento \(E_k(c)\le25\cdot10^{-34}\).

A direção experimental **não é** a direção crítica; sua positividade isolada não decide Schur. A ponte nova em `VariationalTransport.lean` mantém os dois erros físicos e a correção exata

\[
 D_k(c_*)\ge D_k(c)-r^TA^{-1}r-E_k(c)-E_k(c_*),\quad r=Az-b.
\]

`scaled_inverse_residual` demonstra a invariância exata dessa correção sob a congruência diagonal usada para certificar os intervalos. `scaled_inverse_correction_upper` verifica, usando todas as 16 entradas, que \(r^TA^{-1}r<5\cdot10^{-35}\). A escala é um recurso de verificação; a fonte e a métrica física não são modificadas.

Em `TenExplicitCutoff.lean`, seja \(C_*\) o orçamento `familyConstant` da fonte crítica original, e defina-se

\[
 K_*=\max\bigl(10^{22}-1,\lceil (C_*+1)10^{31}\rceil\bigr).
\]

Para todo \(k\ge K_*\), `ten_critical_anchor_at_explicit_cutoff` prova \(E_k(c_*)<D_k(c_*)\). O índice é uma expressão exata dependente de uma constante real da fonte; não foi convertido aqui numa cota numérica racional computável. `ten_critical_form_positive_from_finite_source` deduz o sinal da forma, e `fifth_odd_schur_positive_via_direct_source` transporta-o ao quinto pivô. `ten_original_boundary_positive_via_direct_source` transporta-o à energia de bordo nativa pelo teorema da PR #41, com seu fator quatro original.

## C — Limites e controles contra circularidade

O bloco antigo positivo é uma premissa preexistente e explicitamente identificada; o novo pivô positivo não é uma premissa. A estimativa para a direção experimental usa intervalos theta dos momentos e por isso **não é uma demonstração puramente geométrica do sinal**. A prova não identifica arbitrariamente uma Gram positiva com a Hankel nem torna o déficit positivo apenas pela positividade das normas incidentes e retornadas.

O argumento não produz um controle uniforme de todas as ordens; o tamanho da correção variacional, as margens e os orçamentos dependem da direção. Uma âncora positiva experimental por si só não elimina a correção \(r^TA^{-1}r\). Também não se extrai uma identificação global com zeros ou alturas a partir deste resultado finito.

## D — Reprodução e auditoria

Os módulos novos estão isolados nesta pasta. Com os artefatos históricos e o operador no ambiente fixado pelo repositório, execute `bash research/native-direct-radial-anchor/validate.sh`. O script recompila os módulos com `-DwarningAsError=true`, roda `lake build --wfail` e busca atalhos proibidos. `Audit.lean` verifica axiomas e dependências transitivas, proíbe os certificados antigos do quinto pivô como entradas e exige as pontes de proveniência usadas na prova.

A execução sequencial concluiu os 13 módulos, inclusive `Audit`, e `lake build --wfail` terminou com 8.849 tarefas. A auditoria transitiva das quatro raízes percorreu 84.142 dependências, sem os certificados de sinal proibidos e com apenas `propext`, `Classical.choice` e `Quot.sound`. A busca por `sorry`, `admit`, `native_decide` e novas declarações `axiom` passou. Os registros estão em `evidence/`.

Os `.olean` históricos `ThetaTwenty` e `VariationalSchur` foram reaproveitados da worktree da PR #135; a auditoria é sobre as declarações carregadas. Isso não deve ser confundido com uma recompilação independente de toda a longa cadeia histórica. Verifique os logs e o manifesto de hashes fornecidos para o estado efetivamente validado.

## E — Próximo passo mínimo

Para avançar de forma não circular em outras ordens, procurar uma cota relativa para a correção variacional e o orçamento completo da fonte crítica, com dependência explícita de ordem e de setor. Primeiro testar se a geometria original fornece essa cota para uma família de direções, preservando os cruzamentos e a cauda; o caso finito deste relatório é uma regressão, não uma prova da lei. Uma melhoria localizada é substituir a expressão real \(C_*\) por uma cota racional certificada, produzindo um índice numérico para a direção tratada.
