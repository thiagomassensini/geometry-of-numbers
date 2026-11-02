# Orçamento uniforme da fonte TFVD na direção crítica

**Resultado: PARTIAL.** A fonte e o bordo são os originais. A PR #41 fornece o residual e a direção crítica; a #70 transporta essa direção ao Bézout e conserva os quatro termos TFVD. Aqui demonstramos um orçamento uniforme nos dois vetores, uma taxa explícita na ordem e uma regressão quantitativa na fonte C3. A lei de sinal all-order continua aberta.

## A — Base e proveniência

Base desta branch: PR #142, commit `93d5f1a6da32c5e6a8ddcde08b20963384a884df`; ela continua empilhada sobre as PRs #141, #140 e #139. A PR #41 separa ortogonalização algébrica e positividade e identifica a energia do bordo com o residual usando somente inversibilidade do bloco anterior. A PR #70 demonstra o transporte para o Bézout, o fator correto `c₀²`, a repartição literal e a margem C3 em uma direção finita.

Mantemos a resposta original completada, as duas pernas, o companion, as fases e o bordo. Todas as identidades precedentes à estimativa mantêm dois argumentos independentes e os quatro cruzamentos HH, HT, TH, TT. A norma de coeficientes aqui é um instrumento para limitar o erro **após** a síntese: não se altera nem se identifica com a métrica física do carrier.

## B — O que o Lean demonstra agora

### 1. Erro uniforme sobre direções de ordem fixa

Em `UniformBudget.lean`, seja `‖x‖₁=Σᵢ|xᵢ|`, e seja `E` a soma dos orçamentos originais de HT, TH e TT avaliados com os dois vetores de coeficientes iguais a 1. Para cutoffs independentes `M,P`, `original_kernel_relative_bound` prova

\[
 |B(x,y)-HH_{M,P}(x,y)|\le E_{M,P}^{(r,s)}\,\|x\|_1\|y\|_1.
\]

O lado esquerdo é a norma complexa do pareamento completo de Bézout depois de subtrair a cabeça; o orçamento conserva os três termos restantes e é conservador, pois limita seus módulos separadamente. Para cada setor e dimensão fixa, `original_kernel_uniform_approx` mostra que, para qualquer tolerância positiva, um cutoff comum suficientemente grande funciona **para todos os pares de vetores**, não apenas para vetores escolhidos antes do limite. Não há sinal de pivô nem positividade de prefixo como premissa dessa aproximação.

### 2. Bordo reorganizado e direção da PR #41

`RepartitionBudget.lean` transporta a mesma cota para repartições independentes `U,V`: cabeça+U e cauda−U no primeiro argumento, cabeça+V e cauda−V no segundo. `repartition_original_four_terms` prova novamente a igualdade exata com o kernel original. `repartition_relative_bound` preserva os dois cutoffs, os dois argumentos e os quatro termos; não assume que bordos arbitrários diminuam a cauda.

Para a direção crítica mônica **original** `z`, `repartition_critical_error_bound` prova, apenas com o prefixo antigo invertível,

\[
 |c_0^2p-\operatorname{Re}HH(z,z)|\le E_{M,P}^{U,V}\,\|z\|_1^2.
\]

Isso usa o mesmo fator `c₀²` da #70, e não presume `p>0`. A cota é relativa ao tamanho dos coeficientes de `z`; **não é ainda uma cota relativa ao valor físico assinado ou ao pivô**. Para a partição bruta `U=V=0`, o erro normalizado tende a zero em cada ordem fixa. Nenhuma convergência é afirmada para uma repartição arbitrária dependente do cutoff.

`critical_positive_of_repartition_head` formaliza um teste suficiente em uma bola mônica: se uma cota `R` contém a verdadeira direção crítica e toda direção mônica nessa bola satisfaz `Re HH(x,x)>E R²`, então o pivô é positivo. O sinal da cabeça é hipótese do teste, não resultado geral. O mecanismo exigido para provar essa hipótese diretamente da fonte ainda não foi encontrado; exigi-la somente no vetor crítico sem um certificado independente seria circular.

### 3. Dependência explícita da ordem

`OrderBound.lean` demonstra `repartition_explicit_order_bound`: se os coeficientes da cabeça e da cauda dos dois argumentos até o índice `2r` são limitados respectivamente por `A_L,B_L,A_R,B_R`, então

\[
 |B(x,y)-HH(x,y)|\le 4r^2(A_LB_R+B_LA_R+B_LB_R)\|x\|_1\|y\|_1.
\]

A estimativa vale nos dois setores e para quaisquer dois cutoffs e repartições; é uma cota suficiente, não uma identidade nem uma constante ótima. O corte `2r` é conservador e cobre ambos os setores.

`SourceRate.lean` aplica essa desigualdade à cauda literal preexistente. Definindo a partir dos próprios coeficientes originais

\[
 A_r=\sum_{k=0}^{2r}|c_k|,\qquad
 \rho_{M,r}=\frac{C\,16^{2r}}{M+1},
\]

o Lean prova que existe **uma mesma** constante da fonte `C>0` tal que, para todo cutoff `M`, dimensão finita `r`, setor e par de vetores,

\[
 |B(x,y)-HH_{M,M}(x,y)|\le
 4r^2(2A_r\rho_{M,r}+3\rho_{M,r}^2)\|x\|_1\|y\|_1.
\]

`critical_source_explicit_order_rate` transporta a mesma cota ao residual de Schur da PR #41. O `C` vem do teorema original `literal_tail_jet_envelope`: sua existência foi provada, mas não foi obtida aqui uma cota racional numérica. A estimativa é explícita em `M`, `r`, coeficientes e direção, mas pode crescer muito com a ordem. Ela não é uniforme em `r` e não garante sinal.

### 4. Taxa racional para o bordo acelerado C3 já certificado

`C3OrderRate.lean` reutiliza `completed_tail_jet_error`, que já vale para **qualquer índice de jet** do bordo C3 original em `M=64`. Define a cota racional

\[
 B_r=\frac{96\,14!}{729\,191^{13}}\,4^{4r}.
\]

O Lean prova que a mesma expressão explícita da seção anterior vale com `ρ=Bᵣ` e com a cabeça reorganizada original `regroupedHead64`. `c3_critical_explicit_order_rate` a transporta, para todo `n` finito e os dois setores, à mesma direção de Schur, exigindo somente a inversibilidade do prefixo antigo. Aqui a cota da cauda é racional; `Aᵣ` e a direção ainda são dados da fonte. O fator cresce com a ordem, de modo que o resultado não dá uma margem all-order.

### 5. Regressão física C3 da PR #70

`C3UniformRegression.lean` especializa a repartição à `originalBoundaryJet 64` já existente. Reaproveitando as mesmas caixas C3, a cabeça original, a cauda e o vetor crítico originais, demonstra:

- o orçamento normalizado de HT+TH+TT é no máximo `10⁻¹³`;
- a direção crítica mônica pertence à bola `‖z‖₁≤2`;
- a cabeça supera `10⁻⁸` nessa bola mônica;
- a consequência quantitativa é
  \(c_0^2p>10^{-8}-4\cdot10^{-13}>0\).

O fator 4 aparece ao usar o orçamento uniforme sobre a bola de raio 2. Esta é uma nova aplicação da regra geral ao **mesmo segundo pivô par já certificado**, com margem mais conservadora que a da #70. Não é uma ordem nova e não é evidência de uma lei all-order. A inversibilidade usada é `native_even_one_isUnit_from_source`, demonstrada pela fonte e suas caixas, sem assumir positividade do pivô.

### 6. Diagnóstico da dimensão seguinte — sem certificação

O script `diagnose_c3_order.py` calcula numericamente a cabeça C3/64 e conserva HT, TH e TT na direção crítica de dimensão `r=3`, separadamente nos dois setores. Usa 70 dígitos internos, os 16 momentos decimais existentes e `ζ`/Gamma para avaliar `c₀`, sem usar alturas ou zeros como entrada. Não é aritmética intervalar nem um teorema Lean. Os resultados aproximados foram:

| Setor | `Re HH(z,z)` | orçamento coeficiente a coeficiente `E‖z‖₁²` | cota racional grosseira da seção 4 |
| --- | ---: | ---: | ---: |
| par | `2,7546e−14` | `2,8610e−25` | `1,6244e−11` |
| ímpar | `1,9972e−17` | `2,0474e−25` | `1,6209e−11` |

A comparação do orçamento refinado é **apenas no vetor crítico numérico**, não demonstra uma margem para toda a bola mônica. Nesse diagnóstico ele parece pequeno o bastante em ambos os setores; a cota uniforme grosseira de seção 4 ultrapassa a cabeça e não fecha o teste. Isso localiza o próximo trabalho: certificar limites individuais dos coeficientes da cabeça/cauda e da direção, em vez de substituir todos pelo maior envelope. Essas duas direções já pertencem aos blocos finitos conhecidos; a meta é validar a rota, não anunciar um novo pivô.

## C — O que não foi demonstrado

A desigualdade nova controla erro em coordenadas, não estabelece coercividade da forma nativa ou uma margem relativa ao pivô. O teorema preexistente `no_uniform_native_coercivity` exclui certa coercividade fixa nas coordenadas Hankel originais; ele não é uma impossibilidade de todas as cotas dependentes da ordem nem uma identidade automática entre essas coordenadas e o Bézout.

Também não foram demonstrados uma Gram física positiva global, sinal de todos os pivôs, contratividade all-order ou identificação espectral. O fato de `E→0` para ordem fixa não dá uma faixa uniforme quando a ordem cresce. O fator `16^{2r}`, a massa dos coeficientes e `‖z‖₁²` precisam ser considerados juntamente com a margem da cabeça.

## D — Próxima obrigação concreta

Na mesma partição acelerada original da #70, certificar primeiro em `r=3` os coeficientes individuais necessários da cabeça e da cauda (até índice 6 nesta cota conservadora) e uma faixa para a direção crítica, e confrontar a cabeça com o orçamento refinado. Em seguida buscar para cada ordem uma margem de cabeça em uma bola de direções que contenha a direção crítica, deduzida diretamente das relações/caixas da fonte. Para o próximo bloco, a fórmula geral de coeficientes mostra que bastam estimativas finitas dos jets necessários, mas as caixas da #70 cobrem apenas o caso anterior. Os limites devem ser derivados para a fonte completada e conservar HT, TH e TT; não basta postular que a margem existe.

Para uma lei all-order será preciso controlar quantitativamente, com dependência de ordem e setor, tanto o tamanho da direção crítica quanto a margem da cabeça. Uma cota uniforme positiva sem essas dependências não decorre do resultado atual. Nenhuma conclusão positiva deve ser inferida apenas de aumentar `M`.

## E — Validação e reprodução

Os módulos são compilados separadamente com `-DwarningAsError=true`, pois o build principal sozinho não os cobre. `Audit.lean` examina transitivamente os resultados gerais, exige as pontes da #41/#70 e bloqueia os certificados posteriores de sinal enumerados na auditoria. `AuditC3.lean` audita a regressão, exige as caixas originais e a cauda C3, e proíbe o reaproveitamento dos teoremas anteriores que já concluem o sinal, assim como a calibração theta adicional de `c₀`. `Axioms.lean` audita as declarações públicas.

No host `llm`, com os caches certificados existentes da #70 e suas dependências:

```bash
bash research/tfvd-uniform-relative-source/validate.sh
```

`CARRY_PR70_ROOT` permite apontar para a worktree equivalente com os caches da #70. A validação integral dos módulos anteriores consta em `evidence/validation.log`; o módulo `C3OrderRate` e as auditorias atualizadas foram compilados separadamente depois com as mesmas opções. O `validate.sh` atualizado inclui todos eles para futuras execuções. O diagnóstico reproduz-se com `/home/thlinux/miniforge3/bin/python research/tfvd-uniform-relative-source/diagnose_c3_order.py`; o hash do checkpoint e os logs constam em `evidence/`. As provas novas foram compiladas pelo Lean, mas as dependências `.olean` de pesquisas anteriores foram reutilizadas; isso não constitui reconstrução limpa dos repositórios externos. Não houve alteração das fontes, métricas, pesos ou pins.
