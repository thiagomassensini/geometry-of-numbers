# Euler–Newton em dimensão arbitrária e limite vetorial móvel

Classificação: **PASS estrutural para a carta Euler–Newton em toda dimensão finita; PARTIAL para a positividade canônica all-order.**

Base exata: PR #123, commit `0c80f0d3c00bb03d7852a59faffa9adca80a4d3f`, branch `agent/native-binomial-source-all-order`. Nova branch: `agent/native-euler-newton-all-order`. Host de execução: `llm`. A #123 foi conferida como draft aberta e sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

A #123 fornece `newtonCoordinates` e `newton_input_exact`: a fórmula binomial recompõe exatamente os coeficientes A_r x_r da fonte original em dimensão 2n. `physical_source_newton_all_order` identifica os dois canais completos; `physical_pair_newton_all_order` preserva o pareamento complexo entre fontes, cutoffs e índices radiais independentes. A coerência de prefixos da mesma fonte finitamente suportada também já estava provada.

O módulo nativo `CompletedNativeChiralJetStorageTransport.lean` contém a síntese, a bijetividade regular e o controle uniforme de erro em cada ordem finita. `radialEulerBoundaryJet` já define o jet Euler pelos endereços D=r+1. `physical_values_eq`, da investigação anterior, identifica a carta completada com x_r/sqrt(2) quando F e P não se anulam nos endereços.

A #122 havia demonstrado uma matriz Euler–Newton explícita e sua inversa em quatro fontes. Esta etapa generaliza a matriz e seu limite; não redefine a fonte, o retorno ou a sequência de momentos.

## B — O que foi demonstrado agora

### B.1 — Polinômios determinados pelo endereço original

`shiftedFalling m` reutiliza `Polynomial.descPochhammer` da Mathlib, composto com X−1. Assim:

$$P_m(D)=(D-1)(D-2)\cdots(D-m),\qquad P_0=1.$$

Os teoremas `shifted_falling_degree`, `shifted_falling_monic`, `shifted_falling_diagonal` e `shifted_falling_above` provam grau m, monicidade, coeficiente diagonal 1 e nulidade dos coeficientes acima do grau. `shifted_falling_address` identifica exatamente:

$$P_m(r+1)=m!\binom rm.$$

`shifted_falling_scaled_eval` prova a identidade homogênea para todo t,z complexos, inclusive t=0. Não há divisão pelo passo na prova do limite. As subtrações naturais nos expoentes só são usadas com coeficientes acima do grau já anulados.

### B.2 — Matriz geral e diagrama de coeficientes

Escreva a[m,j] para o coeficiente de D^j em P_m, p_m para `nativeSourceJetOrderPhase m` e t_k=1/(k+1), o passo **radial** original. Não se identifica esse índice com profundidade vertical do carry, nem D com o clock material logarítmico.

`eulerNewtonMatrix N t` define:

$$\boxed{T_t[m,j]=\sqrt2\,p_m i^m a[m,j]t^{m-j}.}$$

O coeficiente a[m,j] é zero para j>m. `eulerNewton N t` é a multiplicação por essa matriz. `eulerChart` escreve a carta Euler da entrada em coordenadas brutas:

$$v_j=t^j\sum_{r<N}\frac{x_r}{\sqrt2}(r+1)^j.$$

`euler_newton_address` prova a identidade em dimensão N arbitrária. `euler_newton_raw_exact` a aplica à grade radial nativa em dimensão 2n:

$$\boxed{T_{t_k}v_{n,k}(x)=y_{n,k}(x),}$$

onde y é **a mesma** `newtonCoordinates` da #123. A fórmula de y conserva p_m, m!, o passo imaginário δ_k=i t_k e os coeficientes binomiais originais.

### B.3 — Identificação com a carta e o estado físicos

`physicalEulerChart` aplica o jet Euler preexistente à carta de valores completados original. `physical_euler_eq` prova sua expressão bruta sob F/P não nulos. Não se cancela amplitude fora desse domínio.

`source_euler_newton_all_order` estabelece o diagrama da fonte original para toda dimensão finita sob essa regularidade. `source_euler_newton_eventually_all_order` descarrega a condição usando o prefixo regular eventual já existente: para n fixado, um único prefixo eventual serve para todas as entradas.

`physical_source_euler_all_order` identifica, para suporte da fonte em 2n:

$$\boxed{U_k(x)=S_{n,k}\big(T_{t_k}v_{n,k}^{\mathrm{phys}}(x)\big).}$$

U é `physicalCompletedFiniteSource` e S é `nativeSourceProjectiveBoundaryJetSynthesis`, ambos preexistentes. Essa igualdade transporta os **dois vetores completos**, com a amplitude projetiva inserida uma vez e a amplitude sqrt(k+1) já pertencente à síntese radial.

`physical_pair_euler_all_order` leva a mesma identidade ao pareamento complexo Green em dois argumentos independentes, com cutoffs e índices radiais distintos. Conservam-se ambas as quadraturas e todos os cruzamentos. Nenhuma comparação apenas diagonal fixa a fase.

### B.4 — Não degenerescência e regressões

`euler_newton_matrix_prefix` prova que uma entrada da matriz depende apenas das ordens m,j e de t, independentemente do cutoff. `euler_newton_above` e `euler_newton_diagonal` dão triangularidade e diagonal constante:

$$T_t[m,m]=\sqrt2\,p_m i^m\ne0.$$

`euler_newton_diagonal_ne_zero` e `euler_newton_det_ne_zero` provam que o determinante é não nulo para **todo N e todo t real**, inclusive zero. Isso é uma mudança de coordenadas finita legítima; não é uma afirmação de isometria ou de positividade de uma forma transportada.

`euler_newton_four_regression` prova exatamente, para todo t e todo v em ℂ⁴, a igualdade com `CarryEulerNewton.eulerToNewton` da #122. Não se comparam apenas valores aproximados ou energias invariantes por fase global.

### B.5 — Limite antes do readout

`euler_newton_at_zero` calcula a matriz limite aplicada a qualquer vetor:

$$\boxed{(T_0w)_m=\sqrt2\,p_m i^m w_m.}$$

`euler_newton_continuous` prova continuidade conjunta em (t,v). `euler_newton_path_tendsto` conclui, em qualquer dimensão finita N:

$$v_k\longrightarrow w\quad\Longrightarrow\quad T_{t_k}v_k\longrightarrow T_0w.$$

`source_newton_path_tendsto` aplica isso à carta Euler física de uma entrada material móvel x_k, utilizando o diagrama exato no prefixo regular eventual. Sua hipótese é explicitamente a convergência dessa carta; ela não foi demonstrada para toda possível família x_k.

`source_newton_path_eventually_bounded` demonstra que a norma Pi dos coeficientes Newton fica eventualmente limitada por uma constante positiva nessas trajetórias. A métrica física Cauchy não é substituída pela norma Pi.

Esses dois lemas de trajetória leem o prefixo 2n da entrada. Para interpretá-lo como a fonte física **inteira**, é preciso a hipótese de suporte usada em `physical_source_euler_all_order`. Os lemas não apagam uma cauda fora do prefixo.

## C — O que foi refutado ou delimitado

Não surgiu uma obstrução nova à carta investigada. As hipóteses de regularidade têm função concreta: permitir a identificação da carta de valores completados com os coeficientes brutos, sem cancelamento ilegítimo de denominadores. A matriz e seu limite estão definidos mesmo em t=0; sua não degenerescência foi provada.

Convergência dos coeficientes não significa convergência dos estados físicos S_{n,k}(y_k). A própria síntese depende de k e as energias separadas dos canais podem crescer. Nenhum desses vetores foi declarado nulo ou descartado por um cancelamento do balanço.

As 1.181 regressões gaussianas racionais verificam dimensões 0,1,2,4,6,8,12,16, passos zero, negativos e radiais, Euler contra Newton por fórmulas independentes, inversão triangular nos casos testados, prefixos, termo constante de trajetórias lineares e os cruzamentos complexos das duas pernas. sqrt(2) é fatorado exatamente nesses testes e tratado efetivamente nas provas Lean. Amplitudes e retornos livres dos testes verificam álgebra, não valores das funções completadas ou sinais físicos. O resultado geral vem do Lean, não da lista finita de testes.

## D — O que permanece aberto

Não foi demonstrada positividade canônica all-order, nem uma Gram hilbertiana positiva de todos os momentos, nem um operador infinito de alturas. O transporte preserva a forma quiral assinada original.

O limite vetorial e a cota dos coeficientes estão provados. O transporte **do limite do pareamento/energia** ao longo dessas trajetórias móveis não foi formalizado nesta etapa. Ele deve usar o controle nativo uniforme em coeficientes da #123, incluindo o fator da norma, e a continuidade da forma de bordo, depois da igualdade do estado completo.

Os resultados são para cada dimensão finita fixada. Não fornecem uniformidade em n, convergência de uma torre infinita ou um sinal para todos os pivôs.

## E — Próximo passo mínimo, validação e reprodução

O próximo teorema concreto é: para n fixado, entradas móveis x_k eventualmente suportadas em 2n e carta Euler convergente a w, provar

$$4\operatorname{Re}\mathcal B(U_k(x_k),U_k(x_k))
\longrightarrow \mathrm{nativeSourceFiniteBoundaryEnergy}(2n,T_0w).$$

A parte vetorial necessária e a limitação dos coeficientes foram demonstradas aqui. O restante é combinar o erro uniforme já existente com essa limitação e provar a continuidade do readout original. Esse teorema seria de convergência e proveniência; o sinal da forma de bordo ainda precisaria de uma propriedade independente da fonte, sem receber a positividade desejada por outro nome.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Após a limpeza, recrie um worktree da branch publicada e ligue `.lake` ao cache comum validado. O cache de entrada da #123 tem SHA256 `f053b84dd9369271910abad2c2f0ab2745c1b05acdffb1f517aab5a04a9183d4`.

São reutilizados 105 objetos ancestrais verificados contra as fontes efetivas, hashes, toolchain, manifesto, pins e fontes nativas. Os cinco módulos novos e Audit são compilados novamente com warnings como erros. Não se alteram os módulos históricos, a fonte, amplitudes, fases, métrica, dressing, completion ou pins.

### Validação concluída

**18 checks passaram**, todos com exit 0. São **24 teoremas e 5 definições**, em cinco módulos matemáticos novos, além do lema privado usado na regressão de quatro fontes. Passaram as compilações individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **1.181 regressões gaussianas racionais** passaram. Os 105 objetos ancestrais foram verificados e reutilizados, sem anunciá-los como recompilados.

As **29 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas e opacos via `value? (allowOpaque := true)`. Há **60826 dependências** no grupo de construção. Em todas as raízes novas são proibidos os momentos canônicos, a energia limite dos momentos e o consumidor de controle de erro; essa etapa termina no transporte/limite vetorial, antes do readout.

Os certificados finitos de positividade e coercividade enumerados também estão proibidos em todas as raízes. Nenhum foi usado. Só são aceitos `propext`, `Classical.choice`, `Quot.sound`; não há axiomas matemáticos novos, `sorry`, `admit` ou `native_decide`. A auditoria percorre também o corpo do lema privado da regressão.

As evidências estão em `evidence/validation.json`, `evidence/lean-Audit.log`, `evidence/kernel-audit-summary.json` e `evidence/preservation.json`. `SHA256SUMS` registra a integridade da pasta. A validação observada foi no host `llm`, sem reivindicação de CI externo. A entrega usa PR draft empilhada sobre a #123, sem merge; fontes e cache verificados são preservados localmente antes da remoção somente do worktree próprio. Branch publicada e trabalhos anteriores são preservados.

Fim do relatório — Euler–Newton exato em toda dimensão finita e limite vetorial móvel; positividade canônica all-order permanece aberta.
