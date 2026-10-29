# Transporte binomial explícito da fonte nativa em toda ordem finita

Classificação: **PASS estrutural para a fórmula e o transporte em toda dimensão finita; PARTIAL para a positividade canônica all-order.**

Base exata: PR #122, commit `85ac7e9d76954e7e9188b6088b056e25ec9d3bd0`, branch `agent/native-euler-newton-four`. Nova branch: `agent/native-binomial-source-all-order`. Execução no host `llm`. A #122 foi conferida como draft aberta, sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

O módulo nativo `CompletedNativeChiralJetStorageTransport.lean` já define:

- `nativeSourceJetOrderPhase` e `nativeSourceChiralJetInputMatrix`: fases, fatoriais, passo imaginário e amplitude projetiva da fonte original.
- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`: igualdade do estado inteiro, com incidência e retorno, antes das normas.
- `nativeSourceChiralJetInput_injective` e `nativeSourceChiralJetInput_eventually_bijective`: bijetividade sob a regularidade já demonstrada no prefixo eventual.
- `storage_one_chiralJetInput_eventually_energy_control`: controle uniforme nas coordenadas de jets para cada dimensão finita.

As PRs anteriores também fornecem `original_source_graph`, `original_source_storage` e `cross_green_eq_original`. Esses resultados identificam o estado físico com a síntese e seu pareamento complexo completo. A PR #122 havia escrito a inversão de coeficientes explicitamente apenas em quatro fontes, além de identificar a fonte crítica completa com `(0,-a,0,-1)`.

Nenhuma dessas premissas foi reimplementada ou confundida com positividade em toda ordem. Os certificados finitos de sinal anteriores não entram nas provas novas.

## B — O que foi demonstrado agora

### B.1 — Inversão binomial efetiva

Para qualquer cutoff N e endereços r,s<N, `inverse_binomial_kernel` demonstra:

$$\sum_{m=0}^{N-1}(-1)^{m-r}\binom mr\binom sm=\mathbf1_{r=s}.$$

Os termos com m<r ou m>s são zero pelos próprios coeficientes binomiais. A subtração natural no expoente é a convenção do stencil original. A prova reduz a parte sobrevivente à soma alternada de coeficientes binomiais da Mathlib.

`binomialMatrix` tem entradas C[m,r]=binom(r,m). `signedBinomialMatrix` contém literalmente `completedGreenForwardWeight m r`. Os teoremas `signed_binomial_mul` e `binomial_signed_mul` provam F C = I e C F = I. A segunda identidade usa álgebra de matrizes quadradas sobre ℂ, sem determinantes da fonte, positividade ou escolha de uma preimagem.

`binomial_stencil_exact` aplica a identidade a qualquer vetor complexo finito. Os resultados incluem N=0 como identidade do espaço vazio.

### B.2 — Fórmula nativa em dimensão 2n

Escreva δ_k = i/(k+1), p_m = (-1)^{floor(m/2)} e A_{k,r} para a amplitude projetiva nativa, sem alterar nenhuma dessas definições. O índice k aqui é a regularização radial; não é profundidade vertical do carry.

`newtonCoordinates` calcula:

$$\boxed{y_m=p_m\,m!\,\delta_k^m\sum_{r=0}^{2n-1}\binom rm x_r.}$$

`native_phase_self_inverse` prova p_m²=1. `newton_input_term` cancela exatamente as fases, fatoriais e potências do passo no coeficiente da matriz nativa. `newton_input_exact` conclui, para **todo n,k e todo x complexo**:

$$\boxed{\mathrm{nativeSourceChiralJetInput}(n,k,y)=(A_{k,r}x_r)_r.}$$

Essa identidade não exige regularidade de F/P, inversibilidade da Hankel ou sinal de momentos. A amplitude ocorre uma vez. A amplitude sqrt(k+1) já está na síntese radial nativa e não é reinserida.

`newton_coordinates_unique` usa a injetividade nativa preexistente somente para provar a unicidade dessas coordenadas quando F e P não se anulam nos endereços. A fórmula e sua identidade direta são anteriores a essa condição.

### B.3 — Mesma fonte e todos os cruzamentos

Para uma fonte material x de suporte contido em {0,...,2n-1}, `physical_source_newton_all_order` prova a igualdade dos **dois vetores completos**:

$$\boxed{\mathrm{physicalCompletedFiniteSource}(k,x)=S_{n,k}(y_{n,k}(x)).}$$

Aqui S é `nativeSourceProjectiveBoundaryJetSynthesis`, já existente. Não se definem novos estados a partir dos momentos.

`physical_pair_newton_all_order` transporta o pareamento complexo inteiro:

$$B_{k,l}(x,z)=\mathcal B\big(S_{n,k}(y_{n,k}(x)),S_{p,l}(y_{p,l}(z))\big).$$

Os argumentos x,z, os cutoffs 2n,2p e os índices radiais k,l são independentes. Mantêm-se as duas quadraturas, a incidência, o retorno e os cruzamentos Green. A hipótese 0<eta<1 pertence à interface Green anterior; não é hipótese de positividade canônica.

### B.4 — Coerência de prefixos

`sourceNewtonCoefficient` escreve a mesma fórmula por soma no suporte finito da fonte, sem escolher cutoff. Ela é uma coordenada da entrada original, não uma nova sequência de momentos.

- `newton_coordinates_of_support`: a carta finita é a restrição dessa família de coeficientes.
- `newton_coordinates_prefix_coherent`: quaisquer dois prefixos contendo a mesma fonte dão exatamente o mesmo coeficiente na mesma ordem.
- `source_newton_above_support` e `newton_coordinates_above_support`: suporte abaixo de N implica coeficientes de ordem ≥N iguais a zero.
- `native_synthesis_prefix_coherent`: as sínteses dos dois prefixos são o mesmo estado físico inteiro.

Essa coerência é para uma mesma entrada finitamente suportada, inclusive famílias móveis quando as hipóteses valem em cada k. Não constitui uma família infinita positiva de jets canônicos, nem prova passagem ao limite de operadores.

`four_coordinates_regression` é igualdade definicional com a fórmula da #122; `critical_coordinates_regression` recupera exatamente `(0,-a,0,-1)` para a fonte crítica completa antiga.

### B.5 — Controle de erro com coordenadas explícitas

Só depois da identificação dos vetores, `source_explicit_energy_control_all_order` reutiliza o teorema nativo de erro e a identidade original de storage:

$$\boxed{\forall n,\ \forall\varepsilon>0,\ \forall^{\mathrm{ev}}k,\ \forall x\text{ suportada em }2n,\quad
|4\operatorname{Re}\mathcal B(U_k(x),U_k(x))-\mathrm{nativeSourceFiniteBoundaryEnergy}(2n,y_{n,k}(x))|
\le\varepsilon\|y_{n,k}(x)\|^2.}$$

O limiar é uniforme nas entradas para o n e a tolerância fixados. Não é uniforme em n. A norma à direita é a norma Pi original dos coeficientes de jets, sem identificá-la com a métrica física Cauchy. Para usar o resultado ao longo de entradas móveis, ainda é necessário controlar essas coordenadas; o fator da norma não pode ser omitido.

## C — O que foi refutado ou delimitado

Não surgiu um NO-GO novo. A investigação encerrou a lacuna específica de escolher apenas uma preimagem por bijetividade: há uma fórmula efetiva e ela recompõe exatamente cada endereço da mesma fonte.

As duas matrizes binomiais são inversas, mas isso não as torna isometrias. As identidades de estado e pareamento preservam a forma quiral assinada original; a inversão de coordenadas não a torna positiva.

As 1.587 regressões gaussianas racionais abrangem dimensões 0,2,4,6,8,10,12,16, ambos os produtos das matrizes, ambos os sentidos da carta nos casos testados, extensões por zero, índices radiais distintos, todos os cruzamentos Cauchy dos pares testados e a fase crítica original. Amplitudes e quocientes livres nesses testes verificam identidades algébricas; não são avaliações das funções completadas nativas nem evidência de sinal. O resultado para todo n vem das provas Lean, não dessa lista finita.

## D — O que permanece aberto

Não foi provada a positividade all-order de H ou K, nem uma Gram positiva global dos momentos canônicos. Não foi construído um operador infinito de alturas.

A primeira obrigação de coeficientes proposta pela #122 foi resolvida para toda dimensão finita. A matriz **Euler–Newton geral**, seu limite em trajetórias Euler móveis e a subsequente aplicação polarizada desse limite ainda não foram formalizados nesta etapa; a matriz de quatro fontes anterior permanece intacta.

A obrigação independente de sinal da forma de bordo completada também permanece. Nenhuma hipótese equivalente a esse sinal foi adicionada à construção ou ao transporte.

## E — Próximo passo mínimo, validação e reprodução

O próximo alvo é o transporte Euler–Newton em qualquer dimensão, aproveitando a inversão agora demonstrada. Se a[m,j] é o coeficiente de D^j no produto (D−1)...(D−m), o mapa candidato, com as mesmas convenções nativas, é:

$$T_t[m,j]=\sqrt2\,p_m i^m a[m,j]t^{m-j}\quad(j\le m),\qquad T_t[m,j]=0\quad(j>m).$$

O teorema concreto a provar é y_{n,k}(x)=T_{t_k}v_{n,k}(x), onde v_j=t_k^j sum_r (r+1)^j x_r/sqrt(2) é a carta Euler da mesma fonte, após o cancelamento legítimo da amplitude. Depois, provar T_{t_k}v_k→T_0v para trajetórias convergentes, **antes** de aplicar o readout. Essa fórmula é uma meta para a próxima etapa, não um teorema desta PR. O sinal continuará exigindo uma propriedade independente da fonte completada.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Para reprodução após a limpeza, recrie um worktree da branch publicada, ligue `.lake` ao cache comum validado e entre nesta pasta. Cache de entrada da #122: SHA256 `54dd9539478db9ed6d49ffccad925703fc4ce1d9756c84badc0723c6e2909897`.

São reutilizados 100 objetos ancestrais conferidos por hashes de fontes e objetos, toolchain, manifesto, pins, árvore principal e fontes nativas. Os cinco módulos novos e Audit são compilados novamente com warnings como erros. O cache não substitui a auditoria das provas novas.

### Validação concluída

**18 checks passaram**, todos com exit 0. São **18 teoremas e 4 definições**, em cinco módulos matemáticos novos. Passaram as compilações individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **1.587 regressões gaussianas racionais** passaram. Os 100 objetos ancestrais foram verificados e reutilizados, sem anunciá-los como recompilados.

As **22 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas e opacos via `value? (allowOpaque := true)`. O grupo de construção contém **21 raízes e 50,326 dependências**; nele estão proibidos os momentos canônicos, a energia limite dos momentos e o consumidor de controle de erro. A **raiz de controle transportado** contém **62,093 dependências** e permite esse readout somente depois das identidades vetoriais.

Os certificados finitos de positividade e coercividade enumerados estão proibidos **em ambos os grupos**. Nenhuma dessas raízes foi usada. O consumidor nativo de erro uniforme é verificado na trilha do grupo de controle. Só são aceitos `propext`, `Classical.choice`, `Quot.sound`; não há axiomas matemáticos novos, `sorry`, `admit` ou `native_decide`.

As evidências estão em `evidence/validation.json`, `evidence/lean-Audit.log`, `evidence/kernel-audit-summary.json` e `evidence/preservation.json`. `SHA256SUMS` registra a integridade da pasta. A validação observada foi no host `llm`, sem reivindicação de CI externo. A entrega usa PR draft empilhada sobre a #122, sem merge; fontes e cache verificados são preservados localmente antes da remoção somente do worktree próprio. Branch publicada e trabalhos anteriores são preservados.

Fim do relatório — fórmula binomial explícita, fonte e cruzamentos transportados em toda dimensão finita; positividade canônica all-order permanece aberta.
