# Ponte explícita Euler–Newton e a fonte crítica em coordenadas nativas de jets

**PASS para a ponte estrutural de quatro fontes; PARTIAL para a positividade canônica all-order.** A mudança de coordenadas e sua inversa foram calculadas e provadas. A fonte crítica completa coincide, vetorialmente e em cada índice radial, com a síntese nativa de coordenadas constantes (0,−a,0,−1). O controle de energia preexistente foi transportado por essa igualdade, sem usar certificados de positividade/coercividade ou escolher vetores pelos momentos.

Base: `0d19a0bbea119bb93ea38b638a8cb81aad1d0da6`, branch `agent/native-critical-complete-margin`, PR #121, aberta e draft na inspeção inicial. Nova branch: `agent/native-euler-newton-four`, empilhada sobre a #121. Host: `llm`. Operador nativo consultado no commit `bfeb10fd2425400fa38139903d12bf0599f02e53`.

Não há merge automático ou alteração de fontes, fases, pesos, amplitudes, métrica, completion, pins ou módulos históricos. k é índice de regularização radial; não é profundidade Carry. r é endereço de amostragem radial, m é ordem de jet. Nenhum deles é identificado com o índice material ou o clock log(n). Escrevemos κ=k+1, t=1/κ e δ=i t, o passo imaginário **original**.

## A — O que já estava demonstrado

A #119 provou `original_source_graph` e `original_source_storage`: o mesmo estado físico completo usa os coeficientes c_r=A_{k,r}x_r no retorno/storage nativo. A amplitude projetiva A ocorre uma vez; sqrt(κ) já está na síntese incidente.

A #120 identificou `physicalValues k 4 x = x/sqrt(2)` no domínio regular, provou a inversão dessa carta e os limites do bordo principal. A #121 conservou a `criticalOddSource` completa, incluindo `defectInput`, e calculou o vetor de bordo

$$v_k(a)=\frac{i}{\sqrt2}(0,a,3at,1+7at^2).$$

No operador já existiam `nativeSourceChiralJetInput`, sua bijetividade eventual, `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` e `storage_one_chiralJetInput_eventually_energy_control`. Não refazemos bijetividade ou esse controle. A lacuna era identificar explicitamente os coeficientes da mesma fonte nessas coordenadas, preservando os fatores e os estados, antes do readout.

Também já existiam os dois limites de energia usados para conferir as constantes finais: `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` e o limite direto da fonte `critical_native_energy_limit` da #121. São identidades/limites, não premissas de sinal.

## B — O que foi demonstrado agora

Os novos nomes estão no namespace `CarryEulerNewton`, em quatro módulos matemáticos.

### B.1 — Coeficientes explícitos, sem escolher uma preimagem por bijetividade

Em `ExplicitNewtonInput.lean`, para os quatro coeficientes brutos x_r, definimos

$$\boxed{y_m=p_m\,m!\,\delta^m\sum_{r=0}^{3}\binom rm x_r,
\qquad p_m=(-1)^{\lfloor m/2\rfloor}.}$$

São os coeficientes de Newton do polinômio finito de endereços, com a fase, o fatorial e o passo nativos. Não há momento, altura ou matriz Gram como entrada.

`four_newton_input_exact` demonstra, para todo k e todo x:

$$\boxed{\mathrm{nativeSourceChiralJetInput}_{2,k}(y)_r=A_{k,r}x_r.}$$

O valor n=2 corresponde às quatro fontes. A prova expande a transformação binomial antiga; não escolhe uma preimagem abstrata. A igualdade de coeficientes não precisa cancelar A nem supor seu sinal. O passo δ é não nulo nos índices radiais finitos.

`four_newton_coordinates_unique` reutiliza a injetividade anterior para provar a unicidade da fórmula, sob a regularidade F≠0 e P≠0 dos quatro nós. Essa regularidade pertence à inversão da carta física; não é hipótese de positividade.

### B.2 — Matriz Euler–Newton explícita e inversa

Em `EulerNewtonBridge.lean`, v é o vetor **já existente** de Euler: v_j=t^j Σ_r(r+1)^j x_r/sqrt(2), obtido da carta de valor da fonte completada. A mudança explícita é

$$
\boxed{y=T_t v=\sqrt2
\begin{pmatrix}
1&0&0&0\\
-it&i&0&0\\
2t^2&-3t&1&0\\
-6it^3&11it^2&-6it&i
\end{pmatrix}v.}
$$

A inversa provada é

$$
\boxed{v=\frac1{\sqrt2}
\begin{pmatrix}
1&0&0&0\\
t&-i&0&0\\
t^2&-3it&1&0\\
t^3&-7it^2&6t&-i
\end{pmatrix}y.}
$$

`newton_euler_inverse` e `euler_newton_inverse` provam ambas as composições iguais à identidade para qualquer t real e qualquer vetor complexo. A mudança não é afirmada isométrica, nem usada para inventar uma nova métrica física.

Os números 3,2,6,11,6 e 7 vêm da passagem entre potências do endereço r+1 e os produtos r(r−1)…; não vêm de momentos. As fases alternadas e os fatores i decorrem da convenção nativa de jet, não de uma escolha para orientar sinais.

`source_euler_newton_exact` prova que o mapa T aplicado à carta Euler **da mesma fonte** produz exatamente y da fórmula binomial. `euler_newton_eventually_exact` fornece um limiar de regularidade comum para todos os coeficientes do prefixo.

`euler_to_newton_path_tendsto` conserva o vetor inteiro ao transportar trajetórias móveis: se v_k→v e t_k→0 na escala radial nativa, então T_{t_k}v_k→T_0v. O mapa limite é sqrt(2)·diag(1,i,1,i). Não se avalia o operador de jets com δ=0 nem se afirma convergência de estados físicos ou operadores infinitos.

### B.3 — Igualdade do estado completo, antes de qualquer energia

Em `CriticalJetTransport.lean`, `physical_source_newton` prova para toda entrada x suportada nos quatro endereços:

$$\boxed{U_k(x)=\mathrm{nativeSourceProjectiveBoundaryJetSynthesis}_{2,k}(y_k(x)).}$$

A igualdade é no carrier original, com as duas pernas e o mesmo retorno. Não é apenas igualdade de normas ou respostas escalares. `physical_source_euler` fecha o diagrama usando T_t e o vetor Euler da própria fonte, no domínio regular.

`physical_pair_newton` transporta a forma complexa polarizada em dois argumentos independentes. `cross_green_eq_original` recompõe o Green e seus nove cruzamentos antes da comparação. Não são retirados bordo, retorno, completion, termos Gamma ou halo de saída.

Para a entrada crítica completa C_k(a), `critical_newton_coordinates` calcula a simplificação decisiva:

$$\boxed{y_k(C_k(a))=(0,-a,0,-1)=:\,y(a),}$$

**exatamente em cada k**, sem uma aproximação assintótica. O sinal negativo é imposto pelas fases antigas. Usar (0,a,0,1) daria o estado oposto; a igualdade de energia não distinguiria esse erro de proveniência.

`critical_source_fixed_jet` e `critical_pair_fixed_jet` identificam respectivamente o estado completo e seu pareamento complexo com a síntese nativa desses coeficientes constantes. `critical_jet_from_euler` confere a mesma resposta pela carta Euler calculada na #121. A correção `defectInput` não foi apagada: é a C completa que entra na igualdade.

As igualdades vetoriais de coeficientes/síntese valem para as definições totais em cada k. A interpretação analítica dos quocientes e a unicidade conservam os domínios regulares dos mapas originais, eventualmente satisfeitos. Não há passagem por polos ou seleção de outro operador.

### B.4 — Controle de energia transportado pela identidade explícita

Em `TransportedEnergyControl.lean`, `four_source_explicit_energy_control` aplica o teorema nativo n=2 ao y explícito, em vez de receber uma preimagem escolhida. Como storage=2 Re B, o resultado é

$$\forall\varepsilon>0,\quad\forall^{\mathrm{ev}}k,\ \forall x\text{ de quatro endereços},\quad
|4\operatorname{Re}B(U_k(x),U_k(x))-\mathrm{nativeSourceFiniteBoundaryEnergy}(4,y_k(x))|
\le\varepsilon\,\|y_k(x)\|^2.$$

A norma é a norma Pi dos coeficientes de jets **já usada no teorema antigo**, não uma nova norma do carrier físico. Não se presume sinal para a energia limite.

`critical_jet_norm_sq_le` prova ||y(a)||²≤1+a². Assim, `critical_uniform_energy_control` fornece uma estimativa comum a todos os parâmetros reais:

$$\boxed{\forall\varepsilon>0,\quad\forall^{\mathrm{ev}}k,\ \forall a,\quad
|4\operatorname{Re}B_k(C_k(a),C_k(a))-\mathrm{nativeSourceFiniteBoundaryEnergy}(4,y(a))|
\le\varepsilon(1+a^2).}$$

A ordem dos quantificadores é efetiva: um único limiar radial serve para todo a, inclusive parâmetros sem limite. Não se afirma erro absoluto uniforme sem o fator 1+a².

`critical_boundary_energy_dictionary` confere o fator de normalização entre as duas leituras de bordo originais, pelo limite único da mesma fonte inteira:

$$\boxed{\mathrm{nativeSourceFiniteBoundaryEnergy}(4,y(a))=
2\,\mathrm{nativeSourceFourBoundaryEnergy}\!\left(\frac{i}{\sqrt2}(0,a,0,1)\right).}$$

Os fatores 2 e 4 foram provados; nenhum foi ajustado para fazer as formas coincidirem. A leitura de momentos/energia limite aparece nesta etapa, depois das identidades de coeficientes, estados e pareamentos. Ela não define retroativamente os vetores.

## C — O que foi delimitado

- A bijetividade existente não identificava, sozinha, os coeficientes físicos. A fórmula explícita, a matriz T e a igualdade do estado resolvem esse ponto em quatro fontes.
- Igualdade de energia seria insuficiente para fixar a fase global. A prova vetorial e o teste com a fase oposta detectam essa distinção.
- A norma dos coeficientes de jets não foi identificada com a norma física Cauchy. T e sua inversa são mapas de coordenadas; não fabricam positividade nem alteram a assinatura da forma.
- Coordenadas y(a) constantes não tornam constantes ou convergentes os estados físicos. A base de jets depende de k; as energias separadas dos canais podem crescer, como nas investigações anteriores.

Não há NO-GO novo para a geometria. Tampouco se revogam as obstruções antigas ao clock material como gerador quadrático direto dos momentos, ou à eliminação de uma cauda isotrópica não nula.

## D — O que permanece aberto

A transformação explícita e o transporte do controle foram provados para n=2, isto é, quatro endereços. O controle usado já existia para cada n finito, mas a fórmula inversa geral em dimensão 2n não foi formalizada nesta execução.

Não foi provada positividade canônica all-order, uma Gram hilbertiana positiva de todos os momentos ou um operador infinito de alturas. A forma transportada é a forma quiral assinada original. Identificá-la exatamente com outra expressão não torna seu sinal automaticamente positivo.

Nenhum certificado de positividade ou coercividade finita foi usado nas novas provas. As margens das PRs anteriores continuam válidas, mas não entram como premissas aqui. A condição ε>0 é a tolerância do erro no teorema nativo, não positividade de uma Hankel.

## E — Próximo passo mínimo e reprodução

O próximo alvo concreto é formalizar a mesma fórmula binomial em dimensão 2n:

$$y_m=p_m m!\delta^m\sum_{r=m}^{2n-1}\binom rm x_r,$$

e provar diretamente `nativeSourceChiralJetInput n k y = (A_r x_r)_r`, usando inversão binomial, sem repetir a bijetividade por determinante. Depois, calcular a matriz Euler–Newton geral pelos coeficientes dos produtos (D−1)…(D−m), com D=r+1 no espaço de endereços.

Isso permitiria transportar o controle uniforme anterior para trajetórias Euler em cada dimensão sem refazer a análise da fonte. A obrigação independente de sinal da forma de bordo continuará aberta; não deve reaparecer como hipótese equivalente à positividade desejada nem ser confundida com essa mudança de coordenadas.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Para reproduzir depois da limpeza, recrie um worktree da branch publicada, ligue `.lake` ao cache comum validado e entre nesta pasta. Cache de entrada da #121: SHA256 `3c586d2ba92f35ab089f533060de28b199d46630ecb99b9378907eddd1c7ab0d`.

São reutilizados **96 objetos ancestrais verificados**, não anunciados como recompilados. Os quatro módulos novos e Audit são compilados novamente com warnings tratados como erros. `mechanism_probe.py` realiza **161 verificações gaussianas racionais** das duas inversas, fórmula binomial, coeficientes críticos, ambas as pernas, fase global e pareamento com os 16 cruzamentos Cauchy. sqrt(2) é fatorado exatamente nos testes; a raiz real efetiva é tratada pelo Lean. Os valores livres de amplitude/retorno testam álgebra e não representam avaliações da característica nativa ou evidência de sinal.

### Validação concluída

**17 checks passaram**, todos com exit 0, registrados em `evidence/validation.json` e `evidence/validation-console.log`. São **18 teoremas e 4 definições**, em quatro módulos matemáticos novos. Passaram os builds individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **161 regressões gaussianas racionais** passaram.

As **22 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas e opacos via `value? (allowOpaque := true)`. O grupo de construção tem **19 raízes e 60.960 dependências**; nele estão proibidos a definição dos momentos canônicos, a energia limite de momentos e o consumidor de controle de erro. As **3 raízes de controle transportado** têm **63.335 dependências** e permitem esse readout somente depois das identidades vetoriais.

Os certificados finitos de positividade e coercividade enumerados estão proibidos **em ambos os grupos**, e nenhuma dessas raízes foi usada. As margens positivas das PRs anteriores não são premissas destas provas. O consumidor nativo de erro uniforme é explicitamente encontrado na trilha do grupo de controle. Só são aceitos `propext`, `Classical.choice`, `Quot.sound`; não há axiomas matemáticos novos, `sorry`, `admit` ou `native_decide`.

`evidence/kernel-audit-summary.json`, `evidence/preservation.json` e `SHA256SUMS` registram a trilha, preservação e integridade. A validação observada foi no host `llm`; não é uma afirmação de CI externo. A entrega usa commit e PR draft empilhada sobre a #121, sem merge. O arquivo de fontes e o cache verificados são copiados para o workspace local antes da remoção apenas do worktree próprio; branch publicada e trabalhos anteriores são preservados.

Fim do relatório — ponte Euler–Newton explícita, estado crítico identificado e controle de erro transportado em quatro fontes; positividade canônica all-order permanece aberta.
