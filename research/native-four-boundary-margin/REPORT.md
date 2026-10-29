# Margem física uniforme a partir do bordo nativo de quatro fontes

**PASS para o alvo quantitativo da PR #119; PARTIAL para a positividade canônica em toda ordem.** A mesma fonte principal possui agora uma margem física estrita, uniforme no parâmetro, que sobrevive ao limite. O ingrediente de sinal é a coercividade N=4 **já demonstrada** no repositório do operador. Não é uma lei nova de sinal em dimensão arbitrária.

Base: `ec12e668413422b6b930e0b891ed6500365e3967`, branch `agent/native-tail-return-graph`, PR #119, aberta e draft na inspeção inicial. Nova branch: `agent/native-four-boundary-margin`, empilhada sobre a #119. Não há merge automático ou edição das PRs anteriores, de `main`, dos módulos históricos, fontes, fases, pesos, métricas, amplitudes ou pins. Host de execução: `llm`; operador nativo no commit `bfeb10fd2425400fa38139903d12bf0599f02e53`.

Aqui k é o **índice de regularização radial**. Não é identificado com a profundidade vertical do Carry. Escrevemos κ=k+1 e t=1/κ.

## A — O que já estava demonstrado

A #119 identificou a fonte física completa da família principal X_k(a) com o grafo do retorno nativo finito e com o storage original. O vetor de coeficientes recebido pelo storage é

$$c_j=A_{k,j}X_k(a)_j,$$

com a amplitude projetiva original A uma única vez. O fator radial sqrt(κ) já pertence à síntese incidente, não a c. `original_source_graph`, `original_source_storage`, `principal_four_port_gram` e `principal_four_eventually_positive` são resultados anteriores.

Também já estavam demonstrados:

- `radialCompletedValueCoefficients` e `radialCompletedInputCoefficients`: mudança de coordenadas prescrita pela própria fonte completada;
- `radialFourScaledBoundary`: quatro jets de bordo da mesma fonte, com pesos t^m;
- `radialFourNormalizedBoundaryInput_scaled`: reconstrução dos coeficientes a partir desses quatro dados, sem eliminar os bordos superiores;
- `storage_one_fourSample_eventually_boundary_coercive`: uma constante ε>0 e um limiar radial comuns a todos os coeficientes de quatro fontes;
- `principal_coefficient_formula` e `principal_coefficients_completed_square`: coeficientes literais e não anulação de X;
- `principal_physical_tendsto`: o Green recomposto tende a h₃−(a+b)h₂+ab h₁, para duas entradas independentes.

A coercividade histórica inclui os dois setores de bordo, os cruzamentos da métrica Cauchy e o resto analítico inteiro da fonte. Sua prova de sinal finito já existia; não foi refeita nem apresentada como resultado all-order. A #119 tinha positividade eventual, mas não bastava inferir dela, isoladamente, positividade **estrita do limite**. Esse é o ponto fechado agora.

## B — O que foi demonstrado agora

Os novos nomes vivem em `CarryBoundaryMargin`. Há três módulos matemáticos separados.

### B.1 — Cancelamento exato do dressing nas coordenadas existentes

`PhysicalBoundaryCoordinates.lean` define `physicalCoefficients`, `physicalValues` e `principalBoundary` reutilizando os mapas nativos. Se F e P não se anulam nos quatro nós, `physical_values_eq` prova:

$$
 d_j=\frac{c_j F_j}{P_j}=\frac{X_k(a)_j}{\sqrt2},
 \qquad c_j=\frac{P_j}{\sqrt2 F_j}X_k(a)_j.
$$

`physical_values_recover` demonstra o caminho inverso e recupera exatamente c. Não renormalizamos a fonte: calculamos suas coordenadas no mapa já usado pelo certificado antigo e verificamos sua inversão. O estado físico, as duas pernas e sua métrica permanecem os mesmos.

Os dois lemas valem para qualquer prefixo finito e qualquer vetor de coeficientes, sob regularidade explícita. A especialização para quatro fontes é feita depois. Não se reivindica um domínio de clock não limitado nem limite de operadores infinitos.

### B.2 — O vetor de bordo inteiro e seu limite não nulo

Em `PrincipalBoundaryLimit.lean`, a fórmula de `principal_boundary_exact` é

$$
 \boxed{V_k(a)=\frac{i}{\sqrt2}
 \left(0,\ a,\ \frac{10a}{\kappa},\ 1+\frac{77a}{\kappa^2}\right).}
$$

Este V é **exatamente** `radialFourScaledBoundary` aplicado a `physicalValues k 4 (principalInput a k)`. Não são vetores escolhidos para produzir uma Gram. Os números 10 e 77 vêm dos quatro coeficientes e jets originais, preservando sua fase imaginária.

`principal_boundary_eventually_exact` descarrega a regularidade com um limiar comum para todo a. `principal_boundary_tendsto` prova primeiro a convergência **do vetor completo**:

$$
 V_k(a)\longrightarrow V_\infty(a)=\frac{i}{\sqrt2}(0,a,0,1).
$$

Somente depois calculamos seu readout quadrático. `boundary_template_norm_sq`, `boundary_limit_norm_sq` e `boundary_limit_ne_zero` demonstram:

$$
\begin{aligned}
 \sum_{j<4}|V_k(a)_j|^2
 &=\frac{a^2+(10at)^2+(1+77at^2)^2}{2},\\
 \sum_{j<4}|V_\infty(a)_j|^2&=\frac{1+a^2}{2}>0.
\end{aligned}
$$

A soma é o tamanho nas **coordenadas de bordo já presentes no certificado coercivo**. Não a identificamos com a norma Cauchy nem com o Green.

Há ainda um controle uniforme, mais forte que tomar um a fixo e passar ao limite. `boundary_shear_lower` prova, para c²≤1/2,

$$
 \frac{a^2+1}{2}\le a^2+(1+ca)^2.
$$

Como c=77t² tende a zero independentemente de a, `principal_boundary_eventually_lower` conclui

$$
 \boxed{\forall^{\mathrm{ev}}k,\ \forall a\in\mathbb R,\quad
 \frac{1+a^2}{4}\le\sum_{j<4}|V_k(a)_j|^2.}
$$

Isso não descarta a terceira coordenada: sua contribuição permanece na identidade exata; sua não negatividade permite a estimativa inferior. Nenhuma componente física é removida.

### B.3 — Transporte da coercividade ao Green completo

`CoercivePhysicalMargin.lean` reutiliza literalmente `storage_one_fourSample_eventually_boundary_coercive`. `physical_four_boundary_coercive` verifica as coordenadas inversas e a igualdade exata de storage da #119 para obter

$$
 \varepsilon\sum_{j<4}|V_k(x)_j|^2\le
 2\operatorname{Re}B(U_k(x),U_k(x)).
$$

É o estado **inteiro** U, com suas duas pernas, amplitude, retorno, completion e métrica originais. Não se aplica a coercividade a uma cauda isotrópica como se ela fosse uma solução independente do retorno. Os defeitos de cabeça/cauda provados na #119 permanecem intactos.

Para a família principal, `principal_uniform_physical_margin` combina as duas desigualdades e dá μ=ε/8:

$$
 \boxed{\exists\mu>0,\quad\forall^{\mathrm{ev}}k,\ \forall a\in\mathbb R,\quad
 \mu(1+a^2)\le\operatorname{Re}B_k(X_k(a),X_k(a)).}
$$

O limiar é comum a **todos** os valores de a. O parâmetro eta continua sujeito apenas às condições originais 0<eta<1; `cross_green_eq_original` recompõe o mesmo estado, incluindo os nove cruzamentos bulk/bordo/commutator. Quatro endereços de entrada não significam truncamento do halo dos campos de saída.

A constante μ é existencial, obtida da coercividade histórica. Não calculamos seu valor decimal ou um limiar numérico K. A divisão por oito é consequência dos fatores demonstrados: storage=2B e a cota (1+a²)/4 do bordo, sem ajuste da fonte.

### B.4 — A margem chega ao limite canônico

Depois do transporte físico, `canonical_uniform_quadratic_margin` usa a identidade de limite já existente e a preservação de desigualdades **não estritas** por limites:

$$
 \boxed{\exists\mu>0,\quad\forall a\in\mathbb R,\quad
 \mu(1+a^2)\le h_3-2ah_2+a^2h_1.}
$$

A estriteza vem de μ(1+a²)>0. Não vem da inferência inválida de que uma sequência eventualmente positiva teria limite necessariamente positivo.

Finalmente, `canonical_second_shifted_schur_margin`, sob **somente a condição algébrica h₁≠0 para a divisão**, especializa a=h₂/h₁:

$$
 \exists\mu>0,\quad
 \mu\left(1+\left(\frac{h_2}{h_1}\right)^2\right)
 \le h_3-\frac{h_2^2}{h_1}.
$$

Esse é um transporte quantitativo ao segundo Schur deslocado, cujo sinal finito já era conhecido. Não é um novo pivô de ordem superior, nem se esconde a condição de denominador do teorema. A margem quadrática anterior não recebe nenhuma hipótese de positividade Hankel ou de sinal dos momentos.

## C — O que foi refutado ou delimitado

- **Positividade eventual sozinha é insuficiente.** A lacuna é fechada pela cota positiva persistente, não por uma regra de limite inexistente.
- **Norma de coordenadas não é o Green.** O vetor de bordo não nulo só produz a conclusão física porque a coercividade do mesmo storage já foi provada. Não substituímos essa desigualdade por uma igualdade Gram artificial.
- **Cancelar o dressing numa carta não muda a fonte.** Verificamos a transformação inversa e mantivemos o fator projetivo uma vez no coeficiente físico recebido pelo storage.
- **Dimensão quatro não implica toda ordem.** A constante vem de um certificado finito específico, não de uma nova lei para todos os tamanhos.

Não surgiram contraexemplos à fonte original. As obstruções da #118 sobre pesos monomiais positivos e da #119 sobre o grafo da cauda não são revogadas por esta margem do estado inteiro.

## D — O que permanece aberto

Não foi construída uma única família infinita Gram dos momentos, nem demonstrada positividade de todas as Hankel, nem controle de um operador de alturas infinito. Também não foi demonstrada convergência forte dos vetores da porta de energia: o limite vetorial provado é o da **carta de quatro jets**, com sua proveniência verificada.

A uniformidade obtida é no parâmetro a desta família e no limiar radial. Não é uma coerção por constante fixa vezes a norma bruta de X_k(a), que cresce com κ, nem uma constante uniforme em todas as ordens.

A dependência de sinal é explícita e legítima para este alvo: a coercividade N=4 e sua margem no bordo são teoremas anteriores da fonte. Não anunciamos que a positividade foi obtida apenas da geometria euclidiana do novo vetor ou sem as dependências analíticas da prova histórica.

Para aumentar a ordem, falta uma lei independente que controle a forma de bordo e o resto nativo no novo setor. Receber uma coercividade arbitrária como hipótese equivalente à positividade desejada não resolveria esse problema. Esta execução mostra como transportar e conservar uma margem **quando ela já foi provada para a fonte concreta**, sem confundir essa etapa com a descoberta de uma lei universal.

## E — Próximo passo mínimo e reprodução

O próximo alvo curto é transportar esta margem para a **fonte crítica completa `criticalOddSource`**, incluindo `defectInput`, antes de aumentar a ordem:

1. Reutilizar `complete_physical_source_split`, `critical_physical_split` e as identidades polarizadas de defeito da #117. Preservar os dois argumentos e a correção completa.
2. Calcular os quatro jets da entrada completa, ou provar uma cota uniforme da correção na escala κ⁻², usando sua dependência bilinear original em a,b.
3. Verificar se a margem μ(1+a²) absorve a correção para um limiar comum em a, sem descartá-la por tender a zero apenas para parâmetros fixos.

Isso testa a passagem da componente principal para o estado original completo. Não equivale a positividade all-order. Depois, a generalização útil é calcular os jets nativos nas ordens seguintes, separando a álgebra triangular da obrigação real de sinal e de resto; não construir uma nova fonte pelos momentos desejados.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem o cache opcional, `python3 validate.py` recompila os ancestrais. Para reproduzir após a limpeza, recrie um worktree da branch publicada, ligue `.lake` ao cache comum validado e entre na pasta da investigação. O cache de entrada é o da #119, SHA256 `248e66ce941e2eafaa92ab31a74e49a3de1da91cbf92590de6afe6bea36369fd`.

Foram reaproveitados **89 objetos ancestrais verificados** por fontes, hashes, árvore central, toolchain, manifest, fontes nativas e pins. Eles não são anunciados como recompilados nesta execução. Os três módulos novos e Audit são compilados novamente com warnings tratados como erros.

`mechanism_probe.py` executa **216 verificações com frações exatas**, incluindo coeficientes, os quatro jets, a estimativa uniforme, duas entradas independentes e o cancelamento de dressing em ambas as quadraturas complexas. sqrt(2) é fatorado de ambos os lados nos testes racionais; o Lean prova a igualdade com a raiz real efetiva. As amostras algébricas F,P verificam identidades, não substituem a característica nativa e não fornecem premissas de sinal. Não usamos zeros, alturas, momentos recalculados ou campanhas numéricas.

### Validação concluída

**16 checks passaram**, todos com exit 0, registrados em `evidence/validation.json` e `evidence/validation-console.log`. São **15 teoremas e 5 definições**, em três módulos matemáticos novos. Passaram os builds individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **216 verificações racionais** passaram.

As **20 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas e opacos via `value? (allowOpaque := true)`. O grupo de construção tem **16 raízes e 55.996 dependências**; o transporte da margem física tem **2 raízes e 66.951 dependências**. Em ambos estão proibidos os momentos canônicos e os atalhos escalares enumerados. Somente as **2 raízes de leitura final**, com **67.502 dependências**, permitem a definição dos momentos e a identidade de limite anterior.

Os dois grupos que usam sinal alcançam explicitamente `storage_one_fourSample_eventually_boundary_coercive` e `radialFourRegularizedStorage_eventually_unit_margin`. A construção das coordenadas e seu limite não usa esses certificados. Os dois teoremas de mera positividade eventual da #119 e os certificados N=7 estão proibidos em todos os grupos. Apenas `propext`, `Classical.choice`, `Quot.sound` são admitidos. Não há `sorry`, `admit`, `native_decide` ou axiomas matemáticos novos.

`evidence/kernel-audit-summary.json`, `evidence/preservation.json` e `SHA256SUMS` registram a trilha e a integridade da entrega. A validação observada foi local no host `llm`; não é uma afirmação de CI externo. A fonte, os pins, `main` e os trabalhos antigos permaneceram preservados.

A publicação é um commit e uma PR draft empilhada sobre a #119, sem merge. O arquivo de fontes e o cache verificados são copiados para o workspace local antes da remoção apenas do worktree próprio; a branch publicada permanece disponível.

Fim do relatório — margem física uniforme e sua passagem ao limite demonstradas em quatro fontes; positividade canônica all-order permanece aberta.
