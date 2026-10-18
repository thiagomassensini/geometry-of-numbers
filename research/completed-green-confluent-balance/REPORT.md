# Balanço Green completado: energia do forcing e compensação central

## Resultado

**PARTIAL — identidade física de compensação demonstrada; sinal all-order OPEN.**

A tentativa localizou e resolveu uma obrigação algébrica concreta: o termo forcing–forcing reduzido é negativo de posto um, mas é exatamente a subtração de Schur da linha central do coeficiente físico restante. Não é preciso postular seu cancelamento ou apagar o complemento escondido pelo readout. O sinal do restante ainda não foi demonstrado.

Não há `PASS_ALL_ORDER`, nova representação Gram positiva ou nova desigualdade estrita para um pivô ainda aberto. A obstrução do PR #36 permanece específica do Krylov material; este trabalho usa o par fonte/companheiro completado e não foi encerrado por aquela obstrução.

## Base e preservação

- Base: `origin/main` verificado em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Branch: `agent/completed-green-confluent-balance`, separada dos PRs #34, #35 e #36.
- Repositório editado: `geometry-of-numbers`, no host `llm`.
- Operador consultado: `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. Nenhuma alteração; os dois arquivos de usuário não rastreados foram preservados e têm hashes conferidos.
- Nenhum worktree criado. Os worktrees anteriores não foram alterados.
- Mesma fonte, amplitudes, fases materiais, endereços, readout, retorno global, dressing, métrica e pins. Somente módulos novos e seu registro no import/audit de Analysis.
- Sem merge automático, conforme o pedido do usuário.

## A. Qual objeto físico existente foi usado?

O par efetivo é `carryMaterialCompanionValuePair`, construído no carrier original seed ⊕ (gradiente material ⊕ retorno global). Se

\[
Z(t)=D(t)Y(t),\qquad F(t)=\ell(Z(t)),
\]

então o par é `C(t)=(-Z'(t),2Z(t))`, com derivada forte real no domínio já demonstrado. O readout é exatamente `(-F'(t),2F(t))`. Sua forma Green é a convenção original `inner x₂ y₁ - inner x₁ y₂`.

O teorema anterior `CarryMaterialGreenPairComparison.material_pair_corrected_green` já identifica a diferença **Green físico menos Green escondido** com o Wronskiano nativo completado. Isso não identifica um Gram positivo. O novo trabalho reaproveita essa arquitetura, sem reconstruí-la e sem trocar a fonte por seus momentos.

O dressing mantém suas derivadas e seu completion arquimediano. Não se identifica esta forma com o Gram Gamma bruto nem se cancela o defeito Gamma/compressed por uma hipótese nova. A ligação positiva entre esses objetos continua sem prova.

## B. Identidades novas e convenções exatas

Denote:

\[
a=\texttt{carryMaterialResponseScale}=h_0>0,
\quad w=\texttt{carryMaterialClockCentralForcing},
\quad f(t)=\texttt{carryMaterialClockForcingScalar}(t),
\quad v(t)=f(t)w.
\]

`w` é o forcing já construído a partir do clock e do centro físico original; `v(t)` é literalmente o primeiro slot de `carryMaterialClockForcingPair t`. Sua escolha não recebe momentos-alvo. A redução projetiva que usa `a` também já existia e é derivada do response da mesma fonte.

### Energia negativa identificada, antes de extrair um sinal global

O novo coeficiente exato é

\[
\mathcal F(t,u)=-a\langle v(t),v(u)\rangle_{\mathbb C}.
\]

A fórmula vetorial de Green com o fator `(u-t)` já era conhecida. Agora são demonstrados sua extensão contínua, energia bilinear para famílias independentes e sinal efetivo da fonte:

\[
G(\operatorname{red}_tF_t,\operatorname{red}_uF_u)
=(u-t)\mathcal F(t,u),
\]

\[
\boxed{\quad
\operatorname{Re}\sum_{i,j}\overline{c_i}\mathcal F(t_i,t_j)c_j
=-h_0\left\|\sum_i c_i v(t_i)\right\|^2\le0.
\quad}
\]

O vetor `v(0)` é não nulo por propriedades do mesmo forcing e do dressing. Portanto `Re 𝓕(0,0)<0` sem assumir qualquer sinal Hankel all-order. Isso exclui usar **este canal isolado** como Gram positivo; não exclui o balanço completado.

Nomes principais: `carryMaterialForcingGreen_bilinear`, `carryMaterialForcingGreen_energy`, `carryMaterialForcingGreen_continuous`, `source_forcing_energy`, `source_forcing_origin_neg`.

### Restante físico e cancelamento central

`carryMaterialForcingRemainderGreen` é a soma dos canais Green central/central, compressed/compressed e **ambos** os cruzamentos compressed/forcing, menos o Green do complemento escondido pelo readout. Não se atribui sinal a essa soma.

Escreva `R_s(t,u)=carryMaterialRealResidual t u`, o residual da fonte já existente. A identidade anterior da fonte dá, numa vizinhança comum de zero, o coeficiente

\[
\mathcal B(t,u)
=2a^2tu\,\overline{F(t)}F(u)R_s(t,u).
\]

O coeficiente restante é

\[
\mathcal R(t,u)=\mathcal B(t,u)-\mathcal F(t,u).
\]

`physical_remainder_factor` prova, a partir dos canais físicos completos,

\[
\texttt{carryMaterialForcingRemainderGreen}(t,u)
=(u-t)\mathcal R(t,u).
\]

No conjunto regular `u≠t`, `physical_remainder_regular` identifica o quociente efetivo. No centro, `physical_remainder_zero_row` e `physical_remainder_origin_limit` provam a linha física inteira e o limite real do quociente perfurado. A diagonal central não é preenchida com zero por convenção. Não se afirma aqui um teorema novo de regularidade Hilbert all-order ou de unicidade da extensão em todas as outras colisões.

A linha central satisfaz

\[
\mathcal R(0,u)=-\mathcal F(0,u),\qquad
\mathcal R(t,0)=-\mathcal F(t,0),\qquad
\mathcal R(0,0)=a\|v(0)\|^2>0.
\]

Como `v(t)` está na mesma linha física `ℂw`, obtém-se o resultado central desta rodada:

\[
\boxed{\quad
\mathcal R(t,u)-
\frac{\mathcal R(t,0)\mathcal R(0,u)}{\mathcal R(0,0)}
=\mathcal B(t,u).
\quad}
\]

Nome: `physical_forcing_schur`. A igualdade é válida sem supor positividade de `𝓡`, de `R_s` ou de Hankel. O pivô central é estritamente positivo por uma norma física e pelo sinal zeroth já conhecido, não por um pivô novo presumido.

Para toda família finita, `physical_remainder_energy` conserva as duas quadraturas e todos os cruzamentos:

\[
\operatorname{Re}\sum_{i,j}\bar c_i\mathcal R(t_i,t_j)c_j
=\operatorname{Re}\sum_{i,j}\bar c_i\mathcal B(t_i,t_j)c_j
+a\left\|\sum_i c_i v(t_i)\right\|^2.
\]

`completed_coefficient_bilinear` identifica `𝓑` como a congruência literal de `R_s`, com pesos `tF(t)` e fator `2a²`, para **dois argumentos e duas famílias de coeficientes independentes**. Não se excluem fases ou termos mistos para obter essa fórmula.

## C. O que a tentativa resolveu e o que não resolveu?

Resolveu a origem, o posto, o sinal e a compensação central do canal negativo de forcing. Seu cancelamento é agora uma igualdade da fonte, não uma hipótese nem uma normalização ajustada.

A tentativa de obter positividade termo a termo encontra uma obstrução concreta: o canal forcing–forcing reduzido tem uma diagonal estritamente negativa. A tentativa de concluir positividade do balanço completo continua **OPEN**; essa diagonal isolada não a refuta.

Não foi encontrada uma realização Gram para os canais restantes. A igualdade de Schur não torna automaticamente mais fraca a obrigação de sinal: provar apenas que `𝓡` é positivo, sem derivá-lo da geometria física, recolocaria o problema como hipótese. Nesta rodada não se usa esse caminho para anunciar sucesso.

## D. Kernel, regressões e alcance

São 25 teoremas públicos novos: 12 na biblioteca e 13 na pesquisa, além de cinco definições de observação. Todas as 30 raízes têm `#print axioms` e guard transitivo de tipos/corpos, permitindo somente `propext`, `Classical.choice`, `Quot.sound`. Inventário exato em `public-roots.json`.

O teste `low_order_source_regression` conserva:

\[
a=h_0,\qquad R_{s;1,1}=h_1,\qquad
R_{s;2,2}=h_2-h_1^2/h_0.
\]

Os índices depois do ponto e vírgula são ordens confluentes de Taylor do residual, não índices materiais nem profundidades. A última entrada conserva o cruzamento central. Os teoremas anteriores de paridade continuam disponíveis para as demais ordens; não foram usados para escolher vetores.

H6/K6 e a família de doze fontes não foram alterados nem usados para definir este candidato. Os novos módulos não dependem dos resultados do PR #36 e não duplicam o trabalho do sétimo pivô do PR #34. Não se recalcularam momentos ou certificados theta; não há teste decimal usado como premissa.

Os resultados da biblioteca sobre sinal têm explicitamente `a≥0` ou `a>0` onde necessário; o módulo de pesquisa descarrega essa condição usando o teorema existente `material_scale_pos`, derivado do momento zeroth da fonte. O Schur e a energia da fonte não recebem positividade Hankel all-order.

**Não provado:** não negatividade de `R_s` em todas as famílias, positividade de `𝓡`, Gram física infinita coerente, PSD/PD canônica all-order ou dominância Gamma/retorno. Nenhum resultado sobre zeros, alturas ou medida positiva presumida entra nas provas.

## E. Menor próxima obrigação matemática

O ponto físico agora explícito é demonstrar, da soma de canais que define o restante, a desigualdade relativa

\[
\operatorname{Re}\sum_{i,j}\bar c_i\mathcal R(t_i,t_j)c_j
\ \ge\ a\left\|\sum_i c_i v(t_i)\right\|^2
\]

para todas as famílias pertinentes, incluindo as direções que anulam `∑cᵢv(tᵢ)`. A igualdade desta rodada mostra exatamente o que essa dominância descontaria. Não basta controlar só a diagonal nem acrescentar um orçamento absoluto de cauda.

O próximo ataque útil é procurar uma identidade Green/Bessel para os **quatro canais restantes e o complemento escondido**, preservando a conexão do dressing e o retorno. A redução de posto um não fornece essa desigualdade e não a torna independente do objetivo por mera renomeação; um avanço de sinal exige uma propriedade física adicional demonstrada para esses mesmos canais.

## Reprodução e evidências

Biblioteca: [CarryMaterialForcingGreenEnergy.lean](../../GeometryOfNumbers/Analysis/CarryMaterialForcingGreenEnergy.lean) e sua auditoria. Ponte com a fonte: [SourceBalance.lean](SourceBalance.lean) e [Audit.lean](Audit.lean).

```bash
python3 research/completed-green-confluent-balance/check_sources.py
python3 research/completed-green-confluent-balance/validate.py
python3 research/completed-green-confluent-balance/verify_evidence.py
```

`validate.py` executa nove comandos: verificação de fontes; build focado com `--wfail`; compilação explícita dos módulos de pesquisa com warnings como erros; build de raiz com `--wfail`; auditorias Foundation/Geometry/Analysis; `git diff --check`. `compile_module.sh` reutiliza o ambiente cruzado já existente do operador, sem dependência ou pin novo.

`source-manifest.json` registra fontes novas, fontes reutilizadas e arquivos preservados do operador. `evidence/validation.json` registra comandos, exit codes, duração e hashes dos logs comprimidos. `verify_evidence.py` valida os logs e o manifesto. O estado final dos checks fica em `VALIDATION.md`; a entrega local registra o commit e a URL do PR. Sem merge automático.
