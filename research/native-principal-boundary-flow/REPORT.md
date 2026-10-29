# Fluxo Green do principal nativo e papel misto da cauda

**Resultado: PARTIAL.** A orientação universal do sinal não foi demonstrada. Obtivemos o fluxo físico exato da componente principal da PR #117, com duas entradas independentes e o resto original completo. Há um **NO-GO específico** para inferir positividade desse fluxo apenas da positividade dos pesos de endereço ou de cada camada isolada da resposta.

Base: `47a0afdefd8694722d2ff8cbe0b0f5afc1e39cf3` (PR #117, branch `agent/native-critical-address-split`, aberta e draft na conferência). Branch nova: `agent/native-principal-boundary-flow`. PR empilhada, sem merge automático. A `main` continua `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`; o operador permanece `bfeb10fd2425400fa38139903d12bf0599f02e53`. Não se alteram fontes, pins, amplitudes, fases, normalizações, métricas ou trabalhos anteriores.

## A — O que já estava demonstrado

A PR #117 provou `critical_input_split`, `complete_physical_source_split`, `completed_parts_split`, os dois cancelamentos mistos e `principal_physical_grid`: o principal da PR #116 é o pareamento físico da componente literal X dos jets 1 e 3. Seu sinal permaneceu aberto.

Reutilizamos a direção original, o perfil O=`nativeOddProfile 1`, `coefficientWeight`, `monomialWeight`, `partField`, `completedSourceParts`, `physicalCompletedFiniteSource`, a forma quiral original e os nove cruzamentos de `crossGreenPair`. A recomposição e a regularidade radial são anteriores à extração escalar. `native_tail_samples` usa a mesma expansão analítica já demonstrada por `response_samples_prefix` e `nativeRemainder`, sem substituir a resposta por um polinômio truncado.

A identidade Euler/Green de toda ordem já existia no operador como `radialEulerPower_green_boundary`, para dados `Fin N`. Não reivindicamos a descoberta dessa identidade. Adaptamos o mecanismo às fontes `Finsupp` utilizadas por X, com todos os traços, e calculamos sua aplicação concreta à componente da PR #117. `part_field_add_weight`, `part_field_reconstruction`, `part_field_finite_locality`, `completed_source_contrast` e `contrast_mean_scale` são reutilizados diretamente.

A ortogonalização da PR #41 continua algébrica: a especialização crítica exige somente h₁≠0. A norma positiva do carrier, o sinal da forma quiral e o sinal do pivô continuam sendo propriedades distintas.

## B — O que foi demonstrado agora

### B.1 — Identidade de bordo em toda ordem, sem apagar o estado

D é o peso de endereço existente, `D c(j)=(j+1)c(j)`, e τ(c) é o valor em 1 da síntese Cauchy finita original. D não é o clock material logarítmico. κ=k+1 é o índice de regularização radial, não a profundidade Carry de uma câmera.

Se K₁ é o produto interno Cauchy original e

$$
\Phi_m(c,d)=\sum_{p=0}^{m-1}(-1)^p\overline{\tau(D^pc)}\,\tau(D^{m-1-p}d),
$$

`source_green_all_order` demonstra, para qualquer m e quaisquer duas fontes complexas finitas:

$$
 K_1(c,D^md)-(-1)^m K_1(D^mc,d)=\Phi_m(c,d).
$$

Nenhum traço foi suprimido e nenhum domínio global sem bordo foi presumido. Para perfis imaginários, incluindo as duas entradas X, `odd_monomial_flux` identifica a soma dos dois kernels ordenados da camada ímpar de endereço com esse fluxo. A fase imaginária e sua conjugação entram efetivamente na prova.

### B.2 — Traços concretos de X e sinais distintos entre camadas

Mantemos exatamente

$$
 X_k(a)=(\kappa^3+12a\kappa)O+a\kappa D^2O.
$$

`principal_boundary_trace` e suas especializações calculam:

$$
\begin{aligned}
\tau(X_k(a))&=0,\\
\tau(DX_k(a))&=ia\kappa,\\
\tau(D^2X_k(a))&=10ia\kappa,\\
\tau(D^3X_k(a))&=i(\kappa^3+77a\kappa).
\end{aligned}
$$

Os números 10, 65 e 77 vêm das diferenças finitas originais e dos coeficientes de Stirling já certificados. Em particular 77=12+65; não há parâmetro ajustado.

Com a,b independentes, `principal_flux_first`, `principal_flux_cubic` e `principal_flux_quintic` demonstram:

$$
\begin{aligned}
\Phi_1(X_a,X_b)&=0,\\
\Phi_3(X_a,X_b)&=-ab\kappa^2,\\
\Phi_5(X_a,X_b)&=-(a+b)\kappa^4-54ab\kappa^2.
\end{aligned}
$$

O fator 54 é `2(12+65)−10²`. Ele resulta dos cruzamentos de bordo, que não podem ser trocados por quadrados isolados.

### B.3 — Fluxo físico completo com o resto analítico nativo

B é a forma original `canonicalCompletedNativeProjectiveChiralForm`, isto é, metade da diferença entre os dois pareamentos das pernas. Não foi mudado esse fator. `principal_physical_flow` primeiro demonstra a divisão com três coeficientes reais livres, sem usar momentos canônicos como entradas da componente X.

Somente depois, `native_principal_flow` substitui os coeficientes efetivos da derivada da resposta: h₀, −h₁, h₂. O resultado é, eventualmente em k,

$$
\boxed{B_k(X_k(a),X_k(b))=
 ab h_1-(a+b)h_2-\frac{54ab h_2}{\kappa^2}+\mathcal T_k(a,b).}
$$

A mesma resposta completa está presente em T. `original_field_head_tail` conserva cada campo bulk/bordo/commutator como vetor antes do pareamento; `original_vector_head_tail` recompõe a síntese inteira. `native_tail_samples` identifica o resto exatamente com `δ⁷ remainderSamples 3 δ`, onde δ=1/κ. `native_tail_field_fixed` e `native_principal_tail_fields` transportam isso a todos os três campos, inclusive para X dependente de k e seu halo de saída. Não há descarte de termos de ordens superiores.

A realidade de T é provada em `principal_tail_flux_real`, depois de preservar a forma complexa e ambas as quadraturas. O resultado não deriva uma norma positiva para T.

`native_principal_tail_tendsto` obtém Tₖ(a,b)→h₃. Esse limite reutiliza `principal_physical_tendsto` da PR #117; não é uma nova prova independente do sinal de h₃ ou do pivô.

### B.4 — O resto é uma componente com duas pernas iguais; seu efeito é misto

`tailComponent` é o vetor do resto da mesma síntese, inserido igualmente nas duas pernas, com a amplitude original. `headComponent` é a diferença literal entre o estado original e essa componente. São componentes de uma decomposição; não são outra fonte completada, outra métrica ou operadores de retorno independentes.

`tail_parts_reconstruct` recompõe a componente a partir dos seus três campos originais. `complete_state_head_tail` conserva o estado inteiro. `head_preserves_contrast` mostra que o contraste original não foi removido.

Chamando Uₖ(a) o estado original de X e Eₖ(a) sua componente de resto, `tail_pairing_zero` dá

$$
 B(E_k(a),E_k(b))=0.
$$

Isso não identifica E com zero nem autoriza seu quociente. `tail_mixed_physical_flux` demonstra que o efeito que permanece é exatamente

$$
\boxed{\mathcal T_k(a,b)=B(U_k(a),E_k(b))+B(E_k(a),U_k(b)).}
$$

É a soma dos dois cruzamentos ordenados, não uma energia separada positiva do resto. `tail_scale_calibration` recupera o fator 2κ da amplitude nativa; nenhuma constante é escolhida para ajustar a identidade. `head_physical_flow` identifica o fluxo das três primeiras camadas com a forma assinada da componente literal head.

As componentes vivem no mesmo carrier completado. Não se afirma que sejam, separadamente, soluções independentes de todas as condições de retorno ou pertencentes a todos os domínios de clocks não limitados. Nenhum novo operador não limitado é aplicado a elas. O estado original e seus mapas físicos permanecem preservados.

### B.5 — Direção crítica e obrigação residual exata

Com a=b=h₂/h₁ e somente h₁≠0, `critical_tail_budget_exact` demonstra:

$$
 B_k(X_{a_*},X_{a_*})=
 \mathcal T_k(a_*,a_*)-\frac{h_2^2}{h_1}
 -\frac{54}{\kappa^2}\frac{h_2^3}{h_1^2}.
$$

Essa é uma identidade, não uma prova de que o resto supera as parcelas subtraídas. A comparação correspondente é equivalente ao sinal desta forma; não a apresentamos como uma causa geométrica independente.

## C — O que foi refutado

`oriented_cubic_nonnegative` demonstra que a camada com coeficiente −v é não negativa na diagonal se v≥0. Entretanto, `oriented_quintic_negative` demonstra que a camada seguinte, com coeficiente q>0, é estritamente negativa para a>0, em qualquer k.

Mais concretamente, `raw_quintic_counterexample` calcula na mesma métrica e no mesmo X, sem momentos como entradas:

$$
 \operatorname{Re}\,\mathrm{symKernel}_{(j+1)^5}(X_0(1),X_0(1))=-56.
$$

Todos os pesos `(j+1)⁵` são estritamente positivos. `positive_weight_not_sufficient` formaliza o contraexemplo à inferência de que isso bastaria para orientar positivamente o fluxo Cauchy/Green.

A razão precisa é que `⟨S c,S(Wc)⟩` não é automaticamente `‖S(√W c)‖²`: as features Cauchy têm cruzamentos, e pesos diagonais positivos nas coordenadas de endereço não são automaticamente um operador positivo na métrica física. Não se altera essa métrica para contornar a obstrução.

**Alcance do NO-GO:** refuta positividade por camada ou apenas por pesos pontuais positivos. O peso monomial é uma camada da resposta, não a resposta nativa completa. Não é um contraexemplo à positividade canônica nem à geometria Carry.

## D — O que permanece aberto

Não foi demonstrada uma orientação universal do fluxo completo, uma lei de sinal para todos os pivôs ou uma representação Gram positiva all-order dos momentos canônicos. A identidade Green em toda ordem não é uma desigualdade de toda ordem.

O novo resultado identifica precisamente onde uma eventual lei deve atuar: no pareamento misto do resto nativo com o estado inteiro. Sua autoforma nula não permite eliminá-lo, e a positividade isolada de alguma energia ou peso não determina os cruzamentos.

A identificação concreta usa os jets 1 e 3, como na PR #117. O alcance em toda ordem de `source_green_all_order` diz respeito à potência de endereço e a fontes finitas arbitrárias; não reivindica uma construção positiva simultânea de todas as Hankel.

## E — Próximo passo mínimo e reprodução

O próximo teste deve usar a componente E agora tipada, e tentar derivar sua relação com o retorno original **antes de aplicar uma desigualdade de sinal**. A obrigação curta é identificar um transporte/fatoração literal para os dois mapas que aparecem em `tail_mixed_physical_flux`, incluindo o mesmo contraste, bordo e completion. O teste deve manter a,b independentes e conferir o primeiro coeficiente e os cruzamentos antes de tentar generalização.

Não basta provar que o resto tem norma positiva: seu efeito é misto e sua autoforma quiral é zero. Também não basta receber `T≥orçamento` como premissa; a última fórmula já mostra que isso renomeia a obrigação de sinal. Se uma nova aplicação de Green apenas reproduzir a mesma comparação sem uma relação independente do retorno, ela não reduz a lacuna.

Comandos no host llm, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem o arquivo opcional de cache, `python3 validate.py` recompila os ancestrais. Para reproduzir após a limpeza, recrie um worktree da branch publicada, ligue `.lake` ao cache comum validado do repositório e entre na pasta da investigação. O arquivo opcional `.cache/input-cache.tar.gz` está identificado por hash em `evidence/cache-restoration.json`.

O cache reutiliza **81 objetos ancestrais com verificação** de fontes, objetos, árvore central, toolchain, manifest, fontes nativas, pins e estados. Eles não são anunciados como recompilados nesta execução. Os quatro módulos novos e Audit são compilados de novo, com warnings tratados como erros.

`mechanism_probe.py` realiza **235 verificações com frações gaussianas exatas**, incluindo ambas as quadraturas, a identidade Green geral, as entradas independentes, fluxos das camadas, decomposição head/tail e os dois pareamentos mistos. Para testar as amplitudes quirais sem arredondamento, usa κ=2r², quando os fatores correspondentes são gaussianos racionais. Não usa valores de momentos, zeros ou alturas e não simula a característica nativa como evidência de sinal.

### Validação concluída

**17 checks locais passaram**, todos com exit 0, registrados em `evidence/validation.json` e `evidence/validation-console.log`. São **49 lemas novos e 9 definições/abreviações**, em quatro módulos novos. Esses módulos e `Audit.lean` foram compilados de novo com warnings tratados como erros. Passaram `lake build --wfail`, os alvos nativos selecionados e as auditorias Foundation/Geometry/Analysis.

As **58 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos. A construção contém 51 raízes e 5.558 dependências: a definição dos momentos canônicos, as fórmulas escalares da grade e os atalhos antigos de sinal/assintótica enumerados são proibidos. As 7 raízes de proveniência contêm 5.635 dependências e permitem a definição dos momentos para a especialização nativa e o limite já conhecido; continuam proibindo os certificados de sinal enumerados. Apenas `propext`, `Classical.choice`, `Quot.sound` são aceitos. Não há axiomas matemáticos novos, `sorry`, `admit` ou `native_decide` nos módulos novos.

`evidence/preservation.json` e `SHA256SUMS` registram a preservação e a integridade dos arquivos. A validação foi executada no host llm; não se apresenta uma execução de CI externa como se tivesse sido observada. A limpeza do worktree próprio depende de commit, push e conferência do arquivo e do cache locais. Os trabalhos anteriores e a branch publicada são preservados, sem merge.


Fim do relatório — fluxo completo identificado; a orientação universal do pareamento misto permanece aberta.
