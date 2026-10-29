# Transporte do limite Euler ao balanço físico e ao pareamento polarizado

Classificação: **PASS estrutural para o transporte solicitado, em toda ordem finita; PARTIAL para a positividade canônica all-order.**

Base exata: PR #124, commit `d75ee311ab5def510be07ac7dc65d866a59af728`, branch `agent/native-euler-newton-all-order`. Nova branch: `agent/native-moving-euler-balance`. Execução no host `llm`. A #124 foi conferida como draft aberta, sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

## A — O que já estava demonstrado

- A #123 fornece `physical_source_newton_all_order`, `physical_pair_newton_all_order` e `source_explicit_energy_control_all_order`: mesma fonte completa, mesmos coeficientes e controle de erro ε ||y||², uniforme nas entradas para cada ordem finita fixada.
- A #124 fornece `source_newton_path_tendsto` e `source_newton_path_eventually_bounded`: uma carta Euler móvel convergente dá coeficientes Newton convergentes a T₀w e eventualmente limitados na norma Pi original.
- O operador já contém `nativeSourceFiniteBoundaryEnergy_continuous`, no módulo `CompletedNativeChiralReturnArbitraryOrder.lean`. Sua prova usa a soma dos coeficientes com todos os cruzamentos. Reutilizamos essa continuidade; não sua equivalência posterior entre positividade e margem.
- `nativeSourceProjectiveBoundaryJetSynthesis_pairing` e `projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient` fornecem a expansão polarizada dos jets e seu limite. `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto` já identifica a expressão de bordo para coeficientes fixos.
- `primeDepthGeometricMoment_eq_canonical`, em `PrimeDepthGeometricMomentRecurrence.lean`, identifica a sequência da leitura nativa com `canonicalCompletedNativeLogDerivativeMoment`, pela recorrência e unicidade da derivada logarítmica.

A passagem desta etapa é de coeficientes **móveis** para o balanço físico e seu pareamento completo. A ortogonalização algébrica e uma interpretação positiva continuam sendo obrigações distintas. Não se usa positividade dos pivôs para construir os estados ou para provar o limite.

## B — O que foi demonstrado agora

As provas novas estão em [UniformMovingError.lean](UniformMovingError.lean), [MovingBalanceLimit.lean](MovingBalanceLimit.lean), [PolarizedBoundaryReadout.lean](PolarizedBoundaryReadout.lean) e [MovingPolarizedPair.lean](MovingPolarizedPair.lean).

### B.1 — O erro completo tende a zero

`uniform_quadratic_error_tendsto_zero` prova um lema quantitativo genérico: se ||y_k||≤C eventualmente e, para toda η>0, |f_k−g_k|≤η ||y_k||² eventualmente, então f_k−g_k→0. Não exige sinal de f ou g. A escolha η=ε/(C²+1) ajusta apenas a tolerância da estimativa existente, sem alterar a fonte ou seus pesos.

Para n fixado, considere fontes materiais x_k com suporte eventualmente em {0,...,2n−1}. Suponha explicitamente que sua carta Euler física converge a w. A #124 dá y_k→T₀w e uma cota eventual dos coeficientes. `physical_balance_error_tendsto_zero` aplica o controle nativo da #123:

$$4\operatorname{Re}\mathcal B(U_k(x_k),U_k(x_k))-E_{2n}(y_k)\longrightarrow0.$$

Aqui U é `physicalCompletedFiniteSource`, y é `newtonCoordinates` e E é exatamente `nativeSourceFiniteBoundaryEnergy`. O fator da norma não foi omitido.

### B.2 — Limite da energia original, com normalização conferida

`physical_balance_tendsto` combina o erro nulo com a continuidade preexistente de E:

$$\boxed{4\operatorname{Re}\mathcal B(U_k(x_k),U_k(x_k))\longrightarrow E_{2n}(T_0w).}$$

`physical_channel_balance_tendsto` usa a identidade original `signed_diagonal_norm`, segundo a qual 2 Re B = ||I||²−||R||². Portanto:

$$\|I_k\|^2-\|R_k\|^2\longrightarrow\tfrac12 E_{2n}(T_0w).$$

Nenhum vetor físico foi substituído por um limite de coordenadas. As normas separadas dos canais não precisam convergir para que esse balanço convirja.

### B.3 — O mesmo pareamento de bordo, em dois argumentos

`originalBoundaryPair` é somente uma **abreviação transparente** da expressão já presente em `nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto`:

$$L_n(u,v)=\sum_{i,j<n}\overline{e_i(u)}e_j(v)h_{i+j}
+\sum_{i,j<n}\overline{o_i(u)}o_j(v)h_{i+j+1},$$

onde e,o são as fases pares/ímpares nativas e h é `primeDepthGeometricMoment`. Não se define uma nova fonte, métrica ou kernel ajustado. A igualdade dessa sequência com a canônica já era um teorema anterior.

`original_boundary_pair_continuous` prova continuidade conjunta desse readout. `original_boundary_pair_diagonal` confere exatamente 4 Re L_n(y,y)=E_{2n}(y), pela unicidade dos dois limites antigos da **mesma síntese física**.

`native_moving_pairing_tendsto` generaliza o limite para coeficientes complexos móveis y_k→u e z_k→v. A prova conserva a soma completa em (Fin n ⊕ Fin n)² e aplica a cada cruzamento o limite do kernel nativo preexistente. Os termos entre paridades só se anulam depois desse limite comprovado.

`physical_moving_pairing_tendsto` transporta o resultado a duas fontes materiais móveis independentes, usando a igualdade vetorial completa antes do pareamento. Para cartas Euler convergentes a u e v:

$$\boxed{\mathcal B(U_k(x_k),U_k(z_k))\longrightarrow L_n(T_0u,T_0v).}$$

As duas fontes devem estar eventualmente suportadas no prefixo 2n. O índice radial k é comum às duas; não se reivindica aqui um limite bivariado em índices radiais arbitrariamente distintos. `physical_green_pairing_tendsto` aplica a igualdade anterior ao `crossGreenPair` completo, para a interface preexistente 0<eta<1.

### B.4 — Simplificação exata em coordenadas Euler

A #124 provou (T₀w)_m=sqrt(2) p_m i^m w_m, com p_m=(-1)^floor(m/2). Os lemas privados `even_limit_phase` e `odd_limit_phase` calculam as fases: p_{2j} i^{2j}=1 e p_{2j+1} i^{2j+1}=i.

`original_boundary_pair_euler_zero` demonstra, em dois argumentos independentes:

$$\boxed{L_n(T_0u,T_0v)=2L_n(u,v).}$$

As fases ímpares se cancelam por conjugação **dentro do readout de bordo já identificado**, depois de preservados os cruzamentos físicos no passo finito. O fator 2 vem das duas ocorrências de sqrt(2), sem ajuste de normalização.

`boundary_energy_euler_zero` conclui E_{2n}(T₀w)=2E_{2n}(w). Assim, `physical_euler_channel_balance_tendsto` fecha o transporte na forma mais direta:

$$\boxed{\|I_k\|^2-\|R_k\|^2\longrightarrow E_{2n}(w).}$$

`physical_green_pairing_euler_tendsto` fecha também a forma polarizada:

$$\boxed{\mathrm{crossGreenPair}_k(x_k,z_k)\longrightarrow2L_n(u,v).}$$

Essas identidades não afirmam que E ou L tenham sinal positivo.

## C — O que foi refutado ou delimitado

Não surgiu um NO-GO novo da fonte canônica. O transporte solicitado passou, com a mesma fonte, amplitude, métrica, retorno, completion e coeficientes.

O controle absoluto de erro e a continuidade determinam o limite; não determinam seu sinal. A identidade E(T₀w)=2E(w) conserva o sinal de E, em vez de fabricá-lo. Positividade das normas de cada canal também não determina o sinal da diferença.

As **627 regressões gaussianas racionais** comparam a fórmula por coeficientes originais e a fórmula por setores/fases, em dois argumentos complexos, incluindo os fatores 2 e 4. Usam pesos racionais livres, inclusive assinados, somente para testar a álgebra; não são momentos canônicos usados como entradas. Os controles positivos, negativos e nulos não afirmam que haja um valor canônico negativo. Os testes não substituem as provas Lean dos limites.

## D — O que permanece aberto

Os teoremas exigem convergência da carta Euler e suporte eventual no prefixo da dimensão fixada. Não foi demonstrado que toda família material possua essas propriedades. Não há uniformidade em n, limite de operadores infinitos ou convergência individual dos dois canais.

A ponte vetorial e a passagem ao readout original estão agora demonstradas para essas trajetórias. Falta uma propriedade independente da fonte que determine o sinal de E_{2n}(w) em toda ordem. Os certificados finitos anteriores continuam válidos, mas não são premissas das provas novas.

`nativeSourceEvenBoundary_positive_iff_stieltjes` já relaciona a positividade estrita dessa forma original à positividade de Stieltjes canônica. Essa equivalência não é uma prova incondicional de nenhum dos lados e não foi usada para obter sinais aqui. O teorema da continuidade de E também não usa a equivalência posterior entre positividade e margem do mesmo módulo.

## E — Próximo passo mínimo e reprodução

O alvo de transporte da #124 foi encerrado. A próxima investigação deve atacar o **sinal do retorno original**, sem outra mudança de coordenadas. Um teste concreto é retomar a direção crítica algébrica, mantendo apenas a inversibilidade necessária do bloco anterior, e procurar na identidade completa de retorno/fluxo um limite inferior para seu balanço que venha de uma propriedade da fonte independente da margem desejada.

A condição E_{2n}(w)>0, ou uma contração recebida como hipótese equivalente, não pode ser apresentada como esse mecanismo. O controle usado nesta etapa é absoluto, ε ||y||²; falta um controle de sinal relativo ao residual crítico. Essa obrigação de sinal já existia; não é anunciada como descoberta nova. Nesta execução não foi encontrada uma lei geométrica independente que a descarregue.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Após a limpeza, recrie um worktree da branch publicada e ligue `.lake` ao cache comum validado. O cache de entrada da #124 tem SHA256 `eb1554b0d4192043efc7979329b22136a8bc52b84895f3b5cffbb895e99bca81`.

São reutilizados 110 objetos ancestrais verificados contra as fontes efetivas, hashes, toolchain, manifesto, pins e fontes nativas. Os quatro módulos novos e Audit são compilados novamente com warnings como erros. Não se alteram módulos históricos, fontes, pesos, amplitudes, fases, métricas, dressing, completion ou pins.

### Validação concluída

**17 checks passaram**, todos com exit 0. São **13 teoremas e 1 abreviação pública**, em quatro módulos matemáticos novos, além de dois lemas privados de fase. Passaram as compilações individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **627 regressões gaussianas racionais** passaram. Os 110 objetos ancestrais foram verificados e reutilizados, sem anunciá-los como recompilados.

As **14 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas, opacos e os dois lemas privados de fase via `value? (allowOpaque := true)`. O grupo algébrico tem 1 raiz e 9304 dependências, com momentos e readout proibidos. O grupo de energia tem 4 raízes e 62167 dependências; verifica a presença efetiva do controle uniforme nativo e da cota/limite vetorial da #124. O grupo polarizado tem 9 raízes e 62494 dependências; verifica o limite do kernel nativo e a igualdade do estado completo.

Os certificados finitos de positividade/coercividade enumerados, incluindo a equivalência entre positividade e margem da forma de bordo, estão proibidos em todos os grupos. Nenhum foi usado. Só são aceitos `propext`, `Classical.choice`, `Quot.sound`; não há axiomas matemáticos novos, `sorry`, `admit` ou `native_decide`.

As evidências estão em `evidence/validation.json`, `evidence/lean-Audit.log`, `evidence/kernel-audit-summary.json` e `evidence/preservation.json`. `SHA256SUMS` registra a integridade da pasta. A validação observada foi no host `llm`, sem reivindicação de CI externo. A entrega usa PR draft empilhada sobre a #124, sem merge; fontes e cache verificados são preservados localmente antes da remoção somente do worktree próprio. Branch publicada e trabalhos anteriores são preservados.

Fim do relatório — transporte do balanço e dos cruzamentos móveis para o readout canônico original; positividade canônica all-order permanece aberta.
