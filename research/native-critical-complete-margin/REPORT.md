# Margem uniforme da fonte crítica completa e controle nativo do defeito

**PASS para o transporte finito solicitado; PARTIAL para a positividade canônica em toda ordem.** A margem da PR #120 foi transportada de `principalInput` para a `criticalOddSource` original completa. A correção `defectInput` foi conservada, com identidade polarizada e controle uniforme O(|ab|/(k+1)²). Um novo lema de trajetórias obtém limites de energia diretamente da fonte e do vetor de bordo, sem usar momentos como entradas.

Base exata: `be8927f6a43580e25a5776e4794ae5afc6f77166`, branch `agent/native-four-boundary-margin`, PR #120, aberta e draft na inspeção inicial. Nova branch: `agent/native-critical-complete-margin`, empilhada sobre a #120. Host: `llm`. Repositório nativo consultado: `carry-self-adjoint-operator`, commit `bfeb10fd2425400fa38139903d12bf0599f02e53`.

Não há merge automático nem modificação de fontes, fases, amplitudes, pesos, métricas, completion, pins, módulos históricos ou trabalhos anteriores. Nesta investigação k é o **índice radial de regularização**, não a profundidade vertical Carry. Escrevemos κ=k+1 e t=1/κ.

## A — O que já estava demonstrado

A #117 forneceu a decomposição literal de coeficientes e dos estados completos:

$$C_k(a)=X_k(a)-Y_k(a),$$

com C=`criticalOddSource`, X=`principalInput`, Y=`defectInput`. `complete_physical_source_split` conserva as duas pernas; `completed_parts_split` conserva os três campos Green. As identidades `principal_defect_kernel_orthogonal`, `defect_principal_kernel_orthogonal` e `critical_kernel_split` mantêm os cruzamentos e sua orientação assinada.

A #119 ligou os coeficientes físicos c_j=A_{k,j}x_j ao storage original, com a amplitude projetiva uma única vez e sqrt(κ) na síntese incidente existente. A #120 verificou a carta de valor, sua inversão e o bordo principal, e demonstrou `principal_uniform_physical_margin`:

$$\exists\mu>0,\quad\forall^{\mathrm{ev}}k,\ \forall a,\quad
\mu(1+a^2)\le\operatorname{Re}B_k(X_k(a),X_k(a)).$$

Seu ingrediente de sinal é a coercividade nativa **já provada para quatro fontes**. Não refazemos nem aumentamos esse certificado.

Também já existiam `storage_one_fourSample_eventually_regularized`, `radialFourRegularizedStorage_continuousAt`, `radialFourRegularizedStorage_zero` e a reconstrução inversa da carta de quatro jets. Esses resultados mantêm o resto analítico da mesma fonte. Foram reutilizados para obter um limite de trajetórias sem passar pela definição dos momentos canônicos.

## B — O que foi demonstrado agora

Os novos nomes pertencem ao namespace `CarryCriticalComplete`, em quatro módulos matemáticos.

### B.1 — A correção e os quatro jets da entrada completa

`CriticalBoundaryTransport.lean` define `sourceBoundary` pela carta já existente aplicada aos coeficientes físicos originais. `physical_values_sub`, `physical_values_smul`, `source_boundary_sub` e `source_boundary_smul` provam sua linearidade exata. `critical_boundary_split` transporta C=X−Y a **todos os quatro dados**, sem descartar componentes.

As fórmulas literais de coeficientes são provadas em `defect_coefficient_formula` e `critical_coefficient_formula`:

$$
\begin{aligned}
Y_k(a)&=\frac{7ia\kappa}{6}(-1,6,-9,4),\\
C_k(a)&=\frac{i\kappa}{6}
(-\kappa^2-6a,\ 3\kappa^2+6a,\ -3\kappa^2,\ \kappa^2).
\end{aligned}
$$

Regularidade é hipótese explícita em `critical_boundary_exact` e `defect_boundary_exact`. `boundary_eventually_exact` fornece um limiar comum para todo a. Nessa carta nativa:

$$
\boxed{V^C_k(a)=\frac{i}{\sqrt2}(0,a,3at,1+7at^2),\qquad
V^Y_k(a)=\frac{i}{\sqrt2}(0,0,7at,70at^2).}
$$

A subtração da correção muda exatamente 10→3 e 77→7 nos jets principais da #120. Não há mudança de amplitude ou nova normalização: o fator 1/sqrt(2) vem do cancelamento de dressing **na carta de valor já existente**, cuja inversão física foi provada na #120.

`critical_boundary_tendsto` e `defect_boundary_tendsto_zero` demonstram primeiro os limites vetoriais completos:

$$V^C_k(a)\to\frac{i}{\sqrt2}(0,a,0,1),\qquad V^Y_k(a)\to0.$$

`critical_template_norm_sq` mantém as quatro parcelas no cálculo, e `critical_boundary_uniform_lower` prova uma cota comum para todos os parâmetros:

$$\forall^{\mathrm{ev}}k,\ \forall a,\quad
\frac{1+a^2}{4}\le\sum_{j<4}|V^C_k(a)_j|^2.$$

Essa soma é uma leitura nas coordenadas antigas de bordo. Não é identificada com a métrica Cauchy nem com o Green.

### B.2 — Novo lema de trajetórias, diretamente da fonte completada

Em `FourSourcePathLimit.lean`, `physical_boundary_regularized` prova, para a mesma função resto R analítica e um limiar comum a todos os x com suporte nos quatro endereços:

$$2\operatorname{Re}B(U_k(x),U_k(x))
=\mathrm{RegularizedStorage}(R,t,\mathrm{sourceBoundary}(k,x)).$$

A prova usa a reconstrução inversa da carta e recupera exatamente o coeficiente físico c_j=A_jx_j antes de aplicar `original_source_storage`. O resto inteiro não é substituído por um polinômio escolhido.

`four_source_path_energy_tendsto` é o lema reutilizável novo. Para qualquer trajetória de coeficientes x_k suportada nos quatro endereços, se seu **vetor de bordo** converge para v, então

$$
\boxed{\operatorname{Re}B(U_k(x_k),U_k(x_k))
\longrightarrow\frac{\mathrm{nativeSourceFourBoundaryEnergy}(v)}2.}
$$

Não se supõe positividade, sinal de pivô, momentos canônicos ou limitação dos coeficientes brutos x_k. O argumento é a continuidade da expressão analítica exata da fonte, depois da convergência vetorial. É válido para trajetórias móveis inteiras nessa dimensão, não apenas para um coeficiente de teste fixo. Não é afirmado aqui um teorema para N arbitrário.

### B.3 — Síntese polarizada e limiar comum para a decomposição física

Em `DefectUniformControl.lean`, `regular_imaginary_pair_exact` reaproveita `complete_complex_pair` com regularidade explícita de um prefixo, independente do parâmetro. Isso permite fortalecer a organização dos quantificadores: `critical_split_uniform` prova

$$
\boxed{\forall^{\mathrm{ev}}k,\ \forall a,b,\quad
 B_k(C_k(a),C_k(b))=B_k(X_k(a),X_k(b))+B_k(Y_k(a),Y_k(b)).}
$$

A igualdade é **complexa**, em dois argumentos independentes. Os termos mistos entre X e Y cancelam na síntese completa pela identidade de kernel anterior; não são omitidos por uma hipótese de ortogonalidade positiva. Não se afirma que cada cruzamento isolado dos campos Green seja zero. `cross_green_eq_original` conserva a recomposição dos nove cruzamentos bulk/bordo/commutator e o halo de saída.

`defect_input_scale` e `defect_pair_factor` dão a fatoração complexa exata, para qualquer k:

$$Y_k(a)=aY_k(1),\qquad B_k(Y_k(a),Y_k(b))=ab\,B_k(Y_k(1),Y_k(1)).$$

As duas quadraturas são mantidas até essa identificação. Só depois `defect_pair_re_factor` aplica a parte real necessária ao sinal.

### B.4 — Pequenez uniforme e taxa quadrática sem momentos como entradas

Aplicando o lema de trajetórias ao **mesmo** Y, seu vetor de bordo tende a zero; `defect_energy_tendsto_zero` conclui

$$\operatorname{Re}B_k(Y_k(1),Y_k(1))\to0.$$

Não se recebe esse limite como hipótese nem se usa o limite escalar antigo expresso por h₂. A auditoria proíbe `defect_physical_tendsto_zero` e `defect_physical_scaled_tendsto` como dependências dos novos resultados.

Para obter a taxa, analisamos κY_k(1), exclusivamente como escala de observação do mesmo canal. `defect_scaled_boundary_tendsto` conserva o vetor e mostra

$$\mathrm{sourceBoundary}(k,\kappa Y_k(1))\to W=\frac{i}{\sqrt2}(0,0,7,0).$$

Por homogeneidade da síntese original e o mesmo lema de trajetórias, `defect_scaled_energy_limit` prova

$$\kappa^2\operatorname{Re}B_k(Y_k(1),Y_k(1))
\to L=\frac{\mathrm{nativeSourceFourBoundaryEnergy}(W)}2.$$

O coeficiente é uma leitura da fonte já existente; nenhum sinal é presumido para L. `defect_uniform_quadratic_rate` escolhe uma cota M>0 para esse limite e sua vizinhança e obtém

$$
\boxed{\exists M>0,\quad\forall^{\mathrm{ev}}k,\ \forall a,b,\quad
|\operatorname{Re}B_k(Y_k(a),Y_k(b))|
\le\frac{M|ab|}{\kappa^2}.}
$$

Separadamente, `defect_uniform_relative_small` dá, para qualquer ε>0, um limiar comum em a,b com cota ε|ab|. `critical_principal_uniform_close` transporta esse controle à diferença entre os **Green completos** de C e X, depois da igualdade polarizada.

A uniformidade é relativa ao fator |ab|. Não se afirma pequeno erro absoluto para parâmetros sem limite. A observação escalada não substitui a fonte na prova de positividade; seu único uso é identificar e limitar a taxa real da correção.

### B.5 — A margem da #120 chega à fonte crítica original inteira

Em `CriticalCompleteMargin.lean`, `critical_uniform_physical_margin` combina a margem principal μ(1+a²) com o controle do defeito, escolhendo ε=μ/2. Para a=b, |ab|=a². A comparação completa dá

$$
\operatorname{Re}B_k(C_k(a),C_k(a))
\ge\mu(1+a^2)-\frac\mu2a^2
\ge\frac\mu2(1+a^2).
$$

Portanto:

$$
\boxed{\exists\nu>0,\quad\forall^{\mathrm{ev}}k,\ \forall a\in\mathbb R,\quad
\nu(1+a^2)\le\operatorname{Re}B_k(C_k(a),C_k(a)),\qquad\nu=\mu/2.}
$$

O limiar é comum a todos os a. A correção não é descartada por tender a zero para cada parâmetro fixo; sua fatoração e o controle uniforme são usados efetivamente na prova.

`critical_native_energy_limit` calcula ainda o limite físico da fonte completa pela carta vetorial e pelo resto analítico, independentemente da definição dos momentos:

$$\operatorname{Re}B_k(C_k(a),C_k(a))
\to\frac{\mathrm{nativeSourceFourBoundaryEnergy}((i/\sqrt2)(0,a,0,1))}2.$$

A compatibilidade desse limite com h₃−2ah₂+a²h₁ já era conhecida pelas identidades anteriores da fonte. Nenhum novo pivô de ordem superior ou identidade de alturas é reivindicado.

## C — O que foi delimitado ou refutado

- Convergência do defeito para cada a,b fixo não autorizaria um limiar comum para toda a família. Aqui provamos o fator ab e a cota uniforme explicitamente.
- A norma dos jets não é o Green. O sinal continua vindo da margem física da #120, cuja dependência é a coercividade histórica N=4.
- O cancelamento dos mistos ocorre na forma recomposta, não em cada campo isolado. As pernas, fases, amplitudes, Gamma/completion, bordos e resto nativo não foram alterados.
- A escala κ usada para observar a taxa não muda a fonte C certificada, nem introduz um peso para forçar positividade.

Não há NO-GO novo para a geometria original. Permanecem válidas as obstruções anteriores à positividade por pesos monomiais isolados e à interpretação de uma cauda diagonal não nula como solução independente do retorno.

## D — O que permanece aberto

O resultado é finito: quatro endereços, a família crítica original desta ordem e todas as suas combinações de parâmetro tratadas uniformemente. Não demonstra positividade de todas as Hankel, convergência de operadores infinitos, nem uma representação Gram positiva global dos momentos.

A uniformidade em a não é coercividade por uma constante fixa vezes a norma bruta de C_k(a), e não é uma constante uniforme em toda ordem. Os coeficientes brutos podem crescer com κ; o lema de trajetórias conserva exatamente essa distinção.

A única raiz nova que usa um certificado de sinal é `critical_uniform_physical_margin`, por transporte da margem principal da #120. As identidades de coeficientes, a passagem vetor→energia, os limites do defeito e sua taxa são estabelecidos sem momentos canônicos como entradas e sem certificado de sinal finito.

## E — Próximo passo mínimo e reprodução

Antes de reconstruir uma teoria all-order, há uma interface anterior a reutilizar. Confirmamos no operador:

- `nativeSourceChiralJetInput_eventually_bijective` já fornece a bijetividade da carta de diferenças finitas em dimensão 2n;
- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` já preserva o estado inteiro nos dois canais;
- `storage_one_chiralJetInput_eventually_energy_control` já controla o storage original uniformemente em todas as coordenadas dessa carta, para cada n finito;
- `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` já é um limite all-order para essa síntese, sem premissa de positividade.

Logo, o próximo alvo não deve repetir bijetividade ou esse limite. Deve calcular a **mudança explícita entre a carta Euler usada aqui e `nativeSourceChiralJetInput`**, começando por n=2 e pelos coeficientes físicos A_j C_k(a)_j, com fases, fatoriais e passo imaginário originais. Não basta escolher uma preimagem pela bijetividade: é preciso identificar os coeficientes e seus limites, sem os definir pelos momentos.

Se a ponte fechar, a ferramenta uniforme já existente poderá tratar trajetórias móveis de jets em dimensões maiores sem repetir a regularização de quatro fontes. A obrigação de sinal da forma de bordo nas novas ordens continuará separada; não se deve convertê-la em hipótese equivalente à positividade que falta e chamar isso de solução.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Para reprodução após a limpeza, recrie um worktree da branch publicada, ligue `.lake` ao cache comum validado e entre nesta pasta. Cache de entrada da #120: SHA256 `371bd0c49e33a6223265cdfb42284ccc1b7f261d1d6f64f298af29d59a7dcc4a`.

São reutilizados **92 objetos ancestrais verificados**, não anunciados como recompilados. Os quatro módulos novos e Audit são compilados novamente com warnings como erros. `mechanism_probe.py` realiza **434 verificações gaussianas racionais** dos coeficientes, jets, decomposição física e dois argumentos independentes, com todos os 16 cruzamentos Cauchy no teste finito. As amostras racionais de resposta testam álgebra; não representam uma avaliação da característica nativa, nem provam seu sinal ou a taxa analítica. Esses resultados são provas Lean da fonte original.

### Validação concluída

**17 checks passaram**, todos com exit 0, registrados em `evidence/validation.json` e `evidence/validation-console.log`. São **31 teoremas e 6 definições**, em quatro módulos matemáticos novos. Passaram os builds individuais com warnings como erros, os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis. As **434 regressões gaussianas racionais** passaram.

As **37 raízes públicas** têm `#print axioms` e auditoria transitiva de tipos e corpos, incluindo teoremas e opacos via `value? (allowOpaque := true)`. As **36 raízes sem uso de sinal** alcançam **62.530 constantes**; nenhuma usa as raízes finitas de positividade/coercividade enumeradas. A **única raiz de margem física** alcança **67.204 constantes** e usa a margem principal da #120, a coercividade N=4 e sua margem de bordo histórica.

A definição dos momentos canônicos e os atalhos escalares enumerados são proibidos **em ambos os grupos**. Também ficam proibidos os dois limites antigos do defeito expressos por momentos, os dois consumidores de mera positividade eventual da #119 e os certificados N=7. Só são aceitos `propext`, `Classical.choice`, `Quot.sound`; não foram adicionados axiomas matemáticos, `sorry`, `admit` ou `native_decide`.

`evidence/kernel-audit-summary.json`, `evidence/preservation.json` e `SHA256SUMS` registram a trilha, preservação e integridade. A validação observada foi no host `llm`; não é uma afirmação de CI externo. A entrega usa commit e PR draft empilhada sobre a #120, sem merge. O arquivo de fontes e o cache verificados são copiados para o workspace local antes da remoção apenas do worktree próprio; branch publicada e trabalhos anteriores permanecem disponíveis.

Fim do relatório — margem transportada à fonte crítica completa, correção polarizada controlada uniformemente e na taxa quadrática; positividade canônica all-order permanece aberta.
