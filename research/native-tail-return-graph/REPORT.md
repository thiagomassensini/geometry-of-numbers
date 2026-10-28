# Retorno nativo da cauda e transporte direto das quatro fontes

**Classificação: PARTIAL para a investigação geral; PASS para o transporte finito solicitado.** A família principal da PR #118 tem agora positividade física eventual, uniforme no parâmetro real, por transporte do certificado **já existente de quatro fontes**. Não é necessário passar por sete fontes. A positividade de todas as Hankel canônicas continua aberta.

Base exata: `d823e590d4fd3b11c908fe10399b1091f4b2abe3`, branch `agent/native-principal-boundary-flow`, PR #118. Nova branch: `agent/native-tail-return-graph`. O trabalho é empilhado sobre a #118; não modifica nem mescla a #118 ou `main`. Host de validação: `llm`. Repositório nativo consultado: `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado e o que as notas ajudaram a localizar

A #118 já decompunha a fonte original U em cabeça H e cauda E, sem retirar campos, retorno ou cruzamentos. A cauda tem duas pernas iguais, E=(z,z), portanto sua autoforma quiral é nula; seu efeito na forma completa permanece nos dois pareamentos mistos. `complete_state_head_tail`, `head_preserves_contrast` e `tail_mixed_physical_flux` são resultados anteriores, não novidades desta investigação.

O mapa unificado, especialmente §§12 e 16, apontou para o retorno finito já tipado e seus certificados de storage. Inicialmente o controle considerado era de sete fontes. A mensagem posterior do usuário localizou o certificado mais curto, **exatamente de quatro fontes**, confirmado no código atual:

- `storage_one_original_fourSample_eventually_pos`;
- `radialReturnTransfer_four_eventually_norm_le_one`;
- `storage_one_fourSample_eventually_boundary_coercive`.

Eles estão em `CarrySelfAdjointOperator/CompletedNativeChiralReturnFourSampleStorage.lean`. São resultados antigos da fonte completada, incluindo regularização, os dois setores de bordo, termos mistos e resto analítico. Esta PR transporta o resultado, sem refazer sua prova nem atribuir-lhe alcance em dimensão arbitrária. A auditoria dos novos resultados exclui explicitamente os dois certificados de sete fontes.

As interfaces reutilizadas são `RadialIncidentSpan`, `radialIncidentVector`, `radialIncidentSynthesis_injective`, `radialReturnTransfer_exact`, `radialReturnedSynthesis_eq_incident_multiply`, `radialReturnEnergyDefect_pairing`, `radialReturnEnergyPort_inner`, `storage_one_eq_finiteTransfer_energy`, `physicalCompletedFiniteSource_original`, `completed_source_weighted_identity` e `cross_green_eq_original`.

O dossiê e o mapa são contexto matemático, não instruções executáveis. Conferimos as dez entradas do manifesto do ZIP; não executamos campanhas de milhares de momentos nem instalamos pacotes sugeridos nos anexos. O Markdown avulso e o do ZIP têm variantes de delimitadores/formatação e uma diferença de notação residual, não igualdade byte a byte. Hashes e limites da leitura estão em `evidence/notes-review.json`.

O novo mapa de inversão/círculo distingue corretamente mudanças de coordenada, balanço assinado e positividade do storage. Suas identidades projetivas não fornecem, por si, uma isometria com o carrier nativo. Não identificamos o círculo unitário daquele modelo com o sinal estrito do Green. O script `certificado_quatro_enderecos.py` foi lido e executado com sucesso localmente; sua identidade de coeficientes foi também provada em Lean nesta investigação.

O dicionário escalar F_X(s) serve para conferir coeficientes e traços; não demonstra preservação de energia. Analogamente, D(j)=j+1 positivo em coordenadas euclidianas não é automaticamente um operador positivo na métrica Cauchy. O contraexemplo −56 da #118 continua válido. Matrizes Jacobi finitas e determinantes numéricos 2×2 não são prova em toda ordem.

## B — O que foi demonstrado agora

### B.1 — A mesma fonte está no domínio do retorno existente

Todos os novos nomes pertencem ao namespace `CarryTailReturn`. Em `FiniteReturnDomain.lean`, `weightedIncident` usa o vetor de incidência existente, com coeficientes w_j x_j. A amplitude radial sqrt(k+1) já está em `radialIncidentVector`; não é inserida novamente nos coeficientes.

Para x com suporte nos primeiros N endereços, `weighted_incident_coe` e `weighted_incident_return` demonstram:

$$
 W_{k,N}(w,x)=\sqrt{k+1}\,S(wx),\qquad
 R_{k,N}W_{k,N}(w,x)=W_{k,N}(q_k w,x),
$$

onde S é a síntese Cauchy original e q_k é o quociente quiral nativo nos mesmos nós radiais. O R desta fórmula é literalmente `radialReturnTransfer`, não um operador reconstruído para a prova.

Se A_j é `incidentWeight k j`, a incidência física de x é `sourceIncident k N x = weightedIncident k N A x`. Os lemas `original_first_leg`, `original_return_leg` e `original_source_graph` dão a identidade vetorial completa:

$$
 U_k(x)=\bigl(W_{k,N}(A,x),R_{k,N}W_{k,N}(A,x)\bigr).
$$

O fator projetivo A ocorre **uma única vez**. O storage antigo recebe c_j=A_j x_j, porque suas features incidentes já contêm sqrt(k+1), mas não esse dressing projetivo.

Esta identificação vale para todo N finito e suporte correspondente. São igualdades das definições totais; regularidade é exigida explicitamente para dividir pelos denominadores e provar não degenerescência. Não se afirma domínio de um clock logarítmico não limitado nem existência de um operador limite infinito.

### B.2 — Domínio da primeira perna não é condição de grafo do par

Em `TailReturnGraph.lean`, `tail_first_leg` e `head_first_leg` colocam as primeiras pernas de E e H no mesmo domínio finito, para N≥4. A seguir calculamos o defeito real do retorno:

$$
 d_k(a)=z_k(a)-R_{k,N}z_k(a)
 =\sqrt{k+1}\,\chi\,S\bigl((1-q_k)\,w_k^{\mathrm{tail}}\,X_k(a)\bigr),
$$

com a constante original `chiralDifference` χ e o resto original `responseTail`. O lema é `tail_return_defect_synthesis`.

`tail_graph_defect` e `head_graph_defect` demonstram, vetorialmente:

$$
 E_2-R E_1=d_k,\qquad H_2-R H_1=-d_k.
$$

Os defeitos cancelam no estado inteiro U=H+E. Não apagamos E nem a rebatizamos como fonte independente.

Em cada prefixo regular, `native_quotient_ne_one` prova q_j≠1 a partir de F≠0 e P≠0. A injetividade da síntese incidente então dá `native_return_fixed_iff_zero`:

$$
 Rx=x\quad\Longleftrightarrow\quad x=0.
$$

Logo, `tail_in_graph_iff_zero` demonstra que E=(z,z) pertence ao grafo do retorno nativo **se e somente se E=0**. `tail_in_graph_eventually_iff_zero` descarrega a regularidade eventualmente, para cada N finito. Não são necessárias hipóteses de sinal ou contractividade para essa obstrução.

### B.3 — A resposta completada é a coordenada de Cayley do retorno

Preservando os denominadores regulares e os fatores nativos, `native_return_response_relation` e `native_return_cayley_coordinate` provam:

$$
 1+q_j=2w_j(1-q_j),\qquad \frac{1+q_j}{1-q_j}=2w_j,
$$

onde w_j=`responseSamples (radialStep k) j` vem da resposta completada já existente. Nenhum momento ou autovalor é fornecido como entrada.

`weighted_cayley_vector` transporta a relação a vetores no domínio incidente:

$$
 W(1,x)+R W(1,x)=2W\bigl(w,(1-q)x\bigr).
$$

A relação é vetorial antes do readout e vale em qualquer prefixo finito regular. Não é uma prova de contractividade: o operador de multiplicação em coordenadas deve ser avaliado na métrica Cauchy, com seus cruzamentos.

### B.4 — A identidade de energia conserva os três termos do defeito

Em `PolarizedReturnDefect.lean`, seja Δ=y−Rx e Δ'=y'−Rx', com primeiras pernas no domínio. `graph_defect_polarized_balance` prova:

$$
\begin{aligned}
2B((x,y),(x',y'))={}&\langle x,(I-R^*R)x'\rangle\\
 &-\langle Rx,\Delta'\rangle-\langle\Delta,Rx'\rangle-\langle\Delta,\Delta'\rangle.
\end{aligned}
$$

As duas entradas são independentes. `diagonal_pair_return_energy` e `tail_energy_defect_cancellation` especializam essa igualdade à cauda com pernas iguais: seu balanço quiral nulo não força energia positiva de porta nula, pois os três termos do defeito continuam presentes.

Para o estado **inteiro**, cujo defeito é zero, `original_source_energy_pairing` identifica exatamente:

$$
 \langle x_A,(I-R^*R)y_A\rangle=2B(U(x),U(y)).
$$

Sob a hipótese explícita ‖R‖≤1, `original_source_port_pairing` reutiliza a porta positiva já existente, sem alterar métrica:

$$
 \langle\mathrm{port}(x_A),\mathrm{port}(y_A)\rangle=2B(U(x),U(y)).
$$

Esse resultado geral é condicional. Na dimensão quatro a hipótese é descarregada pelo certificado antigo, abaixo.

### B.5 — O certificado de coeficientes do usuário foi formalizado

`FourSourceBridge.lean` calcula os quatro coeficientes literais de `principalInput`. Com κ=k+1, são

$$
 X_k(a)=\frac{i\kappa}{6}
 \bigl(-\kappa^2-13a,\;3\kappa^2+48a,\;-3\kappa^2-63a,\;\kappa^2+28a\bigr).
$$

`principal_coefficient_formula`, `principal_coefficients_sq` e `principal_coefficients_completed_square` provam a identidade exata:

$$
 \sum_{j=0}^3|X_k(a)_j|^2=
 \frac{3613\kappa^2}{18}\left(a+\frac{187\kappa^2}{3613}\right)^2
 +\frac{129\kappa^6}{7226}.
$$

`principal_coefficients_sq_pos` e `principal_input_nonzero` concluem X_k(a)≠0 para **todo** k natural e a real. É a norma euclidiana dos coeficientes, usada exclusivamente para não anulação; não a confundimos com a métrica física Cauchy nem com uma nova prova do sinal do Green.

### B.6 — Transporte direto de quatro fontes: corolário candidato fechado

`original_source_storage` verifica a constante e o dressing exatos:

$$
 \operatorname{Re}\mathrm{storage}_k((A_jx_j)_{j<4},1)=2\operatorname{Re}B(U_k(x),U_k(x)).
$$

A regularidade torna A_j não nulo; `weighted_coordinates_ne_zero` preserva a não anulação de x. Aplicando `storage_one_original_fourSample_eventually_pos`, `four_original_physical_positive` obtém positividade estrita para toda fonte não nula suportada nos quatro endereços, em um único limiar eventual.

`principal_four_eventually_positive` fecha precisamente o corolário pedido:

$$
 \boxed{\forall^{\mathrm{ev}} k,\ \forall a\in\mathbb R,\quad
 \operatorname{Re}\,\mathrm{crossGreenPair}_k(X_k(a),X_k(a))>0.}
$$

O limiar é independente de a. A única condição nos parâmetros da decomposição Green é 0<eta<1, como na interface original; o estado recomposto é o mesmo.

`four_original_port_gram` e `principal_four_port_gram` provam também, para a,b independentes, a identidade Gram da **forma física completa**:

$$
 \boxed{\langle\mathrm{port}(x_A(a)),\mathrm{port}(x_A(b))\rangle
 =2\,\mathrm{crossGreenPair}_k(X_k(a),X_k(b)).}
$$

A contractividade N=4 é descarregada por `radialReturnTransfer_four_eventually_norm_le_one`. Não há ampliação para N=7. A igualdade `cross_green_eq_original` recompõe todos os campos e seus nove cruzamentos; quatro endereços de entrada não significam truncar o halo de saída dos campos Green.

## C — O que foi refutado ou deixou de ser necessário

1. **Sete fontes não são necessárias para este transporte.** O certificado N=4 basta, e os certificados positivos N=7 estão proibidos pela auditoria transitiva dos resultados novos. O arquivo N=7 ainda aparece no registro de hashes porque havia sido inspecionado inicialmente; registrar preservação não é usá-lo na prova.
2. **E isotrópico não é uma solução independente do retorno.** Em prefixo regular, E≠0 impede sua condição de grafo. Isso não impede que sua primeira perna esteja no domínio nem refuta o estado completo.
3. **Autoforma quiral nula não permite eliminar a cauda.** Os dois termos mistos e o termo defeito–defeito compensam exatamente a energia de retorno. Suprimi-los altera a forma original.
4. **Cayley ou pesos positivos não fornecem sinal automaticamente.** A relação de Cayley identifica a resposta original, mas não torna a multiplicação positiva na métrica física. Nenhuma nova métrica foi introduzida.

Não há NO-GO para a geometria inteira, nem para todas as possíveis realizações Gram. A obstrução provada diz respeito a tratar a componente diagonal não nula como um par que satisfaz, separadamente, o retorno nativo.

## D — O que permanece aberto

A identidade geral e o domínio finito foram estabelecidos; o sinal foi transportado para N=4. Não foi provada contractividade em todo N, uma representação Gram coerente de todos os momentos canônicos, nem positividade all-order de H e K.

A positividade eventual estrita de uma sequência não garante limite estritamente positivo. Em particular, não inferimos um novo sinal estrito de pivô simplesmente passando ao limite em `principal_four_eventually_positive`. Os sinais finitos canônicos conhecidos permanecem os certificados anteriores.

A proveniência desta prova é explícita: o resultado de sinal vem do **certificado antigo da fonte em dimensão quatro**, que utiliza suas desigualdades finitas já demonstradas. Esta PR não transforma isso em uma lei geométrica independente em dimensão arbitrária e não afirma ausência de dependências analíticas/theta na prova histórica.

O primeiro gate da rota em dimensão arbitrária continua sendo uma estimativa de energia/acretividade da resposta completada na métrica Cauchy original, mantendo bordo e resto, ou uma fatoração positiva com a mesma forma polarizada. A relação de Cayley localiza esse gate; não o descarrega.

## E — Próximo passo mínimo, validação e reprodução

O próximo teste concreto pode agora reutilizar `storage_one_fourSample_eventually_boundary_coercive`, ainda sem aumentar a ordem:

1. Calcular **exatamente** `radialCompletedValueCoefficients` aplicado aos coeficientes físicos A_j X_k(a)_j, verificando o cancelamento do dressing uma única vez.
2. Transportar esses coeficientes para `radialFourScaledBoundary` e calcular o limite vetorial dos quatro jets, preservando as duas entradas e o resto original.
3. Aplicar a coercividade antiga a esse vetor e verificar se sobrevive uma margem não nula na escala do limite.

Esse é um teste quantitativo do transporte, não a suposição de um novo orçamento positivo. Ele evita a passagem inválida de positividade eventual para limite estrito. Seu alcance inicial continua N=4. Uma generalização exigirá uma lei independente para a forma de bordo e seu resto em dimensão arbitrária; não bastará recebê-la como hipótese equivalente à Hankel positiva.

Comandos no host `llm`, nesta pasta:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

Sem cache opcional, `python3 validate.py` recompila os ancestrais. Para reproduzir após a limpeza do worktree, recrie-o na branch publicada, ligue `.lake` ao cache comum validado e entre nesta pasta. O cache de entrada tem hash `c754d763ea54fd58660ec072fb918f2a9d229c92966b0b06e9f7efc9fb580595`, identificado em `evidence/cache-restoration.json`.

A reutilização envolve **85 objetos ancestrais verificados**, não anunciados como recompilados. Os quatro módulos novos e `Audit.lean` são compilados novamente com warnings tratados como erros. A validação também executa os alvos nativos, `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e as verificações de preservação.

`mechanism_probe.py` executa **391 verificações com frações gaussianas exatas**: ambas as quadraturas, fonte inteira, retorno, Cayley, defeitos opostos, identidade polarizada, cancelamento misto e quadrado completo dos coeficientes. As amostras racionais de resposta usadas nesses testes verificam somente identidades algébricas; não são declaradas iguais à função completada nativa, nem usadas para provar seu sinal. Os teoremas universais e o certificado de sinal são verificados no Lean.

### Validação concluída e alcance da auditoria

Passaram **17 checks de integração**, incluindo os quatro módulos novos, `Audit.lean`, os alvos nativos selecionados, `lake build --wfail` e Foundation/Geometry/Analysis. Depois houve uma **rechecagem focalizada do auditor**, também com exit 0, para corrigir a consulta a corpos opacos na API atual do Lean. Os resultados estão em `evidence/validation.json`, `evidence/full-body-audit.json` e nos logs correspondentes.

São **41 teoremas e 7 definições/abreviações**, distribuídos em quatro módulos. As **48 raízes públicas** têm `#print axioms`. O auditor final percorre explicitamente `info.value? (allowOpaque := true)`: tipos, corpos de definições, teoremas e declarações opacas. O script herdado consultava `value?` sem essa opção e não incluía os corpos de teoremas no controle adicional de dependências. Corrigimos isso somente no novo auditor; os arquivos históricos ficaram preservados. A compilação das provas e a checagem de axiomas são distintas dessa guarda de proveniência.

Na auditoria final, as **44 raízes de construção** alcançam **63.893 constantes**; ficam proibidos os momentos canônicos, os certificados de sinal enumerados e os atalhos escalares enumerados. Nenhuma das raízes finitas de sinal é usada nesse grupo. As **4 raízes de controle finito** alcançam **70.367 constantes** e usam precisamente os três resultados N=4 registrados em `full-body-audit.json`. As duas raízes N=7 são proibidas em ambos os grupos. Só são admitidos `propext`, `Classical.choice`, `Quot.sound`; não foram introduzidos axiomas matemáticos, `sorry`, `admit` ou `native_decide`.

`evidence/preservation.json` confirma fonte, pesos, amplitudes, métricas, fases, pins, `main` e trabalhos antigos preservados. `SHA256SUMS` registra a integridade da entrega. Esta é validação observada no host `llm`; não se anuncia CI externo como se tivesse sido executado. A versão atual de `validate.py` já gera o auditor corrigido: a rechecagem extra documenta a correção ocorrida nesta execução, não uma exigência de duplicar o teste em toda reprodução.

A entrega usa commit e PR **draft**, sem merge. O arquivo e o cache verificados são copiados para o workspace local antes da remoção apenas do worktree próprio; a branch publicada e os trabalhos antigos são conservados.

Fim do relatório — transporte direto de quatro fontes fechado; cauda e retorno identificados; positividade canônica em toda ordem permanece aberta.
