# Teste de direções negativas na fonte quiral original

**Classificação: PARTIAL.** A proposta é válida como diagnóstico de um possível contraexemplo. Foram formalizados o transporte de uma direção negativa fixa para amplificação física persistente e dois tratamentos sem inversa para prefixos singulares. Não se encontrou direção canônica negativa, nem uma lei física independente que proíba toda amplificação persistente.

Branch: `agent/native-negative-direction-test`.
Base: `97ad67ca7ae874119e33ce231fa498ba0f39aa1f`, cabeça da PR #63 (`agent/radial-cauchy-conservative-test`). Entrega empilhada em draft, sem merge automático. `main`, PRs anteriores e pins permanecem intactos.

Fonte física consultada: `carry-self-adjoint-operator`, commit `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem edições. A PR #41 foi consultada no commit imutável `ee56930a2c30456cfbd214a29bb31b12d3977204`; seu `SchurLogic` é reutilizado pela recuperação histórica já existente na pilha de pesquisa. Fontes, métrica, amplitudes, fases, endereços, completion, bordos e cruzamentos não foram alterados.

## A — O que já estava demonstrado

O texto fornecido propõe procurar a configuração física obrigatória de uma eventual direção negativa, em vez de começar postulando positividade. A direção é útil, mas várias de suas ferramentas já estavam demonstradas:

- `sourceMomentQuadratic_snoc`, em `NativeSourceAllOrderSchur.lean`: decomposição algébrica completa do bloco aumentado, sem hipótese de sinal.
- `sourceMomentSchur_sewing_of_isUnit`, `sourceMomentSchur_critical_direction_of_isUnit` e `native_inverseSchur_boundary_energy`, da PR #41: bastam inversibilidade e a mesma sequência de momentos, sem `PosDef`, para identificar a direção crítica e sua energia.
- `parityCoordinates_boundary` e `criticalBalance_tendsto`, em `research/critical-source-return/`: relação entre forma canônica e fonte física, com as normalizações originais. O novo transporte com hipótese apenas de inversibilidade reutiliza a versão da PR #41, não a hipótese mais forte da antiga formulação física.
- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` e `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto`, em `CompletedNativeChiralJetStorageTransport.lean`: identificação dos dois canais originais e limite do balanço, conservando a síntese antes da leitura escalar.
- `nativeSourceChiralJetInput_eventually_bijective`, no mesmo módulo: os coeficientes de jets cobrem todo o espaço finito de coeficientes materiais, para cada ordem fixa e índices radiais suficientemente grandes. Esta propriedade não usa positividade da Hankel.
- `radialIncidentSynthesis_injective`, `radialIncidentCoordinates`, `radialReturnTransfer_exact` e `radialReturnTransfer_norm_le_one_iff_storage`, em `CompletedNativeChiralReturnFiniteTransfer.lean`: o retorno finito exato já existe na métrica original. A última equivalência não demonstra seu sinal.
- `storage_one_eventually_eq_source_cross`, em `CompletedNativeChiralReturnSourceTrace.lean`: o storage é o cruzamento da fonte e do companion completado, incluindo os termos de completion.
- `not_eventually_contractive_of_negative_boundary_direction`, em `CompletedNativeChiralReturnArbitraryOrder.lean`, e `negativePivot_not_eventually_contractive`, em `CriticalMargins.lean`: negatividade já excluía contratividade eventual. O novo resultado fortalece isso para amplificação estrita eventual.

Os dois documentos históricos citados no texto, `SURGICAL_TFVD_CHIRAL_POSITIVITY_TRANSPORT_AUDIT.md` e `CHIRAL_RETURN_SOURCE_STORAGE_AUDIT.md`, foram confrontados com as declarações atuais do checkout. Eles não foram tratados como prova autônoma de lacunas atuais.

**Correção central:** pivô negativo e excesso persistente do retorno são o mesmo sinal transportado por uma identidade exata. Não constituem duas restrições independentes. Para excluir o contraexemplo é necessária uma propriedade adicional da fonte, demonstrada sem receber esse sinal como hipótese.

## B — O que foi demonstrado agora

Todos os nomes seguintes pertencem a `CarryNegativeDirection`. As fórmulas físicas usam sempre os canais originais, não um novo fator positivo escolhido a partir dos momentos.

### 1. O espaço físico acessível e a invisibilidade

Em [SourceChart.lean](SourceChart.lean):

- `incident_chart_eventually_bijective`: os jets parametrizam todo o espaço incidente finito original `RadialIncidentSpan k (2*n)`.
- `incident_jet_eventually_injective`: a síntese incidente dos próprios jets é eventualmente injetiva.
- `invisible_incidence_cannot_return`: eventualmente, incidência zero implica coeficiente de jet zero e retorno zero.

Isso exclui o **caso A** do texto no regime radial relevante. A restrição ao espaço físico sintetizado é legítima, mas, nessa ordem finita, não elimina uma parte adicional do espaço incidente original: os jets o cobrem inteiro. Trata-se de uma bijeção linear, sem alegação de isometria das coordenadas de jets. A condição é por ordem fixa; não se afirma um único índice radial válido simultaneamente para todas as ordens.

### 2. Prefixo nulo com novo cruzamento: testemunha sem inversa

Escreva

\[
Q_A(z)=z^TAz,\quad \beta=b^Tz,\quad d=h_{2n+s}.
\]

Em [NullExtension.lean](NullExtension.lean), se `Q_A(z)=0` e `β≠0`, construímos explicitamente

\[
w=\left(-\frac{d^2+1}{2\beta}z,1\right),\qquad
Q_H(w)=d-d^2-1=-\left(d-\frac12\right)^2-\frac34<0.
\]

Os teoremas são `source_quadratic_smul`, `null_coupling_witness_energy`, `null_coupling_witness_negative` e `psd_extension_annihilates_old_null_crossings`; `nullCouplingWitness` é a definição da testemunha.

Não se supõe inversibilidade, nem positividade do bloco antigo, para construir essa direção. A última declaração prova a condição necessária: uma extensão PSD precisa anular o novo cruzamento com toda direção antiga de energia nula. Ela **não** demonstra incondicionalmente essa condição para os momentos canônicos.

### 3. Prefixo singular compatível: completar quadrados sem inversa

Em [SingularSchur.lean](SingularSchur.lean), basta uma solução `Ay=b` para provar

\[
Q_H(x,t)=Q_A(x+ty)+(d-b^Ty)t^2.
\]

`source_sewing_of_solution` prova a identidade e `solution_witness_energy` calcula a energia de `(-y,1)`. `solution_residual_independent` prova que `d-b^Ty` independe da solução escolhida, mesmo se o sistema tiver várias soluções.

Com a hipótese explícita `A.PosSemidef`, `psd_extension_iff_solution_residual` obtém

\[
H\succeq0\quad\Longleftrightarrow\quad d-b^Ty\geq0.
\]

A conclusão não usa inversa. A existência de `y` continua sendo hipótese desse teorema. Não foi formalizada aqui uma classificação completa que derive essa existência apenas da compatibilidade com o núcleo. Tampouco se identificou o residual com uma norma positiva sem prova.

### 4. Direção fixa, excesso persistente e amplificação efetiva

Em [NegativeTransport.lean](NegativeTransport.lean), para uma coordenada de fronteira **fixa** `x`, defina

\[
X_k(x)=\|J_{-,n,k}(x)\|^2-\|J_{+,n,k}(x)\|^2.
\]

`returnExcess_tendsto` e `negative_boundary_iff_persistent_excess` provam

\[
X_k(x)\longrightarrow-\frac{E_{2n}(x)}2,
\qquad
E_{2n}(x)<0\ \Longleftrightarrow\
\exists\varepsilon>0,\ \text{eventualmente }X_k(x)\geq\varepsilon.
\]

Na direção de avanço pode-se escolher `ε=-E/4`. `returnExcess_eq_neg_storage` preserva a identidade exata `X=-Re(storage)`.

`negative_boundary_eventually_amplifies` prova a consequência estrita

\[
E_{2n}(x)<0\ \Longrightarrow\
\text{eventualmente }\|T_{k,2n}\|>1.
\]

`negative_boundary_regular_witness` mantém simultaneamente: todos os pontos do suporte no domínio físico, característica e coordenada Hermite–Biehler positiva não nulas, incidência não nula, excesso uniforme `ε`, amplificação estrita e

\[
\operatorname{Im}\langle V_k,C_k\rangle\leq-\varepsilon/4.
\]

Este é o companion **completado**, não somente a parte material. A síntese conjunta existente é transportada antes da leitura de normas ou do cruzamento. Não se apagou nenhum canal ou termo misto.

`finite_amplification_iff_jet_excess` também prova, eventualmente em cada ordem finita,

\[
\|T_{k,2n}\|>1\quad\Longleftrightarrow\quad
\exists x,\ X_k(x)>0.
\]

Aqui `x` pode depender de `k`. Essa equivalência finita não fornece uma direção fixa com excesso persistente.

### 5. Aplicação à mesma sequência canônica, nos dois setores

Para `s : Fin 2`, com apenas `IsUnit A`, `negative_schur_iff_persistent_excess` prova

\[
p_{s,n}<0\quad\Longleftrightarrow\quad
\exists\varepsilon>0,\ \text{eventualmente }
X_k(\mathrm{criticalCoordinates}(s,n))\geq\varepsilon.
\]

A normalização é `E=4p` e, portanto, `X_k→-2p`. Não há hipótese de positividade do pivô.

`canonical_null_crossing_forces_persistent_return` transporta a testemunha nula com cruzamento não nulo para a mesma fonte canônica. `canonical_solution_residual_forces_persistent_return` faz o mesmo para qualquer solução `Ay=b` com residual negativo. Ambos dispensam inversa; as respectivas condições são hipóteses explícitas. Não se provou que ocorram na fonte canônica.

## C — O que foi refutado ou delimitado

1. **Invisibilidade incidente como mecanismo eventual:** o caso A está excluído para os jets originais pela injetividade já disponível, agora aplicada aos dois canais completos.
2. **Primeira direção negativa sempre após um bloco positivo definido:** isto falha para sequências gerais se uma ordem nula preceder a negatividade. [Regression.lean](Regression.lean) reaproveita o controle da PR #41 `m=(1,0,0,1,0,...)`: o bloco antigo é `diag(1,0)`, a direção `(0,1)` tem energia zero e cruzamento futuro `1`. A testemunha `(0,-1/2,1)` tem energia `-1`. Não se afirma que essa sequência seja canônica.
3. **Compatibilidade `Ay=b` bastaria para positividade:** um segundo controle racional usa `m_0=...=m_3=1`, `m_4=1/2`. O bloco antigo singular admite `y=(1,0)` e tem vetor de núcleo `(1,-1)`, mas o residual e a energia de `(-1,0,1)` valem `-1/2`. Esse controle também é auxiliar, não uma modificação dos momentos originais.
4. **Amplificação finita implica negatividade canônica:** não. Como controle lógico, `D_k(x)=-x²/(k+1)` tende a zero em cada direção fixa, embora seja negativo em toda etapa finita e `D_k(sqrt(k+1))=-1`. Pode-se realizá-lo com incidência identidade e retorno `sqrt(1+1/(k+1))` em uma dimensão. Esta ilustração elementar e seu teste racional estão documentados no experimento; não são teoremas novos sobre a fonte física. Mesmo amplificação estrita eventual não fornece a margem persistente requerida.
5. **Schur negativo mais retorno excessivo seriam duas barreiras independentes:** a nova equivalência mostra exatamente a coincidência dos sinais. Exigir que não exista o excesso persistente, sem uma lei independente para justificá-lo, reformula a obrigação original.

Nada disso refuta a geometria Carry, as realizações finitas certificadas ou a possibilidade de uma conservação física completada ainda não identificada. A PR #63 já mostrou que até um erro vetorial tendendo a zero pode manter um cruzamento finito com o canal crescente; esse termo continua relevante aqui.

## D — O que permanece aberto

Não se encontrou contraexemplo canônico. Não se demonstrou positividade all-order, não degenerescência all-order, nem contratividade eventual do retorno exato em todas as direções. Não se construiu um novo operador de alturas.

A rota por contradição está localizada: uma direção canônica negativa fixa produziria uma fonte admissível, incidente-visível, com amplificação persistente e orientação mista negativa. **As relações já usadas permitem descrever essa configuração condicionalmente; ainda não a tornam impossível.** Domínio, injetividade e existência do retorno exato não determinam sozinhos o sinal do storage.

No caso singular, a necessidade de anular cruzamentos com direções nulas não foi descarregada a partir da fonte original. A identidade com `Ay=b` não prova a existência dessa solução. Esses são limites explícitos das declarações formais.

### Experimento de baixa ordem

[experiment.py](experiment.py) reproduz a Hankel 3×3 usando somente os cinco momentos decimais guardados em `reference-moments.json`, tratados como racionais exatos. A origem é o arquivo fornecido pelo usuário `operador_finito_canonico_N4.json`, SHA256 `f8e56b3de290feef2c878481035b92db0842677ad34006b665c3ea0184eb48bd`. Nenhum zero ou altura é usado como entrada.

| Quantidade | Resultado aproximado dos racionais armazenados |
|---|---:|
| Limiar `bᵀA⁻¹b` | `3,10219999016692233119 × 10⁻¹²` |
| `h₄` | `3,21366415061660121610 × 10⁻¹²` |
| Pivô | `1,11464160449678884911 × 10⁻¹³` |
| Vetor crítico | `(0,00000198041248379585; −0,00510944490987021; 1)` |

A energia da testemunha coincide **exatamente**, por `Fraction`, com o pivô racional positivo. Os últimos dígitos do pivô citado no texto fornecido não foram reproduzidos por estes dados; o valor acima é o resultado efetivamente verificado dos arquivos disponíveis, com o mesmo sinal e ordem de grandeza. Não se atribui uma causa não demonstrada à discrepância. A metainformação de 105 casas do cálculo original não acrescenta dígitos aos momentos exportados; por exemplo, `h₄` contém menos dígitos. Este teste não é uma nova certificação da fonte, nem substitui os certificados Lean finitos anteriores. As saídas e os controles estão em `evidence/experiment.json`.

## E — Próximo passo mínimo

A linha é boa para escolher e acompanhar a direção crítica, inclusive após degenerescência. Para produzir uma prova de positividade, o próximo avanço precisa ser uma relação **independente** da fonte que restrinja a orientação de `sourceValue` com `sourceCompanion`, ou controle o defeito completado no balanço com escala suficiente. Postular contratividade, storage não negativo ou ausência de excesso persistente não resolve essa independência.

O teste operatório concreto herdado da PR #63 continua adequado: construir, nos operadores Green originais e com domínio declarado, o transporte de `physicalSourceValue` para a síntese conjunta `physicalNativeCompanion + physicalCompletionCompanion`, conservando os pareamentos de duas entradas. Confrontar sua identidade de fluxo/bordo com `a(z)=-F′(z)/F(z)`, e não somente com o endereço linear. Começar nas duas colunas admissíveis já verificadas; registrar qualquer defeito em vez de ajustar métrica ou constantes.

Se surgir uma direção antiga nula, a menor obrigação adicional é demonstrar **na fonte**, sem assumir PSD da extensão, que seu novo cruzamento é zero. Caso se obtenha uma solução `Ay=b`, permanece determinar o sinal do residual independente da solução. As declarações desta entrega fornecem testemunhas explícitas para testar uma violação de cada uma dessas obrigações, sem defini-las por positividade.

### Validação e reprodução

Há **20 teoremas e duas definições públicas**, além dos controles anônimos de regressão. `generate_audit.py` inventaria as 22 raízes; `Audit.lean` imprime axiomas e percorre transitivamente os tipos e corpos das provas. Bloqueia consumidores posteriores H6/K6/H7 e gates de positividade/contratividade relevantes, além dos sinais já conhecidos de `h₀` e `h₁`. Só permite os axiomas fundacionais `propext`, `Classical.choice` e `Quot.sound`.

Na mesma pilha de pesquisa já compilada da PR #63:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/native-negative-direction-test/validate.py
```

O validador compila explicitamente os seis módulos com `warningAsError=true`, executa os controles exatos, builds focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/Analysis e regressão das doze fontes. Não se afirma que o build raiz sozinho inclua automaticamente estes módulos de pesquisa.

As dependências históricas e caches compilados são os já utilizados pela PR #63, incluindo a recuperação imutável de `SchurLogic` da PR #41. Este comando reproduz os novos módulos nessa pilha; não é um bootstrap completo de todas as dependências históricas a partir de uma máquina vazia. Não houve novo port ou mudança de pin.

**Execução concluída: 16/16 verificações passaram**, incluindo as 22 raízes públicas, os builds com `--wfail`, as três auditorias e a regressão das doze fontes. Somente os três axiomas fundacionais permitidos ocorreram nas raízes novas.

Os resultados efetivos por comando estão em `evidence/checks.json`; a auditoria das declarações está em `evidence/kernel-Audit.log`. `evidence/preflight.json` e `evidence/source-sha256.json` registram referências, fontes, arquivos protegidos e hashes. O validador também exige preservação dos dois arquivos não rastreados do operador, do resíduo da PR #51, dos worktrees e das fontes da PR #63.

**Conclusão:** o ataque por uma direção negativa foi tornado um diagnóstico formal da própria fonte, incluindo prefixos singulares. Isso melhora a precisão do teste, mas não fornece uma segunda lei de sinal independente. O alcance é PARTIAL, sem reivindicação de positividade canônica em toda ordem.
