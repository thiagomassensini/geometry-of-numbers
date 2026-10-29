# Teste conservativo com o parâmetro radial preservado

**Classificação: PARTIAL.** A família conservativa radial foi construída e comparada com o retorno nativo na métrica original. Há uma identidade exata de defeito, uma obstrução específica e uma lei nova para o cruzamento. Não se demonstrou positividade canônica em toda ordem.

Branch: `agent/radial-cauchy-conservative-test`.
Base: `1470fdb0665d5b8d192433e674efde18cab5ceb8`, cabeça da PR #62. A entrega é uma PR draft empilhada, sem alteração ou merge das PRs anteriores.

Fonte consultada: `carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`. A fonte, métrica, amplitudes, fases, completion, pins e arquivos históricos foram preservados. Os dois arquivos não rastreados do operador e o resíduo local da PR #51 permanecem intactos.

## A — O que já estava demonstrado

A PR #62 excluiu um mapa fixo limitado no carrier Cauchy já identificado entre índices radiais, na primeira direção. Ela não excluiu uma família dependente de `k`. O teste atual conserva explicitamente `k`.

Há um fato anterior que não deve ser anunciado como descoberta nova: **o retorno finito exato dependente de `k` já existe**. Em `CompletedNativeChiralReturnFiniteTransfer.lean`:

- `radialIncidentSynthesis_injective`, `radialIncidentCoordinates`, `radialIncidentVector`: coordenadas recuperadas das colunas físicas originais, sem whitening dos momentos;
- `radialReturnTransfer_exact`, `radialReturnTransfer_basis`, `radialReturnTransfer_unique`: o operador finito realiza a síntese retornada original e é determinado por essa ação;
- `radialReturnTransfer_polarized_balance`, `storage_one_eq_finiteTransfer_energy`: balanços completos;
- `radialReturnTransfer_norm_le_one_iff_storage`: a contratividade desse operador exato ainda exige o sinal do storage original. Esta equivalência não é uma prova desse sinal.

As colunas são `f_j(x)=√x x^j`, no carrier original, com Gram `1/(i+j+2)`. A coluna radial é `v_{k,j}=√(k+1) f_j`; sua Gram é `(k+1)/(i+j+2)`.

O shift físico da PR #62 tem autovalores

\[
\rho_j=\frac{2j+1}{2j+3},\qquad
j+1=\frac{1+\rho_j}{2(1-\rho_j)}.
\]

A fonte retornada usa `q(z_{k,j})`, onde `z_{k,j}=i(j+1)/(k+1)` e `q` é `completedNativeHermiteBiehlerChiralQuotient`, com **toda a característica completada**.

Foram reutilizados os limites vetoriais da PR #42 (`scaled_input_tendsto`, `scaled_returned_tendsto`), recuperados e compilados na PR #62, e a mesma direção mônica da PR #41. `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` e `first_even_boundary_energy` conservam a normalização: duas vezes o balanço tende a `4h₀` no primeiro par.

De `CompletedNativeChiralCayleyHerglotz.lean`, já existia a igualdade regular

\[
q(z)=\frac{a(z)-i}{a(z)+i},\qquad a(z)=-F'(z)/F(z).
\]

Esta identidade e as equivalências de kernels Herglotz/Pick não provam automaticamente positividade de `a`.

## B — O que foi demonstrado agora

### 1. Uma família radial independente dos momentos

Em `RadialConservative.lean`, transportamos a mesma coordenada de endereço pela escala radial:

\[
m_{k,j}=\frac{2j+1-k}{2j+k+3}
=\frac{\rho_j-\alpha_k}{1-\alpha_k\rho_j},\qquad
\alpha_k=\frac{k}{k+2}.
\]

`radial_symbol_shift` e `radial_symbol_scaled_address` provam essas identidades. É a avaliação da mesma transformação de Cayley no endereço `(j+1)/(k+1)`. Não se escolheu uma constante a partir de `h₀`, de pivôs, zeros ou alturas.

O **candidato comparador**, distinguido do retorno nativo, é

\[
C_{k,N}\Bigl(\sum_{j<N}c_jv_{k,j}\Bigr)
=\sum_{j<N}c_jm_{k,j}v_{k,j}.
\]

`conservativeTransfer` é um mapa linear contínuo sobre o espaço finito original `RadialIncidentSpan k N`. Sua continuidade usa dimensão finita e as coordenadas incidentes existentes. Seu domínio não é uma nova realização fabricada a partir dos momentos.

Defina a porta derivada da fatoração

\[
d_{k,j}=\frac{2(k+1)}{2j+k+3},\qquad H_{k,N}(c)=\sum_{j<N}c_jd_{k,j}.
\]

`scalar_conservation` prova

\[
\frac{k+1}{i+j+2}(1-m_{k,i}m_{k,j})=d_{k,i}d_{k,j}.
\]

Depois da síntese dos **dois argumentos independentes**, `polarized_conservation` e `conservative_energy` provam

\[
\langle I(c),I(d)\rangle-\langle C I(c),C I(d)\rangle
=\overline{H(c)}H(d),
\]

\[
\|I(c)\|^2-\|C I(c)\|^2=|H(c)|^2.
\]

`conservativeTransfer_contractive` deduz a contratividade do comparador. A métrica usada é exatamente a Cauchy original. O par composto de saída e porta conserva a informação quadrática; a porta isolada não representa o estado inteiro.

`conservativeSynthesis_snoc_zero` e `conservativePort_snoc_zero` provam coerência exata dos prefixos por extensão com coeficiente zero. Não se reivindicou, a partir disso, uma identificação espectral infinita ou um domínio global para o retorno nativo.

### 2. O retorno nativo continua sendo a mesma fonte

Em `NativeDefect.lean`, `exact_native_transfer_jet` reaproveita o operador exato anterior com os próprios coeficientes `nativeSourceChiralJetInput`. A amplitude completada, fase, pesos do TFVD e fatoriais permanecem nesses coeficientes.

O defeito é o vetor original

\[
\eta_k(c)=R_k(c)-C_k I_k(c)
=\sum_jc_j(q(z_{k,j})-m_{k,j})v_{k,j}.
\]

`native_defect_columns` prova a fórmula. `native_polarized_ledger` conserva os dois cruzamentos ordenados e o pareamento erro–erro:

\[
\langle I(c),I(d)\rangle-\langle R(c),R(d)\rangle
=\overline{H(c)}H(d)
-\langle CI(c),\eta(d)\rangle
-\langle\eta(c),CI(d)\rangle
-\langle\eta(c),\eta(d)\rangle.
\]

Somente depois dessa identidade, `native_energy_ledger` extrai

\[
D_k(c)=|H_k(c)|^2
-2\operatorname{Re}\langle C_kI_k(c),\eta_k(c)\rangle
-\|\eta_k(c)\|^2.
\]

Não se substituiu o retorno nativo pelo comparador conservativo.

### 3. Domínios e denominadores preservados

`finite_eventually_admissible` prova simultaneamente, em cada suporte finito fixo, a pertinência dos pontos à faixa da característica, `F(z_{k,j})≠0` e a não anulação da coordenada Hermite–Biehler positiva.

As identidades algébricas de somas usam as funções totais já definidas em Lean. As identidades analíticas que dividem pelos fatores físicos mantêm as condições de não anulação. Não se usou inversão total para resolver um domínio físico.

O resultado é `∀ N, eventualmente em k, ∀ j< N`. Não é um único índice `k` que torna admissíveis todos os endereços materiais ilimitados. As decomposições físicas já existentes, inclusive `cauchyLaguerre_originalSource_legs` e seus cruzamentos com completion, conservam suas próprias hipóteses de faixa física.

### 4. Onde exatamente os dois transportes divergem

Em `ResponseDefect.lean`, `radial_symbol_cayley` identifica o comparador com a transformação de Cayley da coordenada **linear** `2z`, e `native_response_defect_on_grid` prova, nos pontos regulares:

\[
\boxed{
q(z)-m(z)=
\frac{2i\,[a(z)-2z]}{[a(z)+i][2z+i]},\qquad a(z)=-F'(z)/F(z).
}
\]

Assim, a diferença não é um fator de norma que possa ser apagado. É a diferença entre a resposta completada inteira e o endereço material linear. A identidade usa a função original, com dressing e completion, antes da leitura de momentos.

Em `RadialLimits.lean`, o primeiro termo fornece:

\[
(k+1)(q(z_{k,j})+1)\to4(j+1)h_0,
\qquad
(k+1)(m_{k,j}+1)\to4(j+1),
\]

\[
\boxed{(k+1)(q(z_{k,j})-m_{k,j})\to4(j+1)(h_0-1).}
\]

Os teoremas são `native_symbol_tangent`, `radial_symbol_tangent`, `native_symbol_defect_tangent`. A primeira relação é recuperada da derivada já provada da característica, não de uma hipótese de positividade.

Em `Orientation.lean`, a cota antiga `h₀<1/16` identifica o coeficiente como não nulo; `native_symbol_eventually_ne` prova que os símbolos diferem eventualmente em **cada coluna fixa**, inclusive as duas primeiras. Nenhuma constante foi ajustada para fazer coincidir esses termos.

### 5. Coincidência dominante não basta

`scaled_comparator_tendsto` prova, em toda direção finita fixa de jets, que o vetor do comparador observado tende ao mesmo `-w` do retorno original. Consequentemente,

\[
\sigma_{k,m}\eta_k(x)\longrightarrow0
\]

(`scaled_native_defect_tendsto_zero`). Este avanço remove o defeito dominante não nulo do candidato fixo da PR #62. A comparação radial é melhor nessa escala, mas ainda não é uma igualdade física.

As fronteiras `![1,0]` e `![0,1]` são as mesmas da PR #41. `first_even_coefficients`, `first_odd_coefficients` e `first_odd_scaled_defect_tendsto_zero` fazem os testes concretos em ambos os setores, preservando as duas amostras e suas amplitudes separadas.

### 6. No primeiro par, o erro vai a zero e o cruzamento sobrevive

Em `FirstJet.lean`, a análise é feita sobre a fonte exata:

\[
|H_k|^2\to2,\qquad D_k\to2h_0,\qquad\eta_k\to0.
\]

`first_even_defect_factor` prova a fatoração vetorial que controla a última passagem. Não se deduziu esse limite apenas de um erro escalar normalizado.

Com a identidade completa do balanço, `first_even_mixed_cross_tendsto` obtém

\[
\boxed{
2\operatorname{Re}\langle C_kI_k,\eta_k\rangle\to2(1-h_0).
}
\]

A norma do erro tende a zero, mas a norma do canal com que ele cruza cresce. Portanto o cruzamento não desaparece. Somente a cota já conhecida `h₀<1/16`, isolada em `Orientation.lean`, orienta esse limite como estritamente positivo e prova positividade eventual do cruzamento. Os limites anteriores não recebem sinal de pivôs.

A recuperação do balanço original é exata:

\[
2-2(1-h_0)-0=2h_0.
\]

O primeiro momento não foi redefinido nem normalizado para valer `1`. Este exemplo demonstra por que uma aproximação vetorial de transporte não autoriza apagar o defeito no balanço de canais crescentes.

## C — O que foi refutado

1. A família radial conservativa herdada do endereço não é o retorno completado original. O defeito de primeira ordem é explicitamente não nulo nas duas primeiras colunas.
2. Coincidência do limite dominante dos vetores não identifica o primeiro residual finito.
3. Mesmo `η_k→0` sem normalização, no primeiro par, não autoriza descartar os cruzamentos: há limite misto `2(1-h₀)>0`.
4. A porta positiva do comparador não é a forma canônica inteira. A diferença assinada permanece no mesmo objeto original.

Essas são obstruções à realização testada. Não se excluem outras coligações físicas que realizem a resposta completada `a(z)`, nem se demonstra impossibilidade geral da geometria. Tampouco se exclui a positividade do retorno finito exato já existente.

Não se tentou corrigir o símbolo usando `h₀` como constante ajustada. Coincidir uma derivada por ajuste não provaria a igualdade do kernel em dois argumentos nem as demais ordens.

## D — O que permanece aberto

O retorno finito exato dependente de `k` está definido e realiza a fonte. O que permanece aberto é obter sua conservação com complemento positivo a partir de relações físicas independentes, mantendo a resposta completada em vez de apenas o endereço.

A equivalência entre contratividade e storage não descarrega seu sinal. O mesmo vale para as equivalências Herglotz/Pick já existentes. Não se introduziu um predicado equivalente à positividade para chamá-lo de causa geométrica.

A construção conservativa do comparador é válida em qualquer dimensão finita e coerente por prefixos. Sua identificação com os momentos canônicos falha já no primeiro coeficiente. Nenhum resultado de positividade canônica all-order, convergência do operador de alturas ou identificação com zeros é anunciado.

Para o primeiro ímpar, o limite **normalizado** do defeito é formal. As taxas não normalizadas de crescimento sugeridas pelas tabelas abaixo são apenas diagnósticos numéricos nesta entrega. Não se reivindicou uma expansão completa desse setor.

## E — Próximo passo mínimo

O alvo deve ser a resposta nativa `a(z)=-F'(z)/F(z)`, incluindo seus canais de completion e bordos. A transformação de Cayley do endereço `2z` já foi testada e não serve como substituta.

O passo seguinte mais curto é confrontar uma relação **operatória e física** de fluxo/bordo já existente com `a(z)` em dois argumentos independentes, antes de extrair momentos. Se a relação fornece somente a parte linear do endereço, calcular o resto `a(z)-2z` usando os canais originais da síntese completa; não absorvê-lo numa métrica ou constante nova.

Uma obrigação concreta de proveniência é procurar, nos operadores Green originais e com domínio declarado, o mapa que leva `physicalSourceValue` à síntese conjunta `physicalNativeCompanion + physicalCompletionCompanion`, conservando os pareamentos em duas entradas. As identidades algébricas dessas pernas já existem; falta justificar o mapa por uma construção operatória anterior à resposta, em vez de defini-lo pela tabela de valores de `a(z)`. Esse teste deve começar nas duas colunas admissíveis aqui utilizadas.

Para que isso avance o sinal, é necessário demonstrar uma conservação/fatoração independente para a resposta completada ou controlar seus cruzamentos com escala suficiente. Postular contratividade, ou apenas reescrever o sinal como positividade do kernel Herglotz, não constitui esse avanço.

A lição concreta agora provada é: preservar `k` corrige o limite dominante, mas a informação canônica continua no primeiro termo que cruza com o canal crescente. A próxima estimativa precisa controlar esse cruzamento, não apenas a norma absoluta de `η`.

## Experimentos reproduzíveis e seu alcance

`experiment.py` verifica 125 identidades racionais exatas do complemento e da transformação do shift. Depois avalia a fonte finita original por células centro–pernas, bordo acelerado e dressing Gamma, com 50 casas, em dois cutoffs: 2.048 e 4.096 células.

Não há chamada à zeta, tabela theta, momentos, zeros ou alturas como entrada. A aritmética da Gamma e as avaliações finitas são numéricas, **não intervalos certificados**. A curvatura estimada é uma saída da mesma fonte finita.

Exemplo com 4.096 células e `k=255`:

| Setor | Balanço nativo | Porta do comparador | Energia do defeito | Cruzamento misto |
|---|---:|---:|---:|---:|
| Primeiro par | `0,0462100177` | `1,9698247664` | `0,0146810335` | `1,9089337151` |
| Primeiro ímpar | `0,0000743297` | `7,2851494528` | `310,9591875762` | `−303,6741124531` |

Em cada linha a identidade é porta menos cruzamento menos erro. As duas quadraturas e todos os termos de Gram foram mantidos. As tabelas completas, com os dois cutoffs, estão em `evidence/experiment.json`.

O limite misto estimado no primeiro par é aproximadamente `1,95379001377`; a fórmula para o limite tem prova Lean, e essa aproximação decimal é somente uma avaliação numérica.

## Validação

Os novos arquivos contêm 42 teoremas e oito definições públicas. `generate_audit.py` inventaria as 50 declarações e audita suas dependências transitivas em tipos e corpos. Os grupos anteriores a `orientation` bloqueiam os sinais centrais usados para orientar as obstruções; todos bloqueiam os consumidores posteriores H6/K6/H7 e gates de positividade recebidos.

Não foram acrescentados axiomas matemáticos, `sorry`, `admit` ou `native_decide`. Os únicos axiomas admitidos pela auditoria analítica são `propext`, `Classical.choice` e `Quot.sound`. A fundação discreta conserva sua auditoria própria.

Na mesma pilha já compilada da PR #62:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/radial-cauchy-conservative-test/validate.py
```

O script compila explicitamente os módulos novos com `warningAsError=true`, executa os controles e diagnósticos, os builds focado e raiz com `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e a regressão das doze fontes. Verifica ainda referências históricas, pins, worktrees, arquivos não rastreados protegidos e fontes da PR #62.

**Execução concluída: 17/17 checks passaram.** Os sete módulos (incluindo a auditoria), os testes, os builds com `--wfail`, as três auditorias e a regressão das doze fontes concluíram com código de saída zero. A auditoria de tipos e corpos passou para as 50 raízes públicas, com somente os três axiomas fundacionais permitidos.

Comandos, resultados, tempos e hashes são registrados em `evidence/checks.json`, `evidence/kernel-Audit.log`, `evidence/preflight.json` e `evidence/source-sha256.json`. A dependência das fontes imutáveis da PR #42 é a mesma já documentada e compilada na PR #62; não houve novo port histórico nem mudança de pin.

**Conclusão:** uma família radial conservativa concreta foi testada com a fonte original. O parâmetro radial resolve a incompatibilidade dominante do comparador fixo, mas permanece um defeito de primeira ordem. No primeiro par esse erro vetorial tende a zero e, apesar disso, seu cruzamento conserva exatamente a diferença necessária para recuperar `h₀`. O sinal canônico em toda ordem permanece aberto.
