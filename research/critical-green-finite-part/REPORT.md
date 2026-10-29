# Parte finita do balanço Green crítico completo

**Classificação: PARTIAL.** Esta continuação ataca o próximo alvo da PR #86: extrair a parte finita do balanço Green original, preservando os nove cruzamentos e controlando o resto analítico. A positividade canônica em toda ordem permanece aberta.

Base imutável: `beb07b54e7cffa767a33cc3e1f7d53018a2e9aca`, head da draft [PR #86](https://github.com/thiagomassensini/geometry-of-numbers/pull/86). Branch: `agent/critical-green-finite-part`; base de revisão: `agent/interior-green-critical`. Main, pins, fontes e PRs anteriores são preservados. Sem merge automático.

## A — O que já estava demonstrado

A [PR #41](https://github.com/thiagomassensini/geometry-of-numbers/pull/41) separou a ortogonalização algébrica do sinal: `NativeMomentOrthogonalization.sourceMomentSchur_sewing_of_isUnit` e `sourceMomentSchur_critical_direction_of_isUnit` recebem inversibilidade do bloco antigo, sem pressupor o sinal do próximo residual. A draft continua independente. Aqui se reutiliza a definição original `CarrySelfAdjointOperator.sourceMomentSchur`; os arquivos da #41 não são importados nem modificados.

A #86 identificou os vetores completos, as portas interiores e os nove cruzamentos da direção `J₂−aJ₀`. Reutilizamos `critical_source_original`, `critical_energy_three_sectors`, `critical_mixed_nine_crossings`, `three_regular_eventually`, `first_source_schur_eq` e as portas `basis_contrast`, `projective_mean_response`, `physical_column_inner`. EE=0 é isotropia da forma assinada; o residual não foi declarado nulo nem descartado.

Da fonte original, `completedNativeGreenNormalizedResponse_analyticAt` e `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` fornecem analiticidade e os coeficientes exatos da resposta completada. Os coeficientes pares são zero. Não se presume uma medida espectral positiva.

A [PR #43](https://github.com/thiagomassensini/geometry-of-numbers/pull/43), commit `bc7f36f1bd29d0d09fc23778e9e074c2be82123d`, já certificou duas desigualdades finitas da fonte:

- `CarryCriticalMixed.source_nonlinear_margin_pos`: `h₀h₂−2h₁²>0`;
- `CarryCriticalMixed.source_correction_numerator_pos`: `2h₁³−80h₀h₁h₂+28h₀²h₃>0`.

Elas vêm das caixas racionais dos integrais theta originais. Esta continuação **não as apresenta como novas** e não as utiliza para provar a expansão analítica. São reutilizadas somente no módulo `CertifiedDirection.lean`. O certificado anterior `canonicalCompletedNativeLogDerivativeMoment_zero_pos` fornece h₀>0.

## B — O que foi demonstrado agora

### Mesmo objeto físico, antes do readout

Escrevemos κ=k+1, t=κ⁻¹ e zⱼ=i(j+1)/κ. Este k é o índice radial, não a profundidade Carry nem o endereço material. R=−F′/(2F) é a resposta completada original. O parâmetro Green satisfaz 0<η<1 quando se invoca a reconstrução.

A forma anterior permanece

\[
 \Phi(x,y)=\tfrac12(\langle x^+,y^+\rangle-\langle x^-,y^-\rangle).
\]

Ela é assinada. Não é substituída por uma norma positiva. `greenBalance η a k` abrevia precisamente

\[
 E_k(a)=\Re\Phi(B_a,B_a)+2\Re\Phi(B_a,E_a).
\]

`green_balance_source` identifica essa expressão com a energia assinada da fonte original `J₂−aJ₀`, usando a reconstrução vetorial já provada. Os termos BB, BE, EB e o cancelamento EE seguem as identidades anteriores. O produto físico, as duas pernas, as fases, a amplitude √(2κ), as colunas Cauchy, os bordos, o retorno e o completion são mantidos.

`source_basis_real` mantém dois endereços independentes:

\[
 \Re\Phi(S_i,S_j)=\frac{\kappa}{i+j+2}
 (\Im R(z_i)+\Im R(z_j)).
\]

Os coeficientes reais são forçados pelo jet original:

\[
 c=(-\kappa^2/2-a,\ \kappa^2,\ -\kappa^2/2).
\]

`source_energy_three_samples` soma todos os nove pares ordenados, com os mesmos coeficientes. Somente depois dessa síntese, `green_balance_three_samples` extrai a fórmula escalar exata:

\[
 E_k(a)=\kappa\left[
 (a^2+7a\kappa^2/12+\kappa^4/24)\Im R(z_0)
 +(-2a\kappa^2/3-\kappa^4/30)\Im R(z_1)
 +(a\kappa^2/4+\kappa^4/120)\Im R(z_2)\right].
\]

Ela vale nas condições originais de não anulação de F e E⁺ nos quatro nós do prefixo. `three_regular_eventually` descarrega essas condições para k suficientemente grande. Não se introduz regularidade global como hipótese matemática nova.

### Expansão exata e resto retido

Definimos apenas abreviações escalares de coeficientes, sem alterar a fonte:

\[
 \begin{aligned}
 P(a)&=h_2-2ah_1+a^2h_0,\\
 C(a)&=-a^2h_1+40ah_2-14h_3,\\
 Q(a)&=a^2h_2-462ah_3+147h_4.
 \end{aligned}
\]

`readout_exact_remainder` usa a analiticidade da mesma resposta e demonstra, perto de zero,

\[
 -iR(it)=h_0t-h_1t^3+h_2t^5-h_3t^7+h_4t^9+t^{11}\mathcal R(t),
 \qquad\mathcal R\text{ analítica}.
\]

`green_balance_exact_expansion` prova, para todo a real fixo e todo η admissível, eventualmente:

\[
 \boxed{E_k(a)=P(a)+t^2C(a)+t^4Q(a)+t^6U_{\mathcal R}(a,t).}
\]

O mesmo germe analítico serve para todos os a e η. A fórmula explícita do resto, sem apagar termos cruzados, é

\[
 \begin{aligned}
 Z_{\mathcal R}(a,t)={}&(a^2t^4+7at^2/12+1/24)\Re\mathcal R(t)\\
 &+2048(-2at^2/3-1/30)\Re\mathcal R(2t)\\
 &+177147(at^2/4+1/120)\Re\mathcal R(3t),\\
 U_{\mathcal R}(a,t)={}&-a^2h_3+4580ah_4+t^2a^2h_4+Z_{\mathcal R}(a,t).
 \end{aligned}
\]

As constantes 2048=2¹¹ e 177147=3¹¹ vêm dos nós radiais originais. A igualdade exata, incluindo todos os coeficientes e sinais, é verificada por Lean.

`error_readout_continuousAt` prova continuidade do resto. Os três limites são:

\[
 \begin{aligned}
 E_k(a)&\longrightarrow P(a),\\
 \kappa^2(E_k(a)-P(a))&\longrightarrow C(a),\\
 \kappa^4(E_k(a)-P(a)-\kappa^{-2}C(a))&\longrightarrow Q(a).
 \end{aligned}
\]

Seus nomes são `green_finite_term_limit`, `green_correction_limit` e `green_fourth_correction_limit`.

`green_sixth_order_error_bound` demonstra ainda a estimativa analítica:

\[
 \exists M>0,\quad
 |E_k(a)-P(a)-\kappa^{-2}C(a)-\kappa^{-4}Q(a)|
 \le M\kappa^{-6}\quad\text{eventualmente}.
\]

M e o limiar são existenciais e podem depender da fonte e de a. Não se fornece um cutoff numérico nem uma estimativa uniforme na ordem.

### Direção crítica e sinal reaproveitado

Se a*=h₁/h₀, `finite_term_critical`, recebendo somente h₀≠0, identifica

\[
 P(a_*)=\operatorname{sourceMomentSchur}(h,0,1)=h_2-h_1^2/h_0=:p.
\]

`critical_correction_formula` demonstra

\[
 C(a_*)=-\frac{h_1^3-40h_0h_1h_2+14h_0^2h_3}{h_0^2}.
\]

A #43 já certificou o numerador positivo, com fator 2. `critical_correction_negative` transporta esse certificado: C(a*)<0. `critical_finite_term_positive` reaproveita a outra desigualdade da mesma fonte para obter p>0. Não se recebe positividade de H6/K6.

`critical_green_scaled_correction` identifica a primeira correção com o Schur original. `critical_green_eventually_between` conclui, para cada η admissível,

\[
 \boxed{0<E_k(a_*)<p\quad\text{eventualmente}.}
\]

Não se demonstra monotonicidade. A normalização atual é a mesma Φ da #86, cujo limite é p. A `secondBalance` da #43 tinha limite 2p e parâmetro crítico de sinal oposto. A correção atual corresponde à metade da antiga após essa troca de parâmetro; a relação é explicada pela definição antiga `sourceCoefficient=2h`. Não se mudou uma normalização física para obter o sinal.

A novidade é a extração do **balanço Green completo** com coeficiente de quarta ordem explícito e erro O(κ⁻⁶), não uma nova descoberta da desigualdade finita da #43.

### Validação e reprodução

**PASS nas 16 verificações sequenciais**, no host canônico llm, Lean `v4.32.0`: proveniência, geração da auditoria, build nativo focado com `--wfail`, compilação dos cinco módulos novos e da auditoria, diagnóstico 80/120 dígitos, build raiz com `--wfail`, auditorias Foundation/Geometry/Analysis, preservação da base e `git diff --check`.

São **29 teoremas e 11 definições**, 40 raízes públicas no namespace `CarryGreenFinitePart`. As inspeções transitivas produziram:

| Grupo | Raízes | Constantes únicas em tipos e corpos | Controle |
| --- | ---: | ---: | --- |
| Construção física | 10 | 5822 | Não usa momentos para fabricar estados; bloqueia consumidores posteriores de sinal. |
| Identificação analítica | 26 | 6288 | Não depende dos certificados de sinal da #43, de H6/K6 ou dos polinômios theta listados no guard. |
| Sinais finitos reutilizados | 4 | 6245 | Consome explicitamente h₀>0 e as duas desigualdades da fonte da #43. |
| União | 40 | 6310 | Somente `propext`, `Classical.choice` e `Quot.sound`. |

Foram recompilados também os **33 módulos ancestrais** e as **cinco fontes antigas inalteradas da #43** necessárias à importação do certificado, com hashes registrados. Não há `sorry`, `admit`, `native_decide` ou novos axiomas nas fontes novas. Os módulos históricos, pins e os dois arquivos não rastreados preexistentes do usuário no operador foram conferidos e preservados.

Os logs e comandos estão em `evidence/validation.json`. Os resultados são validação local em Lean; não são uma afirmação sobre CI remoto.

Os módulos de pesquisa não são importados automaticamente pelo build raiz. Cada módulo novo e `Audit.lean` é compilado explicitamente com `-DwarningAsError=true`, além dos builds com `lake build --wfail` e das auditorias Foundation/Geometry/Analysis.

A auditoria separa: construção física sem momentos como entradas; identificação analítica sem certificados de sinal; corolários finitos que consomem explicitamente as duas desigualdades da #43. Percorre tipos e corpos, incluindo constantes privadas, e imprime os axiomas de cada raiz nova. Bloqueia os consumidores posteriores de positividade listados no código.

No host canônico llm, em checkout desta branch e com as dependências anteriores preservadas:

```bash
cd research/critical-green-finite-part
mkdir -p evidence
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 build_pr43.py > evidence/pr43-build.log 2>&1
python3 validate.py
```

`build_pr43.py` recupera do commit publicado as cinco fontes antigas estritamente necessárias ao certificado `IntegralOrientation`, sem modificá-las, e as recompila em cache ignorado. Caso o objeto Git antigo não esteja disponível, buscar antes a referência da PR #43. `record_provenance.py` verifica os hashes das fontes ancestrais, dos certificados recuperados e dos artefatos compilados. Nenhum pin é alterado. A independência lógica dos módulos é auditada pelas dependências das declarações, não por mera presença de imports no ambiente.

O diagnóstico Python avalia a característica original por sua identidade downstream já provada com xi, sem reexecutar toda a síntese material TFVD. Não recebe zeros, alturas ou tabelas de momentos. Confere os nove cruzamentos, a recomposição BB+2BE, a fórmula de três amostras e os dois limites escalados a 80/120 dígitos. O pivô diagnóstico é aproximadamente 8,43685841013415×10⁻⁸; a primeira correção, −1,00459789378746×10⁻¹⁰. O coeficiente de quarta ordem é numericamente −2,00438815849429×10⁻¹¹, sem novo certificado formal do seu sinal. Para κ=10,100,1000, os erros escalados e as recomposições estão em `evidence/finite-part-diagnostic.json`. Esses números são diagnósticos, não certificados Lean de sinal nem demonstrações all-order.

## C — O que foi refutado ou não pode ser inferido

Não se provou uma nova impossibilidade da geometria. A conta exata confirma o cancelamento dos termos divergentes no balanço completo. Não se formalizaram aqui taxas individuais para BB e BE, nem se pode identificar a positividade de uma dessas parcelas com o sinal da soma.

EE=0 continua sem significar estado nulo. A expansão não transforma Φ numa forma positiva. C(a*)<0 não implica positividade de todos os pivôs; p>0 nesta direção vem de um certificado finito independente já existente. A identidade com Schur isoladamente não determina o sinal, conforme a separação da #41.

Não se demonstrou sinal de Q(a*) nem uma regra universal para as correções de outras ordens. Nenhuma equivalência com positividade canônica é utilizada como prova incondicional.

## D — O que permanece aberto

A obrigação local da #86 — desenvolver a parte finita do balanço original e controlar o resto — passa a ter uma identidade e uma estimativa precisas. Permanece aberta uma lei geométrica independente que force o sinal dos Schurs em ordem arbitrária, conservando cruzamentos e cauda.

O sinal favorável nesta direção utiliza as caixas theta antigas. A expansão Green não é uma nova prova geométrica autônoma desses sinais. Também não fornece por si só uma representação Gram positiva infinita dos momentos canônicos, um operador infinito de alturas, identificação de zeros ou uma solução da positividade all-order.

## E — Próximo passo mínimo

Derivar a versão **polarizada** da extração da parte finita para uma direção polinomial finita geral, a partir do mesmo kernel físico `source_basis_real` e da resposta analítica original. Manter os dois argumentos independentes e obter os coeficientes e o resto antes de qualquer hipótese de sinal.

O primeiro teste concreto é o próximo polinômio mônico par, de grau dois na variável de momentos. Com

\[
 A_2=\begin{pmatrix}h_0&h_1\\h_1&h_2\end{pmatrix},\qquad
 \binom{u_0}{u_1}=A_2^{-1}\binom{h_2}{h_3},
\]

investigar o estado original `J₄−u₁J₂−u₀J₀`, com os fatoriais e fases dos jets anteriores. O alvo finito é `h₄−(h₂,h₃)A₂⁻¹(h₂,h₃)ᵀ`, sem presumir seu sinal. Identificar a forma completa e a primeira correção usando apenas a inversibilidade do prefixo para escolher a direção da #41. A identidade deve distinguir o Schur de seu resto e não pressupor sua positividade. Só depois se procura uma desigualdade independente da fonte que oriente o termo finito. Repetir apenas a certificação de mais um coeficiente nesta direção não estabeleceria uma lei de sinal em toda ordem.

FIM DO RELATÓRIO — CRITICAL_GREEN_FINITE_PART
