# Lei geral da correção radial de segunda ordem da fonte Carry

**PASS para o próximo lema da PR #44. PARTIAL para a positividade canônica
em toda ordem.** O limite assintótico antes aberto foi provado para qualquer
dimensão finita fixa, em ambos os setores, inclusive na forma polarizada.
Não foi demonstrado um sinal universal dos pivôs ou das correções.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/all-order-critical-correction`.
Base: `c5af416a49e3203982b6bba95b741bfe97b9932f`, cabeça da PR #44,
cuja base é a PR #43. A continuação é empilhada sobre
`agent/critical-source-coefficient-law`, sem presumir integração à main.
`origin/main` foi conferida em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.

Fonte nativa consultada sem alteração: `carry-self-adjoint-operator`,
commit `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Os dois arquivos de pesquisa não rastreados do operador foram preservados.
Reutilizou-se o checkout limpo em nova branch; nenhuma worktree foi criada.
Não se alteraram PRs anteriores, fonte, normalizações, pesos, métricas ou pins.

## A — O que já estava demonstrado

A PR #44 havia deixado explícita esta obrigação: para os inputs originais
de paridade, provar a taxa de segunda ordem em qualquer dimensão finita,
com a correção calculada dos stencils e sem hipótese de sinal.

Foram reutilizados, entre outros:

- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`: a síntese
  vetorial é a dos dois canais originais, com o mesmo mapa de coeficientes.
- `nativeSourceProjectiveBoundaryJetSynthesis_pairing`: todos os pareamentos
  ordenados de duas sínteses independentes, antes da diagonal e do readout real.
- `nativeSourceProjectiveBoundaryJetSynthesis_energy` e
  `nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage`: fatores
  exatos entre a forma assinada, as normas dos canais e o storage físico.
- `projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope`: identificação
  exata do pareamento físico com o kernel completado, no regime regular.
- `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` e
  `completedNativeGreenResponseTaylorCoefficient_even_eq_zero`: proveniência
  all-order dos coeficientes do readout da fonte completada.
- `greenContraction_below`, `greenContraction_leading`,
  `greenContraction_second`, `source_power_coefficient_exact`: contrações
  dos stencils e cruzamentos Cauchy provadas na PR #44.
- `sourceMomentSchur_critical_direction_of_isUnit`: ortogonalização algébrica
  e identidade crítica sob inversibilidade, sem assumir positividade.
- `all_order_euler_exact`: separação de Euler do resto não linear original.

Não se usaram os antigos limites finitos como premissas do novo limite geral.
Os guardas transitivos verificam isso por nome, além de rejeitar certificados
posteriores específicos de positividade finita. O símbolo `k` abaixo indica
a regularização radial da fonte, não a profundidade vertical do Carry.

## B — O que foi demonstrado agora

### 1. Enunciado principal, com polarização

Sejam `s:Fin 2`, `N:ℕ` e `v,w:Fin N→ℝ`. Os vetores físicos são exatamente

\[
\Phi_k(v)=\mathrm{nativeSourceProjectiveBoundaryJetSynthesis}\ N\ k\
             (\mathrm{parityCoordinates}\ s\ v).
\]

Não são fabricados a partir de uma matriz de momentos. A igualdade vetorial
`synthesis_parity` identifica essa síntese com a combinação dos jets físicos
originais de ordens `2i+s`. As fases e amplitudes são as preexistentes.

Sejam

\[
\begin{aligned}
P_k(v,w)&=\tfrac12\bigl(\langle I_k(v),I_k(w)\rangle
                         -\langle R_k(v),R_k(w)\rangle\bigr),\\
H_s(v,w)&=\sum_{i,j<N}v_iw_jh_{i+j+s},\\
C_s(v,w)&=\sum_{i,j<N}v_iw_jh_{i+j+s+1}
 \bigl(A_{2i+s}A_{2j+s}-B_{2i+s}-B_{2j+s}\bigr).
\end{aligned}
\]

`P_k` é a forma projetiva assinada original, de valor complexo. Seu fator
`1/2` pertence à definição histórica; não foi escolhido para ajustar momentos.
Os coeficientes reais `v,w` são independentes; os estados físicos continuam
complexos, com ambas as quadraturas e todos os cruzamentos.

O novo teorema **`finite_polarized_second_correction`** prova

\[
\boxed{(k+1)^2\,[P_k(v,w)-H_s(v,w)]\longrightarrow C_s(v,w).}
\]

Não há hipótese de positividade, independência linear ou inversibilidade.
O enunciado inclui a dimensão zero. A dimensão e os coeficientes ficam fixos
durante o limite; não há uniformidade em dimensões crescentes.

Na diagonal, o balanço físico original é

\[
D_k(v)=\|I_k(v)\|^2-\|R_k(v)\|^2
      =\mathrm{storage}_k(v).\mathrm{re}=2\operatorname{Re}P_k(v,v).
\]

**`finite_balance_second_correction`** prova exatamente a meta da PR #44:

\[
\boxed{
(k+1)^2\,[D_k(v)-2H_s(v,v)]
\longrightarrow 2C_s(v,v)
=\mathrm{canonicalCorrection}\ s\ N\ v.
}
\]

Logo a correção antes calculada como expressão de coeficientes é agora
identificada com a taxa do mesmo balanço físico em qualquer ordem finita.

### 2. Como o resto foi controlado após a amplificação dos stencils

Em `RawGreenRay.lean`, usa-se o readout COMPLETADO original
`Q=-F'/(2F)`, sem remover dressing, completion ou retorno. Para os pesos
originais `w_pr=(-1)^(p-r) choose(p,r)`, o numerador analítico é

\[
N_{pq}(t)=\sum_{r\le p}\sum_{u\le q}
\frac{w_{pr}w_{qu}}{i(r+u+2)}
\bigl[Q(i(u+1)t)-Q(-i(r+1)t)\bigr].
\]

Esse germe escalar é estudado **depois** da identificação exata do kernel
com a síntese completa. Não substitui os estados ou sua métrica.
`rawGreenRay_analytic` prova sua analiticidade, e `rawGreenRay_odd` identifica
seus coeficientes de ordem `2j+1` com

\[
(-1)^j h_j\,\mathrm{greenContraction}(p,q,2j).
\]

Os coeficientes de ordem par são zero. As contrações da PR #44 dão então:

- todos os coeficientes abaixo de `D=p+q+1` se anulam exatamente;
- o coeficiente de ordem `D+1` também é zero;
- o coeficiente de ordem `D+2` é o peso de correção já calculado, com seus
  fatores de fase e de fatorial.

Em `RadialPairing.lean`, `projective_pairing_eventually_ray` demonstra,
para `p=2i+s`, `q=2j+s`, `τ_k=(k+1)^(-1)`,

\[
\mathfrak B(J_{p,k},J_{q,k})=
\frac{(-1)^{i+j}}{p!q!}\,
\frac{N_{pq}(\tau_k)}{\tau_k^{p+q+1}}
\quad\text{eventualmente}.
\]

São os MESMOS jets `projectiveChiralDifferenceJet`. Todas as fases são
provadas em `parity_phase` e `normalization_eq_phase`; não foram normalizadas
retroativamente ou recebidas como hipótese de transporte.

O lema `analytic_second_coefficient_tendsto`, em `AnalyticExtraction.lean`,
preserva o resto analítico de Taylor até ordem `D+3`. Depois da divisão por
`τ^D`, seu fator é `τ³`; depois da leitura da correção, fica `τ R(τ)→0`.
Assim a amplificação por potências inversas do passo é resolvida por
**anulações exatas**, não por uma estimativa que perde os cancelamentos.

`projective_pairing_second_correction` fecha a taxa entrada a entrada.
A soma finita polarizada vem somente depois; a parte real e a diagonal
são tomadas por último. Não se aproximam separadamente duas energias
divergentes para então subtraí-las.

### 3. Direção crítica arbitrária

Para o vetor crítico preexistente `v=(-A⁻¹b,1)`, a única hipótese adicional
necessária é `IsUnit A`. `critical_boundary_pairing` identifica `H_s(v,v)`
com o pivô `σ=sourceMomentSchur h s n`.

**`critical_second_correction`** demonstra

\[
\boxed{(k+1)^2\,[D_k(v)-2\sigma]\longrightarrow
\mathrm{criticalCorrection}(s,n).}
\]

Não se exige `A.PosDef`, nem `σ>0`. O caso sem inversibilidade não foi
interpretado como uma ortogonalização crítica válida pela inversa total.
A lei para vetores finitos arbitrários continua disponível sem essa hipótese.

`critical_nonlinear_second_correction` prova ainda que o MESMO coeficiente
controla o resto físico não linear após retirar sua constante de Euler:

\[
(k+1)^2\left[N_k(v)-\bigl(2\sigma-2h_0|v_0|^2\bigr)\right]
\longrightarrow \mathrm{criticalCorrection}(s,n).
\]

A constante do resto e sua correção são informações distintas.
As aplicações `critical_eventually_above_of_correction_pos` e
`critical_eventually_below_of_correction_neg` são explicitamente condicionais
ao sinal do coeficiente; não demonstram esse sinal em toda ordem.

### 4. Regressões e um teste novo dentro do mesmo setor

`Regression.lean` reproduz as duas leis das PRs #43 e #44 a partir do novo
teorema geral. Os antigos teoremas assintóticos finitos são proibidos pelo
auditor como dependências dessa reprodução.

Há também os canários exatos:

\[
\mathrm{criticalCorrection}(0,0)=-2h_1,\qquad
\mathrm{criticalCorrection}(1,0)=-10h_2.
\]

A caixa theta original certifica `h2>0`, por redução no kernel.
`first_odd_second_correction` e `first_odd_eventually_below` transportam esse
sinal para a primeira direção crítica ímpar original. Por outro lado, a
segunda direção ímpar tem correção positiva, como certificado na PR #44.

**`odd_sector_opposite_corrections`** prova, portanto, sinais opostos já
dentro do mesmo setor ímpar, nas ordens críticas `n=0` e `n=1`.
Isso não constitui uma campanha de novos pivôs, não altera a PR #32 e
não usa zeros, alturas ou checkpoints decimais como entrada de prova.

## C — O que foi refutado ou descartado

A orientação da correção não pode ser determinada apenas pelo rótulo
par/ímpar: há dois sinais dentro do setor ímpar original.
Esse contraexemplo não é uma obstrução à positividade canônica; os pivôs
envolvidos já possuem certificados próprios positivos.

O orçamento absoluto de caudas não foi reutilizado como coercividade.
Também não se usou positividade do resto não linear como nova causa geral:
no setor crítico ímpar, a identidade preexistente `N_k=D_k` continua válida.

A taxa de segunda ordem NÃO determina o sinal da constante `2σ`.
A mesma forma de expansão admite uma constante positiva, nula ou negativa;
a conclusão de sinal precisa de uma propriedade adicional da fonte.

## D — Certificação e limites do resultado

Foram adicionados somente módulos em `research/all-order-critical-correction/`:
`AnalyticExtraction`, `RawGreenRay`, `RadialPairing`, `PairCorrection`,
`FiniteCorrection`, `CriticalCorrection`, `Regression` e `Audit`.
São **48 teoremas e nove definições/abreviações** de leitura ou coeficientes.
Nenhum operador físico, fonte ou produto interno foi redefinido.

O auditor enumera as 57 declarações públicas e três dependências explícitas,
usa `#print axioms` e percorre transitivamente tipos e corpos: **60 raízes e
6.091 constantes**. Somente `propext`, `Classical.choice` e `Quot.sound`
foram admitidos. Rejeita
certificados posteriores específicos de positividade finita e os antigos
limites assintóticos listados no código. Um segundo guard percorre seis
raízes gerais, com **5.889 constantes transitivas**, para impedir consumo
dos certificados finitos de sinal
listados, incluindo as duas desigualdades da PR #43 e as da PR #44.

Os guardas são verificações de dependências nomeadas. Não substituem a
leitura das hipóteses dos teoremas nem detectam automaticamente toda
reformulação lógica possível. As hipóteses efetivas estão descritas acima.

A validação terminou com **16 checks de código zero**, além do build nativo
separado também aprovado. Inclui builds nativos e focados com `lake build --wfail`, os
oito módulos de pesquisa explicitamente com `-DwarningAsError=true`, o build
da raiz, auditorias Foundation/Geometry/Analysis, regressão H6/K6 com doze
fontes e verificação de que os arquivos históricos permaneceram intactos.
Os resultados e comandos exatos estão em `evidence/checks.json`, os axiomas
em `evidence/kernel-Audit.log`, e os hashes em `evidence/source-sha256.json`.

Reprodução no host canônico, com as camadas de pesquisa ancestrais
compiladas conforme seus respectivos scripts:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/all-order-critical-correction/generate_audit.py
python3 research/all-order-critical-correction/validate.py
```

Não há `sorry`, `admit`, `native_decide`, novos axiomas matemáticos,
alterações de dependências ou ajustes de momentos. Nenhuma conclusão de
CI remoto é presumida pelos builds registrados no host `llm`.

**Alcance:** qualquer dimensão finita fixa e dois vetores reais de
coeficientes independentes, com as quadraturas complexas dos estados
preservadas. Não há estimativa uniforme na dimensão, cutoff radial efetivo,
convergência em norma de um operador infinito ou positividade all-order.

## E — O que falta agora e próximo passo mínimo

A obrigação técnica escrita na parte E da PR #44 está fechada: o coeficiente
formal foi transportado ao limite físico, com as fases e o resto controlados.
Ela não deve mais ser listada como uma ponte aberta.

A lacuna de sinal é outra: ainda não foi identificada uma propriedade
independente da síntese completada que determine `σ>0` em toda ordem.
Nem a existência da ortogonalização algébrica, nem a nova lei de taxa,
nem o sinal de uma correção finita descarregam essa obrigação.

O próximo passo algébrico concreto, anterior a qualquer conjectura de sinal,
é fechar as fórmulas polinomiais dos dois pesos de stencil

\[
A_p=\frac{(p+1)(p+2)}2,\qquad
B_p=\frac{(p+1)(p+2)(p+3)(3p+4)}{24},
\]

atualmente definidos por somas binomiais exatas. Essas fórmulas não são
reivindicadas como novos teoremas Lean desta entrega. Elas permitem testar
uma expressão diferencial do coeficiente, usando o operador de Euler na
funcional de momentos já existente, sem construir outra métrica ou fonte.
O operador de grau polinomial deve ser distinguido do clock material
`log(n+1)` e da profundidade vertical. O teste deve preservar a forma bilinear
completa e verificar se há uma identidade de fluxo/retorno que controle sua
constante, não apenas sua taxa.

Se não surgir essa identidade independente, o resultado honesto continua
sendo uma lei assintótica geral de uma forma ASSINADA. Receber a positividade
do próprio balanço como hipótese ou renomeá-la por um novo predicado não
resolverá a investigação.
