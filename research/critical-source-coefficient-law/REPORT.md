# Extração da fonte completada e orientação das correções críticas

**Classificação: PARTIAL.** A fonte original fornece correções de sinais
opostos em duas direções críticas certificadas. Foi formalizada uma extração
com resto analítico em qualquer ordem finita, além das contrações algébricas
dos seus coeficientes. A positividade canônica em toda ordem continua aberta.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/critical-source-coefficient-law`.
Base exata: `bc7f36f1bd29d0d09fc23778e9e074c2be82123d`, cabeça da PR #43.
A nova PR tem como base `agent/critical-source-mixed-readout`; depende das
PRs #41–#43 ainda abertas. `origin/main` foi conferida em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Não se presumiu integração dessas PRs à main; nenhuma foi modificada ou mesclada.

Fonte nativa consultada, sem alterações:
`carry-self-adjoint-operator` em
`bfeb10fd2425400fa38139903d12bf0599f02e53`.
Nenhuma worktree foi criada. Reutilizou-se o checkout limpo em uma nova branch.
Os dois arquivos de pesquisa não rastreados do operador foram preservados.

## A — O que já estava demonstrado

As seguintes provas são dependências, não resultados novos deste trabalho:

- `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`: costura
  vetorial exata dos dois canais com o mesmo mapa de coeficientes.
- `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto` e
  `nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage`: limite
  da energia assinada original e sua identidade com o storage.
- `critical_balance_tendsto_of_isUnit`: para o prefixo antigo invertível,
  `criticalBalance s n → 2 * sourceMomentSchur h s.val n`, sem sinal novo.
- `CarryCriticalMixed.storage_eq_stencil_slope`: após a síntese completa,
  o mesmo balanço é `2 Re ⟨S β, S(β ℓ)⟩`.
- `storage_one_eq_euler_boundary_add_remainder`: separação exata de Euler
  e do resto não linear no carrier Cauchy original.
- `completedNativeGreenResponseTaylorCoefficient_even_eq_zero` e
  `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical`:
  os coeficientes do readout completado são zero nas ordens pares e os
  momentos canônicos nas ordens ímpares.
- Na PR #43, a segunda direção par tem correção negativa, pivô positivo e
  balanço eventualmente entre zero e seu limite. As duas desigualdades
  `source_nonlinear_margin_pos` e `source_correction_numerator_pos` têm
  certificados theta próprios.

A ortogonalização algébrica da PR #41, as duas quadraturas, os cruzamentos,
completion, retorno e a métrica física permanecem intactos. Não se usaram
zeros, alturas, espectro desejado ou Cholesky para definir a fonte.

## B — O que foi demonstrado agora

### 1. Extração analítica reutilizável, sem hipótese de sinal

Em `SourceTaylor.lean`, definimos apenas abreviações de leitura da fonte:

\[
\ell(t)=-i\,[-F'/F](it),\qquad
c_d=\frac{\ell^{(d)}(0)}{d!}.
\]

`transverseCoefficient_eq_derivative`, `transverseCoefficient_even` e
`transverseCoefficient_odd` provam, em toda ordem,

\[
c_{2j}=0,\qquad c_{2j+1}=2(-1)^j h_j.
\]

`source_exact_remainder M` fornece um resto da **mesma** fonte, analítico na
origem, com igualdade eventual

\[
\ell(t)=\sum_{d<M}c_dt^d+t^M R_M(t).
\]

Em `GeneralExtraction.lean`, `companion_exact_taylor_sewing` transporta
essa igualdade para o **vetor companheiro original** antes do readout.
`balance_exact_taylor_sewing` então fornece, para todo tamanho finito e toda
ordem de Taylor,

\[
D_k(x)=2\operatorname{Re}\langle S_k\beta_k,P_{M,k}(x)\rangle
       +2\operatorname{Re}\langle S_k\beta_k,T_{M,k}(x)\rangle.
\]

`P` é a síntese do prefixo analítico; `T` é a síntese do resto exato
`β_r t_r^M R_M(t_r)`. Ambos usam o mesmo carrier e os mesmos coeficientes.
Um só resto funciona para todos os vetores complexos de cada família finita.
O limiar radial pode depender do tamanho e da ordem. Não há limite uniforme
na dimensão nem passagem ao operador infinito.

### 2. Contração de coeficientes em qualquer ordem

Em `StencilCoefficients.lean` e `KernelCoefficient.lean`, sejam

\[
M_p(d)=\sum_{r=0}^p(-1)^{p-r}\binom pr(r+1)^d,
\quad A_p=\frac{M_p(p+1)}{p!},\quad B_p=\frac{M_p(p+2)}{p!}.
\]

`stencilPower_below` e `stencilPower_self` provam
`M_p(d)=0` para `d<p`, e `M_p(p)=p!`. Com

\[
C_{pq}(d)=\sum_{a=0}^d(-1)^a M_p(a)M_q(d-a),
\]

`greenContraction_below`, `greenContraction_leading` e
`greenContraction_second` provam

\[
\begin{aligned}
C_{pq}(d)&=0 &&(d<p+q),\\
C_{pq}(p+q)&=(-1)^pp!q!,\\
C_{pq}(p+q+2)&=(-1)^pp!q!(B_p+B_q-A_pA_q).
\end{aligned}
\]

`source_power_coefficient_exact` identifica essa contração com a soma
completa dos cruzamentos dos pesos originais e o quociente Cauchy

\[
\frac{(r+1)^{2j+1}+(s+1)^{2j+1}}{r+s+2}.
\]

Não se definiu um kernel positivo substituto. O sinal `i²=-1` na
normalização transversal dá o peso de correção
`correctionWeight p q = A_p A_q - B_p - B_q`.

Os canários exatos são:

| ordens `(p,q)` | peso |
|---|---:|
| `(0,0)` | −1 |
| `(0,2)` | −20 |
| `(2,2)` | −14 |
| `(1,1)` | −5 |
| `(1,3)` | −42 |
| `(3,3)` | −30 |

`canonicalCorrection_even_two` e `canonicalCorrection_odd_two` identificam
as contrações com as correções físicas das duas famílias efetivamente
analisadas. A fórmula geral `canonicalCorrection` é uma expressão explícita
de coeficientes; **ainda não é um teorema de limite assintótico físico em
qualquer dimensão**. A obrigação restante está escrita na parte E.

### 3. Um novo sinal da fonte: segunda direção crítica ímpar

Em `OddReadout.lean` e `OddLimit.lean`, a família original de quatro jets
é `oddJet a = ![0,a,0,-1]`. As fases são as herdadas; em coordenadas
polinomiais ímpares ela representa `a + X`. Foram calculados todos os
cruzamentos dos quatro nós, sem remover canal algum.

Os teoremas `odd_balance_exact_remainder` e
`odd_balance_correction_tendsto` demonstram, para qualquer `a` real,

\[
\begin{aligned}
D_k(a)&=B_0(a)+\tau_k^2 B_2(a)+o(\tau_k^2),\qquad
\tau_k=(k+1)^{-1},\\
B_0(a)&=2h_1a^2+4h_2a+2h_3,\\
B_2(a)&=-10h_2a^2-168h_3a-60h_4.
\end{aligned}
\]

A identidade exata também conserva os termos de ordem quatro/seis e um
resto `τ³ * oddRemainder`, contínuo após a observação. Não se aproximaram
as duas energias enormes separadamente para depois subtrair.

Em `SourceSigns.lean`, as caixas integrais theta preexistentes certificam
pelo kernel, com aritmética inteira/racional:

\[
h_1>0,\quad h_1h_3-h_2^2>0,\quad
P_{\rm odd}:=-10h_2^3+168h_1h_2h_3-60h_1^2h_4>0.
\]

A positividade do pivô ímpar dessa ordem já era conhecida; sua prova via
caixas foi refeita aqui somente para manter a dependência mínima e separada
dos certificados posteriores de Hankel.

Em `OddCritical.lean`, a direção crítica original é identificada exatamente
com `a_*=-h_2/h_1`. Portanto

\[
\boxed{\quad
D_k=2p+\frac{A_{\rm odd}}{(k+1)^2}+o((k+1)^{-2}),\quad
p=h_3-\frac{h_2^2}{h_1}>0,\quad
A_{\rm odd}=\frac{P_{\rm odd}}{h_1^2}>0.
\quad}
\]

`odd_critical_eventually_above` prova `2p < D_k` eventualmente.
O índice é **`s=1,n=1`**, segunda direção crítica ímpar, jets 1 e 3.
Não é um pivô novo de ordem alta, nem a tarefa do sétimo pivô da PR #32.
Não se afirmou monotonicidade nem um cutoff radial efetivo.

### 4. Euler e resto não linear em toda dimensão finita

Em `AllOrderEuler.lean`, `stencil_sum` prova que todos os stencils de
ordem positiva anulam exatamente seu readout de ordem zero. Isso não anula
seus vetores físicos.

`all_order_euler_exact` demonstra, para qualquer vetor complexo original
`x` de dimensão positiva, sob a regularidade local já descarregada
eventualmente,

\[
\boxed{D_k(x)=2h_0|x_0|^2+N_k(x).}
\]

`N_k` é o pareamento com `radialCompletedRemainderSynthesis`, precisamente
o resto não linear físico preexistente. `all_order_nonlinear_tendsto` prova

\[
N_k(x)\longrightarrow
\tfrac12\,\mathrm{nativeSourceFiniteBoundaryEnergy}(x)-2h_0|x_0|^2.
\]

Na direção crítica, `critical_nonlinear_tendsto` exige apenas que o bloco
antigo seja invertível e identifica o limite com

\[
2\sigma-2h_0|x_0|^2.
\]

Isso explica a primeira desigualdade da PR #43: naquela direção par,
`x0=-h1/h0`, e a margem não linear positiva é exatamente
`2(h0*h2-2*h1²)/h0`.

No setor crítico ímpar, `critical_odd_zero_coordinate` e
`critical_odd_nonlinear_exact` provam que Euler é zero e `N_k=D_k`
exatamente no regime regular, em qualquer ordem. Portanto, postular
positividade universal desse resto ímpar **não forneceria uma nova causa
independente** para a positividade do mesmo balanço.

## C — O que foi refutado

`two_critical_corrections_opposite` combina duas orientações da fonte nativa:

- segunda direção par: correção estritamente negativa, PR #43;
- segunda direção ímpar: correção estritamente positiva, prova nova.

`no_universal_critical_approach_from_below` e
`no_universal_critical_approach_from_above` refutam, separadamente, leis
universais que coloquem todos os balanços críticos estritamente abaixo ou
estritamente acima de seus limites.

**Alcance desse NO-GO:** somente uma orientação comum das correções radiais.
Os dois pivôs envolvidos são positivos. Não foi refutada a geometria, a
positividade canônica all-order, uma lei com dependências adicionais, nem
uma possível desigualdade estrutural do balanço completo.

A correção relativa das energias, a correção absoluta de `D_k` e o resto não
linear são quantidades distintas. No novo caso, as energias crescem como
`(k+1)^7` pelos resultados anteriores; a correção de `D_k` decai como
`(k+1)^(-2)`. O sinal positivo dessa correção não substitui a prova de `p>0`.

## D — O que permanece aberto e o que foi auditado

A extração exata com resto analítico e as contrações de coeficientes foram
provadas em toda ordem finita. O controle assintótico físico de segunda
ordem foi fechado nas duas famílias concretas, não uniformemente em toda
dimensão. Faltam a costura geral da normalização singular com essas
contrações e uma propriedade independente da fonte que controle o sinal
do residual canônico em toda ordem.

`analytic_sample_remainder_tendsto` controla o resto em cada nó. Isso,
isoladamente, não controla o balanço depois da amplificação dos stencils;
a potência de crescimento deve entrar na prova geral.

Não apareceu uma propriedade independente que implique todos os sinais
Hankel. Também não há obstrução a todas as possíveis propriedades desse tipo.
A desigualdade da PR #43 continua sendo um certificado específico da fonte.
A investigação deu sua interpretação em Euler e mostrou por que o sinal
da correção não pode ser extrapolado indiscriminadamente.

Novos arquivos: nove módulos de resultados e `Audit.lean`, todos em
`research/critical-source-coefficient-law/`. São 57 teoremas, 23 definições
e uma abreviação; nenhuma alteração em módulos históricos ou bibliotecas.

A evidência reproduzível fica em `evidence/`: preflight dos repositórios,
logs de compilação e auditoria, regressões, checks JSON e hashes dos fontes.
O auditor enumera todas as declarações públicas, usa `#print axioms` e
percorre transitivamente **tipos e corpos**: 84 raízes (81 novas declarações
e três dependências explícitas), 6.223 constantes. Foram admitidos somente
`propext`, `Classical.choice` e `Quot.sound`. Além da lista de axiomas
fundacionais permitidos, rejeita dependência de certificados posteriores
explícitos de positividade finita. Esse guard é uma checagem de dependências
nomeadas, não uma prova automática de toda possível equivalência lógica.

Comandos de reprodução em `llm`:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/critical-source-coefficient-law/generate_audit.py
python3 research/critical-source-coefficient-law/validate.py
```

A validação terminou com **18 checks de código de saída zero**, mais o build
nativo separado também aprovado. O segundo comando executa os builds nativos
e focados com `lake build --wfail`,
os dez módulos de pesquisa explicitamente com `-DwarningAsError=true`,
`lake build --wfail` da raiz, auditorias Foundation/Geometry/Analysis e a
regressão H6/K6 com doze fontes. Os resultados finais constam em
`evidence/checks.json` e nos logs correspondentes. Sem `sorry`, `admit`,
`native_decide`, novos axiomas matemáticos ou mudança de pins.

## E — Próximo passo mínimo

O alvo formal seguinte é uma identidade de **taxa**, sem hipótese de sinal.
Para `s∈{0,1}` e `v:Fin N→ℝ`, usando o input original de paridade, provar

\[
(k+1)^2\left[D_k(v)-2\sum_{i,j<N}v_i h_{i+j+s}v_j\right]
\longrightarrow
2\sum_{i,j<N}v_iv_j h_{i+j+s+1}
\left[A_{2i+s}A_{2j+s}-B_{2i+s}-B_{2j+s}\right].
\]

As contrações do lado direito já foram formalizadas, assim como a expansão
vetorial exata com resto. Falta controlar o resto após as potências inversas
do passo e costurar todas as fases na passagem ao limite em dimensão
arbitrária. Não se deve receber essa igualdade como nova hipótese.
Na direção crítica, a substituição por `2sigma` usará apenas a inversibilidade
do prefixo, já disponível nas provas anteriores.

Depois dessa taxa, a pergunta de sinal continua sendo física: qual relação
da fonte limita o balanço completo ou seu resto **sem assumir o mesmo
pivô positivo**? O coeficiente de segunda ordem pode ser positivo, negativo
ou nulo; nenhuma das orientações comuns foi validada em toda ordem.

A próxima investigação deve procurar uma desigualdade independente ou um
cancelamento exato do objeto completo. Não extrapolar sinais finitos, não
normalizar a fonte para ajustar momentos e não promover `N_k>0` no setor
ímpar a explicação independente quando ali `N_k=D_k`.
