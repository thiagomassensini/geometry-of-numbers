# Cruzamentos Green depois da centralização do forcing

**PARTIAL.** A centralização original da PR #54 elimina também as duas
parcelas do primeiro componente do canal comprimido. O cruzamento que
sobrevive possui uma expressão explícita na segunda perna original. Sua
primeira derivada tem sinal positivo demonstrado a partir da fonte material.
**Isso ainda não determina o sinal do balanço completo, nem dos pivôs em toda
ordem.** O complemento oculto e as duas compensações Green são conservados.

Base imutável: `fedca533a34d9d494641e848f9f7d3284a9af38a`, PR #54.
Branch: `agent/forcing-mixed-green-slope`.
Host canônico: `ssh llm`, `/home/thlinux/geometry-of-numbers`.
A PR é empilhada sobre a #54; nenhuma PR anterior é presumida integrada à
main. Sem merge automático. Não houve mudanças no repositório do operador,
nos arquivos históricos ou em outras worktrees.

## A — O que já estava demonstrado

A PR #37, recuperada no commit
`bf2ff244e363b110a4e54ba897e475b81552bbdb`, fornece a identidade física
`physical_remainder_factor` e o coeficiente `remainderCoefficient` R.
O numerador contém central/central, compressed/compressed, os dois
cruzamentos compressed/forcing e o complemento oculto do readout.

A PR #54 constrói `centeredCoefficients`, com a fonte original
`v(t)=f(t)w`, `f=carryMaterialClockForcingScalar`,
`w=carryMaterialClockCentralForcing`, e demonstra `f(0)≠0`. Para cada
família `(c,t)`, o coeficiente adicional no centro é

\[
\widehat c_0=-\frac{\sum_i c_i f(t_i)}{f(0)}.
\]

A cauda é preservada. Já estavam provados `forcing_vector_centered`,
`forcing_kernel_centered`, `remainder_centered_bilinear` e
`physical_pullback_exact`. O forcing completo retém a segunda perna
`at v(t)`, embora seu coeficiente forcing/forcing seja anulado.

A PR #41 fornece o polinômio mônico residual exato Pₛ,ₙ e sua energia
assinada, sem presumir o sinal do pivô. Os teoremas
`exact_even_green_residual`, `exact_odd_green_residual` da #54 e
`reducedJetPair_canonical_schur_limit` da #53 continuam sendo os consumidores
corretos da identidade completa. Não são uma hipótese de Gram positiva.

Na biblioteca atual, `carryMaterialClock_complement_origin_derivative`
prova QY′(0)=−i w, e `carryMaterialCentralClock_complement_norm_lower`
prova ‖w‖²>1/32. Esses resultados materiais, anteriores à presente rodada,
são reutilizados: a orientação de primeira ordem abaixo não é anunciada
como uma nova desigualdade theta ou como uma lei dos pivôs.

## B — O que foi demonstrado agora

### 1. Os dois cruzamentos, antes de tomar a diagonal

Escrevemos `a=carryMaterialResponseScale`, Cₜ=(pₜ,qₜ) para o par
comprimido ORIGINAL já vestido, e definimos somente as observações

\[
\eta(t)=\langle w,p_t\rangle,\qquad
\gamma(t)=\langle w,q_t\rangle.
\]

M(t,u) é a SOMA dos dois cruzamentos Green depois da redução projetiva,
com dois argumentos independentes. `mixed_forcing_exact` prova

\[
M(t,u)=-a(u-t)
 [\overline{f(t)}\eta(u)+\overline{\eta(t)}f(u)]
 +a^2tu[\overline{\gamma(t)}f(u)-\overline{f(t)}\gamma(u)].
\]

`mixed_hidden_regular` conserva literalmente o Green oculto H(t,u):

\[
\frac{M-H}{u-t}=
 -a[\overline{f(t)}\eta(u)+\overline{\eta(t)}f(u)]
 +\frac{a^2tu}{u-t}
 [\overline{\gamma(t)}f(u)-\overline{f(t)}\gamma(u)]
 -\frac{H(t,u)}{u-t},\quad u\ne t.
\]

Dressing, sua derivada, clock, domínio e global return permanecem nos
pares originais que definem p,q,H. Não foi construído um novo vetor a partir
dos momentos. Os probes escalares são aplicados somente depois desses
pares físicos completos.

### 2. Uma eliminação adicional, exata e polarizada

Denotemos a primeira parcela por A(t,u) e a segunda por T(t,u).
`companion_bilinear` demonstra

\[
A[c,d]=-a\left[
 \overline{\sum_i c_i f(t_i)}\sum_jd_j\eta(u_j)
 +\overline{\sum_ic_i\eta(t_i)}\sum_jd_jf(u_j)\right].
\]

Como a centralização da #54 anula ambas as sínteses de f,
`companion_centered_bilinear` dá **A[ĉ,d̂]=0**. Também os bordos de T
no centro são zero, por seus fatores t u. Logo
`centered_mixed_coefficient` dá **(A+T)[ĉ,d̂]=T[c,d]**.

Isso retira efetivamente a dependência de η, o primeiro componente do
par comprimido, do cruzamento centralizado. Não é somente uma troca de
nome da positividade. Não exige derivar p em ordens superiores.

`mixed_regular_anchor` fornece a versão diretamente física, sem atribuir
valores confluentes a canais separados:

\[
\frac{M(t,u)}{u-t}
-\overline{\frac{f(t)}{f(0)}}\frac{M(0,u)}u
-\frac{M(t,0)}{-t}\frac{f(u)}{f(0)}=T(t,u),
\quad t,u\ne0,\quad u\ne t.
\]

As identidades de somas usam divisão total do corpo em T. Seu valor formal
em u=t **não é apresentado como prolongamento físico**. A identidade acima
é o resultado regular que independe dessa convenção.

### 3. A segunda perna fornece um quociente próprio da fonte

Na vizinhança onde f não zera, a observação

\[
\chi(t)=-\frac{\gamma(t)}{f(t)}
\]

satisfaz, por `retained_regular_ratio`,

\[
T(t,u)=a^2tu\,\overline{f(t)}f(u)
 \frac{\chi(u)-\overline{\chi(t)}}{u-t}.
\]

`value_ratio_undressed` identifica a MESMA observação sem o fator comum
D de dressing:

\[
\chi(t)=2i\frac{\langle w,QY_t\rangle}{\alpha(t)},
\qquad \alpha(t)=\texttt{carryMaterialClockCentralCoefficient}(Y_t).
\]

A identidade exige α(t)≠0; α(0)=1 já era um teorema. É o cancelamento de um
fator escalar neste readout, não uma alteração da fonte nem uma retirada do
completion dos demais canais. Em particular, H continua vestido.

A prova diferencia PRIMEIRO o vetor qₜ:
`compressed_value_origin_derivative`, depois seu pareamento com w:
`value_probe_origin_derivative`. Finalmente
`value_ratio_origin_derivative`, `forcing_slope_material_lower` e
`value_ratio_positive_near` demonstram

\[
\chi(0)=0,\qquad
\chi'(0)=2\|w\|^2>\frac1{16},\qquad
\operatorname{Re}\frac{\chi(t)}t>\|w\|^2
\quad\text{eventualmente para }t\to0,\ t\ne0.
\]

O guard de dependências do grupo `slope` também rejeita
`material_scale_pos` e os controles sintéticos: este sinal não recebe um
novo pivô positivo, certificado finito Hankel ou sinal theta como entrada.
O limite `retained_two_ray_tendsto` testa o quociente fora da diagonal:

\[
\frac{\chi(2t)-\overline{\chi(t)}}t\longrightarrow2\|w\|^2.
\]

Essa é UMA aproximação ao centro. Não é convergência conjunta arbitrária
nem positividade de todas as famílias.

## C — O que foi refutado ou impedido

### A derivada positiva não produz sozinha uma Gram

Para qualquer C>0, o controle SINTÉTICO g(t)=Ct−t³ tem g(0)=0,
g′(0)=C. Seu quociente de Loewner real é

\[
L(t,u)=C-(t^2+tu+u^2).
\]

`control_regular` e `control_response_derivative` identificam o mesmo
kernel fora da diagonal e suas diagonais derivadas. `control_quadratic`
prova, nos nós 0,s e coeficientes (−1,1),

\[
L(0,0)-L(0,s)-L(s,0)+L(s,s)=-s^2<0\quad(s\ne0).
\]

Quando 3s²<C, as duas diagonais são positivas
(`control_positive_diagonals`). O controle pode ter EXATAMENTE a mesma
primeira derivada da fonte (`control_same_native_first_jet`).

Portanto, sinal de primeira ordem, mesmo com diagonais positivas, não
basta para inferir positividade da forma polarizada. Isso refuta essa
inferência específica. **Não é um contraexemplo para a χ canônica**, nem
uma obstrução à geometria completa.

### A fase não pode ser apagada

`retained_cross_phase_split` mantém a identidade exata

\[
\chi(u)-\overline{\chi(t)}
=\chi(u)-\chi(t)+\chi(t)-\overline{\chi(t)}.
\]

`value_ratio_phase_first_order_zero` prova somente que o último termo,
dividido por t, tende a zero. Não prova χ(t) real. Para um ponto fixo t,
o numerador do quociente retido na diagonal é χ(t)−conj χ(t). Sem seu
cancelamento com os demais canais, uma extensão isolada não está garantida.
O controle racional adicional g(t)=Ct+i t² tem a mesma primeira derivada
e defeito diagonal 2i t². É um controle lógico sintético, não um resultado
sobre o sinal ou a fase da fonte canônica.

## D — O que permanece aberto e validação

`complete_mixed_hidden_factor` conserva a identidade física da #37:

\[
(M-H)+G_{\rm central}+G_{\rm compressed}=(u-t)R(t,u)
\]

na vizinhança aberta original. `diagonal_compensation` demonstra

\[
(M-H)(t,t)=-G_{\rm central}(t,t)-G_{\rm compressed}(t,t).
\]

Assim, a continuação confluente é conhecida para o numerador COMPLETO.
Não foi demonstrada divisibilidade separada de M−H, nem foi imposta
regularidade vetorial material de ordem arbitrária. Nenhum valor zero da
divisão total Lean é usado como prova de continuidade física.

O novo cancelamento simplifica os cruzamentos no conjunto regular e nas
expressões de coeficientes. **Não foi concluída sua extração confluente
separada em toda ordem**, nem uma estimativa relativa do termo oculto nas
direções Pₛ,ₙ. Para os jets completos, seguem válidos os teoremas da #54:
a forma par é Lₕ(pq)−Lₕ(p)Lₕ(q)/h₀, a ímpar é Lₕ₊₁(pq), e sua avaliação
nos polinômios exatos da #41 dá os pivôs assinados. Não há novo sinal geral.

Os quatro módulos novos contêm **33 teoremas e dez definições**, auditados
em 43 raízes por `#print axioms` e guard transitivo de tipos e corpos.
Permitem-se somente `propext`, `Classical.choice`, `Quot.sound`.
Os guards rejeitam certificados posteriores H6/K6/H7 e a positividade geral
do defeito do retorno; a regressão finita é executada separadamente.

`validate.py` executa 15 verificações: geração do inventário, cinco
compilações explícitas com warnings como erros, controles racionais, build
focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/Analysis,
regressão das doze fontes, histórico inalterado e `git diff --check`.
**As 15 verificações passaram.** Os fechamentos transitivos tiveram 5.393
constantes no grupo mixed, 5.473 no centered, 5.309 no slope e 3.841 nos
controles. Comandos e resultados ficam em `evidence/checks.json`; hashes das fontes,
refs preservadas e dependências ficam nos manifestos e preflight.

O teste Python usa `Fraction` nas duas componentes complexas e um carrier
sintético de duas coordenadas. Verifica quatro famílias retangulares com
os dois cruzamentos físicos, a projeção oculta polarizada e três controles
de primeira derivada positiva com forma indefinida. Não contém momentos,
alturas, zeros ou integral theta como entradas. Não certifica a fonte nativa.

Reprodução no ambiente canônico já preparado da #54:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/forcing-mixed-green-slope/validate.py
```

As fontes imutáveis/cache de #37, #41, #53 e #54 são dependências explícitas
do script de compilação, não módulos presumidos presentes em main.
Fonte, pesos, amplitudes, fases, métrica, domínio, retorno, correções e pins
foram preservados. Os arquivos não rastreados e todas as worktrees anteriores
foram conservados. Nenhum resultado finito foi rebatizado como all-order.

## E — Próximo passo mínimo

O primeiro componente η dos cruzamentos já pode ser eliminado pela
centralização original; não precisa ser estimado nem receber um sinal.
O próximo alvo fica no quociente retido de χ e no complemento oculto,
**com as compensações central e comprimida que garantem a confluência**.

A investigação concreta mais curta é identificar o primeiro coeficiente
NÃO real de χ, se houver, e a compensação dele no Green oculto/central/
comprimido, a partir dos pareamentos materiais originais. Isso exige provar
somente a regularidade dos probes escalares necessária à ordem testada,
não postular Dom(Lⁿ) para todos os vetores. Um teste em dois índices
independentes deve preceder qualquer tentativa de Gram de χ.

Em seguida, uma estimativa útil deve controlar esse grupo completo no
polinômio EXATO Pₛ,ₙ da #41, com erro relativo e uma margem sobrevivente ao
limite físico da #53. A margem não pode ser recebida como outro nome do
novo pivô positivo. O sinal local demonstrado aqui fornece uma calibração
da segunda perna, mas o controle sintético mostra por que não o substitui.

**Conclusão:** a obrigação da #54 foi reduzida por um cancelamento adicional
exato e por uma expressão explícita do canal retido. Não foi provada a
positividade canônica em toda ordem, nem uma nova realização Gram completa.
