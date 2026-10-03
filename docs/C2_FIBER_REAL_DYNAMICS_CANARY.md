# Dinâmica real exata de uma fibra C2

## STATUS

**PASS — C2 center fiber is an exact fixed real contraction-rotation orbit;
C2 legs are the same base step with an explicit logarithmic correction.**

CENTER_FIXED_STEP = PASS. LEG_EXACT_CORRECTION = PASS.

Este PASS é exclusivamente sobre a dinâmica pointwise da fibra.
Não fecha naturalidade de uma TFVD com peso operatorial nem o gate das
três fases da Forma Centro–Pernas.

## Checkpoints, proveniência e escopo

- geometry-of-numbers baseline:
  93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f.
- Branch de trabalho: canary-c2-fiber-real-dynamics.
- Worktree no llm: /home/thlinux/geometry-of-numbers-phase-canary.
- Única fonte histórica lida nesta rodada:
  CarrySelfAdjointOperator/C2FiberDepthLogTransport.lean,
  carry-self-adjoint-operator em
  cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa.
  SHA256 do arquivo:
  50f62cae94d5570d48e984a38b022c3a205ac5579c8dc7b354b844ef2ecb7439.
- Sem import histórico, sem reconstrução da fonte diagonal, sem mudanças
  em R2/Foundation/Geometry, sem commit/merge/push.

O manifesto SOURCE_MANIFEST.json registra SHA256 da fonte, dos módulos locais
consultados e da implementação. PRESERVATION_BEFORE.json e
PRESERVATION_AFTER.json registram a preservação dos canários anteriores
e dos hunks paralelos do main.

## FIBER

~~~lean
c2FiberPoint (m : ℕ) (epsilon : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * m + epsilon
~~~

| Coordenada | Papel |
| --- | --- |
| m | Core fixo; positivo no domínio físico |
| k | Profundidade vertical variável da fibra crescente |
| epsilon | Offset material: 0 no centro, -1 e +1 nas pernas |
| x_k | Ponto material determinado por m, k e epsilon |

Não há sample arbitrário. O ponto central real corresponde ao natural
2^k m via c2FiberPoint_center_eq_nat.
c2FiberCenter_hasCarryDepthAtLeast prova a proveniência residual de k.
c2FiberCenter_not_hasCarryDepthAtLeast_succ prova que, quando Odd m,
essa é a profundidade intrínseca exata do centro.

Sem oddness, a mesma dinâmica algébrica continua válida, mas k é somente
um nível suportado, podendo haver profundidade adicional no fator m.
Não se afirma que um m arbitrário já seja o core máximo canônico.
Para a leitura C2 de centros divisíveis por 4 e pernas ímpares positivas
do domínio usual, usar core ímpar positivo e k≥2.

Positividade física:

- c2FiberPoint_center_pos para m>0 e todo k;
- c2FiberPoint_right_pos para m>0 e todo k;
- c2FiberPoint_left_pos para m>0 e k≥1, portanto também no regime C2 k≥2.

## CENTER LOG

Theorems:

- c2FiberPoint_centered;
- c2FiberPoint_centered_log;
- c2FiberPoint_centered_log_increment.

Para m>0:

$$
x_k-\epsilon=2^k m,\qquad
\log(x_k-\epsilon)=k\log 2+\log m,
$$

$$
\log(x_{k+1}-\epsilon)-\log(x_k-\epsilon)=\log 2.
$$

O incremento é derivado da coordenada multiplicativa da fibra. Não foi
atribuído por definição à fase.

## LEG LOG DEFECT

Definição independente do estado angular:

$$
d_k=\operatorname{c2FiberLogDefect}(m,\epsilon,k)
    =\log\left(1+\frac{\epsilon}{2^k m}\right).
$$

Para m>0 e x_k>0, c2FiberPoint_log_center_defect e
c2FiberPoint_log_eq_depth_core_defect provam:

$$
\log x_k-\log(x_k-\epsilon)=d_k,\qquad
\log x_k=k\log 2+\log m+d_k.
$$

Para x_k,x_{k+1}>0, c2FiberPoint_log_increment_defect prova:

$$
\log x_{k+1}-\log x_k=\log 2+d_{k+1}-d_k.
$$

O porte usa positividade física, fortalecendo a condição histórica
de não anulamento. As identidades são derivadas localmente com
Real.log_mul/log_pow/log_div e álgebra de corpos.

c2FiberLogDefect_center prova d_k=0 SOMENTE para epsilon=0.
c2FiberLogDefect_right_pos prova defect estritamente positivo na perna
direita. c2FiberPoint_right_log_increment_lt certifica exatamente:

$$
\log 9-\log 5<\log 2.
$$

Portanto a correção das pernas não foi descartada nem aproximada.
Não se afirma que a rotação corretiva seja diferente da identidade para
todo t: t=0 e periodicidade angular permanecem possíveis.

## REAL STATE

~~~lean
c2FiberRealState (m : ℕ) (epsilon t : ℝ) (k : ℕ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k) :=
  realCriticalDepthState 2 k (by decide)
    (-t * Real.log (c2FiberPoint m epsilon k))
~~~

As provas hm/hx registram o domínio; não selecionam a fase.
A amplitude é o objeto crítico local anterior, determinado somente por k.
A fase é o logaritmo do ponto material, determinado pela fibra.

c2FiberRealState_energy reutiliza diretamente
realCriticalDepthState_energy:

$$
E(X_k)=\operatorname{realDepthMass}(2,k).
$$

Não há cálculo novo de energia nem seleção retroativa de metade.

## CENTER FIXED STEP

Com eta = criticalVerticalAmplitudeRatio 2 (by decide):

$$
F_t(v)=\operatorname{scaleRealPlane}(\eta)
       \bigl(R_{-t\log 2}v\bigr).
$$

c2CenterFiberStep é essa definição.
Sua contração vem dos resultados locais
criticalVerticalAmplitudeRatio_pos e
criticalVerticalAmplitudeRatio_lt_one: 0<eta<1.

**c2CenterFiberRealState_succ_eq_fixedStep**:

$$
X_{k+1}=F_t(X_k)\quad(\epsilon=0).
$$

**c2CenterFiberRealState_eq_iterate_step**:

$$
X_k=F_t^{[k]}(X_0).
$$

A prova do passo usa o incremento logarítmico já derivado,
realCriticalAmplitude_succ_verticalRatio e rotateRealPlane_add.
A iteração é uma indução sobre o passo provado, não a definição do estado.

## CORE/DEPTH PHASE FACTORIZATION

**c2CenterFiber_phase_factorization**:

$$
R_{-t\log(2^k m)}v
 =R_{-t\,k\log 2}\bigl(R_{-t\log m}v\bigr).
$$

O core fornece um offset angular fixo; cada nível acrescenta
-t log 2. Prova: decomposição do log, ring e rotateRealPlane_add.

## LEG STEP

**c2LegFiberRealState_succ_eq_correctedStep**, para offsets com ambos os
pontos materiais positivos, em particular as duas pernas admissíveis:

$$
X_{k+1}
 =\eta R_{-t(\log 2+d_{k+1}-d_k)}X_k.
$$

**c2LegFiberRealState_succ_eq_fixedStep_add_logDefect**:

$$
X_{k+1}=R_{-t(d_{k+1}-d_k)}\bigl(F_t(X_k)\bigr).
$$

add_logDefect significa composição de rotações, não soma de vetores.
São resultados mais gerais que epsilon=±1; a especialização física mantém
os mesmos defects. Nenhuma hipótese de passo fixo puro foi imposta às pernas.

## TFVD NATURALITY

**CANDIDATE / OPEN — não implementada uma TFVD operator-valued.**

A API atual usa um escalar eta:

$$
(B_\eta x)_{k+1}
 =\eta^{-1}x_{k+2}-2x_{k+1}+\eta x_k,
\quad
Tr_\eta x=(x_0,\eta^{-1}x_1-x_0),
$$

$$
R_\eta(a,b)_k=\eta^k(a+kb),
\quad K_\eta(r)=r\eta^r.
$$

As definições estão em RealCarryWeightedValve/RealCarryL2; análise/síntese
e seu roundtrip estão em RealCarryTfvd. R2 permanece correto para essas
definições. O lift a duas coordenadas reais já existe no canário material.
Isso fornece reconstrução componente a componente para entradas ℓ², mas
não certifica naturalidade sob rotações cujo ângulo depende de k.
O estado desta rodada é pointwise; não foi empacotado num Hilbert novo.

Aqui a rotação de profundidade é Q_omega x(k)=R_{k omega}x(k), com
omega=-t log 2. Ela varia com k, portanto não cai na hipótese de rotação
constante dentro de cada fibra do canário material anterior.
Shifts mudam o ângulo; linearidade real sozinha não permite fatorá-lo.

Um próximo-alvo legítimo é conjugação pela rotação de profundidade ou uma
TFVD com C=eta R_omega e seu inverso, no mesmo carrier de duas quadraturas:

$$
(B_Cx)_{k+1}=C^{-1}x_{k+2}-2x_{k+1}+Cx_k,\qquad
Tr_Cx=(x_0,C^{-1}x_1-x_0).
$$

Também seria necessário transportar return/Green e bordo, provar os
domínios e a identidade correspondente. Esses são alvos documentais;
nenhum desses operadores foi definido, nenhum intertwining foi provado
e não se conclui FAIL da TFVD atual.

## THREE-PHASE CENTER-LEG GATE

**THREE_PHASE_CENTER_LEG_GATE = OPEN.**

Para um centro c=2^k m e as pernas positivas:

$$
\theta_-=-t\log(c-1),\quad
\theta_0=-t\log c,\quad
\theta_+=-t\log(c+1),
$$

$$
\theta_\pm-\theta_0=-t\,d_k^\pm.
$$

Essa última relação é consequência algébrica das identidades de log
formalizadas; não foi adicionada como theorem angular separado.
centerLegForm usa um ângulo comum nas posições construídas.
Não existe nesta rodada uma ponte que substitua as três fases físicas
por esse ângulo comum; seus resultados de zero não foram aplicados à fibra.

## AXIOMS e exemplos

Todos os 27 nomes públicos (4 definições, 23 teoremas) recebem
#assert_analysis_axioms e #print axioms no Audit.
c2FiberCenter_hasCarryDepthAtLeast imprime somente propext.
Os outros 26 nomes imprimem propext, Classical.choice, Quot.sound.
Nenhum axioma adicional, sorry, admit ou unsafe.
As duas pequenas lemmas privadas são cobertas transitivamente pelos capstones.

Exemplos formais no Audit verificam:

- core 1, depth 2: pernas 3/5 e centro 4;
- defects exatos log(3/4) e log(5/4);
- contração energética do passo e 0<eta<1;
- semente central de core 1 em depth 0;
- suporte residual de depth 2 e ausência de suporte em depth 3.

VALIDATION.json contém os builds e os audits executados no llm.
AXIOMS.json contém os footprints de todos os nomes públicos.

| Verificação | Resultado | Segundos |
| --- | --- | --- |
| lake build GeometryOfNumbers.Analysis.C2FiberRealDynamics | PASS | 3.480 |
| lake build GeometryOfNumbers.Analysis | PASS | 3.520 |
| lake build GeometryOfNumbers.Analysis.Audit | PASS | 3.527 |
| audit-foundation.sh | PASS | 9.301 |
| audit-geometry.sh | PASS | 12.628 |
| audit-analysis.sh | PASS | 20.378 |
| git diff --check | PASS | 0.316 |
| busca de placeholders/trust escapes | PASS | 0.311 |
| diff de Foundation/Geometry e núcleo R2 vertical | sem alterações | 0.305 |

Os builds incluem os capstones e os 11 exemplos formais do Audit.
Uma checagem adicional cobre todos os módulos Real*.lean existentes;
nenhum módulo R2 foi alterado. O manifesto de preservação compara hashes
de 10 arquivos anteriores, removendo somente os acréscimos desta rodada
nos três arquivos compartilhados. Todos coincidem com o checkpoint anterior.
O patch paralelo do main (.gitignore/HUMAN_THEORY) também mantém seu hash.

## FILES

Novos nesta rodada:

- GeometryOfNumbers/Analysis/C2FiberRealDynamics.lean;
- docs/C2_FIBER_REAL_DYNAMICS_CANARY.md.

Modificados somente por acréscimos desta rodada:

- GeometryOfNumbers/Analysis.lean — import;
- GeometryOfNumbers/Analysis/Audit.lean — guards, prints e exemplos;
- docs/SOURCE_PROVENANCE.md — fonte histórica e crosswalk local.

Artefatos locais:
/home/thlinux/Downloads/FORMALIZANDO/c2_fiber_real_dynamics_work.
Artefatos no llm:
/home/thlinux/c2-fiber-real-dynamics-artifacts.
R2 e canários anteriores preservados, sem commit/merge/push.

## SEMANTIC CONCLUSION

**Sim.** No domínio positivo de uma fibra C2, o centro sobe por repetição
exata do mesmo passo real de contração crítica e rotação. As pernas seguem
esse passo composto com a correção angular exata determinada pelo
incremento de seu defect logarítmico.

A origem de amplitude, depth e clock está separada e explícita.
Naturalidade da TFVD rotacional e leitura centro–pernas de três fases
permanecem gates downstream abertos.
