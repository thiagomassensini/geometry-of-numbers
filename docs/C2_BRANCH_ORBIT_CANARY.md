# Órbita real deformada e massa quadrática do ramo C2

## STATUS

**PASS — the historical C2 branch mass is exactly the quadratic energy sum
of the real deformed contraction-rotation orbit; unit mass occurs exactly
at sigma = 1/2.**

O critério de massa unitária e as barreiras são enunciados sob sigma>0.
A família em sigma é uma **deformação/comparison family downstream**.
Não redefine a amplitude crítica nem fornece uma nova origem fundacional
da metade. A especialização crítica é identificada com o passo preexistente.

## Checkpoints e fontes

- geometry-of-numbers baseline:
  93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f.
- Branch de trabalho: canary-c2-branch-orbit.
- Worktree llm: /home/thlinux/geometry-of-numbers-phase-canary.
- formalizacao_C2:
  dc35555879e3c0f188508c729c4a0ea31be246fb.
- Fontes históricas lidas: LeanC2/Operators/BranchBarrier.lean e,
  depois do fechamento da massa, LeanC2/Operators/Tilt.lean.
- Esses dois arquivos estão sem alterações no checkout histórico.
  Outras alterações desse checkout foram preservadas; não se executou
  build histórico nem se importou sua dependência fundacional.

SHA256 de BranchBarrier:
eb1d769fb96b36591771fc0b89962a8ff37d07f950d7b1199a121e9b48445372.
SHA256 de Tilt:
7ce7e98951150abad471047cca5a74391d82c60a70ddbf33fc3126b6a037b1ed.

Hashes, cópias históricas e módulos locais consultados:
SOURCE_MANIFEST.json. Nenhuma mudança em R2/Foundation/Geometry ou nos
canários anteriores. Sem commit, merge ou push.

## Auditoria literal do BranchBarrier

As declarações históricas confirmadas são:

~~~lean
branchWeightSigma (sigma : ℝ) := (2 : ℝ)^(-2 * sigma)
branchNormSqSigma (sigma : ℝ) :=
  2 * ∑' j : ℕ, branchWeightSigma sigma ^ (j + 2)
~~~

Também foram conferidos os enunciados e provas presentes de:

- branchWeightSigma_half;
- branchNormSq_closed_form;
- branchNormSq_half;
- branchNormSq_lt_one_of_half_lt;
- branchNormSq_gt_one_of_pos_of_lt_half;
- branchNormSq_barrier_eq_one;
- branchNormSq_barrier.

O canário não copia wrappers complexos nem o módulo inteiro. A cópia local
legacy é apenas a expressão real mínima. Os critérios são reconstruídos
por rpow, série geométrica e álgebra escalar no projeto novo.

## DEFORMED STEP

Definições:

$$
a(\sigma)=2^{-\sigma},\qquad
q_{\rm branch}(\sigma)=a(\sigma)^2.
$$

c2RadialAmplitudeRatio, c2RadialEnergyRatio e
c2RadialEnergyRatio_eq_rpow provam:

$$
q_{\rm branch}(\sigma)=2^{-2\sigma}.
$$

Não é o parâmetro de deformação recíproca da Forma Centro–Pernas.
É a razão de energia da família comparativa radial.

c2DeformedFiberStep mantém t no vetor:

$$
F_{\sigma,t}(v)=
\operatorname{scaleRealPlane}(a(\sigma))
\bigl(R_{-t\log 2}v\bigr).
$$

c2DeformedFiberStep_energy:

$$
E(F_{\sigma,t}v)=q_{\rm branch}(\sigma)E(v).
$$

A prova usa scaleRealPlane_energy e rotateRealPlane_energy.
c2DeformedFiberStep_energy_independent_time deriva igualdade para
quaisquer t1,t2. A independência de tempo é um resultado, não uma omissão
do parâmetro na definição.

## CRITICAL SPECIALIZATION

**F_(1/2,t) = existing center step? YES.**

c2RadialAmplitudeRatio_half:

$$
a(1/2)=2^{-1/2}.
$$

c2DeformedFiberStep_half_eq_c2CenterFiberStep prova igualdade de funções:

$$
F_{1/2,t}=\operatorname{c2CenterFiberStep}(t).
$$

A ponte usa criticalVerticalAmplitudeRatio_eq_rpow já local. Não se usa
massa unitária para definir essa razão ou selecionar a amplitude crítica.

## ITERATED ENERGY

c2DeformedFiberStep_iterate_energy, por indução sobre Function.iterate:

$$
E(F_{\sigma,t}^{[k]}v)=q_{\rm branch}(\sigma)^k E(v).
$$

A direção unitária é realCriticalDepthSeed 2 0, preexistente e igual
a (1,0). Nenhum seed foi normalizado nesta rodada.
c2DeformedUnitOrbit_energy:

$$
E(F_{\sigma,t}^{[k]}e_1)=q_{\rm branch}(\sigma)^k.
$$

## BRANCH INDEXING

First depth: **k=2**. Branch multiplicity: **2**.

A indexação é a regra de admissão recuperada do histórico:
centros C2 divisíveis por quatro, lidos desde o primeiro depth genuíno.
Ela é realizada nas coordenadas novas pela identidade certificada:

~~~lean
c2BranchDepth_ge_two_iff_center_four_dvd (m k : ℕ) (hm : Odd m) :
  4 ∣ 2^k * m ↔ 2 ≤ k
~~~

Assim j+2 percorre exatamente os níveis dessa restrição de admissão.
Isso não afirma que a família algébrica de fibras deixe de existir abaixo
de depth 2 ou que toda escolha possível de domínio seja forçada por essa
prova; a regra histórica foi preservada e seu domínio foi representado
geometricamente.

c2BranchDirections_distinct e c2BranchDirections_card provam que os dois
pontos de offset -1 e +1 são distintos e têm cardinalidade dois.
No regime m positivo/ímpar e k≥2, a positividade das duas pernas vem dos
teoremas do canário C2FiberRealDynamics.

O fator 2 conta as duas direções radiais; não é energia da soma dos vetores,
nem uma identificação dos seus ângulos físicos.

## ORBIT MASS

A definição mantém a órbita com t:

~~~lean
c2BranchOrbitMass sigma t :=
  2 * ∑' j : ℕ,
    realPlaneEnergy
      ((c2DeformedFiberStep sigma t)^[j+2]
        (realCriticalDepthSeed 2 0 (by decide)))
~~~

c2BranchOrbitMass_eq_geometric_series:

$$
M(\sigma,t)=2\sum_{j\ge0}q_{\rm branch}(\sigma)^{j+2}.
$$

c2BranchOrbitMass_independent_time é derivado desse theorem, que por sua
vez usa a energia da órbita real e a invariância angular.

Para sigma>0, c2RadialEnergyRatio_pos/lt_one e
c2BranchUnitOrbitEnergy_summable certificam convergência.
c2BranchOrbitMass_closed_form:

$$
M(\sigma,t)=\frac{2q_{\rm branch}(\sigma)^2}
                 {1-q_{\rm branch}(\sigma)}.
$$

As definições de tsum e o crosswalk algébrico são totais em Lean. A leitura
como massa acumulada convergente e sua classificação nesta rodada usam
explicitamente sigma>0; não se interpreta o tsum fora desse domínio como
uma soma divergente de valor finito.

## LEGACY CROSSWALK

legacyC2BranchWeight e legacyC2BranchNormSq reproduzem literalmente as
duas definições reais históricas auditadas.
c2RadialEnergyRatio_eq_legacyBranchWeight prova a igualdade dos pesos.

**Exact equality: YES.**

**c2BranchOrbitMass_eq_legacyBranchNormSq**:

$$
M(\sigma,t)=\operatorname{legacyC2BranchNormSq}(\sigma).
$$

O kernel verifica a igualdade com a expressão legacy local.
Sua identidade com a expressão do outro repositório é a auditoria literal
dos conteúdos registrados no manifesto, sem import de código histórico.
Nenhum cálculo numérico ou ajuste de constante foi usado.

## UNIT MASS

c2BranchOrbitMass_half:

$$
M(1/2,t)=1.
$$

Para sigma>0:

| Theorem | Critério |
| --- | --- |
| c2BranchOrbitMass_eq_one_iff | M=1 iff sigma=1/2 |
| c2BranchOrbitMass_lt_one_iff | M<1 iff sigma>1/2 |
| c2BranchOrbitMass_gt_one_iff | M>1 iff sigma<1/2 |

Os nomes contrai/satura/expande referem-se à MASSA DE RAMO comparada com 1.
Para todo sigma>0, o próprio passo F tem q<1 e continua sendo uma contração
energética, inclusive quando a soma de massa de ramo é maior que 1.

Esse é um critério da família comparativa radial. Não modifica a
genealogia fundacional da metade.

## Pernas físicas e identidade operatorial

**branch orbit mass forgets angular leg defects by quadratic invariance;
it does not assert that the left/right vector states have equal phases.**

O canário anterior preserva os defects logarítmicos das pernas. A massa
desta rodada é uma leitura quadrática radial pura; não transporta uma
configuração física de três fases para centerLegForm de ângulo comum.
O gate de três fases permanece aberto.

Não foi construída API de adjoint nem uma identidade F*F. A energia
explícita x²+y² é suficiente para todos os resultados desta rodada.

## TILT AUDIT

**TILT_ZERO_LOCUS_ONLY_MATCHES_BRANCH_DEFECT.**

O arquivo histórico define:

$$
\operatorname{tilt}(\delta,x)=x^{-\delta},
$$

$$
\operatorname{tiltBracket}(\delta,c)
 =(c-1)^{-\delta}+(c+1)^{-\delta}-2c^{-\delta}.
$$

É curvatura local, dependente de c; a função tilt em si vale 1 em delta=0.
O observable de zero comparável à massa menos 1 é o BRACKET do tilt.
bracket_tilt_zero_iff_delta_zero prova seu locus para delta>-1,c>1.
normalizedTiltCurvature_zero_iff_delta_zero preserva esse locus.

Com delta=sigma-1/2 e sigma>0, ambos têm zero exatamente em sigma=1/2,
assim como M-1. Essa comparação é uma auditoria documental dos teoremas
históricos e do novo critério; Tilt não foi portado nesta rodada.
tiltBracket_ne_zero_of_sigma_pos_of_ne_half já registra diretamente no
histórico a leitura delta=sigma-1/2 sob sigma>0,c>1.

Não são literalmente M-1: para sigma>1/2 o bracket é positivo
(tiltBracket_pos_of_pos), enquanto M-1 é negativo. Para 0<sigma<1/2,
o bracket é negativo (tiltBracket_neg_of_neg_one_lt) e M-1 é positivo.
Há ainda o zero histórico delta=-1, fora do domínio sigma>0 usado aqui.

## AXIOMS, validação e exemplos

Todos os 29 nomes públicos (6 definições e 23 teoremas) entram no Audit
com #assert_analysis_axioms e #print axioms.
c2BranchDepth_ge_two_iff_center_four_dvd imprime propext, Quot.sound.
Os outros nomes públicos imprimem propext, Classical.choice, Quot.sound.
As quatro lemmas privadas são verificadas transitivamente pelos capstones.
Nenhum axioma extra, sorry, admit ou unsafe.

Os 10 exemplos formais verificam cardinalidade, primeiro depth, exclusão
do depth 1 no core 1, q crítico, igualdade dos passos, massa crítica,
M(1,t)=1/6, massa maior que 1 em sigma=1/4, crosswalk e somabilidade.
Todos são provas formais, sem avaliação numérica como substituto.

VALIDATION.json/logs contêm comandos, tempos e resultados dos builds/audits.
AXIOMS.json lista os footprints de todos os nomes públicos.
PRESERVATION_AFTER.json verifica os arquivos anteriores e o patch paralelo
do main, removendo somente os acréscimos desta rodada dos arquivos comuns.

| Verificação no llm | Resultado | Segundos |
| --- | --- | --- |
| lake build GeometryOfNumbers.Analysis.C2BranchOrbitCanary | PASS | 3.413 |
| lake build GeometryOfNumbers.Analysis | PASS | 3.534 |
| lake build GeometryOfNumbers.Analysis.Audit | PASS | 3.456 |
| audit-foundation.sh | PASS | 9.224 |
| audit-geometry.sh | PASS | 12.921 |
| audit-analysis.sh | PASS | 21.119 |
| git diff --check | PASS | 0.299 |
| busca de placeholders/trust escapes | PASS | 0.314 |
| diff de Foundation/Geometry e núcleo R2 vertical | sem alterações | 0.299 |

Uma checagem adicional cobre todos os módulos Real*.lean existentes.
Os hashes de 12 arquivos anteriores coincidem com o checkpoint preservado
após remover somente os acréscimos autorizados nos três arquivos comuns.
Os arquivos dos canários anteriores não foram editados.

## FILES

Novos:

- GeometryOfNumbers/Analysis/C2BranchOrbitCanary.lean;
- docs/C2_BRANCH_ORBIT_CANARY.md.

Modificados:

- GeometryOfNumbers/Analysis.lean — import;
- GeometryOfNumbers/Analysis/Audit.lean — guards, prints e exemplos;
- docs/SOURCE_PROVENANCE.md — genealogia e limites deste crosswalk.

Artefatos:
/home/thlinux/Downloads/FORMALIZANDO/c2_branch_orbit_work e
/home/thlinux/c2-branch-orbit-artifacts no llm.
Todos os canários anteriores e R2 preservados; sem commit/merge/push.

## SEMANTIC CONCLUSION

**Sim.** A expressão real histórica da massa de ramo C2 é exatamente
a soma das energias quadráticas da órbita real deformada. O parâmetro t
está presente nos vetores e desaparece por invariância angular da energia.
A massa unitária classifica sigma=1/2 no domínio positivo da família
comparativa; não altera a origem anterior da amplitude crítica.
