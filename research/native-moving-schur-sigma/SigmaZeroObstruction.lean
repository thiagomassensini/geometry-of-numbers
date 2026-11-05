import SigmaNeighborhood
import SigmaQuadratic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.LinearAlgebra.Matrix.PosDef
import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation
import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolventAnalytic
import CPFormal.Analytic.CpGenuineRealAxisPositivity
import MomentLogConvexity

/-!
# Obstrução off-critical: auditoria, correção e isolamento da obrigação analítica

Este módulo audita e corrige a versão anterior (que continha três erros reais) e deixa
registrado, com rigor, **o que está provado**, **o que é condicional**, **o que permanece
em aberto** e **o que foi refutado**. Preserva-se a fonte original e sua genealogia:
bracket geométrico → Genuine → escalar nativo → fator arquimediano → característica
completada `F = completedNativeOperatorCharacteristic` → log-derivada → momentos → Hankel.
Objetos preservados: `completedSigmaResponse`, `completedSigmaDensity`, `completedSigmaLogJet`,
`sigmaMatrix`, `sigmaMomentForm`, `sigma_log_jet_center_eq_canonical`.

Não se assume RH, positividade central all-order, dominância de tilt, contractividade de
Green, certificado HP, nem qualquer hipótese equivalente à negatividade pretendida.

## Correções da auditoria

* **Problema A (coordenada do zero).** A antiga `SigmaPositiveRealZero` usava
  `F (displacedHeight x 0) = 0`, que é altura **zero** e deslocamento horizontal `x` — não
  um zero de altura real positiva. Corrigido por `PositiveHeightZero` (`F (γ) = 0`, `γ>0`,
  altura real positiva no eixo). Mantido como **hipótese**: a existência não é aqui provada.

* **Problema B (falso polo da soma finita).** A soma geométrica **finita** é um polinômio e
  **não** tem polo. Separado rigorosamente: `finite_partial_sum_eq` (polinômio, sem polo);
  `infinite_geometric_series` (série convergente para `‖ζz‖<1`); e
  `cauchy_kernel_denominator_zero_nonreal` (o **denominador** do núcleo de Cauchy — a forma
  fechada / continuação meromorfa — anula-se no ponto **não-real** `ζ⁻¹`).

* **Problema C (ponte `hbridge` circular — REFUTADA).** A antiga `SigmaNonRealNode` exigia
  que uma janela de três momentos coincidisse **exatamente** com os de um único par
  conjugado não-real de peso positivo, o que já **força** o determinante Hankel `2×2`
  negativo. Isso é assumir o sinal. Removida. O lema algébrico `pair_negative_direction`
  é **preservado apenas como modelo auxiliar de dois nós**, sem aplicação à fonte original.

## Rota analítica (fatos PROVADOS sobre a fonte original)

* `displacedProductC_ofReal_eq_density`: para deslocamento admissível, o produto deslocado
  `D_d(t) = F(t−id)·F(t+id)` coincide, no eixo real, com a densidade completada
  `completedSigmaDensity d t` (via `sigma_response_conjugate`).
* `displacedProductC_vanishes_at_shifted_zero`: um zero `F(γ)=0` anula `D_d` em `t=γ+id`.
* `shifted_zero_u_im`: após `u=t²`, o nó deslocado tem `Im((γ+id)²)=2γd ≠ 0` (não-real).

## O que falta (ABERTO) e o teorema condicional honesto

O fechamento incondicional depende de **duas obrigações analíticas independentes**, nenhuma
delas hipótese de sinal:
1. que o zero deslocado produza um **polo não-removível** da função geradora dos jets
   (identidade geradora + continuação meromorfa);
2. a **obstrução de Hamburger**: se toda Hankel deslocada é PSD, os jets são momentos de uma
   medida positiva (de suporte compacto, pelo raio de convergência positivo), cuja
   transformada de Cauchy é analítica fora do eixo real — logo sem polo não-real.

`offcritical_not_posSemidef_of_zero` demonstra que, **dadas** essas duas obrigações, o zero
força a falha de PSD em ordem finita. O teorema usa apenas o fato PROVADO da não-realidade
`Im((γ+id)²)=2γd≠0`; as duas obrigações entram como predicados abstratos explícitos.
-/

namespace CarrySigmaObstruction
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryMomentLogConvex
  CPFormal.Analytic.Cp
open CarrySelfAdjointOperator.CompletedNativeRealHPCarrierCertificate
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Parte 1 — função geradora: soma finita (polinômio) vs série infinita (com polo) -/

/-- **Soma parcial FINITA** — é um polinômio em `z`; **não possui polo** algum. (Correção
do Problema B: a identidade de soma geométrica finita não exibe polo.) -/
theorem finite_partial_sum_eq (ζ z : ℂ) (L : ℕ) (hz : ζ * z ≠ 1) :
    ∑ n ∈ Finset.range L, (ζ * z) ^ n = ((ζ * z) ^ L - 1) / (ζ * z - 1) :=
  geom_sum_eq hz L

/-- **Série infinita convergente** para `‖ζz‖<1`, com forma fechada o núcleo de Cauchy
`(1−ζz)⁻¹`. É esta — não a soma finita — que tem continuação meromorfa com polo. -/
theorem infinite_geometric_series (ζ z : ℂ) (h : ‖ζ * z‖ < 1) :
    HasSum (fun n : ℕ => (ζ * z) ^ n) (1 - ζ * z)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h

/-- **O polo não-real (correto).** O denominador do núcleo de Cauchy `(1−ζz)⁻¹` — a forma
fechada / continuação meromorfa da série — anula-se em `z=ζ⁻¹`, que é **não-real** quando o
nó `ζ` é não-real. -/
theorem cauchy_kernel_denominator_zero_nonreal (ζ : ℂ) (hζ : ζ ≠ 0) (hIm : ζ.im ≠ 0) :
    1 - ζ * ζ⁻¹ = 0 ∧ (ζ⁻¹).im ≠ 0 := by
  refine ⟨by rw [mul_inv_cancel₀ hζ]; ring, ?_⟩
  rw [Complex.inv_im]
  exact div_ne_zero (neg_ne_zero.mpr hIm) (Complex.normSq_pos.mpr hζ).ne'

/-! ## Parte 2 — modelo auxiliar de dois nós (NÃO aplicado à fonte original) -/

/-- Momentos reais de um nó complexo com peso real. Modelo auxiliar. -/
def nodeMoment (w : ℝ) (ζ : ℂ) (n : ℕ) : ℝ := w * (ζ ^ n).re

/-- Momentos reais de um par conjugado de nós. Modelo auxiliar. -/
def pairMoment (w : ℝ) (ζ : ℂ) (n : ℕ) : ℝ := 2 * w * (ζ ^ n).re

/-- O par conjugado é a soma de dois nós conjugados. -/
theorem pairMoment_eq (w : ℝ) (ζ : ℂ) (n : ℕ) :
    pairMoment w ζ n = nodeMoment w ζ n + nodeMoment w (starRingEnd ℂ ζ) n := by
  unfold pairMoment nodeMoment
  have hc : ((starRingEnd ℂ) ζ ^ n).re = (ζ ^ n).re := by
    rw [← map_pow, Complex.conj_re]
  rw [hc]; ring

/-- **Modelo auxiliar de dois nós (NÃO é um teorema sobre a fonte original).** A sequência
de momentos de um par conjugado não-real com peso positivo tem uma Hankel `2×2` de
determinante negativo: `m₀(m₀m₂−m₁²) = −8 w³ (Im ζ)² < 0`. Isto ilustra o mecanismo, mas
**não** afirma que os jets de `completedSigmaLogJet` sejam dessa forma. -/
theorem pair_negative_direction (w : ℝ) (ζ : ℂ) (hw : 0 < w) (hIm : ζ.im ≠ 0) :
    pairMoment w ζ 0 *
        (pairMoment w ζ 0 * pairMoment w ζ 2 - pairMoment w ζ 1 * pairMoment w ζ 1) < 0 := by
  have h0 : pairMoment w ζ 0 = 2 * w := by
    unfold pairMoment; rw [pow_zero, Complex.one_re]; ring
  have h1 : pairMoment w ζ 1 = 2 * w * ζ.re := by
    unfold pairMoment; rw [pow_one]
  have h2 : pairMoment w ζ 2 = 2 * w * (ζ.re * ζ.re - ζ.im * ζ.im) := by
    unfold pairMoment; rw [pow_two, Complex.mul_re]
  rw [h0, h1, h2]
  nlinarith [mul_pos (mul_pos (mul_pos hw hw) hw) (mul_self_pos.mpr hIm)]

/-! ## Parte 3 — fatos PROVADOS sobre a fonte original deslocada -/

/-- A forma de momentos sigma é a forma quadrática da Hankel deslocada `sigmaMatrix`. -/
theorem sigmaMomentForm_eq_quadratic (d : ℝ) (s N : ℕ) (v : Fin N → ℝ) :
    sigmaMomentForm d s N v = v ⬝ᵥ (sigmaMatrix d s N *ᵥ v) := by
  unfold sigmaMomentForm sigmaMatrix sourceMomentMatrix
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Zero de altura real positiva** da característica completada: `F(γ)=0` com `γ>0`. É a
coordenada correta (altura real positiva no eixo), distinta do antigo zero pontual em
altura nula. Mantida como hipótese; a existência não é aqui afirmada. -/
def PositiveHeightZero : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ completedNativeOperatorCharacteristic (γ : ℂ) = 0

/-- Produto completo deslocado `D_d(τ) = F(τ−id)·F(τ+id)`, em argumento complexo. -/
def displacedProductC (d : ℝ) (τ : ℂ) : ℂ :=
  completedNativeOperatorCharacteristic (τ - Complex.I * (d : ℂ)) *
    completedNativeOperatorCharacteristic (τ + Complex.I * (d : ℂ))

/-- **Identidade no eixo real.** Para deslocamento admissível, `D_d(t)` coincide com a
densidade completada `completedSigmaDensity d t` (via a simetria de conjugação
`sigma_response_conjugate`). -/
theorem displacedProductC_ofReal_eq_density (d t : ℝ)
    (hd₁ : -(1/2 : ℝ) < d) (hd₂ : d < (1/2 : ℝ)) :
    displacedProductC d (t : ℂ) = (completedSigmaDensity d t : ℂ) := by
  have e2 : (t : ℂ) + Complex.I * (d : ℂ) = displacedHeight (-d) t := by
    unfold displacedHeight; push_cast; ring
  show completedNativeOperatorCharacteristic ((t : ℂ) - Complex.I * (d : ℂ)) *
      completedNativeOperatorCharacteristic ((t : ℂ) + Complex.I * (d : ℂ))
      = (completedSigmaDensity d t : ℂ)
  rw [e2]
  show completedSigmaResponse d t * completedSigmaResponse (-d) t = (completedSigmaDensity d t : ℂ)
  rw [sigma_response_conjugate d t hd₁ hd₂, Complex.mul_conj,
    show completedSigmaDensity d t = ‖completedSigmaResponse d t‖ ^ 2 from rfl,
    Complex.normSq_eq_norm_sq]

/-- **Zero deslocado.** Um zero `F(γ)=0` anula o produto deslocado em `τ = γ + id`. -/
theorem displacedProductC_vanishes_at_shifted_zero (d γ : ℝ)
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    displacedProductC d ((γ : ℂ) + Complex.I * (d : ℂ)) = 0 := by
  unfold displacedProductC
  have h : (γ : ℂ) + Complex.I * (d : ℂ) - Complex.I * (d : ℂ) = (γ : ℂ) := by ring
  rw [h, hzero, zero_mul]

/-- **Nó não-real no plano `u=t²`.** O zero deslocado `t=γ+id` dá `u=(γ+id)²` com
`Im u = 2γd`, não-nulo para `γ>0`, `d≠0`: o nó é genuinamente **não-real**. -/
theorem shifted_zero_u_im (γ d : ℝ) :
    (((γ : ℂ) + Complex.I * (d : ℂ)) ^ 2).im = 2 * γ * d := by
  simp only [pow_two, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Parte 3b — a função geradora dos jets: normalização e identidade de coeficientes

Avanço efetivo sobre a fonte original (não condicional, salvo admissibilidade do
deslocamento). Aqui `L = log D_d` com `D_d = displacedProductC d`. A função geradora
pretendida é `G_d(u) = ∑ₙ hₙ(d) uⁿ` com `hₙ(d) = completedSigmaLogJet d n`. A fórmula
candidata `G_d(t²) = −(1/4t)·D_d'(t)/D_d(t)` tem o coeficiente `1/4` **verificado por
derivação** (não copiado como axioma): de `(2n+2)! = 2(n+1)(2n+1)!` segue
`(n+1)/(2(2n+2)!) = 1/(4(2n+1)!)`, e expandindo `−L'(t)/(4t)` com `L` par o coeficiente de
`t^{2n}` é exatamente `−L^{(2n+2)}(0)/(4(2n+1)!)`. A normalização do Lean é feita sob medida
para isso. -/

/-- **Normalização 1/4 (derivada, não assumida).** O coeficiente da definição é exatamente
`−1/(4·(2n+1)!)`: `completedSigmaLogJet d n = −(1/(4(2n+1)!))·L^{(2n+2)}(0)`, `L = log densidade`. -/
theorem completedSigmaLogJet_quarter_normalization (d : ℝ) (n : ℕ) :
    completedSigmaLogJet d n =
      -(1 / (4 * ((2 * n + 1).factorial : ℝ))) *
        iteratedDeriv (2 * n + 2) (fun t : ℝ => Real.log (completedSigmaDensity d t)) 0 := by
  have hf : ((2 * n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * n + 1)).ne'
  have hcoef : (-((n + 1 : ℕ) : ℝ) / (2 * ((2 * n + 2).factorial : ℝ)))
      = -(1 / (4 * ((2 * n + 1).factorial : ℝ))) := by
    have hs : ((2 * n + 2).factorial : ℝ) = (2 * (n : ℝ) + 2) * ((2 * n + 1).factorial : ℝ) := by
      have h2 : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1).factorial := by
        have e : 2 * n + 2 = (2 * n + 1) + 1 := by ring
        rw [e, Nat.factorial_succ]
      rw [h2]; push_cast; ring
    rw [hs]; push_cast; field_simp; ring
  unfold completedSigmaLogJet
  rw [hcoef]

/-- **Jets = coeficientes log-derivativos da fonte original deslocada.** Para deslocamento
admissível, cada jet é o `(2n+2)`-ésimo coeficiente de Taylor (normalizado por `1/(4(2n+1)!)`)
de `log D_d` na fonte **original** `D_d = F(t−id)·F(t+id)`. Liga `completedSigmaLogJet` a
`completedNativeOperatorCharacteristic` sem predicado abstrato. -/
theorem completedSigmaLogJet_eq_logDisplacedProduct (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaLogJet d n =
      -(1 / (4 * ((2 * n + 1).factorial : ℝ))) *
        iteratedDeriv (2 * n + 2)
          (fun t : ℝ => Real.log ((displacedProductC d (t : ℂ)).re)) 0 := by
  rw [completedSigmaLogJet_quarter_normalization]
  have hfun : (fun t : ℝ => Real.log (completedSigmaDensity d t))
      = (fun t : ℝ => Real.log ((displacedProductC d (t : ℂ)).re)) := by
    funext t
    rw [displacedProductC_ofReal_eq_density d t hd₁ hd₂, Complex.ofReal_re]
  rw [hfun]

/-- The sigma jets are even in the displacement: the original displaced product
is unchanged when its two characteristic factors are interchanged. -/
theorem completedSigmaLogJet_neg (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaLogJet (-d) n = completedSigmaLogJet d n := by
  rw [completedSigmaLogJet_eq_logDisplacedProduct (-d) n (by linarith) (by linarith),
    completedSigmaLogJet_eq_logDisplacedProduct d n hd₁ hd₂]
  congr 2
  funext t
  have hleft : (t : ℂ) - Complex.I * ((-d : ℝ) : ℂ) =
      (t : ℂ) + Complex.I * (d : ℂ) := by push_cast; ring
  have hright : (t : ℂ) + Complex.I * ((-d : ℝ) : ℂ) =
      (t : ℂ) - Complex.I * (d : ℂ) := by push_cast; ring
  simp only [displacedProductC, hleft, hright, mul_comm]

#print axioms completedSigmaLogJet_neg

/-- **`D_d` é par no eixo real** (para deslocamento admissível): `D_d(−t) = D_d(t)`. Isto
justifica que a geradora é genuinamente função de `u = t²` (só potências pares de `t`),
pela evenness de `F` (`completedNativeOperatorCharacteristic_neg`). -/
theorem displacedProductC_even_ofReal (d t : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    displacedProductC d (-(t : ℂ)) = displacedProductC d (t : ℂ) := by
  have hsp : operatorHeightParameter ((t : ℂ) + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip := by
    have e : (t : ℂ) + Complex.I * (d : ℂ) = displacedHeight (-d) t := by
      unfold displacedHeight; push_cast; ring
    rw [e]; exact displacedHeight_strip (-d) t (by linarith) (by linarith)
  have hsm : operatorHeightParameter ((t : ℂ) - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip := by
    have e : (t : ℂ) - Complex.I * (d : ℂ) = displacedHeight d t := rfl
    rw [e]; exact displacedHeight_strip d t hd₁ hd₂
  unfold displacedProductC
  have h1 : completedNativeOperatorCharacteristic (-(t : ℂ) - Complex.I * (d : ℂ))
      = completedNativeOperatorCharacteristic ((t : ℂ) + Complex.I * (d : ℂ)) := by
    have e : -(t : ℂ) - Complex.I * (d : ℂ) = -((t : ℂ) + Complex.I * (d : ℂ)) := by ring
    rw [e, completedNativeOperatorCharacteristic_neg hsp]
  have h2 : completedNativeOperatorCharacteristic (-(t : ℂ) + Complex.I * (d : ℂ))
      = completedNativeOperatorCharacteristic ((t : ℂ) - Complex.I * (d : ℂ)) := by
    have e : -(t : ℂ) + Complex.I * (d : ℂ) = -((t : ℂ) - Complex.I * (d : ℂ)) := by ring
    rw [e, completedNativeOperatorCharacteristic_neg hsm]
  rw [h1, h2, mul_comm]

/-! ## Parte 3c — não-anulação na origem: `D_d(0) > 0` (incondicional, admissível)

Descarrega a obrigação "`D_d` não identicamente nula / `D_d(0) ≠ 0`" usando apenas o
não-anulamento já formalizado da característica original: `F = ξ-factor · heightScalar`,
o fator arquimediano não anula na faixa, e o escalar nativo em `−id` é
`genuineContinuation(1/2+d)`, não-nulo em `(0,1)`. -/

/-- **`D_d(0) > 0` para `|d| < 1/2`.** A densidade completada na origem é estritamente
positiva, logo `D_d` não é identicamente nula no componente que contém a origem. Sem
hipótese de não-anulação adicional. -/
theorem completedSigmaDensity_zero_pos (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    0 < completedSigmaDensity d 0 := by
  have hresp : completedSigmaResponse d 0 ≠ 0 := by
    show completedNativeOperatorCharacteristic (displacedHeight d 0) ≠ 0
    rw [completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar]
    refine mul_ne_zero
      (nativeXiCompletionFactor_ne_zero (displacedHeight_strip d 0 hd₁ hd₂)) ?_
    unfold nativeHeightScalar
    rw [nativeScalar_eq_genuineContinuation_unconditional, displacedHeight_parameter]
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    exact genuineContinuation_ofReal_ne_zero (by linarith) (by linarith)
  unfold completedSigmaDensity
  exact pow_pos (norm_pos_iff.mpr hresp) 2

/-- `D_d(0) ≠ 0` (versão complexa na origem), via a identidade no eixo real. -/
theorem displacedProductC_zero_ne_zero (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    displacedProductC d ((0 : ℝ) : ℂ) ≠ 0 := by
  rw [displacedProductC_ofReal_eq_density d 0 hd₁ hd₂, ne_eq, Complex.ofReal_eq_zero]
  exact (completedSigmaDensity_zero_pos d hd₁ hd₂).ne'

/-! ## Parte 3d — domínio: `D_d` holomorfa no ponto deslocado `t₀=γ+id`

**Observação de domínio (obrigatória, Etapa 3).** `F` é holomorfa exatamente em
`completedNativeHeightDomain = {z | |Im z| < 1/2}`
(`mem_completedNativeHeightDomain_iff_im_bounds`). Em `t₀ = γ+id` os fatores de
`D_d = F(·−id)·F(·+id)` são avaliados em `t₀−id = γ` (`Im=0`, sempre no domínio) e em
`t₀+id = γ+2id` (`Im=2d`, no domínio **sse `|d|<1/4`**). Portanto a holomorfia de `D_d` em
`t₀` só é garantida para `0<|d|<1/4` com a analiticidade conhecida de `F` na faixa centrada;
para `1/4 ≤ |d| < 1/2` seria necessária uma continuação meromorfa mais ampla de `F`, não
estabelecida aqui. **Não se extrapola a prova para todo `0<|d|<1/2`.** -/

/-- **Holomorfia de `D_d` em `t₀=γ+id` para `|d|<1/4`.** Ambos os fatores estão no domínio
de analiticidade de `F` (`γ` tem `Im=0`; `γ+2id` tem `Im=2d`, dentro de `|Im|<1/2`). -/
theorem displacedProductC_analyticAt (d γ : ℝ)
    (hd₁ : -(1 / 4 : ℝ) < d) (hd₂ : d < (1 / 4 : ℝ)) :
    AnalyticAt ℂ (displacedProductC d) ((γ : ℂ) + Complex.I * (d : ℂ)) := by
  set t₀ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ) with ht₀
  have hdom1 : (t₀ - Complex.I * (d : ℂ)) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter (t₀ - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have e : t₀ - Complex.I * (d : ℂ) = displacedHeight 0 γ := by
      rw [ht₀]; simp only [displacedHeight, Complex.ofReal_zero, mul_zero, sub_zero]; ring
    rw [e]; exact displacedHeight_strip 0 γ (by norm_num) (by norm_num)
  have hdom2 : (t₀ + Complex.I * (d : ℂ)) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter (t₀ + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have e : t₀ + Complex.I * (d : ℂ) = displacedHeight (-(2 * d)) γ := by
      rw [ht₀]; simp only [displacedHeight]; push_cast; ring
    rw [e]; exact displacedHeight_strip (-(2 * d)) γ (by linarith) (by linarith)
  have hg1 : AnalyticAt ℂ (fun τ : ℂ => τ - Complex.I * (d : ℂ)) t₀ :=
    analyticAt_id.sub analyticAt_const
  have hg2 : AnalyticAt ℂ (fun τ : ℂ => τ + Complex.I * (d : ℂ)) t₀ :=
    analyticAt_id.add analyticAt_const
  have hF1 : AnalyticAt ℂ
      (fun τ : ℂ => completedNativeOperatorCharacteristic (τ - Complex.I * (d : ℂ))) t₀ :=
    AnalyticAt.comp (f := fun τ : ℂ => τ - Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom1) hg1
  have hF2 : AnalyticAt ℂ
      (fun τ : ℂ => completedNativeOperatorCharacteristic (τ + Complex.I * (d : ℂ))) t₀ :=
    AnalyticAt.comp (f := fun τ : ℂ => τ + Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom2) hg2
  unfold displacedProductC
  exact hF1.mul hF2

/-- **Holomorfia de `D_d` na origem para `|d|<1/2`.** Ambos os fatores `F(∓id)` têm
`Im=∓d`, dentro da faixa `|Im z|<1/2`. -/
theorem displacedProductC_analyticAt_origin (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    AnalyticAt ℂ (displacedProductC d) 0 := by
  have hdom1 : ((0 : ℂ) - Complex.I * (d : ℂ)) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have e : (0 : ℂ) - Complex.I * (d : ℂ) = displacedHeight d 0 := by
      simp only [displacedHeight]; push_cast; ring
    rw [e]; exact displacedHeight_strip d 0 hd₁ hd₂
  have hdom2 : ((0 : ℂ) + Complex.I * (d : ℂ)) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have e : (0 : ℂ) + Complex.I * (d : ℂ) = displacedHeight (-d) 0 := by
      simp only [displacedHeight]; push_cast; ring
    rw [e]; exact displacedHeight_strip (-d) 0 (by linarith) (by linarith)
  have hg1 : AnalyticAt ℂ (fun τ : ℂ => τ - Complex.I * (d : ℂ)) 0 :=
    analyticAt_id.sub analyticAt_const
  have hg2 : AnalyticAt ℂ (fun τ : ℂ => τ + Complex.I * (d : ℂ)) 0 :=
    analyticAt_id.add analyticAt_const
  have hF1 : AnalyticAt ℂ
      (fun τ : ℂ => completedNativeOperatorCharacteristic (τ - Complex.I * (d : ℂ))) 0 :=
    AnalyticAt.comp (f := fun τ : ℂ => τ - Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom1) hg1
  have hF2 : AnalyticAt ℂ
      (fun τ : ℂ => completedNativeOperatorCharacteristic (τ + Complex.I * (d : ℂ))) 0 :=
    AnalyticAt.comp (f := fun τ : ℂ => τ + Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom2) hg2
  unfold displacedProductC
  exact hF1.mul hF2

/-- **Vizinhança de não-anulação da origem (Etapa A.2).** Para `|d|<1/2`, `D_d` não se anula
numa vizinhança complexa da origem — pré-requisito para um ramo holomorfo local de `log D_d`
e da derivada logarítmica `D_d'/D_d`. -/
theorem displacedProductC_analyticAt_of_shiftedDomains (d : ℝ) (z : ℂ)
    (hdom₁ : z - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain)
    (hdom₂ : z + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain) :
    AnalyticAt ℂ (displacedProductC d) z := by
  have hg₁ : AnalyticAt ℂ (fun w : ℂ => w - Complex.I * (d : ℂ)) z :=
    analyticAt_id.sub analyticAt_const
  have hg₂ : AnalyticAt ℂ (fun w : ℂ => w + Complex.I * (d : ℂ)) z :=
    analyticAt_id.add analyticAt_const
  have hF₁ : AnalyticAt ℂ
      (fun w : ℂ => completedNativeOperatorCharacteristic (w - Complex.I * (d : ℂ))) z :=
    AnalyticAt.comp (f := fun w : ℂ => w - Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom₁) hg₁
  have hF₂ : AnalyticAt ℂ
      (fun w : ℂ => completedNativeOperatorCharacteristic (w + Complex.I * (d : ℂ))) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + Complex.I * (d : ℂ))
      (completedNativeOperatorCharacteristic_analyticAt hdom₂) hg₂
  unfold displacedProductC
  exact hF₁.mul hF₂

theorem displacedProductC_ne_zero_nhds_zero (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ z : ℂ in 𝓝 0, displacedProductC d z ≠ 0 := by
  have h0 : displacedProductC d 0 ≠ 0 := by
    have h := displacedProductC_zero_ne_zero d hd₁ hd₂
    rwa [Complex.ofReal_zero] at h
  exact ((displacedProductC_analyticAt_origin d hd₁ hd₂).continuousAt).eventually_ne h0

/-- **O germe real do log sigma é analítico na origem.** Isto liga a analiticidade
complexa do produto deslocado à função real cujas derivadas definem os jets sigma.
Em particular, a sequência completa dessas derivadas possui uma série de Taylor com
raio positivo; a identificação dos coeficientes pares com a geradora e a EDO local
permanecem gates separados. -/
theorem completedSigmaLogDensity_analyticAt_origin (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    AnalyticAt ℝ (fun t : ℝ => Real.log (completedSigmaDensity d t)) 0 := by
  have hreal : AnalyticAt ℝ
      (fun t : ℝ => (displacedProductC d (t : ℂ)).re) 0 :=
    (displacedProductC_analyticAt_origin d hd₁ hd₂).re_ofReal
  have hvalue : displacedProductC d (0 : ℂ) =
      (completedSigmaDensity d 0 : ℂ) := by
    simpa using displacedProductC_ofReal_eq_density d 0 hd₁ hd₂
  have hpositive : 0 < (displacedProductC d (0 : ℂ)).re := by
    rw [hvalue, Complex.ofReal_re]
    exact completedSigmaDensity_zero_pos d hd₁ hd₂
  have hlog := hreal.log hpositive
  have heq : (fun t : ℝ => Real.log (completedSigmaDensity d t)) =
      (fun t : ℝ => Real.log (displacedProductC d (t : ℂ)).re) := by
    funext t
    rw [displacedProductC_ofReal_eq_density d t hd₁ hd₂, Complex.ofReal_re]
  rw [heq]
  exact hlog

/-- The original shifted sigma density is even on the real axis. -/
theorem completedSigmaDensity_even (d t : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaDensity d (-t) = completedSigmaDensity d t := by
  apply Complex.ofReal_injective
  calc
    (completedSigmaDensity d (-t) : ℂ) =
        displacedProductC d ((-t : ℝ) : ℂ) := by
          symm
          exact displacedProductC_ofReal_eq_density d (-t) hd₁ hd₂
    _ = displacedProductC d (-(t : ℂ)) := by norm_num
    _ = displacedProductC d (t : ℂ) := displacedProductC_even_ofReal d t hd₁ hd₂
    _ = (completedSigmaDensity d t : ℂ) := displacedProductC_ofReal_eq_density d t hd₁ hd₂

/-- The real log-density is even on the real axis. -/
theorem completedSigmaLogDensity_even (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    (fun t : ℝ => Real.log (completedSigmaDensity d (-t))) =
      (fun t : ℝ => Real.log (completedSigmaDensity d t)) := by
  funext t
  rw [completedSigmaDensity_even d t hd₁ hd₂]

/-- Every odd derivative of the analytic log-density vanishes at the center. -/
theorem completedSigmaLogDensity_odd_iteratedDeriv_eq_zero (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    iteratedDeriv (2 * n + 1)
      (fun t : ℝ => Real.log (completedSigmaDensity d t)) 0 = 0 := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  have heven : (fun t : ℝ => L (-t)) = L := by
    exact completedSigmaLogDensity_even d hd₁ hd₂
  have hderiv := congrArg (fun f : ℝ → ℝ => iteratedDeriv (2 * n + 1) f 0) heven
  rw [iteratedDeriv_comp_neg] at hderiv
  have hpowEven (k : ℕ) : (-1 : ℝ) ^ (k * 2) = 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, pow_add, ih]
        norm_num
  have hpow : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [show 2 * n + 1 = n * 2 + 1 by omega, pow_add, hpowEven n]
    norm_num
  simp only [L, neg_zero, hpow, smul_eq_mul] at hderiv
  linarith

/-- Ordinary Taylor series of the analytic real log-density germ. -/
def completedSigmaLogDensityTaylorSeries (d : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n =>
    iteratedDeriv n (fun t : ℝ => Real.log (completedSigmaDensity d t)) 0 /
      (n.factorial : ℝ))

/-- Taylor coefficient sequence of the derivative of the real log-density. -/
def completedSigmaLogDensityDerivativeTaylorCoefficient (d : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (deriv (fun t : ℝ => Real.log (completedSigmaDensity d t))) 0 /
    (n.factorial : ℝ)

/-- Taylor series of the derivative of the real log-density. -/
def completedSigmaLogDensityDerivativeTaylorSeries (d : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (completedSigmaLogDensityDerivativeTaylorCoefficient d)

/-- The derivative Taylor series converges to the actual derivative near the origin. -/
theorem completedSigmaLogDensityDerivativeTaylorSeries_hasFPowerSeriesAt (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    HasFPowerSeriesAt (deriv (fun t : ℝ => Real.log (completedSigmaDensity d t)))
      (completedSigmaLogDensityDerivativeTaylorSeries d) 0 := by
  exact (completedSigmaLogDensity_analyticAt_origin d hd₁ hd₂).deriv.hasFPowerSeriesAt

/-- Even powers in the Taylor series of the log-density derivative vanish. -/
theorem completedSigmaLogDensityDerivativeTaylorCoefficient_even_eq_zero
    (d : ℝ) (n : ℕ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaLogDensityDerivativeTaylorCoefficient d (2 * n) = 0 := by
  unfold completedSigmaLogDensityDerivativeTaylorCoefficient
  rw [← iteratedDeriv_succ']
  rw [completedSigmaLogDensity_odd_iteratedDeriv_eq_zero d n hd₁ hd₂]
  simp

/-- Odd Taylor coefficients of the log-density derivative are exactly `-4` times the
original sigma jets. This is the coefficient identity behind `L'(t)=-4tG_d(t²)`. -/
theorem completedSigmaLogDensityDerivativeTaylorCoefficient_odd_eq_jet
    (d : ℝ) (n : ℕ) :
    completedSigmaLogDensityDerivativeTaylorCoefficient d (2 * n + 1) =
      -4 * completedSigmaLogJet d n := by
  unfold completedSigmaLogDensityDerivativeTaylorCoefficient
  rw [← iteratedDeriv_succ', completedSigmaLogJet_quarter_normalization]
  have hf : ((2 * n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * n + 1)).ne'
  field_simp [hf]

/-- The Taylor series of the original sigma jets in the reduced variable `u`. -/
def completedSigmaLogJetGeneratingSeries (d : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (completedSigmaLogJet d)

/-- Sum of the convergent Taylor series whose coefficients are the original sigma jets. -/
def completedSigmaLogJetGeneratingFunction (d u : ℝ) : ℝ :=
  (completedSigmaLogJetGeneratingSeries d).sum u

private theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The original sigma jets satisfy the exponential coefficient bound H2.  This is
obtained from the analytic Taylor coefficients of the log-density and the exact
normalization of `completedSigmaLogJet`; no auxiliary moment sequence is used. -/
theorem completedSigmaLogJet_exponential_bound (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧
      ∀ n, |completedSigmaLogJet d n| ≤ C * R ^ n := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  let S := completedSigmaLogDensityTaylorSeries d
  have hL : AnalyticAt ℝ L 0 :=
    completedSigmaLogDensity_analyticAt_origin d hd₁ hd₂
  have hrS : 0 < S.radius := hL.hasFPowerSeriesAt.radius_pos
  obtain ⟨C, r, hC, hr, hbound⟩ := S.le_mul_pow_of_radius_pos hrS
  have hcoeff (n : ℕ) : completedSigmaLogJet d n =
      -(((n + 1 : ℕ) : ℝ) / 2) * (S (2 * n + 2) (fun _ => 1)) := by
    rw [completedSigmaLogJet_quarter_normalization]
    simp only [S, completedSigmaLogDensityTaylorSeries,
      FormalMultilinearSeries.ofScalars_apply_eq]
    have hfact : ((2 * n + 2).factorial : ℝ) =
        ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1).factorial : ℝ) := by
      have hn : 2 * n + 2 = (2 * n + 1) + 1 := by omega
      rw [hn, Nat.factorial_succ]
      push_cast
      rfl
    rw [hfact]
    push_cast
    have hnum : (2 : ℝ) * (n : ℝ) + 2 = 2 * ((n : ℝ) + 1) := by ring
    rw [hnum]
    simp only [smul_eq_mul, one_pow]
    field_simp [show ((2 * n + 1).factorial : ℝ) ≠ 0 by positivity]
    ring
  let A : ℝ := C * r ^ 2
  let q : ℝ := 2 * r ^ 2
  have hA : 0 < A := by positivity
  have hq : 0 < q := by positivity
  have hboundJet : ∀ n, ‖completedSigmaLogJet d n‖ ≤ A * q ^ n := by
    intro n
    rw [hcoeff n]
    have hTaylor := hbound (2 * n + 2)
    change ‖S (2 * n + 2)‖ ≤ C * r ^ (2 * n + 2) at hTaylor
    have hTaylorCoeff : ‖S (2 * n + 2) (fun _ => 1)‖ ≤
        C * r ^ (2 * n + 2) := by
      have heq : ‖S (2 * n + 2)‖ = ‖S (2 * n + 2) (fun _ => 1)‖ := by
        simp [S, completedSigmaLogDensityTaylorSeries]
      rw [← heq]
      exact hTaylor
    have hnreal : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast nat_succ_le_two_pow n
    have hfactor : 0 ≤ ((n + 1 : ℕ) : ℝ) / 2 := by positivity
    calc
      ‖-(((n + 1 : ℕ) : ℝ) / 2) * S (2 * n + 2) (fun _ => 1)‖
          = (((n + 1 : ℕ) : ℝ) / 2) * ‖S (2 * n + 2) (fun _ => 1)‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hfactor]
      _ ≤ (((n + 1 : ℕ) : ℝ) / 2) * (C * r ^ (2 * n + 2)) :=
            mul_le_mul_of_nonneg_left hTaylorCoeff hfactor
      _ ≤ (2 : ℝ) ^ n * (C * r ^ 2 * (r ^ 2) ^ n) := by
            have hpow : r ^ (2 * n + 2) = r ^ 2 * (r ^ 2) ^ n := by
              calc
                r ^ (2 * n + 2) = r ^ (2 * n) * r ^ 2 := by
                  rw [show 2 * n + 2 = 2 * n + 2 by omega, pow_add]
                _ = (r ^ 2) ^ n * r ^ 2 := by rw [pow_mul]
                _ = r ^ 2 * (r ^ 2) ^ n := by ring
            rw [hpow]
            have hfac : (((n + 1 : ℕ) : ℝ) / 2) ≤ (2 : ℝ) ^ n := by
              linarith
            have hcommon : 0 ≤ C * r ^ 2 * (r ^ 2) ^ n := by positivity
            have heq : (((n + 1 : ℕ) : ℝ) / 2) *
                (C * (r ^ 2 * (r ^ 2) ^ n)) =
                (((n + 1 : ℕ) : ℝ) / 2) * (C * r ^ 2 * (r ^ 2) ^ n) := by ring
            rw [heq]
            exact mul_le_mul_of_nonneg_right hfac hcommon
      _ = A * q ^ n := by
            simp only [A, q]
            rw [mul_pow]
            ring
  refine ⟨A, q, le_of_lt hA, hq, ?_⟩
  intro n
  simpa [Real.norm_eq_abs] using hboundJet n

#print axioms completedSigmaLogJet_exponential_bound

/-- At shift zero the original sigma matrix is exactly the Hankel matrix of the
original sigma jets. -/
theorem completedSigmaLogJet_sigmaMatrix_eq_hankel (d : ℝ) (N : ℕ) :
    sigmaMatrix d 0 N = hankelMatrix (completedSigmaLogJet d) N := by
  ext i j
  simp [sigmaMatrix, sourceMomentMatrix, hankelMatrix]

#print axioms completedSigmaLogJet_sigmaMatrix_eq_hankel

/-- The assumed all-order positivity of the original sigma matrices is precisely
H1 for the same, unmodified sequence of sigma jets. -/
theorem completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd (d : ℝ)
    (hσ : ∀ N, (sigmaMatrix d 0 N).PosSemidef) :
    ∀ N, (hankelMatrix (completedSigmaLogJet d) N).PosSemidef := by
  intro N
  rw [← completedSigmaLogJet_sigmaMatrix_eq_hankel d N]
  exact hσ N

#print axioms completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd

/-- Under the hypothetical all-order sigma positivity and the Cauchy bound H2,
the complex resolvent sums the original sigma-jet series throughout its explicit
Neumann disk. -/
theorem completedSigmaLogJet_resolvent_hasSum_of_sigmaMatrix_psd (d : ℝ)
    (hσ : ∀ N, (sigmaMatrix d 0 N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ n, |completedSigmaLogJet d n| ≤ C * R ^ n)
    {u : ℂ} (hu : ‖u‖ * R < 1) :
    HasSum (fun n : ℕ => (completedSigmaLogJet d n : ℂ) * u ^ n)
      (momentResolventCoefficient
        (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
        hC hR hbound
        (momentComplexUnit
          (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)) u) := by
  exact momentResolventCoefficient_hasSum_moments_of_radius
    (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
    hC hR hbound hu

#print axioms completedSigmaLogJet_resolvent_hasSum_of_sigmaMatrix_psd

/-- **Raio positivo da geradora dos jets sigma originais.** O bound geométrico dos
coeficientes da série Taylor analítica do log-density é transferido aos jets por
`h_n = -(n+1)/2 · [t^(2n+2)] log D_d`; o fator linear é absorvido por `2^n`.
Isto prova convergência real positiva da série definida com `completedSigmaLogJet`;
a identidade diferencial ainda será derivada separadamente. -/
theorem completedSigmaLogJetGeneratingSeries_radius_pos (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    0 < (completedSigmaLogJetGeneratingSeries d).radius := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  let S := completedSigmaLogDensityTaylorSeries d
  have hL : AnalyticAt ℝ L 0 := by
    exact completedSigmaLogDensity_analyticAt_origin d hd₁ hd₂
  have hrS : 0 < S.radius := by
    exact hL.hasFPowerSeriesAt.radius_pos
  obtain ⟨C, r, hC, hr, hbound⟩ := S.le_mul_pow_of_radius_pos hrS
  have hcoeff (n : ℕ) : completedSigmaLogJet d n =
      -(((n + 1 : ℕ) : ℝ) / 2) * (S (2 * n + 2) (fun _ => 1)) := by
    rw [completedSigmaLogJet_quarter_normalization]
    simp only [S, completedSigmaLogDensityTaylorSeries,
      FormalMultilinearSeries.ofScalars_apply_eq]
    have hfact : ((2 * n + 2).factorial : ℝ) =
        ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1).factorial : ℝ) := by
      have hn : 2 * n + 2 = (2 * n + 1) + 1 := by omega
      rw [hn, Nat.factorial_succ]
      push_cast
      rfl
    rw [hfact]
    push_cast
    have hnum : (2 : ℝ) * (n : ℝ) + 2 = 2 * ((n : ℝ) + 1) := by ring
    rw [hnum]
    simp only [smul_eq_mul, one_pow]
    field_simp [show ((2 * n + 1).factorial : ℝ) ≠ 0 by positivity]
    ring
  let A : ℝ := C * r ^ 2
  let q : ℝ := 2 * r ^ 2
  have hA : 0 < A := by positivity
  have hq : 0 < q := by positivity
  have hboundJet : ∀ n, ‖completedSigmaLogJet d n‖ ≤ A * q ^ n := by
    intro n
    rw [hcoeff n]
    have hTaylor := hbound (2 * n + 2)
    change ‖S (2 * n + 2)‖ ≤ C * r ^ (2 * n + 2) at hTaylor
    have hTaylorCoeff : ‖S (2 * n + 2) (fun _ => 1)‖ ≤
        C * r ^ (2 * n + 2) := by
      have heq : ‖S (2 * n + 2)‖ = ‖S (2 * n + 2) (fun _ => 1)‖ := by
        simp [S, completedSigmaLogDensityTaylorSeries]
      rw [← heq]
      exact hTaylor
    have hnreal : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast nat_succ_le_two_pow n
    have hfactor : 0 ≤ ((n + 1 : ℕ) : ℝ) / 2 := by positivity
    calc
      ‖-(((n + 1 : ℕ) : ℝ) / 2) * S (2 * n + 2) (fun _ => 1)‖
          = (((n + 1 : ℕ) : ℝ) / 2) * ‖S (2 * n + 2) (fun _ => 1)‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hfactor]
      _ ≤ (((n + 1 : ℕ) : ℝ) / 2) * (C * r ^ (2 * n + 2)) :=
            mul_le_mul_of_nonneg_left hTaylorCoeff hfactor
      _ ≤ (2 : ℝ) ^ n * (C * r ^ 2 * (r ^ 2) ^ n) := by
            have hpow : r ^ (2 * n + 2) = r ^ 2 * (r ^ 2) ^ n := by
              calc
                r ^ (2 * n + 2) = r ^ (2 * n) * r ^ 2 := by
                  rw [show 2 * n + 2 = 2 * n + 2 by omega, pow_add]
                _ = (r ^ 2) ^ n * r ^ 2 := by
                  rw [pow_mul]
                _ = r ^ 2 * (r ^ 2) ^ n := by ring
            rw [hpow]
            have hfac : (((n + 1 : ℕ) : ℝ) / 2) ≤ (2 : ℝ) ^ n := by
              linarith
            have hcommon : 0 ≤ C * r ^ 2 * (r ^ 2) ^ n := by positivity
            have heq : (((n + 1 : ℕ) : ℝ) / 2) *
                (C * (r ^ 2 * (r ^ 2) ^ n)) =
                (((n + 1 : ℕ) : ℝ) / 2) * (C * r ^ 2 * (r ^ 2) ^ n) := by ring
            rw [heq]
            exact mul_le_mul_of_nonneg_right hfac hcommon
      _ = A * q ^ n := by
            simp only [A, q]
            rw [mul_pow]
            ring
  let ρ : NNReal := ⟨1 / (2 * q), by positivity⟩
  have hradius : (ρ : ENNReal) ≤
      (completedSigmaLogJetGeneratingSeries d).radius := by
    apply (completedSigmaLogJetGeneratingSeries d).le_radius_of_bound A
    intro n
    change ‖FormalMultilinearSeries.ofScalars ℝ (completedSigmaLogJet d) n‖ *
        (1 / (2 * q) : ℝ) ^ n ≤ A
    rw [FormalMultilinearSeries.ofScalars_norm]
    calc
      ‖completedSigmaLogJet d n‖ * (1 / (2 * q) : ℝ) ^ n ≤
          (A * q ^ n) * (1 / (2 * q) : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (hboundJet n) (by positivity)
      _ = A * (1 / 2 : ℝ) ^ n := by
            rw [mul_assoc, ← mul_pow]
            congr 2
            field_simp [ne_of_gt hq]
      _ ≤ A := by
            exact mul_le_of_le_one_right hA.le
              (pow_le_one₀ (by norm_num) (by norm_num))
  have hposNN : 0 < ρ := by
    change 0 < 1 / (2 * q)
    positivity
  exact lt_of_lt_of_le (by exact_mod_cast hposNN) hradius

/-- The jet series converges to its sum on a neighborhood of the origin. -/
theorem completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    HasFPowerSeriesAt (completedSigmaLogJetGeneratingFunction d)
      (completedSigmaLogJetGeneratingSeries d) 0 := by
  exact ((completedSigmaLogJetGeneratingSeries d).hasFPowerSeriesOnBall
    (completedSigmaLogJetGeneratingSeries_radius_pos d hd₁ hd₂)).hasFPowerSeriesAt

/-- Complex coefficient series obtained by scalar extension from the original real sigma jets. -/
def completedSigmaLogJetComplexSeries (d : ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (completedSigmaLogJet d n : ℂ))

/-- Complex analytic sum of the same original sigma-jet sequence. -/
def completedSigmaLogJetComplexGeneratingFunction (d : ℝ) (u : ℂ) : ℂ :=
  (completedSigmaLogJetComplexSeries d).sum u

/-- Scalar extension preserves the convergence radius because `‖(x : ℂ)‖ = ‖x‖`. -/
theorem completedSigmaLogJetComplexSeries_radius_pos (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    0 < (completedSigmaLogJetComplexSeries d).radius := by
  have hr : (completedSigmaLogJetComplexSeries d).radius =
      (completedSigmaLogJetGeneratingSeries d).radius := by
    simp [completedSigmaLogJetComplexSeries, completedSigmaLogJetGeneratingSeries,
      FormalMultilinearSeries.radius]
  rw [hr]
  exact completedSigmaLogJetGeneratingSeries_radius_pos d hd₁ hd₂

/-- The complex generating function is analytic near zero and has precisely the original jets
as its Taylor coefficients. -/
theorem completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    HasFPowerSeriesAt (completedSigmaLogJetComplexGeneratingFunction d)
      (completedSigmaLogJetComplexSeries d) 0 := by
  exact ((completedSigmaLogJetComplexSeries d).hasFPowerSeriesOnBall
    (completedSigmaLogJetComplexSeries_radius_pos d hd₁ hd₂)).hasFPowerSeriesAt

/-- Under all-order positivity, the native analytic generating function and the
constructed resolvent coincide near the origin.  Both values are identified by
their convergent sums of the same original sigma jets. -/
theorem completedSigmaLogJetComplexGeneratingFunction_eq_resolvent_eventually
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (hσ : ∀ N, (sigmaMatrix d 0 N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ n, |completedSigmaLogJet d n| ≤ C * R ^ n) :
    ∀ᶠ u : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d u =
        momentResolventCoefficient
          (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
          hC hR hbound
          (momentComplexUnit
            (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)) u := by
  have hseries := completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂
  have hseriesSum := hseries.eventually_hasSum
  have hnorm : Filter.Tendsto (fun u : ℂ => ‖u‖ * R) (𝓝 0) (𝓝 0) := by
    have hnorm' : Filter.Tendsto (fun u : ℂ => ‖u‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.continuousAt :
        ContinuousAt (fun u : ℂ => ‖u‖) (0 : ℂ)).tendsto
    simpa using hnorm'.mul_const R
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ * R < 1 := by
    have hevent := hnorm.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa using hevent
  have hresolventSum : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun n : ℕ => (completedSigmaLogJet d n : ℂ) * u ^ n)
        (momentResolventCoefficient
          (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
          hC hR hbound
          (momentComplexUnit
            (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)) u) := by
    filter_upwards [hsmall] with u hu
    exact completedSigmaLogJet_resolvent_hasSum_of_sigmaMatrix_psd
      d hσ hC hR hbound hu
  filter_upwards [hseriesSum, hresolventSum] with u hsumAnalytic hsumResolvent
  have hsumAnalytic' :
      HasSum (fun n : ℕ => (completedSigmaLogJet d n : ℂ) * u ^ n)
        (completedSigmaLogJetComplexGeneratingFunction d u) := by
    simpa [completedSigmaLogJetComplexSeries,
      completedSigmaLogJetComplexGeneratingFunction,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hsumAnalytic
  exact hsumAnalytic'.unique hsumResolvent

#print axioms completedSigmaLogJetComplexGeneratingFunction_eq_resolvent_eventually

private def oddIndexEquiv : ℕ ≃ {k : ℕ // k % 2 = 1} where
  toFun n := ⟨2 * n + 1, by omega⟩
  invFun k := k.1 / 2
  left_inv n := by
    simp [Nat.mul_add_div]
  right_inv k := by
    rcases k with ⟨k, hk⟩
    apply Subtype.ext
    change 2 * (k / 2) + 1 = k
    have hmod := Nat.mod_add_div k 2
    rw [hk] at hmod
    omega

/-- The Taylor series identities above imply the real local differential equation
for the log-density and the original sigma-jet generating function. The proof splits
the convergent derivative series into even and odd indices, kills the even terms by
parity, and reindexes the odd terms by `k=2n+1`. -/
theorem completedSigmaLogDensity_derivative_eq_generatingFunction_eventually
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      deriv (fun x : ℝ => Real.log (completedSigmaDensity d x)) t =
        -4 * t * completedSigmaLogJetGeneratingFunction d (t ^ 2) := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  let c := completedSigmaLogDensityDerivativeTaylorCoefficient d
  let O : Set ℕ := {k | k % 2 = 1}
  have hDerivSeries := completedSigmaLogDensityDerivativeTaylorSeries_hasFPowerSeriesAt
    d hd₁ hd₂
  have hGenSeries := completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt d hd₁ hd₂
  have hSquare : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun t : ℝ => t ^ 2) 0).tendsto
  have hDerivEventually := hDerivSeries.eventually_hasSum
  have hGenEventually := hSquare.eventually hGenSeries.eventually_hasSum
  filter_upwards [hDerivEventually, hGenEventually] with t hDerivHasSum hGenHasSum
  have hDerivSum : HasSum (fun k : ℕ => c k * t ^ k) (deriv L t) := by
    simpa [L, completedSigmaLogDensityDerivativeTaylorSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hDerivHasSum
  have hGenSum : HasSum (fun n : ℕ => completedSigmaLogJet d n * (t ^ 2) ^ n)
      (completedSigmaLogJetGeneratingFunction d (t ^ 2)) := by
    simpa [completedSigmaLogJetGeneratingSeries, completedSigmaLogJetGeneratingFunction,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hGenHasSum
  let f : ℕ → ℝ := fun k => c k * t ^ k
  have hEvenCoeff : ∀ k, k % 2 = 0 → c k = 0 := by
    intro k hk
    have hk' : k = 2 * (k / 2) := by omega
    rw [hk']
    exact completedSigmaLogDensityDerivativeTaylorCoefficient_even_eq_zero
      d (k / 2) hd₁ hd₂
  have hDecomp := hDerivSum.summable.tsum_subtype_add_tsum_subtype_compl O
  have hComplementZero : ∑' k : (Oᶜ : Set ℕ), f k = 0 := by
    have hall : ∀ k : (Oᶜ : Set ℕ), f k = 0 := by
      intro k
      have hkO : ¬ k.val % 2 = 1 := by
        intro heq
        apply k.property
        change k.val % 2 = 1
        exact heq
      have hk : k.val % 2 = 0 := by
        have hm := Nat.mod_lt k.val (by norm_num : 0 < 2)
        omega
      simp [f, hEvenCoeff k.val hk]
    simp [hall]
  have hDerivOdd : deriv L t = ∑' k : (O : Set ℕ), f k := by
    calc
      deriv L t = ∑' k : ℕ, f k := hDerivSum.tsum_eq.symm
      _ = (∑' k : (O : Set ℕ), f k) + ∑' k : (Oᶜ : Set ℕ), f k := by
        simpa [f] using hDecomp.symm
      _ = ∑' k : (O : Set ℕ), f k := by rw [hComplementZero, add_zero]
  have hReindex : (∑' k : (O : Set ℕ), f k) = ∑' n : ℕ, f (2 * n + 1) := by
    calc
      (∑' k : (O : Set ℕ), f k) =
          ∑' k : {k : ℕ // k % 2 = 1}, f k := rfl
      _ = ∑' n : ℕ, f (2 * n + 1) :=
          (Equiv.tsum_eq oddIndexEquiv (fun k : {k : ℕ // k % 2 = 1} => f k.val)).symm
  have hOddTerms : (∑' n : ℕ, f (2 * n + 1)) =
      ∑' n : ℕ, (-4 * t) * (completedSigmaLogJet d n * (t ^ 2) ^ n) := by
    apply tsum_congr
    intro n
    simp only [f, c, completedSigmaLogDensityDerivativeTaylorCoefficient_odd_eq_jet]
    rw [pow_succ]
    ring
  have hFactor : (∑' n : ℕ,
      (-4 * t) * (completedSigmaLogJet d n * (t ^ 2) ^ n)) =
      -4 * t * completedSigmaLogJetGeneratingFunction d (t ^ 2) := by
    rw [tsum_mul_left, hGenSum.tsum_eq]
  rw [hDerivOdd, hReindex, hOddTerms, hFactor]

/-- The complex derivative of the displaced product, restricted to the real axis, agrees
locally with the derivative of the original real density. -/
theorem displacedProductC_deriv_ofReal_eq_density_deriv_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      deriv (displacedProductC d) (t : ℂ) =
        ((deriv (fun x : ℝ => completedSigmaDensity d x) t : ℝ) : ℂ) := by
  have hD := displacedProductC_analyticAt_origin d hd₁ hd₂
  have hρ : AnalyticAt ℝ (completedSigmaDensity d) 0 := by
    have hreal : AnalyticAt ℝ (fun t : ℝ => (displacedProductC d (t : ℂ)).re) 0 :=
      hD.re_ofReal
    have heq : (completedSigmaDensity d) =
        (fun t : ℝ => (displacedProductC d (t : ℂ)).re) := by
      funext t
      rw [displacedProductC_ofReal_eq_density d t hd₁ hd₂, Complex.ofReal_re]
    rw [heq]
    exact hreal
  have hcast : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) :=
    by convert Complex.continuous_ofReal.continuousAt.tendsto using 1; simp
  have hDreal := hcast.eventually hD.eventually_analyticAt
  filter_upwards [hDreal, hρ.eventually_analyticAt] with t hDt hρt
  have hDcomp : HasDerivAt (fun x : ℝ => displacedProductC d (x : ℂ))
      (deriv (displacedProductC d) (t : ℂ)) t := by
    simpa using (hDt.differentiableAt.hasDerivAt.comp_ofReal :
      HasDerivAt (fun x : ℝ => displacedProductC d (x : ℂ))
        (deriv (displacedProductC d) (t : ℂ)) t)
  have hρcomp : HasDerivAt (fun x : ℝ => (completedSigmaDensity d x : ℂ))
      ((deriv (fun x : ℝ => completedSigmaDensity d x) t : ℝ) : ℂ) t := by
    simpa using (hρt.differentiableAt.hasDerivAt.ofReal_comp :
      HasDerivAt (fun x : ℝ => (completedSigmaDensity d x : ℂ))
        ((deriv (fun x : ℝ => completedSigmaDensity d x) t : ℝ) : ℂ) t)
  have hEq : (fun x : ℝ => (completedSigmaDensity d x : ℂ)) =ᶠ[𝓝 t]
      (fun x : ℝ => displacedProductC d (x : ℂ)) := by
    filter_upwards [] with x
    symm
    exact displacedProductC_ofReal_eq_density d x hd₁ hd₂
  have hDcomp' := hDcomp.congr_of_eventuallyEq hEq
  exact hDcomp'.deriv.symm.trans hρcomp.deriv

/-- The convergent jet identity gives the differential equation for the real density itself. -/
theorem completedSigmaDensity_deriv_eq_generatingFunction_mul_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      deriv (completedSigmaDensity d) t =
        -4 * t * completedSigmaLogJetGeneratingFunction d (t ^ 2) *
          completedSigmaDensity d t := by
  have hD := displacedProductC_analyticAt_origin d hd₁ hd₂
  have hρ : AnalyticAt ℝ (completedSigmaDensity d) 0 := by
    have hreal : AnalyticAt ℝ (fun t : ℝ => (displacedProductC d (t : ℂ)).re) 0 :=
      hD.re_ofReal
    have heq : (completedSigmaDensity d) =
        (fun t : ℝ => (displacedProductC d (t : ℂ)).re) := by
      funext t
      rw [displacedProductC_ofReal_eq_density d t hd₁ hd₂, Complex.ofReal_re]
    rw [heq]
    exact hreal
  have hzero : completedSigmaDensity d 0 ≠ 0 :=
    (completedSigmaDensity_zero_pos d hd₁ hd₂).ne'
  have hnonzero : ∀ᶠ t : ℝ in 𝓝 0, completedSigmaDensity d t ≠ 0 :=
    hρ.continuousAt.eventually_ne hzero
  have hlog := completedSigmaLogDensity_derivative_eq_generatingFunction_eventually
    d hd₁ hd₂
  filter_upwards [hlog, hρ.eventually_analyticAt, hnonzero] with t hlogt hρt hnt
  have hlogDeriv := (hρt.differentiableAt.hasDerivAt.log hnt).deriv
  rw [hlogDeriv] at hlogt
  have hmul := congrArg (fun x : ℝ => x * completedSigmaDensity d t) hlogt
  rw [div_mul_cancel₀ _ hnt] at hmul
  calc
    deriv (completedSigmaDensity d) t =
        (-4 * t * completedSigmaLogJetGeneratingFunction d (t ^ 2)) *
          completedSigmaDensity d t := hmul
    _ = -4 * t * completedSigmaLogJetGeneratingFunction d (t ^ 2) *
          completedSigmaDensity d t := by ring

/-- On the real axis the complexified convergent series has the same value as the real series. -/
theorem completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d ((t : ℂ) ^ 2) =
        (completedSigmaLogJetGeneratingFunction d (t ^ 2) : ℂ) := by
  have hRealSeries := completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt d hd₁ hd₂
  have hComplexSeries := completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂
  have hRealSq : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun t : ℝ => t ^ 2) 0).tendsto
  have hComplexSq : Filter.Tendsto (fun t : ℝ => (t : ℂ) ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ) ^ 2) 0).tendsto
  have hRealEventually := hRealSq.eventually hRealSeries.eventually_hasSum
  have hComplexEventually := hComplexSq.eventually hComplexSeries.eventually_hasSum
  filter_upwards [hRealEventually, hComplexEventually] with t hRSum hCSum
  have hRSum' : HasSum (fun n : ℕ => completedSigmaLogJet d n * (t ^ 2) ^ n)
      (completedSigmaLogJetGeneratingFunction d (t ^ 2)) := by
    simpa [completedSigmaLogJetGeneratingSeries, completedSigmaLogJetGeneratingFunction,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hRSum
  have hCSum' : HasSum
      (fun n : ℕ => (completedSigmaLogJet d n : ℂ) * ((t : ℂ) ^ 2) ^ n)
      (completedSigmaLogJetComplexGeneratingFunction d ((t : ℂ) ^ 2)) := by
    simpa [completedSigmaLogJetComplexSeries, completedSigmaLogJetComplexGeneratingFunction,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hCSum
  have hMap := hRSum'.mapL Complex.ofRealCLM
  have hMap' : HasSum
      (fun n : ℕ => (completedSigmaLogJet d n : ℂ) * ((t : ℂ) ^ 2) ^ n)
      (completedSigmaLogJetGeneratingFunction d (t ^ 2) : ℂ) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hMap
  have hsum := hCSum'.unique hMap'
  exact hsum

/-- The complex differential expression vanishes on a real neighborhood of the origin. -/
theorem displacedProductC_differentialExpression_ofReal_eq_zero_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      deriv (displacedProductC d) (t : ℂ) +
        4 * (t : ℂ) *
          completedSigmaLogJetComplexGeneratingFunction d ((t : ℂ) ^ 2) *
          displacedProductC d (t : ℂ) = 0 := by
  have hDderiv := displacedProductC_deriv_ofReal_eq_density_deriv_eventually d hd₁ hd₂
  have hρderiv := completedSigmaDensity_deriv_eq_generatingFunction_mul_eventually
    d hd₁ hd₂
  have hG := completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually d hd₁ hd₂
  filter_upwards [hDderiv, hρderiv, hG] with t hDt hρt hGt
  have hDvalue := displacedProductC_ofReal_eq_density d t hd₁ hd₂
  have hρcomplex := congrArg (fun x : ℝ => (x : ℂ)) hρt
  rw [hDt, hGt, hDvalue]
  push_cast at hρcomplex ⊢
  rw [hρcomplex]
  ring

/-- **Local complex differential equation.** The analytic complex expression vanishes on a
neighborhood of the origin because it vanishes on a real neighborhood accumulating there. -/
theorem displacedProductC_local_differentialEquation (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      deriv (displacedProductC d) z +
        4 * z * completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) *
          displacedProductC d z = 0 := by
  let E : ℂ → ℂ := fun z => deriv (displacedProductC d) z +
    (4 * z) * (completedSigmaLogJetComplexGeneratingFunction d (z ^ 2) *
      displacedProductC d z)
  have hD := displacedProductC_analyticAt_origin d hd₁ hd₂
  have hG := (completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂).analyticAt
  change AnalyticAt ℂ (completedSigmaLogJetComplexGeneratingFunction d) (0 : ℂ) at hG
  have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) (0 : ℂ) := by fun_prop
  have hGsq : AnalyticAt ℂ
      (fun z : ℂ => completedSigmaLogJetComplexGeneratingFunction d (z ^ 2)) (0 : ℂ) := by
    exact AnalyticAt.comp_of_eq (g := completedSigmaLogJetComplexGeneratingFunction d)
      (f := fun z : ℂ => z ^ 2) (y := (0 : ℂ)) (x := (0 : ℂ)) hG hsq (by simp)
  have hE : AnalyticAt ℂ E 0 := by
    dsimp [E]
    fun_prop
  have hline := displacedProductC_differentialExpression_ofReal_eq_zero_eventually
    d hd₁ hd₂
  have hcast : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto using 1
    simp
  have hcastP : Filter.Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcast.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    simpa using (Complex.ofReal_ne_zero.mpr ht)
  have hacc : (0 : ℝ) ∈ closure {t : ℝ | t ≠ 0} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨ε / 2, ne_of_gt (half_pos hε), ?_⟩
    simpa [Real.dist_eq, abs_of_pos (half_pos hε)] using half_lt_self hε
  haveI : Filter.NeBot (𝓝[≠] (0 : ℝ)) := by
    apply (mem_closure_iff_nhdsWithin_neBot).mp
    exact hacc
  have hlineP : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), E (t : ℂ) = 0 := by
    have hline' := hline.filter_mono (nhdsWithin_le_nhds (s := {t : ℝ | t ≠ 0}))
    filter_upwards [hline'] with t ht
    dsimp [E]
    convert ht using 1
    ring
  have hfrequent : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), E z = 0 := by
    by_contra hnot
    have hne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), E z ≠ 0 := by
      have hdouble : ¬¬(∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), E z ≠ 0) := by
        simpa only [Filter.Frequently] using hnot
      exact not_not.mp hdouble
    have hneR := hcastP.eventually hne
    obtain ⟨t, hzero, hnonzero⟩ := (hlineP.and hneR).exists
    exact hnonzero hzero
  have hEzero := hE.frequently_zero_iff_eventually_zero.mp hfrequent
  simpa [E, mul_assoc] using hEzero

/-- Under the hypothetical all-order positivity of the original sigma matrices,
the local differential equation can be written with the constructed moment
resolvent itself. -/
theorem displacedProductC_local_resolventDifferentialEquation
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (hσ : ∀ N, (sigmaMatrix d 0 N).PosSemidef) :
    ∃ C R : ℝ, ∃ hC : 0 ≤ C, ∃ hR : 0 < R,
      ∃ hbound : ∀ n, |completedSigmaLogJet d n| ≤ C * R ^ n,
      ∀ᶠ z : ℂ in 𝓝 0,
        deriv (displacedProductC d) z +
          4 * z * momentResolventCoefficient
            (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
            hC hR hbound
            (momentComplexUnit
              (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)) (z ^ 2) *
          displacedProductC d z = 0 := by
  obtain ⟨C, R, hC, hR, hbound⟩ :=
    completedSigmaLogJet_exponential_bound d hd₁ hd₂
  let hH := completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ
  have hlocal := displacedProductC_local_differentialEquation d hd₁ hd₂
  have hresolvent := completedSigmaLogJetComplexGeneratingFunction_eq_resolvent_eventually
    d hd₁ hd₂ hσ hC hR hbound
  have hsq : Filter.Tendsto (fun z : ℂ => z ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => z ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun z : ℂ => z ^ 2) 0).tendsto
  have hresolventSq := hsq.eventually hresolvent
  refine ⟨C, R, hC, hR, hbound, ?_⟩
  filter_upwards [hlocal, hresolventSq] with z hz hG
  rw [hG] at hz
  simpa [hH] using hz

#print axioms displacedProductC_local_resolventDifferentialEquation

/-- The upper right strip joining the origin to the shifted zero when `d>0`. -/
def positiveDisplacementDomain (d : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ 0 < z.im ∧ z.im < (1 / 2 : ℝ) - d}

theorem positiveDisplacementDomain_isOpen (d : ℝ) :
    IsOpen (positiveDisplacementDomain d) := by
  change IsOpen ({z : ℂ | 0 < z.re} ∩
    ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < (1 / 2 : ℝ) - d}))
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

theorem positiveDisplacementDomain_convex (d : ℝ) :
    Convex ℝ (positiveDisplacementDomain d) := by
  change Convex ℝ ({z : ℂ | 0 < z.re} ∩
    ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < (1 / 2 : ℝ) - d}))
  exact (convex_halfSpace_re_gt 0).inter
    ((convex_halfSpace_im_gt 0).inter
      (convex_halfSpace_im_lt ((1 / 2 : ℝ) - d)))

theorem positiveDisplacementDomain_sq_im_pos {d : ℝ} {z : ℂ}
    (hz : z ∈ positiveDisplacementDomain d) : 0 < (z ^ 2).im := by
  rcases hz with ⟨hzre, hzim, _⟩
  have him : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]
    ring
  rw [him]
  positivity

/-- Both factors of the original displaced characteristic remain in its natural
strip throughout the upper right continuation domain. -/
theorem displacedProductC_analyticOnNhd_positiveDomain (d : ℝ)
    (hd₀ : 0 < d) (hd₁ : d < (1 / 4 : ℝ)) :
    AnalyticOnNhd ℂ (displacedProductC d) (positiveDisplacementDomain d) := by
  intro z hz
  rcases hz with ⟨hzre, hzim, hzimUpper⟩
  have him₁ : (z - Complex.I * (d : ℂ)).im = z.im - d := by simp
  have him₂ : (z + Complex.I * (d : ℂ)).im = z.im + d := by simp
  have hdom₁ : z - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    rw [mem_completedNativeHeightDomain_iff_im_bounds, him₁]
    constructor <;> linarith
  have hdom₂ : z + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    rw [mem_completedNativeHeightDomain_iff_im_bounds, him₂]
    constructor <;> linarith
  exact displacedProductC_analyticAt_of_shiftedDomains d z hdom₁ hdom₂

/-- The local resolvent differential equation analytically continues from the
Neumann disk around zero into the entire upper right strip. -/
theorem displacedProductC_resolventDifferentialEquation_on_positiveDomain
    (d : ℝ) (hd₀ : 0 < d) (hd₁ : d < (1 / 4 : ℝ))
    (hσ : ∀ N, (sigmaMatrix d 0 N).PosSemidef) :
    ∃ C R : ℝ, ∃ hC : 0 ≤ C, ∃ hR : 0 < R,
      ∃ hbound : ∀ n, |completedSigmaLogJet d n| ≤ C * R ^ n,
      ∀ z ∈ positiveDisplacementDomain d,
        deriv (displacedProductC d) z + 4 * z *
          momentResolventCoefficient
            (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)
            hC hR hbound
            (momentComplexUnit
              (completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ)) (z ^ 2) *
          displacedProductC d z = 0 := by
  have hdLow : -(1 / 2 : ℝ) < d := by linarith
  have hdHigh : d < (1 / 2 : ℝ) := by linarith
  obtain ⟨C, R, hC, hR, hbound, hlocal⟩ :=
    displacedProductC_local_resolventDifferentialEquation d hdLow hdHigh hσ
  let hH := completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ
  let e := momentComplexUnit hH
  let G : ℂ → ℂ := momentResolventCoefficient hH hC hR hbound e
  let E : ℂ → ℂ := fun z => deriv (displacedProductC d) z +
    4 * z * G (z ^ 2) * displacedProductC d z
  have hlocalE : E =ᶠ[𝓝 0] 0 := by
    filter_upwards [hlocal] with z hz
    simpa [E, G, hH, e] using hz
  let r : ℝ := min (((1 / 2 : ℝ) - d) / 2) (1 / (R + 1))
  have hr₁ : 0 < (((1 / 2 : ℝ) - d) / 2) := by linarith
  have hr₂ : 0 < 1 / (R + 1) := by positivity
  have hr : 0 < r := by positivity
  have hrBound₁ : r ≤ (((1 / 2 : ℝ) - d) / 2) := min_le_left _ _
  have hrBound₂ : r ≤ 1 / (R + 1) := min_le_right _ _
  have hrQuarter : r < 1 / 4 := by
    calc
      r ≤ (((1 / 2 : ℝ) - d) / 2) := hrBound₁
      _ < 1 / 4 := by linarith
  have hden : 0 < R + 1 := by linarith
  have hrTimesR : r * R < 1 := by
    have hprod : r * (R + 1) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hrBound₂ (by positivity : 0 ≤ R + 1)
      have hcancel : (1 / (R + 1)) * (R + 1) = 1 := by
        field_simp
      rw [hcancel] at hmul
      exact hmul
    nlinarith
  have hrSqR : r ^ 2 * R < 1 := by
    have hrle1 : r ≤ 1 := by
      calc
        r ≤ 1 / (R + 1) := hrBound₂
        _ ≤ 1 := by
          rw [div_le_one hden]
          linarith
    have hrsq : r ^ 2 ≤ r := by
      calc
        r ^ 2 = r * r := by ring
        _ ≤ 1 * r := mul_le_mul_of_nonneg_right hrle1 hr.le
        _ = r := by ring
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrsq hR.le) hrTimesR
  have hGdiffDisk : DifferentiableOn ℂ G {u : ℂ | ‖u‖ * R < 1} := by
    intro u hu
    exact (momentResolventCoefficient_differentiableAt_of_radius
      hH hC hR hbound e hu).differentiableWithinAt
  have hGopenDisk : IsOpen {u : ℂ | ‖u‖ * R < 1} := by
    exact isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hGanalyticDisk : AnalyticOnNhd ℂ G {u : ℂ | ‖u‖ * R < 1} :=
    hGdiffDisk.analyticOnNhd hGopenDisk
  have hGdiffNonreal : DifferentiableOn ℂ G {u : ℂ | u.im ≠ 0} := by
    simpa [G] using momentResolventCoefficient_differentiableOn hH hC hR hbound e
  have hGopenNonreal : IsOpen {u : ℂ | u.im ≠ 0} :=
    isOpen_ne_fun Complex.continuous_im continuous_const
  have hGanalyticNonreal : AnalyticOnNhd ℂ G {u : ℂ | u.im ≠ 0} :=
    hGdiffNonreal.analyticOnNhd hGopenNonreal
  have hDanalyticΩ := displacedProductC_analyticOnNhd_positiveDomain d hd₀ hd₁
  have hDanalyticBall : AnalyticOnNhd ℂ (displacedProductC d) (Metric.ball 0 r) := by
    intro z hz
    have hzNorm : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hzImAbs : |z.im| < 1 / 4 :=
      lt_of_le_of_lt (Complex.abs_im_le_norm z) (lt_trans hzNorm hrQuarter)
    have hzImBounds := abs_lt.mp hzImAbs
    have him₁ : (z - Complex.I * (d : ℂ)).im = z.im - d := by simp
    have him₂ : (z + Complex.I * (d : ℂ)).im = z.im + d := by simp
    have hstrip₁ : -1 / 2 < (z - Complex.I * (d : ℂ)).im ∧
        (z - Complex.I * (d : ℂ)).im < 1 / 2 := by
      rw [him₁]
      constructor <;> linarith
    have hstrip₂ : -1 / 2 < (z + Complex.I * (d : ℂ)).im ∧
        (z + Complex.I * (d : ℂ)).im < 1 / 2 := by
      rw [him₂]
      constructor <;> linarith
    have hdom₁ : z - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
      rw [mem_completedNativeHeightDomain_iff_im_bounds]
      constructor <;> linarith [hstrip₁.1, hstrip₁.2]
    have hdom₂ : z + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
      rw [mem_completedNativeHeightDomain_iff_im_bounds]
      constructor <;> linarith [hstrip₂.1, hstrip₂.2]
    exact displacedProductC_analyticAt_of_shiftedDomains d z hdom₁ hdom₂
  have hGsquare : AnalyticOnNhd ℂ (fun z : ℂ => G (z ^ 2))
      (positiveDisplacementDomain d ∪ Metric.ball 0 r) := by
    intro z hz
    rcases hz with hzΩ | hzBall
    · have him : (z ^ 2).im ≠ 0 :=
        (ne_of_gt (positiveDisplacementDomain_sq_im_pos hzΩ))
      have hGz := hGanalyticNonreal (z ^ 2) him
      have hsq : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
      change AnalyticAt ℂ (G ∘ (fun w : ℂ => w ^ 2)) z
      exact (AnalyticAt.comp (g := G) (f := fun w : ℂ => w ^ 2) (x := z)
        hGz hsq)
    · have hzNorm : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hzBall
      have hrad : ‖z ^ 2‖ * R < 1 := by
        rw [norm_pow]
        have hnormSq : ‖z‖ ^ 2 < r ^ 2 := by
          nlinarith [sq_nonneg (r - ‖z‖), norm_nonneg z]
        exact lt_of_lt_of_le
          (mul_lt_mul_of_pos_right hnormSq hR)
          (le_of_lt hrSqR)
      have hGz := hGanalyticDisk (z ^ 2) hrad
      have hsq : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
      change AnalyticAt ℂ (G ∘ (fun w : ℂ => w ^ 2)) z
      exact (AnalyticAt.comp (g := G) (f := fun w : ℂ => w ^ 2) (x := z)
        hGz hsq)
  have hDanalytic : AnalyticOnNhd ℂ (displacedProductC d)
      (positiveDisplacementDomain d ∪ Metric.ball 0 r) := by
    intro z hz
    rcases hz with hzΩ | hzBall
    · exact hDanalyticΩ z hzΩ
    · exact hDanalyticBall z hzBall
  have hEanalytic : AnalyticOnNhd ℂ E
      (positiveDisplacementDomain d ∪ Metric.ball 0 r) := by
    intro z hz
    have hDz := hDanalytic z hz
    have hDdz := hDz.deriv
    have hGz : AnalyticAt ℂ (fun w : ℂ => G (w ^ 2)) z := hGsquare z hz
    have hzlin : AnalyticAt ℂ (fun w : ℂ => (4 : ℂ) * w) z := by fun_prop
    change AnalyticAt ℂ (fun w : ℂ => deriv (displacedProductC d) w +
      (4 : ℂ) * w * G (w ^ 2) * displacedProductC d w) z
    exact hDdz.add ((hzlin.mul hGz).mul hDz)
  let a : ℝ := r / 4
  let w : ℂ := (a : ℂ) + Complex.I * (a : ℂ)
  have ha : 0 < a := by positivity
  have hwRe : w.re = a := by simp [w]
  have hwIm : w.im = a := by simp [w]
  have haUpper : a < (1 / 2 : ℝ) - d := by
    dsimp [a]
    linarith [hrBound₁]
  have hwΩ : w ∈ positiveDisplacementDomain d := by
    rw [positiveDisplacementDomain, Set.mem_setOf_eq, hwRe, hwIm]
    exact ⟨ha, ha, haUpper⟩
  have hwNorm : ‖w‖ < r := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hwRe, hwIm, abs_of_pos ha] at h
    calc
      ‖w‖ ≤ a + a := h
      _ = r / 2 := by dsimp [a]; ring
      _ < r := by linarith
  have hwBall : w ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hwNorm
  have hUnionPreconnected :
      IsPreconnected (positiveDisplacementDomain d ∪ Metric.ball (0 : ℂ) r) := by
    apply IsPreconnected.union' ⟨w, hwΩ, hwBall⟩
    · exact (positiveDisplacementDomain_convex d).isPreconnected
    · exact (convex_ball (0 : ℂ) r).isPreconnected
  have hzeroMem : (0 : ℂ) ∈ positiveDisplacementDomain d ∪ Metric.ball 0 r := by
    right
    exact Metric.mem_ball_self hr
  have hzeroOnUnion : Set.EqOn E 0 (positiveDisplacementDomain d ∪ Metric.ball 0 r) :=
    hEanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hUnionPreconnected hzeroMem hlocalE
  refine ⟨C, R, hC, hR, hbound, ?_⟩
  intro z hz
  have hzE := hzeroOnUnion (Set.mem_union_left _ hz)
  simpa [E, G, hH, e] using hzE

#print axioms positiveDisplacementDomain_isOpen
#print axioms positiveDisplacementDomain_convex
#print axioms positiveDisplacementDomain_sq_im_pos
#print axioms displacedProductC_analyticOnNhd_positiveDomain
#print axioms displacedProductC_resolventDifferentialEquation_on_positiveDomain

/-- The upper right domain accumulates at the origin. -/
theorem zero_mem_closure_positiveDisplacementDomain (d : ℝ)
    (hd₀ : 0 < d) (hd₁ : d < (1 / 4 : ℝ)) :
    (0 : ℂ) ∈ closure (positiveDisplacementDomain d) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let a : ℝ := min (ε / 4) (((1 / 2 : ℝ) - d) / 4)
  have ha : 0 < a := by
    have hgap : 0 < (1 / 2 : ℝ) - d := by linarith
    dsimp [a]
    exact lt_min (by positivity) (by linarith)
  let w : ℂ := (a : ℂ) + Complex.I * (a : ℂ)
  have hre : w.re = a := by simp [w]
  have him : w.im = a := by simp [w]
  have haUpper : a < (1 / 2 : ℝ) - d := by
    dsimp [a]
    have hgap : 0 < (1 / 2 : ℝ) - d := by linarith
    have hmin := min_le_right (ε / 4) (((1 / 2 : ℝ) - d) / 4)
    linarith
  have hwΩ : w ∈ positiveDisplacementDomain d := by
    rw [positiveDisplacementDomain, Set.mem_setOf_eq, hre, him]
    exact ⟨ha, ha, haUpper⟩
  have hnorm : ‖w‖ ≤ a + a := by
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = a + a := by simp [hre, him, abs_of_pos ha]
  have hnormlt : ‖w‖ < ε := by
    calc
      ‖w‖ ≤ a + a := hnorm
      _ ≤ ε / 2 := by
        dsimp [a]
        have hmin := min_le_left (ε / 4) (((1 / 2 : ℝ) - d) / 4)
        linarith
      _ < ε := by linarith
  have hdist : dist w 0 < ε := by simpa [dist_eq_norm] using hnormlt
  exact ⟨w, hwΩ, by simpa using hdist⟩

#print axioms zero_mem_closure_positiveDisplacementDomain

/-- All-order positivity of the original sigma matrices would force a holomorphic
linear ODE for the displaced product throughout the upper right strip. Its solution
cannot vanish at the shifted zero while the product is nonzero near the origin. -/
theorem sigmaMatrix_not_all_psd_of_positive_zero
    (d γ : ℝ) (hd₀ : 0 < d) (hd₁ : d < (1 / 4 : ℝ)) (hγ : 0 < γ)
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    ¬ ∀ N, (sigmaMatrix d 0 N).PosSemidef := by
  intro hσ
  have hdLow : -(1 / 2 : ℝ) < d := by linarith
  have hdHigh : d < (1 / 2 : ℝ) := by linarith
  obtain ⟨C, R, hC, hR, hbound, hEDO⟩ :=
    displacedProductC_resolventDifferentialEquation_on_positiveDomain d hd₀ hd₁ hσ
  let hH := completedSigmaLogJet_hankel_psd_of_sigmaMatrix_psd d hσ
  let G : ℂ → ℂ := momentResolventCoefficient hH hC hR hbound (momentComplexUnit hH)
  let D : ℂ → ℂ := displacedProductC d
  let Ω := positiveDisplacementDomain d
  let z₀ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ)
  have hz₀re : z₀.re = γ := by simp [z₀]
  have hz₀im : z₀.im = d := by simp [z₀]
  have hz₀Ω : z₀ ∈ Ω := by
    change z₀ ∈ positiveDisplacementDomain d
    rw [positiveDisplacementDomain, Set.mem_setOf_eq, hz₀re, hz₀im]
    exact ⟨hγ, hd₀, by linarith⟩
  have hDanalyticΩ : AnalyticOnNhd ℂ D Ω := by
    simpa [D, Ω] using displacedProductC_analyticOnNhd_positiveDomain d hd₀ hd₁
  have hDanalytic : AnalyticAt ℂ D z₀ := hDanalyticΩ z₀ hz₀Ω
  have hDzero : D z₀ = 0 := by
    simpa [D, z₀] using displacedProductC_vanishes_at_shifted_zero d γ hzero
  have hGnonreal : DifferentiableOn ℂ G {u : ℂ | u.im ≠ 0} := by
    simpa [G] using momentResolventCoefficient_differentiableOn hH hC hR hbound
      (momentComplexUnit hH)
  have huim : (z₀ ^ 2).im ≠ 0 := by
    rw [shifted_zero_u_im]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hγ)) (ne_of_gt hd₀)
  have hGanalytic : AnalyticAt ℂ G (z₀ ^ 2) :=
    (hGnonreal.analyticOnNhd
      (isOpen_ne_fun Complex.continuous_im continuous_const)) (z₀ ^ 2) huim
  have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) z₀ := by fun_prop
  have hGsq : AnalyticAt ℂ (fun z : ℂ => G (z ^ 2)) z₀ :=
    AnalyticAt.comp_of_eq (g := G) (f := fun z : ℂ => z ^ 2)
      (y := z₀ ^ 2) (x := z₀) hGanalytic hsq rfl
  let A : ℂ → ℂ := fun z => -(4 * z * G (z ^ 2))
  have hAanalytic : AnalyticAt ℂ A z₀ := by
    dsimp [A]
    fun_prop
  have hDnearZero : ∀ᶠ z : ℂ in 𝓝 0, D z ≠ 0 := by
    simpa [D] using displacedProductC_ne_zero_nhds_zero d hdLow hdHigh
  have hzeroClosure : (0 : ℂ) ∈ closure Ω := by
    simpa [Ω] using zero_mem_closure_positiveDisplacementDomain d hd₀ hd₁
  by_cases horderTop : analyticOrderAt D z₀ = ⊤
  · have hlocalZero : D =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp horderTop
    have hDzeroΩ := hDanalyticΩ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (positiveDisplacementDomain_convex d).isPreconnected hz₀Ω hlocalZero
    obtain ⟨z, hzD, hzΩ⟩ := (mem_closure_iff_nhds.mp hzeroClosure)
      {z : ℂ | D z ≠ 0} hDnearZero
    exact hzD (hDzeroΩ hzΩ)
  · have hDorderNat :
        (analyticOrderNatAt D z₀ : ℕ∞) = analyticOrderAt D z₀ :=
      Nat.cast_analyticOrderNatAt horderTop
    have hEqEventually : (fun z : ℂ => deriv D z) =ᶠ[𝓝 z₀]
        (fun z : ℂ => A z * D z) := by
      filter_upwards [(positiveDisplacementDomain_isOpen d).mem_nhds hz₀Ω]
        with z hz
      have hzODE := hEDO z hz
      have hsum : deriv D z + 4 * z * G (z ^ 2) * D z = 0 := by
        simpa [D, G, hH] using hzODE
      calc
        deriv D z = -(4 * z * G (z ^ 2) * D z) := eq_neg_of_add_eq_zero_left hsum
        _ = A z * D z := by dsimp [A]; ring
    have hOrderEq : analyticOrderAt (deriv D) z₀ =
        analyticOrderAt A z₀ + analyticOrderAt D z₀ := by
      calc
        analyticOrderAt (deriv D) z₀ =
            analyticOrderAt (fun z : ℂ => A z * D z) z₀ :=
          analyticOrderAt_congr hEqEventually
        _ = analyticOrderAt A z₀ + analyticOrderAt D z₀ := by
          change analyticOrderAt (A * D) z₀ = _
          exact analyticOrderAt_mul hAanalytic hDanalytic
    have hDerivativeOrder := hDanalytic.analyticOrderAt_deriv_add_one
    have hDerivativeOrder' : analyticOrderAt (deriv D) z₀ + 1 =
        analyticOrderAt D z₀ := by
      simpa [hDzero] using hDerivativeOrder
    rw [hOrderEq, ← hDorderNat] at hDerivativeOrder'
    cases hAorder : analyticOrderAt A z₀ with
    | top =>
        rw [hAorder] at hDerivativeOrder'
        simp at hDerivativeOrder'
    | coe m =>
        rw [hAorder] at hDerivativeOrder'
        simp only [← ENat.coe_one, ← ENat.coe_add] at hDerivativeOrder'
        have hnat : m + analyticOrderNatAt D z₀ + 1 = analyticOrderNatAt D z₀ := by
          exact_mod_cast hDerivativeOrder'
        omega

#print axioms sigmaMatrix_not_all_psd_of_positive_zero

/-- Evenness of the original jets transports all-order positivity from a negative
displacement to the corresponding positive displacement. -/
theorem sigmaMatrix_not_all_psd_of_negative_zero
    (d γ : ℝ) (hd₀ : d < 0) (hd₁ : -(1 / 4 : ℝ) < d) (hγ : 0 < γ)
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    ¬ ∀ N, (sigmaMatrix d 0 N).PosSemidef := by
  intro hσ
  have hlow : -(1 / 2 : ℝ) < d := by linarith
  have hhigh : d < (1 / 2 : ℝ) := by linarith
  have hσneg : ∀ N, (sigmaMatrix (-d) 0 N).PosSemidef := by
    intro N
    have hmat : sigmaMatrix (-d) 0 N = sigmaMatrix d 0 N := by
      rw [completedSigmaLogJet_sigmaMatrix_eq_hankel (-d) N,
        completedSigmaLogJet_sigmaMatrix_eq_hankel d N]
      ext i j
      simp only [hankelMatrix]
      exact completedSigmaLogJet_neg d (i.val + j.val)
        (by linarith) (by linarith)
    rw [hmat]
    exact hσ N
  have hnot := sigmaMatrix_not_all_psd_of_positive_zero (-d) γ
    (by linarith) (by linarith) hγ hzero
  exact hnot hσneg

#print axioms sigmaMatrix_not_all_psd_of_negative_zero

/-- The sigma matrix is symmetric, so failure of positive semidefiniteness gives
a real coefficient vector with strictly negative original sigma quadratic form. -/
theorem exists_sigmaMatrix_negative_direction {d : ℝ}
    (hnot : ¬ ∀ N, (sigmaMatrix d 0 N).PosSemidef) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0 := by
  push Not at hnot
  rcases hnot with ⟨N, hN⟩
  let M := sigmaMatrix d 0 N
  have hsymm : M.IsSymm := by
    simpa [M] using CarryMovingSigma.sigma_matrix_symm d 0 N
  have hHerm : M.IsHermitian := by simpa using hsymm
  have hnotQuad : ¬ ∀ v : Fin N → ℝ, 0 ≤ star v ⬝ᵥ (M *ᵥ v) := by
    intro hquad
    apply hN
    exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, hquad⟩
  push Not at hnotQuad
  rcases hnotQuad with ⟨v, hv⟩
  have hvneg : v ⬝ᵥ (M *ᵥ v) < 0 := by
    simpa [Pi.star_apply, star_trivial] using hv
  have hvne : v ≠ 0 := by
    intro hv0
    subst v
    simp at hvneg
  exact ⟨N, v, hvne, by simpa [M] using hvneg⟩

#print axioms exists_sigmaMatrix_negative_direction

/-- **Original-source finite-order obstruction.** Given a positive-height zero of
the native completed characteristic, every nonzero shift with `|d|<1/4` has a
finite original sigma matrix and a real nonzero direction of strictly negative
quadratic form. -/
theorem exists_sigmaMatrix_negative_direction_of_zero
    (d γ : ℝ) (hγ : 0 < γ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ))
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0 := by
  have habs := abs_lt.mp hd₁
  have hdne : d ≠ 0 := abs_pos.mp hd₀
  by_cases hdpos : 0 < d
  · exact exists_sigmaMatrix_negative_direction
      (sigmaMatrix_not_all_psd_of_positive_zero d γ hdpos habs.2 hγ hzero)
  · have hdneg : d < 0 := lt_of_le_of_ne (not_lt.mp hdpos) hdne
    exact exists_sigmaMatrix_negative_direction
      (sigmaMatrix_not_all_psd_of_negative_zero d γ hdneg habs.1 hγ hzero)

#print axioms exists_sigmaMatrix_negative_direction_of_zero

/-! ### CHECKPOINT A — identidade diferencial local (FECHADO)

Para todo `|d|<1/2`, `completedSigmaLogJetGeneratingSeries_radius_pos` fornece raio positivo
para a série dos jets originais; sua soma real e sua extensão complexa analítica estão
formalizadas. A igualdade de somas convergentes, a paridade dos coeficientes e a normalização
`1/4` provam a identidade real da log-derivada. A restrição real de `displacedProductC` tem a
derivada da densidade real, e a diferenciação de `log` produz a equação para a densidade.

`displacedProductC_differentialExpression_ofReal_eq_zero_eventually` mostra que a expressão
complexa da EDO zera na reta real perto da origem. Ela é analítica complexa no ponto; zeros
reais que acumulam na origem e o princípio de zeros isolados dão
`displacedProductC_local_differentialEquation`, que prova a EDO complexa numa vizinhança de
zero. Portanto, a obrigação local está fechada sem medida de Hamburger.

Isso ainda não propaga a EDO até o zero deslocado. As hipóteses de zero positivo, a propagação
no domínio e a construção do operador limitado permanecem obrigações posteriores da missão.
O domínio já provado para a anulação em `γ+id` é `0<|d|<1/4`; a identidade local e a
não-anulação na origem valem para `|d|<1/2`. -/

/-! ## Parte 4 — teorema condicional honesto: isolamento da obrigação analítica -/

/-- Deslocamento admissível: estritamente dentro da banda de reflexão. -/
def AdmissibleShift (d : ℝ) : Prop := -(1/2 : ℝ) < d ∧ d < (1/2 : ℝ)

/-- **Fechamento condicional (sem hipótese de sinal).** Dadas as duas obrigações analíticas
isoladas — (`hpoleFromZero`) que o nó deslocado não-real `(γ+id)²` é um polo não-removível
`Pole` da função geradora dos jets; (`hHamburger`) que um polo não-real da geradora é
incompatível com a positividade semidefinida de toda Hankel deslocada (obstrução de
momentos de Hamburger) — um zero de altura positiva força a falha de PSD em ordem finita.

O único insumo usado aqui é o fato PROVADO `shifted_zero_u_im` (`Im((γ+id)²)=2γd≠0`). O
predicado `Pole` fica **abstrato e explícito**: o teorema não assume nada sobre o sinal de
qualquer forma quadrática; a negatividade é **derivada**. -/
theorem offcritical_not_posSemidef_of_zero
    (d γ : ℝ) (hγ : 0 < γ) (hd0 : d ≠ 0)
    {Pole : ℂ → Prop}
    (hpoleFromZero : Pole (((γ : ℂ) + Complex.I * (d : ℂ)) ^ 2))
    (hHamburger : ∀ u : ℂ, u.im ≠ 0 → Pole u →
      ∃ N : ℕ, ¬ (sigmaMatrix d 0 N).PosSemidef) :
    ∃ N : ℕ, ¬ (sigmaMatrix d 0 N).PosSemidef := by
  refine hHamburger _ ?_ hpoleFromZero
  rw [shifted_zero_u_im]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hγ)) hd0

#print axioms finite_partial_sum_eq
#print axioms infinite_geometric_series
#print axioms cauchy_kernel_denominator_zero_nonreal
#print axioms completedSigmaLogJet_quarter_normalization
#print axioms completedSigmaLogJet_eq_logDisplacedProduct
#print axioms completedSigmaLogDensity_analyticAt_origin
#print axioms completedSigmaDensity_even
#print axioms completedSigmaLogDensity_odd_iteratedDeriv_eq_zero
#print axioms displacedProductC_even_ofReal
#print axioms completedSigmaDensity_zero_pos
#print axioms displacedProductC_zero_ne_zero
#print axioms displacedProductC_analyticAt
#print axioms displacedProductC_analyticAt_origin
#print axioms displacedProductC_ne_zero_nhds_zero
#print axioms completedSigmaLogDensity_analyticAt_origin
#print axioms completedSigmaLogJetGeneratingSeries_radius_pos
#print axioms completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt
#print axioms completedSigmaLogDensityDerivativeTaylorSeries_hasFPowerSeriesAt
#print axioms completedSigmaLogDensity_derivative_eq_generatingFunction_eventually
#print axioms completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
#print axioms displacedProductC_deriv_ofReal_eq_density_deriv_eventually
#print axioms completedSigmaDensity_deriv_eq_generatingFunction_mul_eventually
#print axioms completedSigmaLogJetComplexGeneratingFunction_ofReal_eq_eventually
#print axioms displacedProductC_differentialExpression_ofReal_eq_zero_eventually
#print axioms displacedProductC_local_differentialEquation
#print axioms completedSigmaLogJetGeneratingFunction_hasFPowerSeriesAt
#print axioms displacedProductC_ofReal_eq_density
#print axioms displacedProductC_vanishes_at_shifted_zero
#print axioms shifted_zero_u_im
#print axioms pair_negative_direction
#print axioms offcritical_not_posSemidef_of_zero

end
end CarrySigmaObstruction
