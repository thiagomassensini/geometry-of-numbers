import SigmaNeighborhood
import SigmaQuadratic
import Mathlib.Algebra.Field.GeomSum

/-!
# Obstrução off-critical: zero real positivo força direção negativa numa Hankel deslocada

A partir de `completedSigmaLogJet`, `sigmaMatrix` e a identificação central já formalizada
(`sigma_log_jet_center_eq_canonical`, `sigma_moment_form_center`), demonstramos que a
existência de um **zero real positivo** da característica completada obriga, para **todo
deslocamento não nulo admissível**, a existência de uma **direção negativa** em alguma
Hankel deslocada.

A prova é em duas partes, como pedido:

**Parte 1 — identidade da função geradora e o polo não real.**
Um nó `ζ` com peso real `w` gera a sequência de momentos `nodeMoment w ζ n = w·Re(ζⁿ)`.
A soma geradora parcial é o núcleo de Cauchy racional `w·((ζz)^L−1)/(ζz−1)`
(`node_generating_series`), cujo polo está em `z = ζ⁻¹`. Quando `ζ` é não-real, esse polo é
**não-real** (`node_pole_nonreal`). Um par conjugado `ζ, ζ̄` dá a sequência real
`pairMoment w ζ n = 2w·Re(ζⁿ)` (`pairMoment_eq`).

**Parte 2 — obstrução via momentos positivos.**
Sequências de momentos de nós **reais** com pesos positivos têm todas as Hankel PSD. O
contrapositivo é explícito: um par conjugado **não-real** produz uma Hankel 2×2 com
determinante negativo, logo uma direção negativa explícita no vetor `(m₁, −m₀)`
(`pair_negative_direction`, via `det = −8 w³ (Im ζ)² < 0`).

**Capstone.** Um zero real positivo induz, em cada deslocamento não nulo, um par de nós
não-reais numa janela dos jets sigma (`SigmaNonRealNode`), e daí a direção negativa
(`positive_real_zero_forces_negative_direction`). O conteúdo analítico profundo (zero ⟹ nó
não-real nos jets) fica **isolado como hipótese explícita** `hbridge`; não se assume RH,
positividade central, dominância de tilt, contractividade de Green nem certificados de sinal
all-order. É matriz e sinal; a geometria mostra a obstrução *se* o zero existe.
-/

namespace CarrySigmaObstruction
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CPFormal.Analytic.Cp
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Parte 1: a identidade da função geradora e o polo não real -/

/-- Momentos reais de um único nó complexo com peso real: a parte real das potências. -/
def nodeMoment (w : ℝ) (ζ : ℂ) (n : ℕ) : ℝ := w * (ζ ^ n).re

/-- Momentos reais de um par conjugado de nós: `2w·Re(ζⁿ) = w·Re(ζⁿ) + w·Re(ζ̄ⁿ)`. -/
def pairMoment (w : ℝ) (ζ : ℂ) (n : ℕ) : ℝ := 2 * w * (ζ ^ n).re

/-- O par conjugado é genuinamente a soma de dois nós conjugados. -/
theorem pairMoment_eq (w : ℝ) (ζ : ℂ) (n : ℕ) :
    pairMoment w ζ n = nodeMoment w ζ n + nodeMoment w (starRingEnd ℂ ζ) n := by
  unfold pairMoment nodeMoment
  have hc : ((starRingEnd ℂ) ζ ^ n).re = (ζ ^ n).re := by
    rw [← map_pow, Complex.conj_re]
  rw [hc]; ring

/-- **Identidade da função geradora.** A soma geradora parcial dos momentos de um nó é o
núcleo de Cauchy racional, exibindo o polo em `z = ζ⁻¹` (denominador `ζz − 1`). -/
theorem node_generating_series (ζ z : ℂ) (L : ℕ) (hz : ζ * z ≠ 1) :
    ∑ n ∈ Finset.range L, (ζ * z) ^ n = ((ζ * z) ^ L - 1) / (ζ * z - 1) :=
  geom_sum_eq hz L

/-- **O polo não-real.** Para um nó não-real `ζ`, o polo `z = ζ⁻¹` do núcleo de Cauchy é
não-real (anula o denominador e tem parte imaginária não nula). -/
theorem node_pole_nonreal (ζ : ℂ) (hζ : ζ ≠ 0) (hIm : ζ.im ≠ 0) :
    ζ * ζ⁻¹ = 1 ∧ (ζ⁻¹).im ≠ 0 := by
  refine ⟨mul_inv_cancel₀ hζ, ?_⟩
  rw [Complex.inv_im]
  exact div_ne_zero (neg_ne_zero.mpr hIm) (Complex.normSq_pos.mpr hζ).ne'

/-! ## Parte 2: a obstrução via momentos positivos -/

/-- A forma de momentos sigma é a forma quadrática da Hankel deslocada `sigmaMatrix`. -/
theorem sigmaMomentForm_eq_quadratic (d : ℝ) (s N : ℕ) (v : Fin N → ℝ) :
    sigmaMomentForm d s N v = v ⬝ᵥ (sigmaMatrix d s N *ᵥ v) := by
  unfold sigmaMomentForm sigmaMatrix sourceMomentMatrix
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Obstrução de momentos positivos (kernel 2×2).** A sequência de momentos de um par
conjugado não-real com peso positivo tem uma Hankel 2×2 com determinante negativo, logo o
vetor `(m₁, −m₀)` é uma direção negativa explícita: `m₀·(m₀m₂ − m₁²) = −8 w³ (Im ζ)² < 0`. -/
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

/-! ## O deslocamento admissível, o zero real positivo e o nó não-real -/

/-- Deslocamento admissível: estritamente dentro da banda de reflexão. -/
def AdmissibleShift (d : ℝ) : Prop := -(1/2 : ℝ) < d ∧ d < (1/2 : ℝ)

/-- **Zero real positivo** da característica completada, em coordenadas sigma: um zero de
altura nula (`t = 0`) num deslocamento estritamente positivo (`x > 0`). -/
def SigmaPositiveRealZero : Prop :=
  ∃ x : ℝ, 0 < x ∧ completedNativeOperatorCharacteristic (displacedHeight x 0) = 0

/-- **Nó não-real nos jets sigma.** No deslocamento `d`, uma janela de comprimento 2 dos
jets sigma coincide com a sequência de momentos de um par conjugado não-real de peso
positivo. É a consequência local concreta de um zero real positivo — não é RH, positividade
central, dominância de tilt, contractividade de Green nem certificado all-order. -/
def SigmaNonRealNode (d : ℝ) : Prop :=
  ∃ (s : ℕ) (w : ℝ) (ζ : ℂ), 0 < w ∧ ζ.im ≠ 0 ∧
    ∀ i j : Fin 2, completedSigmaLogJet d (i.val + j.val + s) = pairMoment w ζ (i.val + j.val)

/-- **A obstrução.** Um nó não-real nos jets sigma produz uma direção negativa explícita
numa Hankel deslocada. -/
theorem sigma_nonreal_node_negative_direction (d : ℝ) (h : SigmaNonRealNode d) :
    ∃ (s N : ℕ) (v : Fin N → ℝ), sigmaMomentForm d s N v < 0 := by
  obtain ⟨s, w, ζ, hw, hIm, hmatch⟩ := h
  refine ⟨s, 2, ![pairMoment w ζ 1, -(pairMoment w ζ 0)], ?_⟩
  have hval : sigmaMomentForm d s 2 ![pairMoment w ζ 1, -(pairMoment w ζ 0)]
      = ∑ i : Fin 2, ∑ j : Fin 2,
          (![pairMoment w ζ 1, -(pairMoment w ζ 0)]) i *
          (![pairMoment w ζ 1, -(pairMoment w ζ 0)]) j * pairMoment w ζ (i.val + j.val) := by
    unfold sigmaMomentForm
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hmatch i j]
  rw [hval]
  have key := pair_negative_direction w ζ hw hIm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Nat.add_zero, Nat.zero_add, Nat.reduceAdd]
  nlinarith [key]

/-! ## O capstone -/

/-- **Zero real positivo força direção negativa.** Dada a ponte analítica que, de um zero
real positivo, extrai um nó não-real nos jets sigma em cada deslocamento não nulo admissível,
conclui-se uma direção negativa em alguma Hankel deslocada, para todo tal deslocamento. -/
theorem positive_real_zero_forces_negative_direction
    (hzero : SigmaPositiveRealZero)
    (hbridge : SigmaPositiveRealZero →
      ∀ d : ℝ, AdmissibleShift d → d ≠ 0 → SigmaNonRealNode d) :
    ∀ d : ℝ, AdmissibleShift d → d ≠ 0 →
      ∃ (s N : ℕ) (v : Fin N → ℝ), sigmaMomentForm d s N v < 0 :=
  fun d hd hd0 => sigma_nonreal_node_negative_direction d (hbridge hzero d hd hd0)

/-- Versão explícita na matriz: a direção negativa é uma direção negativa da própria
Hankel deslocada `sigmaMatrix d s N`. -/
theorem positive_real_zero_forces_negative_hankel_direction
    (hzero : SigmaPositiveRealZero)
    (hbridge : SigmaPositiveRealZero →
      ∀ d : ℝ, AdmissibleShift d → d ≠ 0 → SigmaNonRealNode d) :
    ∀ d : ℝ, AdmissibleShift d → d ≠ 0 →
      ∃ (s N : ℕ) (v : Fin N → ℝ), v ⬝ᵥ (sigmaMatrix d s N *ᵥ v) < 0 := by
  intro d hd hd0
  obtain ⟨s, N, v, hv⟩ :=
    positive_real_zero_forces_negative_direction hzero hbridge d hd hd0
  exact ⟨s, N, v, by rwa [← sigmaMomentForm_eq_quadratic]⟩

#print axioms node_pole_nonreal
#print axioms pair_negative_direction
#print axioms sigma_nonreal_node_negative_direction
#print axioms positive_real_zero_forces_negative_hankel_direction

end
end CarrySigmaObstruction
