import SigmaNeighborhood
import SigmaQuadratic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef

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
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CPFormal.Analytic.Cp
open scoped BigOperators Matrix
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
#print axioms displacedProductC_ofReal_eq_density
#print axioms displacedProductC_vanishes_at_shifted_zero
#print axioms shifted_zero_u_im
#print axioms pair_negative_direction
#print axioms offcritical_not_posSemidef_of_zero

end
end CarrySigmaObstruction
