import HankelLimitObject
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Finsupp.SMulWithZero

/-!
# A forma bilinear polarizada do objeto-limite

O objeto-limite `hankelForm h s` (`HankelLimitObject`) é uma forma **quadrática** em
`ℕ →₀ ℝ`. Aqui exibimos sua **polarização**: a forma bilinear simétrica

`hankelBilin h s x y = ∑_{i,j} x i · h(i+j+s) · y j`

cujo valor na diagonal recupera a forma quadrática, e que é genuinamente bilinear.

* `hankelBilin_self`: `hankelBilin h s x x = hankelForm h s x` (diagonal = quadrática).
* `hankelBilin_comm`: simetria `hankelBilin h s x y = hankelBilin h s y x` (o núcleo de
  Hankel `h(i+j+s)` é simétrico em `i,j`).
* `hankelBilin_add_left/right`, `hankelBilin_smul_left/right`: bilinearidade plena.
* `hankelForm_smul`: `hankelForm h s (c • x) = c² · hankelForm h s x` — a câmera escala a
  forma por `c²`, logo **preserva o sinal** (é o tema escala/sinal no limite).
* `hankelForm_add`: a **identidade de polarização**
  `hankelForm h s (x+y) = hankelForm h s x + hankelForm h s y + 2 · hankelBilin h s x y`.
* `hankelBilin_sq_le`: **Cauchy–Schwarz do objeto-limite** — se a forma-limite é positiva
  semidefinida (`∀ z, 0 ≤ hankelForm h s z`), então
  `hankelBilin h s x y ² ≤ hankelForm h s x · hankelForm h s y`.

Matriz e sinal, forma bilinear; nada de zeros, nada de RH. Auto-contido; não modifica nada.
-/

namespace CarryTiltSlice
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Forma bilinear polarizada** do núcleo de Hankel. -/
def hankelBilin (h : ℕ → ℝ) (s : ℕ) (x y : ℕ →₀ ℝ) : ℝ :=
  x.sum fun i xi => y.sum fun j yj => xi * h (i + j + s) * yj

/-- A forma quadrática como soma finita sobre qualquer finset que contém o suporte. -/
theorem hankelForm_eq_sum (h : ℕ → ℝ) (s : ℕ) (z : ℕ →₀ ℝ) {F : Finset ℕ}
    (hF : z.support ⊆ F) :
    hankelForm h s z = ∑ i ∈ F, ∑ j ∈ F, z i * h (i + j + s) * z j := by
  unfold hankelForm
  simp only [Finsupp.sum]
  rw [Finset.sum_subset hF]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_subset hF]
    intro j _ hj
    rw [Finsupp.notMem_support_iff.mp hj, mul_zero]
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    simp

/-- A forma bilinear como soma finita sobre qualquer finset que contém ambos os suportes. -/
theorem hankelBilin_eq_sum (h : ℕ → ℝ) (s : ℕ) (x y : ℕ →₀ ℝ) {F : Finset ℕ}
    (hx : x.support ⊆ F) (hy : y.support ⊆ F) :
    hankelBilin h s x y = ∑ i ∈ F, ∑ j ∈ F, x i * h (i + j + s) * y j := by
  unfold hankelBilin
  simp only [Finsupp.sum]
  rw [Finset.sum_subset hx]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_subset hy]
    intro j _ hj
    rw [Finsupp.notMem_support_iff.mp hj, mul_zero]
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    simp

/-- **Diagonal = quadrática.** A polarização avaliada na diagonal recupera a forma
quadrática do objeto-limite. -/
theorem hankelBilin_self (h : ℕ → ℝ) (s : ℕ) (x : ℕ →₀ ℝ) :
    hankelBilin h s x x = hankelForm h s x := rfl

/-- **Simetria.** O núcleo de Hankel `h(i+j+s)` é simétrico em `i,j`. -/
theorem hankelBilin_comm (h : ℕ → ℝ) (s : ℕ) (x y : ℕ →₀ ℝ) :
    hankelBilin h s x y = hankelBilin h s y x := by
  rw [hankelBilin_eq_sum h s x y (F := x.support ∪ y.support)
        Finset.subset_union_left Finset.subset_union_right,
      hankelBilin_eq_sum h s y x (F := x.support ∪ y.support)
        Finset.subset_union_right Finset.subset_union_left]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.add_comm a b]
  ring

/-- Aditividade no argumento direito. -/
theorem hankelBilin_add_right (h : ℕ → ℝ) (s : ℕ) (x y z : ℕ →₀ ℝ) :
    hankelBilin h s x (y + z) = hankelBilin h s x y + hankelBilin h s x z := by
  have hx : x.support ⊆ x.support ∪ (y.support ∪ z.support) := Finset.subset_union_left
  have hy : y.support ⊆ x.support ∪ (y.support ∪ z.support) :=
    fun a ha => Finset.mem_union_right _ (Finset.mem_union_left _ ha)
  have hz : z.support ⊆ x.support ∪ (y.support ∪ z.support) :=
    fun a ha => Finset.mem_union_right _ (Finset.mem_union_right _ ha)
  have hyz : (y + z).support ⊆ x.support ∪ (y.support ∪ z.support) :=
    fun a ha => Finset.mem_union_right _ (Finsupp.support_add ha)
  rw [hankelBilin_eq_sum h s x (y + z) hx hyz,
      hankelBilin_eq_sum h s x y hx hy,
      hankelBilin_eq_sum h s x z hx hz, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finsupp.add_apply]
  ring

/-- Homogeneidade no argumento direito. -/
theorem hankelBilin_smul_right (h : ℕ → ℝ) (s : ℕ) (c : ℝ) (x y : ℕ →₀ ℝ) :
    hankelBilin h s x (c • y) = c * hankelBilin h s x y := by
  have hx : x.support ⊆ x.support ∪ y.support := Finset.subset_union_left
  have hy : y.support ⊆ x.support ∪ y.support := Finset.subset_union_right
  have hcy : (c • y).support ⊆ x.support ∪ y.support :=
    fun a ha => hy (Finsupp.support_smul ha)
  rw [hankelBilin_eq_sum h s x (c • y) hx hcy,
      hankelBilin_eq_sum h s x y hx hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finsupp.smul_apply, smul_eq_mul]
  ring

/-- Aditividade no argumento esquerdo (via simetria). -/
theorem hankelBilin_add_left (h : ℕ → ℝ) (s : ℕ) (x y z : ℕ →₀ ℝ) :
    hankelBilin h s (x + y) z = hankelBilin h s x z + hankelBilin h s y z := by
  rw [hankelBilin_comm, hankelBilin_add_right, hankelBilin_comm h s z x,
      hankelBilin_comm h s z y]

/-- Homogeneidade no argumento esquerdo (via simetria). -/
theorem hankelBilin_smul_left (h : ℕ → ℝ) (s : ℕ) (c : ℝ) (x y : ℕ →₀ ℝ) :
    hankelBilin h s (c • x) y = c * hankelBilin h s x y := by
  rw [hankelBilin_comm, hankelBilin_smul_right, hankelBilin_comm h s y x]

/-- **Escala da câmera.** A forma-limite escala por `c²` — logo o sinal é invariante. -/
theorem hankelForm_smul (h : ℕ → ℝ) (s : ℕ) (c : ℝ) (x : ℕ →₀ ℝ) :
    hankelForm h s (c • x) = c ^ 2 * hankelForm h s x := by
  rw [← hankelBilin_self, hankelBilin_smul_left, hankelBilin_smul_right, hankelBilin_self]
  ring

/-- **Identidade de polarização.** A forma quadrática do objeto-limite é polarizada pela
forma bilinear simétrica. -/
theorem hankelForm_add (h : ℕ → ℝ) (s : ℕ) (x y : ℕ →₀ ℝ) :
    hankelForm h s (x + y)
      = hankelForm h s x + hankelForm h s y + 2 * hankelBilin h s x y := by
  rw [← hankelBilin_self, hankelBilin_add_left, hankelBilin_add_right,
      hankelBilin_add_right, hankelBilin_self, hankelBilin_self,
      hankelBilin_comm h s y x]
  ring

/-- A forma-limite num deslocamento `x + t • y` é um trinômio em `t` com coeficiente
dominante `hankelForm h s y`. -/
theorem hankelForm_add_smul (h : ℕ → ℝ) (s : ℕ) (x y : ℕ →₀ ℝ) (t : ℝ) :
    hankelForm h s (x + t • y)
      = hankelForm h s y * (t * t) + 2 * hankelBilin h s x y * t + hankelForm h s x := by
  rw [hankelForm_add, hankelForm_smul, hankelBilin_smul_right]
  ring

/-- **Cauchy–Schwarz do objeto-limite.** Se a forma-limite é positiva semidefinida, a
forma bilinear polarizada satisfaz a desigualdade de Cauchy–Schwarz. -/
theorem hankelBilin_sq_le (h : ℕ → ℝ) (s : ℕ)
    (hpos : ∀ z : ℕ →₀ ℝ, 0 ≤ hankelForm h s z) (x y : ℕ →₀ ℝ) :
    hankelBilin h s x y ^ 2 ≤ hankelForm h s x * hankelForm h s y := by
  have hquad : ∀ t : ℝ,
      0 ≤ hankelForm h s y * (t * t) + 2 * hankelBilin h s x y * t + hankelForm h s x := by
    intro t
    rw [← hankelForm_add_smul]
    exact hpos _
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith [hd]

#print axioms hankelBilin_self
#print axioms hankelForm_add
#print axioms hankelBilin_sq_le

end
end CarryTiltSlice
