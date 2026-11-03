import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import MomentComplexification

/-!
# Núcleo analítico do Checkpoint B: cota de razão por log-convexidade

Lema geral, autocontido e reutilizável (independente da fonte sigma), que é o coração do
Checkpoint B da rota de construção do operador auto-adjunto limitado (GNS sem Hamburger):

Se `a : ℕ → ℝ` é não-negativa, **log-convexa** (`aₙ₊₁² ≤ aₙ·aₙ₊₂`) e tem **crescimento
exponencial controlado** (`aₙ ≤ C·(R²)ⁿ` com `R>0`), então `a₁ ≤ R²·a₀`.

Aplicado a `aₙ = L(X^{2n} p²)` (que é log-convexa por Cauchy–Schwarz da Hankel PSD, e
limitada exponencialmente por H2), isto dá exatamente `L(X²p²) ≤ R²·L(p²)` — a desigualdade
de multiplicação limitada. A instanciação à fonte (funcional `L` sobre `Polynomial ℝ`,
positividade de Hankel ⇒ `aₙ≥0` e log-convexidade, cota de Cauchy ⇒ H2) permanece a
formalizar; este arquivo entrega o núcleo matemático verificado.
-/

namespace CarryMomentLogConvex
open Filter
open scoped BigOperators Matrix
set_option autoImplicit false

/-- The finite Hankel matrix associated with a real sequence. -/
def hankelMatrix (h : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => h (i.val + j.val)

/-- The moment functional on real polynomials, defined from the original sequence. -/
def momentFunctional (h : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  p.sum fun n a => a * h n

/-- The functional is additive. -/
theorem momentFunctional_add (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentFunctional h (p + q) = momentFunctional h p + momentFunctional h q := by
  unfold momentFunctional
  apply Polynomial.sum_add_index
  · intro n
    simp
  · intro n a b
    simp only [add_mul]

/-- Monomials are sent to the corresponding moments. -/
theorem momentFunctional_C_mul_X_pow (h : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    momentFunctional h (Polynomial.C a * Polynomial.X ^ n) = a * h n := by
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  simp [momentFunctional, Polynomial.sum_monomial_index]

/-- The moment functional commutes with finite sums of polynomials. -/
theorem momentFunctional_sum {α : Type*} [DecidableEq α] (h : ℕ → ℝ)
    (s : Finset α) (p : α → Polynomial ℝ) :
    momentFunctional h (∑ i ∈ s, p i) = ∑ i ∈ s, momentFunctional h (p i) := by
  induction s using Finset.induction_on with
  | empty => simp [momentFunctional]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, momentFunctional_add, ih]

/-- Scalar linearity of the moment functional. -/
theorem momentFunctional_C_mul (h : ℕ → ℝ) (a : ℝ) (p : Polynomial ℝ) :
    momentFunctional h (Polynomial.C a * p) = a * momentFunctional h p := by
  have hp := p.as_sum_range_C_mul_X_pow
  calc
    momentFunctional h (Polynomial.C a * p) = momentFunctional h
        (Polynomial.C a *
          ∑ i ∈ Finset.range (p.natDegree + 1),
            Polynomial.C (p.coeff i) * Polynomial.X ^ i) := by rw [← hp]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          a * (p.coeff i * h i) := by
      rw [Finset.mul_sum, momentFunctional_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hmono :
          Polynomial.C a * (Polynomial.C (p.coeff i) * Polynomial.X ^ i) =
            Polynomial.C (a * p.coeff i) * Polynomial.X ^ i := by
        calc
          _ = (Polynomial.C a * Polynomial.C (p.coeff i)) * Polynomial.X ^ i := by ac_rfl
          _ = Polynomial.C (a * p.coeff i) * Polynomial.X ^ i := by rw [← map_mul]
      rw [hmono, momentFunctional_C_mul_X_pow]
      ring
    _ = a * momentFunctional h p := by
      have hLp : momentFunctional h p =
          ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * h i := by
        calc
          momentFunctional h p = momentFunctional h
              (∑ i ∈ Finset.range (p.natDegree + 1),
                Polynomial.C (p.coeff i) * Polynomial.X ^ i) := by rw [← hp]
          _ = ∑ i ∈ Finset.range (p.natDegree + 1),
                momentFunctional h (Polynomial.C (p.coeff i) * Polynomial.X ^ i) :=
              momentFunctional_sum h _ _
          _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * h i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [momentFunctional_C_mul_X_pow]
      rw [← Finset.mul_sum, hLp]

#print axioms momentFunctional_C_mul

/-- Applying the functional to a product expands into the finite Hankel quadratic kernel.
The cutoffs are the original polynomial degrees; no auxiliary moment sequence is used. -/
theorem momentFunctional_mul_eq_double_sum (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentFunctional h (p * q) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ∑ j ∈ Finset.range (q.natDegree + 1),
          p.coeff i * q.coeff j * h (i + j) := by
  have hp := p.as_sum_range_C_mul_X_pow
  have hq := q.as_sum_range_C_mul_X_pow
  calc
    momentFunctional h (p * q) = momentFunctional h
        ((∑ i ∈ Finset.range (p.natDegree + 1),
          Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
          (∑ j ∈ Finset.range (q.natDegree + 1),
          Polynomial.C (q.coeff j) * Polynomial.X ^ j)) := by rw [← hp, ← hq]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (q.natDegree + 1),
            p.coeff i * q.coeff j * h (i + j) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [momentFunctional_sum]
      simp_rw [momentFunctional_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hmono :
          (Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
              (Polynomial.C (q.coeff j) * Polynomial.X ^ j) =
            Polynomial.C (p.coeff i * q.coeff j) * Polynomial.X ^ (i + j) := by
        calc
          _ = (Polynomial.C (p.coeff i) * Polynomial.C (q.coeff j)) *
              (Polynomial.X ^ i * Polynomial.X ^ j) := by ac_rfl
          _ = Polynomial.C (p.coeff i * q.coeff j) * Polynomial.X ^ (i + j) := by
            simp only [map_mul, pow_add]
      rw [hmono, momentFunctional_C_mul_X_pow]

#print axioms momentFunctional_mul_eq_double_sum

/-- Shifted product expansion, retaining the original moments `h (m+i+j)`. -/
theorem momentFunctional_X_pow_mul_eq_double_sum (h : ℕ → ℝ) (m : ℕ)
    (p q : Polynomial ℝ) :
    momentFunctional h (Polynomial.X ^ m * (p * q)) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ∑ j ∈ Finset.range (q.natDegree + 1),
          p.coeff i * q.coeff j * h (m + i + j) := by
  have hp := p.as_sum_range_C_mul_X_pow
  have hq := q.as_sum_range_C_mul_X_pow
  have hexpand :
      Polynomial.X ^ m *
          ((∑ i ∈ Finset.range (p.natDegree + 1),
              Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
            ∑ j ∈ Finset.range (q.natDegree + 1),
              Polynomial.C (q.coeff j) * Polynomial.X ^ j) =
        ∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (q.natDegree + 1),
            Polynomial.X ^ m *
              ((Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
                (Polynomial.C (q.coeff j) * Polynomial.X ^ j)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  calc
    momentFunctional h (Polynomial.X ^ m * (p * q)) = momentFunctional h
        (Polynomial.X ^ m *
          ((∑ i ∈ Finset.range (p.natDegree + 1),
              Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
            ∑ j ∈ Finset.range (q.natDegree + 1),
              Polynomial.C (q.coeff j) * Polynomial.X ^ j)) := by rw [← hp, ← hq]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (q.natDegree + 1),
            p.coeff i * q.coeff j * h (m + i + j) := by
      rw [hexpand, momentFunctional_sum]
      simp_rw [momentFunctional_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hmono :
          Polynomial.X ^ m *
              ((Polynomial.C (p.coeff i) * Polynomial.X ^ i) *
                (Polynomial.C (q.coeff j) * Polynomial.X ^ j)) =
            Polynomial.C (p.coeff i * q.coeff j) * Polynomial.X ^ (m + i + j) := by
        calc
          _ = (Polynomial.C (p.coeff i) * Polynomial.C (q.coeff j)) *
              (Polynomial.X ^ m * Polynomial.X ^ i * Polynomial.X ^ j) := by ac_rfl
          _ = Polynomial.C (p.coeff i * q.coeff j) *
              Polynomial.X ^ (m + i + j) := by
            rw [map_mul, ← pow_add, ← pow_add]
      rw [hmono, momentFunctional_C_mul_X_pow]

#print axioms momentFunctional_X_pow_mul_eq_double_sum

/-- A positive semidefinite Hankel matrix makes every finite polynomial-square
quadratic form nonnegative. This is the coefficient-vector form of H1 and does
not assume a measure or an operator representation. -/
theorem hankel_quadratic_nonneg {h : ℕ → ℝ} {N : ℕ}
    (hH : (hankelMatrix h N).PosSemidef) (c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * h (i.val + j.val) := by
  have hq := hH.dotProduct_mulVec_nonneg c
  have heq : star c ⬝ᵥ (hankelMatrix h N *ᵥ c) =
      ∑ i, ∑ j, c i * c j * h (i.val + j.val) := by
    simp [dotProduct, Matrix.mulVec, hankelMatrix, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [heq] at hq
  exact hq

#print axioms hankel_quadratic_nonneg

/-- H1 implies positivity of the moment functional on polynomial squares. -/
theorem momentFunctional_square_nonneg {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p : Polynomial ℝ) :
    0 ≤ momentFunctional h (p ^ 2) := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := fun i => p.coeff i.val
  have hquad := hankel_quadratic_nonneg (hH N) c
  rw [pow_two, momentFunctional_mul_eq_double_sum]
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range N, p.coeff i * p.coeff j * h (i + j)) =
        ∑ j : Fin N, p.coeff i * p.coeff j * h (i + j) := by
    symm
    exact Fin.sum_univ_eq_sum_range (fun j => p.coeff i * p.coeff j * h (i + j)) N
  have houter :
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        p.coeff i * p.coeff j * h (i + j)) =
      ∑ i : Fin N, ∑ j : Fin N,
        p.coeff i * p.coeff j * h (i.val + j.val) := by
    calc
      _ = ∑ i ∈ Finset.range N, ∑ j : Fin N,
          p.coeff i * p.coeff j * h (i + j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hinner i
      _ = ∑ i : Fin N, ∑ j : Fin N,
          p.coeff i * p.coeff j * h (i.val + j.val) := by
        symm
        exact Fin.sum_univ_eq_sum_range
          (fun i => ∑ j : Fin N, p.coeff i * p.coeff j * h (i + j)) N
  have hquad' :
      0 ≤ ∑ i : Fin N, ∑ j : Fin N,
        p.coeff i * p.coeff j * h (i.val + j.val) := by
    simpa [c] using hquad
  simpa [N, houter] using hquad'

#print axioms momentFunctional_square_nonneg

/-- The symmetric bilinear form induced by the moment functional. -/
noncomputable def momentB (h : ℕ → ℝ) (p q : Polynomial ℝ) : ℝ :=
  momentFunctional h (p * q)

/-- The associated quadratic form. -/
noncomputable def momentQ (h : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  momentFunctional h (p ^ 2)

/-- Cauchy--Schwarz for the Hankel form, derived from positivity on squares. -/
theorem momentB_sq_le_momentQ_mul {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p q : Polynomial ℝ) :
    (momentB h p q) ^ 2 ≤ momentQ h p * momentQ h q := by
  have hquad (t : ℝ) :
      0 ≤ momentQ h p + 2 * t * momentB h p q + t ^ 2 * momentQ h q := by
    have hpoly :
        (p + Polynomial.C t * q) ^ 2 =
          p ^ 2 + Polynomial.C (2 * t) * (p * q) + Polynomial.C (t ^ 2) * q ^ 2 := by
      rw [pow_two]
      simp only [map_mul, map_pow, map_ofNat]
      ring
    have hn := momentFunctional_square_nonneg hH (p + Polynomial.C t * q)
    rw [hpoly, momentFunctional_add, momentFunctional_add,
      momentFunctional_C_mul, momentFunctional_C_mul] at hn
    simpa [momentB, momentQ] using hn
  by_cases hq : momentQ h q = 0
  · have hp := hquad 1
    have hm := hquad (-1)
    simp [hq] at hp hm
    by_contra hx
    have hx' : momentB h p q ≠ 0 := by
      intro hz
      apply hx
      rw [hz, hq]
      simp
    have ht := hquad (-(momentQ h p + 1) / (2 * momentB h p q))
    simp [hq] at ht
    field_simp [hx'] at ht
    nlinarith
  · have hqpos : 0 < momentQ h q := lt_of_le_of_ne
      (momentFunctional_square_nonneg hH q) (Ne.symm hq)
    have h := hquad (-(momentB h p q) / momentQ h q)
    field_simp [hqpos.ne'] at h
    nlinarith

#print axioms momentB_sq_le_momentQ_mul

/-- A zero-norm polynomial is orthogonal to every polynomial. -/
theorem momentB_eq_zero_of_momentQ_eq_zero {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) {p q : Polynomial ℝ}
    (hp : momentQ h p = 0) : momentB h p q = 0 := by
  have hcs := momentB_sq_le_momentQ_mul hH p q
  rw [hp, zero_mul] at hcs
  nlinarith [sq_nonneg (momentB h p q)]

#print axioms momentB_eq_zero_of_momentQ_eq_zero

/-- Shift the polynomial by `X^n` inside the Hankel quadratic form. -/
noncomputable def shiftedMomentQ (h : ℕ → ℝ) (p : Polynomial ℝ) (n : ℕ) : ℝ :=
  momentQ h (Polynomial.X ^ n * p)

/-- Every term of the shifted quadratic sequence is nonnegative. -/
theorem shiftedMomentQ_nonneg {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p : Polynomial ℝ) (n : ℕ) :
    0 ≤ shiftedMomentQ h p n := by
  exact momentFunctional_square_nonneg hH (Polynomial.X ^ n * p)

#print axioms shiftedMomentQ_nonneg

/-- The shifted quadratic sequence is log-convex, by Cauchy--Schwarz. -/
theorem shiftedMomentQ_logConvex {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p : Polynomial ℝ) (n : ℕ) :
    shiftedMomentQ h p (n + 1) ^ 2 ≤
      shiftedMomentQ h p n * shiftedMomentQ h p (n + 2) := by
  have hcs := momentB_sq_le_momentQ_mul hH
      (Polynomial.X ^ n * p) (Polynomial.X ^ (n + 2) * p)
  have hprod :
      (Polynomial.X ^ n * p) * (Polynomial.X ^ (n + 2) * p) =
        (Polynomial.X ^ (n + 1) * p) ^ 2 := by
    have hx : (Polynomial.X : Polynomial ℝ) ^ n * Polynomial.X ^ (n + 2) =
        Polynomial.X ^ (n + 1) * Polynomial.X ^ (n + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc
      _ = (Polynomial.X ^ n * Polynomial.X ^ (n + 2)) * (p * p) := by ring
      _ = (Polynomial.X ^ (n + 1) * Polynomial.X ^ (n + 1)) * (p * p) := by rw [hx]
      _ = (Polynomial.X ^ (n + 1) * p) ^ 2 := by rw [pow_two]; ring
  have hleft : momentB h (Polynomial.X ^ n * p) (Polynomial.X ^ (n + 2) * p) =
      shiftedMomentQ h p (n + 1) := by
    change momentFunctional h _ = momentFunctional h _
    rw [hprod]
  have hright : momentQ h (Polynomial.X ^ n * p) = shiftedMomentQ h p n := rfl
  have hlast : momentQ h (Polynomial.X ^ (n + 2) * p) = shiftedMomentQ h p (n + 2) := rfl
  rw [hleft, hright, hlast] at hcs
  exact hcs

#print axioms shiftedMomentQ_logConvex

/-- Finite coefficient formula for the shifted quadratic sequence. -/
theorem shiftedMomentQ_eq_double_sum (h : ℕ → ℝ) (p : Polynomial ℝ) (n : ℕ) :
    shiftedMomentQ h p n =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        ∑ j ∈ Finset.range (p.natDegree + 1),
          p.coeff i * p.coeff j * h (2 * n + i + j) := by
  have hpoly :
      (Polynomial.X ^ n * p) ^ 2 = Polynomial.X ^ (2 * n) * (p * p) := by
    calc
      _ = (Polynomial.X ^ n * Polynomial.X ^ n) * (p * p) := by rw [pow_two]; ring
      _ = Polynomial.X ^ (2 * n) * (p * p) := by
        rw [← pow_add]
        congr 1
        rw [two_mul]
  calc
    shiftedMomentQ h p n = momentFunctional h ((Polynomial.X ^ n * p) ^ 2) := rfl
    _ = momentFunctional h (Polynomial.X ^ (2 * n) * (p * p)) := by rw [hpoly]
    _ = _ := momentFunctional_X_pow_mul_eq_double_sum h (2 * n) p p

#print axioms shiftedMomentQ_eq_double_sum

/-- H2 gives an exponential bound on the shifted quadratic sequence, with a
constant depending only on the fixed polynomial. -/
theorem shiftedMomentQ_expBounded {h : ℕ → ℝ} (p : Polynomial ℝ)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, shiftedMomentQ h p n ≤ K * (R ^ 2) ^ n := by
  let K : ℝ :=
    ∑ i ∈ Finset.range (p.natDegree + 1),
      ∑ j ∈ Finset.range (p.natDegree + 1),
        |p.coeff i| * |p.coeff j| * (C * R ^ (i + j))
  have hK : 0 ≤ K := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    positivity
  refine ⟨K, hK, ?_⟩
  intro n
  have hterm (i j : ℕ) :
      |p.coeff i * p.coeff j * h (2 * n + i + j)| ≤
        (|p.coeff i| * |p.coeff j| * (C * R ^ (i + j))) * R ^ (2 * n) := by
    have hh := hbound (2 * n + i + j)
    have hcoef : 0 ≤ |p.coeff i| * |p.coeff j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      _ = |p.coeff i| * |p.coeff j| * |h (2 * n + i + j)| := by
        rw [abs_mul, abs_mul]
      _ ≤ |p.coeff i| * |p.coeff j| * (C * R ^ (2 * n + i + j)) :=
        mul_le_mul_of_nonneg_left hh hcoef
      _ = (|p.coeff i| * |p.coeff j| * (C * R ^ (i + j))) * R ^ (2 * n) := by
        rw [show 2 * n + i + j = 2 * n + (i + j) by omega, pow_add]
        ring
  have htri :
      |∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (p.natDegree + 1),
            p.coeff i * p.coeff j * h (2 * n + i + j)| ≤
        ∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (p.natDegree + 1),
            |p.coeff i * p.coeff j * h (2 * n + i + j)| := by
    calc
      _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          |∑ j ∈ Finset.range (p.natDegree + 1),
            p.coeff i * p.coeff j * h (2 * n + i + j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs _ _
  have hsum := calc
      (∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (p.natDegree + 1),
            |p.coeff i * p.coeff j * h (2 * n + i + j)|) ≤
        ∑ i ∈ Finset.range (p.natDegree + 1),
          ∑ j ∈ Finset.range (p.natDegree + 1),
            (|p.coeff i| * |p.coeff j| * (C * R ^ (i + j))) * R ^ (2 * n) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterm i j
      _ = K * R ^ (2 * n) := by
        simp_rw [← Finset.sum_mul]
        rfl
  have ha := shiftedMomentQ_eq_double_sum h p n
  have habs : shiftedMomentQ h p n ≤ |shiftedMomentQ h p n| := le_abs_self _
  calc
    shiftedMomentQ h p n ≤ |shiftedMomentQ h p n| := habs
    _ ≤ K * R ^ (2 * n) := by
      rw [ha]
      exact le_trans htri hsum
    _ = K * (R ^ 2) ^ n := by rw [pow_mul]

#print axioms shiftedMomentQ_expBounded

/-- **Cota de razão por log-convexidade (núcleo do Checkpoint B).** Uma sequência
não-negativa log-convexa com crescimento exponencial limitado satisfaz `a₁ ≤ R²·a₀`.
Sem hipótese de positividade estrita dos termos. -/
theorem logConvex_expBounded_ratio {a : ℕ → ℝ} {C R : ℝ}
    (hpos : ∀ n, 0 ≤ a n)
    (hlogconv : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2))
    (hR : 0 < R)
    (hbound : ∀ n, a n ≤ C * (R ^ 2) ^ n) :
    a 1 ≤ R ^ 2 * a 0 := by
  -- Passo 1: monotonia da razão (sem divisão): `aₙ·a₁ ≤ aₙ₊₁·a₀`.
  have hcross : ∀ n, a n * a 1 ≤ a (n + 1) * a 0 := by
    intro n
    induction n with
    | zero => nlinarith [hpos 0, hpos 1]
    | succ n ih =>
      rcases eq_or_lt_of_le (hpos n) with h0 | hn
      · have hsq : a (n + 1) ^ 2 ≤ 0 := by
          have h := hlogconv n; rw [← h0, zero_mul] at h; exact h
        have han1 : a (n + 1) = 0 := by
          have : a (n + 1) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        rw [han1, zero_mul]
        exact mul_nonneg (hpos (n + 2)) (hpos 0)
      · have key : a n * (a (n + 1) * a 1) ≤ a n * (a (n + 2) * a 0) := by
          nlinarith [mul_le_mul_of_nonneg_right ih (hpos (n + 1)),
            mul_le_mul_of_nonneg_right (hlogconv n) (hpos 0)]
        exact le_of_mul_le_mul_left key hn
  -- Passo 2: cota geométrica inferior: `a₀·a₁ⁿ ≤ aₙ·a₀ⁿ`.
  have hpow : ∀ n, a 0 * a 1 ^ n ≤ a n * a 0 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right ih (hpos 1),
        mul_le_mul_of_nonneg_right (hcross n) (pow_nonneg (hpos 0) n),
        hpos 0, hpos 1, pow_nonneg (hpos 0) n]
  -- Passo 3: conclusão.
  rcases eq_or_lt_of_le (hpos 0) with h0 | h0
  · -- caso degenerado `a₀ = 0`: `a₁² ≤ a₀·a₂ = 0 ⇒ a₁ = 0`.
    have hsq : a 1 ^ 2 ≤ 0 := by
      have h := hlogconv 0; rw [← h0, zero_mul] at h; exact h
    have ha1 : a 1 = 0 := by
      have : a 1 ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [ha1, ← h0, mul_zero]
  · -- caso `a₀ > 0`: contradição exponencial se `a₁ > R²·a₀`.
    by_contra hcon
    rw [not_le] at hcon
    have hRa : 0 < R ^ 2 * a 0 := by positivity
    set r : ℝ := a 1 / (R ^ 2 * a 0) with hr_def
    have hr1 : 1 < r := by
      rw [hr_def, lt_div_iff₀ hRa, one_mul]; exact hcon
    have ha1 : a 1 = r * (R ^ 2 * a 0) := by
      rw [hr_def, div_mul_cancel₀ _ hRa.ne']
    have hb : ∀ n, a 0 * r ^ n ≤ C := by
      intro n
      have hub : a n * a 0 ^ n ≤ C * (R ^ 2 * a 0) ^ n := by
        have h1 : a n * a 0 ^ n ≤ C * (R ^ 2) ^ n * a 0 ^ n :=
          mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg h0.le n)
        calc a n * a 0 ^ n ≤ C * (R ^ 2) ^ n * a 0 ^ n := h1
          _ = C * (R ^ 2 * a 0) ^ n := by rw [mul_pow]; ring
      have hchain : a 0 * a 1 ^ n ≤ C * (R ^ 2 * a 0) ^ n := le_trans (hpow n) hub
      have hexp : a 1 ^ n = r ^ n * (R ^ 2 * a 0) ^ n := by rw [ha1, mul_pow]
      rw [hexp] at hchain
      have hpos_pow : 0 < (R ^ 2 * a 0) ^ n := pow_pos hRa n
      have hfinal : (a 0 * r ^ n) * (R ^ 2 * a 0) ^ n ≤ C * (R ^ 2 * a 0) ^ n := by
        nlinarith [hchain]
      exact le_of_mul_le_mul_right hfinal hpos_pow
    have htend : Tendsto (fun n => a 0 * r ^ n) atTop atTop :=
      Tendsto.const_mul_atTop h0 (tendsto_pow_atTop_atTop_of_one_lt hr1)
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop C).exists
    exact absurd (hb n) (not_le.mpr hn)

#print axioms logConvex_expBounded_ratio

/-- The H1 and H2 moment hypotheses force multiplication by `X` to be bounded
on the polynomial pre-Hilbert space. This is Checkpoint B. -/
theorem momentQ_X_mul_le {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) (p : Polynomial ℝ) :
    momentQ h (Polynomial.X * p) ≤ R ^ 2 * momentQ h p := by
  obtain ⟨K, hK, hKbound⟩ := shiftedMomentQ_expBounded p hC hR hbound
  have hratio := logConvex_expBounded_ratio
    (a := shiftedMomentQ h p) (C := K) (R := R)
    (fun n => shiftedMomentQ_nonneg hH p n)
    (fun n => shiftedMomentQ_logConvex hH p n)
    hR
    hKbound
  simpa [shiftedMomentQ, momentQ] using hratio

#print axioms momentQ_X_mul_le

/-- Quadratic expansion for the Hankel form. -/
theorem momentQ_add (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentQ h (p + q) = momentQ h p + 2 * momentB h p q + momentQ h q := by
  have hpoly : (p + q) ^ 2 = p ^ 2 + Polynomial.C (2 : ℝ) * (p * q) + q ^ 2 := by
    rw [pow_two]
    simp only [map_ofNat]
    ring
  unfold momentQ momentB
  rw [hpoly, momentFunctional_add, momentFunctional_add, momentFunctional_C_mul]

/-- Scaling a polynomial scales its quadratic form by the square of the scalar. -/
theorem momentQ_C_mul (h : ℕ → ℝ) (a : ℝ) (p : Polynomial ℝ) :
    momentQ h (Polynomial.C a * p) = a ^ 2 * momentQ h p := by
  have hpoly : (Polynomial.C a * p) ^ 2 = Polynomial.C (a ^ 2) * p ^ 2 := by
    rw [pow_two]
    calc
      _ = (Polynomial.C a * Polynomial.C a) * (p * p) := by ring
      _ = Polynomial.C (a ^ 2) * p ^ 2 := by
        rw [← map_mul]
        simp only [pow_two]
  unfold momentQ
  rw [hpoly, momentFunctional_C_mul]

/-- The zero-norm polynomials form a submodule, by Cauchy--Schwarz. -/
def momentNullSubmodule (h : ℕ → ℝ)
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) : Submodule ℝ (Polynomial ℝ) where
  carrier := {p | momentQ h p = 0}
  zero_mem' := by simp [momentQ, momentFunctional]
  add_mem' := by
    intro p q hp hq
    have hpQ : momentQ h p = 0 := hp
    have hqQ : momentQ h q = 0 := hq
    have horth := momentB_eq_zero_of_momentQ_eq_zero
      (hH := hH) (p := p) (q := q) hpQ
    change momentQ h (p + q) = 0
    rw [momentQ_add, hpQ, hqQ, horth]
    ring
  smul_mem' := by
    intro a p hp
    change momentQ h (a • p) = 0
    rw [Polynomial.smul_eq_C_mul]
    rw [momentQ_C_mul, hp]
    ring

#print axioms momentNullSubmodule

theorem momentB_add_left (h : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentB h (p + q) r = momentB h p r + momentB h q r := by
  unfold momentB
  rw [add_mul, momentFunctional_add]

theorem momentB_add_right (h : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentB h p (q + r) = momentB h p q + momentB h p r := by
  unfold momentB
  rw [mul_add, momentFunctional_add]

theorem momentB_comm (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentB h p q = momentB h q p := by
  unfold momentB
  rw [mul_comm]

theorem momentB_C_mul_left (h : ℕ → ℝ) (a : ℝ) (p q : Polynomial ℝ) :
    momentB h (Polynomial.C a * p) q = a * momentB h p q := by
  unfold momentB
  calc
    momentFunctional h ((Polynomial.C a * p) * q) =
        momentFunctional h (Polynomial.C a * (p * q)) := by congr 1; ring
    _ = a * momentFunctional h (p * q) := momentFunctional_C_mul h a (p * q)

/-- The Hankel bilinear form descends to the quotient by its null submodule. -/
noncomputable def quotientMomentInner {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    (x y : Polynomial ℝ ⧸ momentNullSubmodule h hH) : ℝ :=
  Quotient.liftOn₂ x y (fun p q => momentB h p q) (by
    intro p q p' q' hp hq
    have hpMem := (QuotientAddGroup.leftRel_apply).mp hp
    have hqMem := (QuotientAddGroup.leftRel_apply).mp hq
    change -p + p' ∈ momentNullSubmodule h hH at hpMem
    change -q + q' ∈ momentNullSubmodule h hH at hqMem
    change momentQ h (-p + p') = 0 at hpMem
    change momentQ h (-q + q') = 0 at hqMem
    have hp0 : momentQ h (-p + p') = 0 := hpMem
    have hq0 : momentQ h (-q + q') = 0 := hqMem
    have hleft := momentB_eq_zero_of_momentQ_eq_zero
      (hH := hH) (p := -p + p') (q := q) hp0
    have hright := momentB_eq_zero_of_momentQ_eq_zero
      (hH := hH) (p := -q + q') (q := p') hq0
    have hright' : momentB h p' (-q + q') = 0 := by
      rw [momentB_comm]
      exact hright
    have hpdecomp : p' = p + (-p + p') := by ring
    have hqdecomp : q' = q + (-q + q') := by ring
    calc
      momentB h p q = momentB h p' q := by
        rw [hpdecomp, momentB_add_left, hleft, add_zero]
      _ = momentB h p' q' := by
        rw [hqdecomp, momentB_add_right, hright', add_zero])

#print axioms quotientMomentInner

@[simp] theorem quotientMomentInner_mk {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p q : Polynomial ℝ) :
    quotientMomentInner hH (Submodule.Quotient.mk p) (Submodule.Quotient.mk q) =
      momentB h p q := rfl

/-- The quotient carries the induced positive definite real inner product core. -/
noncomputable instance quotientMomentInnerProductCore {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    InnerProductSpace.Core ℝ (Polynomial ℝ ⧸ momentNullSubmodule h hH) where
  inner := quotientMomentInner hH
  conj_inner_symm := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      induction y using Submodule.Quotient.induction_on with
      | _ q => simp [quotientMomentInner_mk, momentB_comm]
  re_inner_nonneg := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      have hp := momentFunctional_square_nonneg hH p
      simpa [quotientMomentInner_mk, momentB, momentQ, pow_two] using hp
  add_left := by
    intro x y z
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      induction y using Submodule.Quotient.induction_on with
      | _ q =>
        induction z using Submodule.Quotient.induction_on with
        | _ r =>
          simp only [← Submodule.Quotient.mk_add, quotientMomentInner_mk, momentB_add_left]
  smul_left := by
    intro x y a
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      induction y using Submodule.Quotient.induction_on with
      | _ q =>
        rw [← Submodule.Quotient.mk_smul (momentNullSubmodule h hH) a p]
        simp [quotientMomentInner_mk, Polynomial.smul_eq_C_mul, momentB_C_mul_left]
  definite := by
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      have hp : momentQ h p = 0 := by
        simpa [quotientMomentInner_mk, momentB, momentQ, pow_two] using hx
      change Submodule.Quotient.mk p = Submodule.Quotient.mk 0
      apply (Submodule.Quotient.eq (momentNullSubmodule h hH)).2
      change momentQ h (p - 0) = 0
      simpa using hp

#print axioms quotientMomentInnerProductCore

noncomputable instance quotientMomentSeminormedAddCommGroup {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    SeminormedAddCommGroup (Polynomial ℝ ⧸ momentNullSubmodule h hH) := by
  letI : PreInnerProductSpace.Core ℝ (Polynomial ℝ ⧸ momentNullSubmodule h hH) :=
    (quotientMomentInnerProductCore hH).toCore
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
    (F := Polynomial ℝ ⧸ momentNullSubmodule h hH)

noncomputable instance quotientMomentInnerProductSpace {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    InnerProductSpace ℝ (Polynomial ℝ ⧸ momentNullSubmodule h hH) := by
  letI : PreInnerProductSpace.Core ℝ (Polynomial ℝ ⧸ momentNullSubmodule h hH) :=
    (quotientMomentInnerProductCore hH).toCore
  exact InnerProductSpace.ofCore (𝕜 := ℝ)
    (F := Polynomial ℝ ⧸ momentNullSubmodule h hH)
    (quotientMomentInnerProductCore hH).toCore

/-- Complete Hilbert space obtained from the Hankel polynomial quotient. -/
noncomputable abbrev momentHilbert (h : ℕ → ℝ)
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :=
  UniformSpace.Completion (Polynomial ℝ ⧸ momentNullSubmodule h hH)

#print axioms momentHilbert

theorem momentHilbert_complete (h : ℕ → ℝ)
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    CompleteSpace (momentHilbert h hH) := inferInstance

#print axioms momentHilbert_complete

/-- Multiplication by `X` as a linear map on polynomials. -/
noncomputable def polynomialMulX : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := Polynomial.X * p
  map_add' p q := by ring
  map_smul' a p := by
    simp only [RingHom.id_apply, Polynomial.smul_eq_C_mul]
    ring

/-- H1 and H2 make the null submodule invariant under multiplication by `X`. -/
theorem momentNullSubmodule_mulX_invariant {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    ∀ p ∈ momentNullSubmodule h hH,
      Polynomial.X * p ∈ momentNullSubmodule h hH := by
  intro p hp
  change momentQ h p = 0 at hp
  change momentQ h (Polynomial.X * p) = 0
  have hnonneg := momentFunctional_square_nonneg hH (Polynomial.X * p)
  have hup := momentQ_X_mul_le hH hC hR hbound p
  rw [hp, mul_zero] at hup
  exact le_antisymm hup hnonneg

/-- The polynomial multiplier followed by the quotient map. -/
noncomputable def polynomialMulXToQuotient {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    Polynomial ℝ →ₗ[ℝ] Polynomial ℝ ⧸ momentNullSubmodule h hH :=
  (momentNullSubmodule h hH).mkQ.comp polynomialMulX

/-- Multiplication by `X` descends to the null-space quotient. -/
noncomputable def quotientMulX {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    (Polynomial ℝ ⧸ momentNullSubmodule h hH) →ₗ[ℝ]
      (Polynomial ℝ ⧸ momentNullSubmodule h hH) := by
  apply (momentNullSubmodule h hH).liftQ (polynomialMulXToQuotient hH)
  intro p hp
  change (momentNullSubmodule h hH).mkQ (Polynomial.X * p) = 0
  apply (Submodule.Quotient.eq (momentNullSubmodule h hH)).2
  have hp' : Polynomial.X * p ∈ momentNullSubmodule h hH :=
    momentNullSubmodule_mulX_invariant hH hC hR hbound p hp
  simpa using hp'

#print axioms quotientMulX

@[simp] theorem quotientMulX_mk {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) (p : Polynomial ℝ) :
    quotientMulX hH hC hR hbound (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (Polynomial.X * p) := by
  simp [quotientMulX, Submodule.liftQ_apply, polynomialMulXToQuotient,
    polynomialMulX, Submodule.mkQ_apply]

/-- The quotient norm squared is exactly the original quadratic form. -/
theorem momentQuotient_norm_mk_sq {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) (p : Polynomial ℝ) :
    ‖(Submodule.Quotient.mk p : Polynomial ℝ ⧸ momentNullSubmodule h hH)‖ ^ 2 =
      momentQ h p := by
  rw [← real_inner_self_eq_norm_sq]
  change quotientMomentInner hH (Submodule.Quotient.mk p) (Submodule.Quotient.mk p) =
    momentQ h p
  rw [quotientMomentInner_mk]
  unfold momentB momentQ
  rw [pow_two]

/-- Multiplication by `X` is bounded by `R` on the polynomial quotient. -/
theorem quotientMulX_norm_bound {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (q : Polynomial ℝ ⧸ momentNullSubmodule h hH) :
    ‖quotientMulX hH hC hR hbound q‖ ≤ R * ‖q‖ := by
  induction q using Submodule.Quotient.induction_on with
  | _ p =>
    rw [quotientMulX_mk]
    have hmul := momentQ_X_mul_le hH hC hR hbound p
    have hsq :
        ‖(Submodule.Quotient.mk (Polynomial.X * p) :
          Polynomial ℝ ⧸ momentNullSubmodule h hH)‖ ^ 2 ≤
        (R * ‖(Submodule.Quotient.mk p :
          Polynomial ℝ ⧸ momentNullSubmodule h hH)‖) ^ 2 := by
      rw [mul_pow, momentQuotient_norm_mk_sq, momentQuotient_norm_mk_sq]
      exact hmul
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _))).mp hsq

#print axioms quotientMulX_norm_bound

/-- Continuous multiplication-by-`X` operator on the polynomial quotient. -/
noncomputable def quotientMulXContinuous {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    (Polynomial ℝ ⧸ momentNullSubmodule h hH) →L[ℝ]
      (Polynomial ℝ ⧸ momentNullSubmodule h hH) :=
  LinearMap.mkContinuous (quotientMulX hH hC hR hbound) R
    (quotientMulX_norm_bound hH hC hR hbound)

#print axioms quotientMulXContinuous

/-- Extend multiplication by `X` from the dense polynomial quotient to its Hilbert completion. -/
noncomputable def momentQuotientEmbedding {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :
    (Polynomial ℝ ⧸ momentNullSubmodule h hH) →L[ℝ] momentHilbert h hH :=
  UniformSpace.Completion.toComplL (𝕜 := ℝ)
    (E := Polynomial ℝ ⧸ momentNullSubmodule h hH)

noncomputable def momentHilbertMulX {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    momentHilbert h hH →L[ℝ] momentHilbert h hH := by
  let Q := Polynomial ℝ ⧸ momentNullSubmodule h hH
  let H := momentHilbert h hH
  let e : Q →L[ℝ] H := momentQuotientEmbedding hH
  let f : Q →L[ℝ] H := e.comp (quotientMulXContinuous hH hC hR hbound)
  exact ContinuousLinearMap.extend f e

/-- The completed multiplier agrees with `X` on every polynomial class. -/
theorem momentHilbertMulX_on_quotient {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) (p : Polynomial ℝ) :
    momentHilbertMulX hH hC hR hbound
        (momentQuotientEmbedding hH (Submodule.Quotient.mk p)) =
      momentQuotientEmbedding hH (Submodule.Quotient.mk (Polynomial.X * p)) := by
  let Q := Polynomial ℝ ⧸ momentNullSubmodule h hH
  let e : Q →L[ℝ] momentHilbert h hH := momentQuotientEmbedding hH
  have hdense : DenseRange (e : Q → momentHilbert h hH) := by
    change DenseRange (UniformSpace.Completion.coe' : Q → UniformSpace.Completion Q)
    exact UniformSpace.Completion.denseRange_coe
  have hunif : IsUniformInducing (e : Q → momentHilbert h hH) := by
    change IsUniformInducing (UniformSpace.Completion.coe' : Q → UniformSpace.Completion Q)
    exact UniformSpace.Completion.isUniformInducing_coe Q
  change (ContinuousLinearMap.extend
      (e.comp (quotientMulXContinuous hH hC hR hbound)) e)
      (e (Submodule.Quotient.mk p)) = _
  rw [ContinuousLinearMap.extend_eq
    (e.comp (quotientMulXContinuous hH hC hR hbound)) hdense hunif]
  change e (quotientMulX hH hC hR hbound (Submodule.Quotient.mk p)) =
    e (Submodule.Quotient.mk (Polynomial.X * p))
  rw [quotientMulX_mk]

#print axioms momentHilbertMulX_on_quotient

#print axioms momentHilbertMulX

/-- The extended multiplier intertwines the completion embedding with the quotient map. -/
theorem momentHilbertMulX_coe {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (q : Polynomial ℝ ⧸ momentNullSubmodule h hH) :
    momentHilbertMulX hH hC hR hbound (momentQuotientEmbedding hH q) =
      momentQuotientEmbedding hH (quotientMulX hH hC hR hbound q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ p =>
    simpa [quotientMulX_mk] using
      momentHilbertMulX_on_quotient hH hC hR hbound p

#print axioms momentHilbertMulX_coe

/-- Multiplication by `X` is symmetric on the polynomial quotient. -/
theorem quotientMulX_symmetric {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (p q : Polynomial ℝ ⧸ momentNullSubmodule h hH) :
    inner ℝ (quotientMulX hH hC hR hbound p) q =
      inner ℝ p (quotientMulX hH hC hR hbound q) := by
  induction p using Submodule.Quotient.induction_on with
  | _ a =>
    induction q using Submodule.Quotient.induction_on with
    | _ b =>
      simp only [quotientMulX_mk]
      change quotientMomentInner hH
          (Submodule.Quotient.mk (Polynomial.X * a)) (Submodule.Quotient.mk b) =
        quotientMomentInner hH (Submodule.Quotient.mk a)
          (Submodule.Quotient.mk (Polynomial.X * b))
      rw [quotientMomentInner_mk, quotientMomentInner_mk]
      unfold momentB
      congr 1
      ring

#print axioms quotientMulX_symmetric

/-- The continuous extension remains symmetric on the full Hilbert completion. -/
theorem momentHilbertMulX_symmetric {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (x y : momentHilbert h hH) :
    inner ℝ (momentHilbertMulX hH hC hR hbound x) y =
      inner ℝ x (momentHilbertMulX hH hC hR hbound y) := by
  let P : momentHilbert h hH → momentHilbert h hH → Prop := fun u v =>
    inner ℝ (momentHilbertMulX hH hC hR hbound u) v =
      inner ℝ u (momentHilbertMulX hH hC hR hbound v)
  have hclosed : IsClosed {z : momentHilbert h hH × momentHilbert h hH | P z.1 z.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  change P x y
  refine UniformSpace.Completion.induction_on₂ (p := P) x y hclosed ?_
  intro p q
  change inner ℝ (momentHilbertMulX hH hC hR hbound (p : momentHilbert h hH))
      (q : momentHilbert h hH) =
    inner ℝ (p : momentHilbert h hH)
      (momentHilbertMulX hH hC hR hbound (q : momentHilbert h hH))
  change inner ℝ (momentHilbertMulX hH hC hR hbound (momentQuotientEmbedding hH p))
      (momentQuotientEmbedding hH q) =
    inner ℝ (momentQuotientEmbedding hH p)
      (momentHilbertMulX hH hC hR hbound (momentQuotientEmbedding hH q))
  rw [momentHilbertMulX_coe hH hC hR hbound p,
    momentHilbertMulX_coe hH hC hR hbound q]
  change inner ℝ
      ((quotientMulX hH hC hR hbound p :
        Polynomial ℝ ⧸ momentNullSubmodule h hH) : momentHilbert h hH)
      (q : momentHilbert h hH) =
    inner ℝ (p : momentHilbert h hH)
      ((quotientMulX hH hC hR hbound q :
        Polynomial ℝ ⧸ momentNullSubmodule h hH) : momentHilbert h hH)
  simp only [UniformSpace.Completion.inner_coe]
  exact quotientMulX_symmetric hH hC hR hbound p q

#print axioms momentHilbertMulX_symmetric

/-- The bounded symmetric multiplier is self-adjoint on the complete Hilbert space. -/
theorem momentHilbertMulX_isSelfAdjoint {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    IsSelfAdjoint (momentHilbertMulX hH hC hR hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact momentHilbertMulX_symmetric hH hC hR hbound

#print axioms momentHilbertMulX_isSelfAdjoint

/-- The cyclic vector represented by the constant polynomial `1`. -/
noncomputable def momentHilbertUnit {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) : momentHilbert h hH :=
  momentQuotientEmbedding hH (Submodule.Quotient.mk 1)

/-- Powers of the Hilbert-space multiplier act on the cyclic vector as monomials. -/
theorem momentHilbertMulX_pow_unit {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) (n : ℕ) :
    ((momentHilbertMulX hH hC hR hbound) ^ n) (momentHilbertUnit hH) =
      momentQuotientEmbedding hH
        (Submodule.Quotient.mk (Polynomial.X ^ n)) := by
  induction n with
  | zero => simp [momentHilbertUnit]
  | succ n ih =>
    rw [pow_succ']
    rw [mul_apply_eq_comp, ih]
    rw [momentHilbertMulX_coe, quotientMulX_mk]
    congr 1
    rw [pow_succ]
    ring_nf

#print axioms momentHilbertMulX_pow_unit

/-- The self-adjoint realization reconstructs every original moment. -/
theorem momentHilbert_recovers_moment {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) (n : ℕ) :
      inner ℝ (((momentHilbertMulX hH hC hR hbound) ^ n) (momentHilbertUnit hH))
      (momentHilbertUnit hH) = h n := by
  rw [momentHilbertMulX_pow_unit]
  simp only [momentHilbertUnit, momentQuotientEmbedding,
    UniformSpace.Completion.coe_toComplL,
    UniformSpace.Completion.inner_coe]
  change quotientMomentInner hH (Submodule.Quotient.mk (Polynomial.X ^ n))
      (Submodule.Quotient.mk 1) = h n
  rw [quotientMomentInner_mk]
  unfold momentB
  have hmono : Polynomial.X ^ n * (1 : Polynomial ℝ) =
      Polynomial.C 1 * Polynomial.X ^ n := by simp
  rw [hmono, momentFunctional_C_mul_X_pow]
  norm_num

#print axioms momentHilbert_recovers_moment

/-- Coordinatewise complexification of a bounded real operator. -/
noncomputable def complexifyMomentOperator {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    RealHilbertComplexification E →L[ℂ] RealHilbertComplexification E := by
  let g : RealHilbertComplexification E → RealHilbertComplexification E :=
    fun x => RealHilbertComplexification.mk (T (RealHilbertComplexification.re x))
      (T (RealHilbertComplexification.im x))
  let f : RealHilbertComplexification E →ₗ[ℂ] RealHilbertComplexification E :=
    LinearMap.mk (AddHom.mk g (by
      intro x y
      apply RealHilbertComplexification.ext (E := E)
      · simp [g, T.map_add]
      · simp [g, T.map_add])) (by
      intro z x
      apply RealHilbertComplexification.ext (E := E)
      · simp [g, RealHilbertComplexification.re_smul, map_sub, map_smul]
      · simp [g, RealHilbertComplexification.im_smul, map_add, map_smul])
  refine f.mkContinuous ‖T‖ ?_
  intro x
  have hx : ‖x‖ ^ 2 = ‖RealHilbertComplexification.re x‖ ^ 2 +
      ‖RealHilbertComplexification.im x‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 x
  have hfx : ‖f x‖ ^ 2 = ‖T (RealHilbertComplexification.re x)‖ ^ 2 +
      ‖T (RealHilbertComplexification.im x)‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 (f x)
  have hre := T.le_opNorm (RealHilbertComplexification.re x)
  have him := T.le_opNorm (RealHilbertComplexification.im x)
  have hre_sq : ‖T (RealHilbertComplexification.re x)‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖RealHilbertComplexification.re x‖ ^ 2 := by
    have hnT := norm_nonneg T
    have hnx := norm_nonneg (RealHilbertComplexification.re x)
    have hnTx := norm_nonneg (T (RealHilbertComplexification.re x))
    nlinarith [sq_nonneg (‖T‖ * ‖RealHilbertComplexification.re x‖ -
      ‖T (RealHilbertComplexification.re x)‖)]
  have him_sq : ‖T (RealHilbertComplexification.im x)‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖RealHilbertComplexification.im x‖ ^ 2 := by
    have hnT := norm_nonneg T
    have hnx := norm_nonneg (RealHilbertComplexification.im x)
    have hnTx := norm_nonneg (T (RealHilbertComplexification.im x))
    nlinarith [sq_nonneg (‖T‖ * ‖RealHilbertComplexification.im x‖ -
      ‖T (RealHilbertComplexification.im x)‖)]
  have hsq : ‖f x‖ ^ 2 ≤ (‖T‖ * ‖x‖) ^ 2 := by
    rw [hfx, mul_pow, hx]
    nlinarith [hre_sq, him_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

#print axioms complexifyMomentOperator

/-- Pointwise formula for the bounded complexified operator. -/
theorem complexifyMomentOperator_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (x : RealHilbertComplexification E) :
    complexifyMomentOperator T x =
      RealHilbertComplexification.mk (T (RealHilbertComplexification.re x))
        (T (RealHilbertComplexification.im x)) := by
  unfold complexifyMomentOperator
  simp [LinearMap.mkContinuous_apply]

#print axioms complexifyMomentOperator_apply

/-- Complexification preserves symmetry of a real bounded operator. -/
theorem complexifyMomentOperator_symmetric {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hSym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) :
    (complexifyMomentOperator T :
      RealHilbertComplexification E →ₗ[ℂ] RealHilbertComplexification E).IsSymmetric := by
  change ∀ x y, inner ℂ (complexifyMomentOperator T x) y =
    inner ℂ x (complexifyMomentOperator T y)
  intro x y
  rw [complexifyMomentOperator_apply, complexifyMomentOperator_apply,
    RealHilbertComplexification.inner_apply]
  apply Complex.ext <;>
    simp [RealHilbertComplexification.complexInner, hSym]

/-- The complexified bounded symmetric operator is self-adjoint. -/
theorem complexifyMomentOperator_isSelfAdjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (complexifyMomentOperator T) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply complexifyMomentOperator_symmetric T
  intro x y
  exact hT.isSymmetric x y

#print axioms complexifyMomentOperator_symmetric
#print axioms complexifyMomentOperator_isSelfAdjoint

/-- Complex Hilbert space associated with the real GNS completion. -/
abbrev momentComplexHilbert {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef) :=
  RealHilbertComplexification (momentHilbert h hH)

/-- The moment multiplier acting on the complexification. -/
noncomputable abbrev momentComplexMulX {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    momentComplexHilbert hH →L[ℂ] momentComplexHilbert hH :=
  complexifyMomentOperator (momentHilbertMulX hH hC hR hbound)

/-- The complex moment multiplier remains self-adjoint. -/
theorem momentComplexMulX_isSelfAdjoint {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) :
    IsSelfAdjoint (momentComplexMulX hH hC hR hbound) := by
  apply complexifyMomentOperator_isSelfAdjoint
  exact momentHilbertMulX_isSelfAdjoint hH hC hR hbound

#print axioms momentComplexMulX_isSelfAdjoint

/-- A nonreal complex number lies in the resolvent set of the complexified
self-adjoint moment multiplier. -/
theorem momentComplexMulX_mem_resolventSet {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ (momentComplexMulX hH hC hR hbound) := by
  have hnot : z ∉ spectrum ℂ (momentComplexMulX hH hC hR hbound) := by
    intro hspec
    have hre := (momentComplexMulX_isSelfAdjoint hH hC hR hbound).mem_spectrum_eq_re hspec
    have him := congrArg Complex.im hre
    exact hz (by simpa using him)
  exact Classical.not_not.mp (by simpa only [spectrum, Set.mem_compl_iff] using hnot)

/-- The usual Neumann denominator is invertible for every nonreal parameter. -/
theorem momentComplexMulX_one_sub_smul_isUnit {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k) {u : ℂ} (hu : u.im ≠ 0) :
    IsUnit (1 - u • momentComplexMulX hH hC hR hbound) := by
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero] at hu
    exact hu (by simp)
  have hinv_im : (u⁻¹).im ≠ 0 := by
    intro hzero
    have hns : Complex.normSq u ≠ 0 := mt Complex.normSq_eq_zero.mp hu0
    have hdiv : -u.im / Complex.normSq u = 0 := by
      simpa only [Complex.inv_im] using hzero
    rcases (div_eq_zero_iff.mp hdiv) with hneg | hnorm
    · exact hu (neg_eq_zero.mp hneg)
    · exact hu0 (Complex.normSq_eq_zero.mp hnorm)
  let z : ℂˣ := Units.mk0 (u⁻¹) (inv_ne_zero hu0)
  have hres := momentComplexMulX_mem_resolventSet hH hC hR hbound hinv_im
  have hunit : IsUnit ((z : ℂ) • (1 : momentComplexHilbert hH →L[ℂ]
      momentComplexHilbert hH) - momentComplexMulX hH hC hR hbound) := by
    have hunit' := (spectrum.mem_resolventSet_iff).mp hres
    simpa [z, Units.val_mk0, Algebra.algebraMap_eq_smul_one] using hunit'
  have hscaled := (IsUnit.smul_sub_iff_sub_inv_smul z
    (momentComplexMulX hH hC hR hbound)).mp hunit
  have hzval : (z⁻¹ : ℂ) = u := by
    simp [z, Units.val_mk0]
  have hzval' : ((z⁻¹ : ℂˣ) : ℂ) = u := by
    rw [Units.val_inv_eq_inv_val]
    exact hzval
  change IsUnit (1 - ((z⁻¹ : ℂˣ) : ℂ) •
    momentComplexMulX hH hC hR hbound) at hscaled
  rw [hzval'] at hscaled
  exact hscaled

/-- The scalar matrix coefficient of the complex resolvent, with the vector
in the first slot so it is holomorphic in Mathlib's conjugate-linear-first
inner-product convention. -/
noncomputable def momentResolventReadout {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ e).comp ((ContinuousLinearMap.apply ℂ (E := H) H) e)

/-- Scalar resolvent coefficient of the complexified moment operator. -/
noncomputable def momentResolventCoefficient {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (e : momentComplexHilbert hH) (u : ℂ) : ℂ :=
  momentResolventReadout e (Ring.inverse
    (1 - u • momentComplexMulX hH hC hR hbound))

/-- The scalar resolvent coefficient is complex differentiable off the real
axis. -/
theorem momentResolventCoefficient_differentiableAt {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (e : momentComplexHilbert hH) {u : ℂ} (hu : u.im ≠ 0) :
    DifferentiableAt ℂ (momentResolventCoefficient hH hC hR hbound e) u := by
  let A := momentComplexMulX hH hC hR hbound
  have hunit : IsUnit (1 - u • A) := by
    exact momentComplexMulX_one_sub_smul_isUnit hH hC hR hbound hu
  have hinv : DifferentiableAt ℂ Ring.inverse (1 - u • A) :=
    differentiableAt_inverse hunit
  have hmul : DifferentiableAt ℂ (fun z : ℂ => z • A) u :=
    (differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) u).smul_const A
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 - z • A) u := hmul.const_sub 1
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => Ring.inverse (1 - z • A)) u := by
    simpa only [Function.comp_def] using DifferentiableAt.comp u hinv harg
  have hread : DifferentiableAt ℂ
      (momentResolventReadout e : (momentComplexHilbert hH →L[ℂ]
        momentComplexHilbert hH) → ℂ)
      (Ring.inverse (1 - u • A)) :=
    (momentResolventReadout e).differentiableAt
  change DifferentiableAt ℂ (fun z : ℂ =>
    momentResolventReadout e (Ring.inverse (1 - z • A))) u
  simpa only [Function.comp_def] using DifferentiableAt.comp u hread hcomp

/-- Holomorphy of the scalar moment resolvent on the complement of the real axis. -/
theorem momentResolventCoefficient_differentiableOn {h : ℕ → ℝ}
    (hH : ∀ N, (hankelMatrix h N).PosSemidef)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hbound : ∀ k, |h k| ≤ C * R ^ k)
    (e : momentComplexHilbert hH) :
    DifferentiableOn ℂ (momentResolventCoefficient hH hC hR hbound e)
      {u : ℂ | u.im ≠ 0} := by
  intro u hu
  exact (momentResolventCoefficient_differentiableAt hH hC hR hbound e hu).differentiableWithinAt

#print axioms momentComplexMulX_mem_resolventSet
#print axioms momentComplexMulX_one_sub_smul_isUnit
#print axioms momentResolventCoefficient_differentiableAt
#print axioms momentResolventCoefficient_differentiableOn


end CarryMomentLogConvex
