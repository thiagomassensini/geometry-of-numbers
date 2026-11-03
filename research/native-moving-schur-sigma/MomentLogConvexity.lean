import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef

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

end CarryMomentLogConvex
