import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor
import GeometryOfNumbers.Analysis.LogarithmicMomentHankel
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.Basic

/-! Algebra after the completed moments have been extracted. This module
does not define a physical source, a replacement sequence, or a metric. -/
namespace NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
open scoped BigOperators
noncomputable section

def momentFunctional (h : ℕ → ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ h).comp ((Polynomial.toFinsuppIsoLinear ℝ).trans
    (AddMonoidAlgebra.coeffLinearEquiv ℝ)).toLinearMap

@[simp] theorem momentFunctional_X_pow (h : ℕ → ℝ) (n : ℕ) :
    momentFunctional h (Polynomial.X ^ n) = h n := by
  simp [momentFunctional, Polynomial.X_pow_eq_monomial]

def momentForm (h : ℕ → ℝ) (p q : Polynomial ℝ) : ℝ :=
  momentFunctional h (p * q)

theorem momentForm_symm (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentForm h p q = momentForm h q p := by simp [momentForm, mul_comm]

@[simp] theorem momentForm_monomials (h : ℕ → ℝ) (i j : ℕ) :
    momentForm h (Polynomial.X ^ i) (Polynomial.X ^ j) = h (i + j) := by
  simp [momentForm, ← pow_add]

@[simp] theorem momentForm_sub_left (h : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentForm h (p - q) r = momentForm h p r - momentForm h q r := by
  simp [momentForm, sub_mul]

@[simp] theorem momentForm_sub_right (h : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentForm h p (q - r) = momentForm h p q - momentForm h p r := by
  simp [momentForm, mul_sub]

@[simp] theorem momentForm_smul_left (h : ℕ → ℝ) (a : ℝ) (p q : Polynomial ℝ) :
    momentForm h (a • p) q = a * momentForm h p q := by
  simp [momentForm]

@[simp] theorem momentForm_smul_right (h : ℕ → ℝ) (a : ℝ) (p q : Polynomial ℝ) :
    momentForm h p (a • q) = a * momentForm h p q := by
  simp [momentForm]

/-- Multiplication by X is algebraically symmetric for every moment
functional; this statement does not imply positivity. -/
theorem momentForm_multiply_X (h : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentForm h (Polynomial.X * p) q = momentForm h p (Polynomial.X * q) := by
  unfold momentForm
  congr 1
  ring

def coefficientPolynomial {N : ℕ} (a : Fin N → ℝ) : Polynomial ℝ :=
  ∑ i : Fin N, a i • Polynomial.X ^ (i : ℕ)

/-- All ordered crossings, including the two distinct arguments, survive. -/
theorem momentForm_coefficients (h : ℕ → ℝ) {N : ℕ} (a b : Fin N → ℝ) :
    momentForm h (coefficientPolynomial a) (coefficientPolynomial b) =
      carryPairingBilinear (fun i j => h (i + j)) N a b := by
  simp only [coefficientPolynomial, momentForm, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
    ← pow_add, momentFunctional_X_pow, carryPairingBilinear]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def hankelPairing (h : ℕ → ℝ) (i j : ℕ) : ℝ := h (i + j)

theorem hankelPairing_symm (h : ℕ → ℝ) (i j : ℕ) :
    hankelPairing h i j = hankelPairing h j i := by simp [hankelPairing, add_comm]

/-- Same elimination as carryPairingRemainder, now performed on actual
polynomials. Total division at zero preserves the entire residual. -/
def residualPolynomial (h : ℕ → ℝ) : ℕ → ℕ → Polynomial ℝ
  | 0, i => Polynomial.X ^ i
  | n + 1, i => residualPolynomial h n i -
      (carryPairingRemainder (hankelPairing h) n i n /
        carryPairingPivot (hankelPairing h) n) • residualPolynomial h n n

/-- Exact polarized identity, including zero and negative pivots. -/
theorem residualPolynomial_pairing (h : ℕ → ℝ) (n i j : ℕ) :
    momentForm h (residualPolynomial h n i) (residualPolynomial h n j) =
      carryPairingRemainder (hankelPairing h) n i j := by
  induction n generalizing i j with
  | zero => simp [residualPolynomial, carryPairingRemainder, hankelPairing]
  | succ n ih =>
    simp only [residualPolynomial, momentForm_sub_left, momentForm_sub_right,
      momentForm_smul_left, momentForm_smul_right, ih]
    rw [carryPairingRemainder_symm (hankelPairing_symm h) n n j]
    unfold carryPairingPivot
    simp only [carryPairingRemainder]
    rw [carryPairingRemainder_symm (hankelPairing_symm h) n n j]
    by_cases hd : carryPairingRemainder (hankelPairing h) n n n = 0
    · simp [hd]
    · field_simp
      ring

def orthogonalPolynomial (h : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  residualPolynomial h n n

/-- A Schur pivot is its residual self-pairing, not yet a Hilbert norm. -/
theorem orthogonalPolynomial_self (h : ℕ → ℝ) (n : ℕ) :
    momentForm h (orthogonalPolynomial h n) (orthogonalPolynomial h n) =
      carryPairingPivot (hankelPairing h) n :=
  residualPolynomial_pairing h n n n

theorem orthogonalPolynomial_residual_orthogonal (h : ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0)
    (r : ℕ) (hr : r < n) (j : ℕ) :
    momentForm h (orthogonalPolynomial h r) (residualPolynomial h n j) = 0 := by
  induction n generalizing r j with
  | zero => omega
  | succ n ih =>
    simp only [residualPolynomial, momentForm_sub_right, momentForm_smul_right]
    by_cases he : r = n
    · subst r
      simp only [orthogonalPolynomial, residualPolynomial_pairing]
      rw [carryPairingRemainder_symm (hankelPairing_symm h) n n j]
      have hd := hp n (by omega)
      unfold carryPairingPivot at hd ⊢
      field_simp
      ring
    · have hrn : r < n := by omega
      have hp' : ∀ k < n, carryPairingPivot (hankelPairing h) k ≠ 0 :=
        fun k hk => hp k (by omega)
      rw [ih hp' r hrn j, ih hp' r hrn n]
      ring

/-- Genuine algebraic orthogonalization, requiring nonzero preceding pivots
and no positivity assumptions. -/
theorem orthogonalPolynomial_orthogonal (h : ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0)
    (r : ℕ) (hr : r < n) :
    momentForm h (orthogonalPolynomial h r) (orthogonalPolynomial h n) = 0 :=
  orthogonalPolynomial_residual_orthogonal h n hp r hr n

/-- Nonzero signed pivots already give independent polynomial coordinates.
Linear independence is not a sign certificate. -/
theorem orthogonalPolynomial_linearIndependent (h : ℕ → ℝ) (N : ℕ)
    (hp : ∀ r < N, carryPairingPivot (hankelPairing h) r ≠ 0) :
    LinearIndependent ℝ (fun i : Fin N => orthogonalPolynomial h i) := by
  have hoff (i j : Fin N) (hne : i ≠ j) :
      momentForm h (orthogonalPolynomial h i) (orthogonalPolynomial h j) = 0 := by
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun he => hne (Fin.ext he)) with hij | hji
    · exact orthogonalPolynomial_orthogonal h j
        (fun r hr => hp r (lt_trans hr j.isLt)) i hij
    · rw [momentForm_symm]
      exact orthogonalPolynomial_orthogonal h i
        (fun r hr => hp r (lt_trans hr i.isLt)) j hji
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have ht := congrArg (fun p => momentForm h p (orthogonalPolynomial h i)) ha
  simp only [momentForm, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    smul_eq_mul, zero_mul, map_zero] at ht
  change (∑ j : Fin N, a j * momentForm h (orthogonalPolynomial h j)
    (orthogonalPolynomial h i)) = 0 at ht
  rw [Finset.sum_eq_single i] at ht
  · rw [orthogonalPolynomial_self] at ht
    exact (mul_eq_zero.mp ht).resolve_right (hp i i.isLt)
  · intro j _ hji
    rw [hoff j i hji, mul_zero]
  · simp

end
end NativeMomentOrthogonalization
