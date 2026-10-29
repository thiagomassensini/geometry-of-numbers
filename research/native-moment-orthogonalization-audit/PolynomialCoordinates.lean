import MomentFunctional
import Mathlib.Algebra.Polynomial.Sequence

namespace NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
noncomputable section

/-- The triangular coordinate construction has a unit leading coefficient
even at a zero pivot. Neither independence nor existence requires signs. -/
theorem residualPolynomial_monic_degree (h : ℕ → ℝ) (n i : ℕ) (hni : n ≤ i) :
    (residualPolynomial h n i).Monic ∧ (residualPolynomial h n i).degree = i := by
  induction n generalizing i with
  | zero => simp [residualPolynomial, Polynomial.monic_X_pow]
  | succ n ih =>
    have hi := ih i (by omega)
    have hn := ih n le_rfl
    let a := carryPairingRemainder (hankelPairing h) n i n /
      carryPairingPivot (hankelPairing h) n
    have hlt : (a • residualPolynomial h n n).degree < (residualPolynomial h n i).degree := by
      apply lt_of_le_of_lt (Polynomial.degree_smul_le a _)
      rw [hn.2, hi.2]
      exact_mod_cast (show n < i by omega)
    change (residualPolynomial h n i - a • residualPolynomial h n n).Monic ∧
      (residualPolynomial h n i - a • residualPolynomial h n n).degree = i
    exact ⟨hi.1.sub_of_left hlt, (Polynomial.degree_sub_eq_left_of_degree_lt hlt).trans hi.2⟩

def momentPolynomialSequence (h : ℕ → ℝ) : Polynomial.Sequence ℝ where
  elems' := orthogonalPolynomial h
  degree_eq' i := (residualPolynomial_monic_degree h i i le_rfl).2

/-- Stronger than the signed-pivot independence test: polynomial coordinates
remain independent even when the bilinear form is degenerate. -/
theorem polynomial_coordinates_independent (h : ℕ → ℝ) :
    LinearIndependent ℝ (orthogonalPolynomial h) :=
  (momentPolynomialSequence h).linearIndependent

def momentPolynomialBasis (h : ℕ → ℝ) : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  (momentPolynomialSequence h).basis (fun i => by
    change IsUnit (orthogonalPolynomial h i).leadingCoeff
    have hm : (orthogonalPolynomial h i).leadingCoeff = 1 :=
      (residualPolynomial_monic_degree h i i le_rfl).1
    rw [hm]
    exact isUnit_one)

theorem momentPolynomialBasis_apply (h : ℕ → ℝ) (i : ℕ) :
    momentPolynomialBasis h i = orthogonalPolynomial h i :=
  (momentPolynomialSequence h).basis_eq_self _ i

theorem polynomial_from_coefficients (p : Polynomial ℝ) (N : ℕ)
    (hdegree : p.natDegree < N) :
    coefficientPolynomial (fun i : Fin N => p.coeff i) = p := by
  unfold coefficientPolynomial
  rw [Fin.sum_univ_eq_sum_range (fun k => p.coeff k • (Polynomial.X : Polynomial ℝ) ^ k) N]
  simpa only [Polynomial.smul_eq_C_mul] using
    (p.as_sum_range_C_mul_X_pow' hdegree).symm

theorem orthogonalPolynomial_from_coefficients (h : ℕ → ℝ) (n : ℕ) :
    coefficientPolynomial (fun i : Fin (n+1) => (orthogonalPolynomial h n).coeff i) =
      orthogonalPolynomial h n := by
  apply polynomial_from_coefficients
  have hd := Polynomial.natDegree_eq_of_degree_eq_some
    (residualPolynomial_monic_degree h n n le_rfl).2
  change (orthogonalPolynomial h n).natDegree < n + 1
  simpa only [orthogonalPolynomial, hd] using Nat.lt_succ_self n

end
end NativeMomentOrthogonalization
