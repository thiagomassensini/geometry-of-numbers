import JacobiLogic
import GeometryOfNumbers.Analysis.FiniteClockHeightLedger

/-! Counterexamples to generic implications, never replacements for the
canonical sequence. All coefficients below are explicitly control data. -/
namespace NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
open GeometryOfNumbers.Analysis.FiniteClockHeightLedger
open scoped BigOperators Matrix
noncomputable section

/-- A normalized formal characteristic (1-2u)(1+u). -/
def controlPhi (n : ℕ) : ℝ := if n = 0 then 1 else if n = 1 then -1
  else if n = 2 then -2 else 0

def controlLogMoments : ℕ → ℝ := finiteLogMoment controlPhi

theorem controlLogMoments_relation :
    IsLogDerivativeMomentSequence controlPhi controlLogMoments :=
  finiteLogMoment_isSequence _ (by norm_num [controlPhi])

theorem controlLogMoments_zero : controlLogMoments 0 = 1 := by
  norm_num [controlLogMoments, finiteLogMoment_recurrence, controlPhi]

theorem controlLogMoments_one : controlLogMoments 1 = 5 := by
  have h := finiteLogMoment_recurrence controlPhi 1
  change controlLogMoments 1 = _ at h
  have h0 : finiteLogMoment controlPhi 0 = 1 := controlLogMoments_zero
  norm_num [controlPhi, Finset.sum_range_succ, h0] at h
  exact h

theorem controlLogMoments_two : controlLogMoments 2 = 7 := by
  have h := finiteLogMoment_recurrence controlPhi 2
  change controlLogMoments 2 = _ at h
  have h0 : finiteLogMoment controlPhi 0 = 1 := controlLogMoments_zero
  have h1 : finiteLogMoment controlPhi 1 = 5 := controlLogMoments_one
  norm_num [controlPhi, Finset.sum_range_succ, h0, h1] at h
  exact h

theorem controlLogMoments_negative_pivot :
    carryPairingPivot (hankelPairing controlLogMoments) 1 = -18 := by
  norm_num [carryPairingPivot_one, hankelPairing, controlLogMoments_zero,
    controlLogMoments_one, controlLogMoments_two]

theorem controlLogMoments_negative_residual :
    momentForm controlLogMoments (orthogonalPolynomial controlLogMoments 1)
      (orthogonalPolynomial controlLogMoments 1) = -18 := by
  rw [orthogonalPolynomial_self, controlLogMoments_negative_pivot]

theorem controlLogMoments_orthogonal :
    momentForm controlLogMoments (orthogonalPolynomial controlLogMoments 0)
      (orthogonalPolynomial controlLogMoments 1) = 0 := by
  apply orthogonalPolynomial_orthogonal
  · intro r hr
    have : r = 0 := by omega
    subst r
    norm_num [carryPairingPivot_zero, hankelPairing, controlLogMoments_zero]
  · omega

theorem controlLogMoments_not_posSemidef :
    ¬ (hankelGram controlLogMoments 2).PosSemidef := by
  intro hp
  have ht := hp.dotProduct_mulVec_nonneg ![-5, 1]
  norm_num [hankelGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    controlLogMoments_zero, controlLogMoments_one, controlLogMoments_two] at ht

theorem log_recurrence_does_not_imply_posSemidef :
    ¬ (∀ phi h : ℕ → ℝ, phi 0 ≠ 0 → IsLogDerivativeMomentSequence phi h →
      (hankelGram h 2).PosSemidef) := by
  intro hall
  exact controlLogMoments_not_posSemidef
    (hall controlPhi controlLogMoments (by norm_num [controlPhi]) controlLogMoments_relation)

/-- An exactly diagonal indefinite moment form on 1,X. -/
def rotationMoments (n : ℕ) : ℝ := if n % 4 = 0 then 1
  else if n % 4 = 2 then -1 else 0

def signatureTwo : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def rotationOperator : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem rotation_gram : hankelGram rotationMoments 2 = signatureTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hankelGram, rotationMoments, signatureTwo]

theorem rotation_shift : shiftedHankel rotationMoments 2 = !![0, -1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [shiftedHankel, rotationMoments]

/-- The symmetric transported *form* is G times the operation matrix.
With a signature instead of I, these are different objects. -/
theorem rotation_form_operation :
    signatureTwo * rotationOperator = shiftedHankel rotationMoments 2 := by
  rw [rotation_shift]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signatureTwo, rotationOperator, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotation_square : rotationOperator * rotationOperator = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationOperator, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotation_no_real_eigenvector (lambda : ℝ) (v : Fin 2 → ℝ)
    (he : rotationOperator *ᵥ v = lambda • v) : v = 0 := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  norm_num [rotationOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hz : v 0 ^ 2 + v 1 ^ 2 = 0 := by
    nlinarith [congrArg (fun t : ℝ => t * v 1) h0,
      congrArg (fun t : ℝ => t * v 0) h1]
  have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
  ext i
  fin_cases i <;> simp [hv0, hv1]

theorem rotation_negative_self : momentForm rotationMoments Polynomial.X Polynomial.X = -1 := by
  simpa [rotationMoments] using momentForm_monomials rotationMoments 1 1

/-- A zero self-pairing in a prefix, with an independent future crossing. -/
def futureCrossMoments (n : ℕ) : ℝ := if n = 0 ∨ n = 3 then 1 else 0

theorem future_zero_self :
    momentForm futureCrossMoments Polynomial.X Polynomial.X = 0 := by
  simpa [futureCrossMoments] using momentForm_monomials futureCrossMoments 1 1

theorem future_nonzero_cross :
    momentForm futureCrossMoments Polynomial.X (Polynomial.X ^ 2) = 1 := by
  simpa [futureCrossMoments] using momentForm_monomials futureCrossMoments 1 2

theorem future_zero_not_radical :
    ¬ (∀ q : Polynomial ℝ, momentForm futureCrossMoments Polynomial.X q = 0) := by
  intro hall
  have h := hall (Polynomial.X ^ 2)
  rw [future_nonzero_cross] at h
  norm_num at h

theorem future_failed_orthogonalization :
    momentForm futureCrossMoments (orthogonalPolynomial futureCrossMoments 1)
      (orthogonalPolynomial futureCrossMoments 2) = 1 := by
  have hp1 : orthogonalPolynomial futureCrossMoments 1 = Polynomial.X := by
    norm_num [orthogonalPolynomial, residualPolynomial, carryPairingRemainder,
      carryPairingPivot, hankelPairing, futureCrossMoments]
  have hp2 : orthogonalPolynomial futureCrossMoments 2 = Polynomial.X ^ 2 := by
    norm_num [orthogonalPolynomial, residualPolynomial, carryPairingRemainder,
      carryPairingPivot, hankelPairing, futureCrossMoments]
  rw [hp1, hp2, future_nonzero_cross]

theorem future_prefix_posSemidef : (hankelGram futureCrossMoments 2).PosSemidef := by
  have he : hankelGram futureCrossMoments 2 = Matrix.diagonal ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [hankelGram, futureCrossMoments]
  rw [he]
  exact Matrix.posSemidef_diagonal_iff.mpr (by intro i; fin_cases i <;> norm_num)

theorem future_prefix_not_whitenable :
    ¬ ∃ B, finiteJacobiTransport B (hankelGram futureCrossMoments 2) = 1 := by
  rw [exists_whitening_iff_posDef]
  intro hp
  have ht := hp.diag_pos (i := (1 : Fin 2))
  norm_num [hankelGram, futureCrossMoments] at ht

theorem future_extension_not_posSemidef :
    ¬ (hankelGram futureCrossMoments 3).PosSemidef := by
  intro hp
  have ht := hp.dotProduct_mulVec_nonneg ![0, 1, -1]
  norm_num [hankelGram, futureCrossMoments, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at ht

/-- A true radical, in contrast: constant moments are evaluation at 1. -/
theorem constantMomentFunctional (p : Polynomial ℝ) :
    momentFunctional (fun _ => 1) p = p.eval 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [momentFunctional, Polynomial.eval_monomial]

theorem constant_true_radical (q : Polynomial ℝ) :
    momentForm (fun _ => 1) (Polynomial.X - 1) q = 0 := by
  simp [momentForm, constantMomentFunctional]

/-- Actual global radicals, unlike isotropic vectors, are stable under the
operation; this is the condition needed for a legitimate algebra quotient. -/
theorem radical_multiply_X (h : ℕ → ℝ) (p : Polynomial ℝ)
    (hp : ∀ q, momentForm h p q = 0) (q : Polynomial ℝ) :
    momentForm h (Polynomial.X * p) q = 0 := by
  rw [momentForm_multiply_X, hp]

def negativePointMoments (n : ℕ) : ℝ := (-1) ^ n

theorem negativePoint_gram_one : hankelGram negativePointMoments 1 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [hankelGram, negativePointMoments]

theorem negativePoint_shift_one : shiftedHankel negativePointMoments 1 = -1 := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [shiftedHankel, negativePointMoments]

theorem negativePoint_gram_posDef : (hankelGram negativePointMoments 1).PosDef := by
  rw [negativePoint_gram_one]
  exact Matrix.PosDef.one

def negativePointWhitening : FiniteGramWhitening negativePointMoments 1 :=
  FiniteGramWhitening.ofIdentity _ _ 1 (by simp [finiteJacobiTransport, negativePoint_gram_one])

theorem negativePoint_Jacobi :
    finiteJacobiSection negativePointMoments 1 negativePointWhitening = -1 := by
  simp [finiteJacobiSection, negativePointWhitening, FiniteGramWhitening.ofIdentity,
    finiteJacobiTransport, negativePoint_shift_one]

theorem negativePoint_no_positive_height : ¬ ∃ t : ℝ, t ^ 2 * (-1) = 1 := by
  rintro ⟨t, ht⟩
  nlinarith [sq_nonneg t]

end
end NativeMomentOrthogonalization
