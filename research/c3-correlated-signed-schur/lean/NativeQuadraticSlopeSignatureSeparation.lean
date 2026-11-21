import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Tactic

/-!
# All-order exact scaling conjugation for completed-source moment Hankels

A positive quadratic scale a > 0 changes magnitudes and logarithmic
slopes but PRESERVES the inertial signature of a finite Hankel form.
This is algebraic for ANY residual jet sequence, not the C2 all-order
sign theorem: what remains is its normalized original physical residual.

The original H_n is passed to this module as an arbitrary sequence;
we do NOT replace the native original moments with a spectral measure.
-/

namespace CarryWheelNativeSignedGate

open CarrySelfAdjointOperator Matrix
open scoped Matrix BigOperators

noncomputable section

def momentQuadraticScale (a : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  a ^ (n+1) * r n

def momentSlopeDiagonal (a : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => a ^ i.val)

theorem momentQuadraticScale_sourceEntry (a : ℝ)
    (r : ℕ → ℝ) (s N : ℕ) (i j : Fin N) :
    sourceMomentMatrix (momentQuadraticScale a r) s N i j =
      a ^ (s+1) * a ^ i.val *
        (sourceMomentMatrix r s N i j) * a ^ j.val := by
  simp only [sourceMomentMatrix, momentQuadraticScale]
  have heq : i.val + j.val + s + 1 = (s+1) + i.val + j.val := by omega
  rw [heq, pow_add, pow_add]
  ring

theorem momentQuadraticScale_matrix_congruence (a : ℝ)
    (r : ℕ → ℝ) (s N : ℕ) :
    sourceMomentMatrix (momentQuadraticScale a r) s N =
      (a ^ (s+1)) •
        (momentSlopeDiagonal a N * sourceMomentMatrix r s N *
          momentSlopeDiagonal a N) := by
  ext i j
  rw [momentQuadraticScale_sourceEntry]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp [momentSlopeDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring


/-- Exact all-order determinant factorization. The amplitude-scale factor
is a POSITIVE square when a > 0. -/
def momentScaleDetFactor (a : ℝ) (s N : ℕ) : ℝ :=
  (a ^ (s+1)) ^ N * (∏ i : Fin N, a ^ i.val) ^ 2

theorem momentQuadraticScale_det_eq
    (a : ℝ) (r : ℕ → ℝ) (s N : ℕ) :
    (sourceMomentMatrix (momentQuadraticScale a r) s N).det =
      momentScaleDetFactor a s N *
        (sourceMomentMatrix r s N).det := by
  rw [momentQuadraticScale_matrix_congruence]
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul,
    Matrix.det_diagonal, momentSlopeDiagonal, momentScaleDetFactor]
  ring

theorem momentScaleDetFactor_pos
    (a : ℝ) (ha : 0 < a) (s N : ℕ) :
    0 < momentScaleDetFactor a s N := by
  unfold momentScaleDetFactor
  positivity

theorem momentQuadraticScale_det_pos_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s N : ℕ) :
    0 < (sourceMomentMatrix (momentQuadraticScale a r) s N).det ↔
      0 < (sourceMomentMatrix r s N).det := by
  rw [momentQuadraticScale_det_eq]
  exact mul_pos_iff_of_pos_left (momentScaleDetFactor_pos a ha s N)

theorem momentQuadraticScale_det_neg_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s N : ℕ) :
    (sourceMomentMatrix (momentQuadraticScale a r) s N).det < 0 ↔
      (sourceMomentMatrix r s N).det < 0 := by
  rw [momentQuadraticScale_det_eq]
  have hp := momentScaleDetFactor_pos a ha s N
  constructor
  · intro h
    by_contra hn
    have hr : 0 ≤ (sourceMomentMatrix r s N).det := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hp.le hr)) h
  · intro h
    exact mul_neg_of_pos_of_neg hp h


theorem momentQuadraticScale_posSemidef_of_posSemidef
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s N : ℕ)
    (hr : (sourceMomentMatrix r s N).PosSemidef) :
    (sourceMomentMatrix (momentQuadraticScale a r) s N).PosSemidef := by
  rw [momentQuadraticScale_matrix_congruence]
  let D := momentSlopeDiagonal a N
  have hD : Dᴴ = D := by
    simp [D, momentSlopeDiagonal]
  have hcong : (D * sourceMomentMatrix r s N * D).PosSemidef := by
    have h := hr.conjTranspose_mul_mul_same D
    simpa only [hD] using h
  exact hcong.smul (pow_pos ha _).le

theorem momentQuadraticScale_inv_comp
    (a : ℝ) (ha : a ≠ 0) (r : ℕ → ℝ) :
    momentQuadraticScale a⁻¹ (momentQuadraticScale a r) = r := by
  funext n
  simp only [momentQuadraticScale, inv_pow]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha), one_mul]

/-- POSITIVE QUADRATIC SLOPE GAUGE DOES NOT CREATE PSD:
it preserves the full signature for every finite size and shift. -/
theorem momentQuadraticScale_posSemidef_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s N : ℕ) :
    (sourceMomentMatrix (momentQuadraticScale a r) s N).PosSemidef ↔
      (sourceMomentMatrix r s N).PosSemidef := by
  constructor
  · intro h
    have hInv : 0 < a⁻¹ := inv_pos.mpr ha
    have hBack :=
      momentQuadraticScale_posSemidef_of_posSemidef a⁻¹ hInv
        (momentQuadraticScale a r) s N h
    rwa [momentQuadraticScale_inv_comp a ha.ne' r] at hBack
  · exact momentQuadraticScale_posSemidef_of_posSemidef a ha r s N

/-- Any order positivity after removal of an arbitrary positive modal
slope is exactly the original all-order sign obligation, not its proof. -/
theorem momentQuadraticScale_allPSD_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) :
    (∀ (s N : ℕ),
      (sourceMomentMatrix (momentQuadraticScale a r) s N).PosSemidef) ↔
      ∀ (s N : ℕ), (sourceMomentMatrix r s N).PosSemidef := by
  constructor
  · intro h s N
    exact (momentQuadraticScale_posSemidef_iff a ha r s N).mp (h s N)
  · intro h s N
    exact (momentQuadraticScale_posSemidef_iff a ha r s N).mpr (h s N)


/-- The positive quadratic modal scale preserves STRICT PosDef as well,
for every finite dimension. -/
theorem momentQuadraticScale_posDef_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s N : ℕ) :
    (sourceMomentMatrix (momentQuadraticScale a r) s N).PosDef ↔
      (sourceMomentMatrix r s N).PosDef := by
  constructor
  · intro h
    have hrPSD := (momentQuadraticScale_posSemidef_iff a ha r s N).mp h.posSemidef
    apply (hrPSD.posDef_iff_det_ne_zero).mpr
    have hdetScaled : (sourceMomentMatrix (momentQuadraticScale a r) s N).det ≠ 0 :=
      h.det_pos.ne'
    intro hzero
    apply hdetScaled
    rw [momentQuadraticScale_det_eq, hzero, mul_zero]
  · intro h
    have hsPSD := (momentQuadraticScale_posSemidef_iff a ha r s N).mpr h.posSemidef
    apply (hsPSD.posDef_iff_det_ne_zero).mpr
    rw [momentQuadraticScale_det_eq]
    exact mul_ne_zero (momentScaleDetFactor_pos a ha s N).ne' h.det_pos.ne'

/-- DIRECT SCHUR SIGN LAW. When the old genuine prefix is positive,
removing a positive quadratic slope cannot turn a positive Schur
pivot into a non-positive one, or conversely, in ANY dimension. -/
theorem momentQuadraticScale_sourceSchur_pos_iff
    (a : ℝ) (ha : 0 < a) (r : ℕ → ℝ) (s n : ℕ)
    (hprev : (sourceMomentMatrix r s n).PosDef) :
    0 < sourceMomentSchur (momentQuadraticScale a r) s n ↔
      0 < sourceMomentSchur r s n := by
  have hprevScaled :
      (sourceMomentMatrix (momentQuadraticScale a r) s n).PosDef :=
    (momentQuadraticScale_posDef_iff a ha r s n).mpr hprev
  calc
    0 < sourceMomentSchur (momentQuadraticScale a r) s n ↔
        (sourceMomentMatrix (momentQuadraticScale a r) s (n+1)).PosDef :=
      (sourceMomentMatrix_succ_posDef_iff _ s n hprevScaled).symm
    _ ↔ (sourceMomentMatrix r s (n+1)).PosDef :=
      momentQuadraticScale_posDef_iff a ha r s (n+1)
    _ ↔ 0 < sourceMomentSchur r s n :=
      sourceMomentMatrix_succ_posDef_iff _ s n hprev

end
end CarryWheelNativeSignedGate
