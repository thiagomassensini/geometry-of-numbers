import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Tactic

/-!
# Signed two-mode adversary: SAME INVERSE-SQUARE HEIGHTS,
# OPPOSITE SCHUR SIGNS in every shifted finite 2x2 Hankel.

This is an intentionally synthetic *signed residue* model, NOT original
C2/Genuine and NOT an assertion of off-line zeros. It proves that
knowing all positive modal heights from log-slopes (without a residue
sign theorem) is insufficient to infer Hankel PSD.
-/

namespace CarryWheelNativeSignedGate
open CarrySelfAdjointOperator Matrix
open scoped Matrix

noncomputable section

def signedTwoMode (a c w : ℝ) (n : ℕ) : ℝ :=
  a ^ (n+1) + w * c ^ (n+1)

/-- All four moment products are retained, exact at every shift. -/
theorem signedTwoMode_det_formula (a c w : ℝ) (s : ℕ) :
    (sourceMomentMatrix (signedTwoMode a c w) s 2).det =
      w * (a*c) ^ (s+1) * (a-c)^2 := by
  simp [Matrix.det_fin_two, sourceMomentMatrix, signedTwoMode]
  ring_nf


/-- The exponential scale of the TWO-BY-TWO determinant is exactly
a*c, INDEPENDENT of the sign w of the second residue. -/
theorem signedTwoMode_det_shift_scale (a c w : ℝ) (s : ℕ) :
    (sourceMomentMatrix (signedTwoMode a c w) (s+1) 2).det =
      (a*c) * (sourceMomentMatrix (signedTwoMode a c w) s 2).det := by
  rw [signedTwoMode_det_formula, signedTwoMode_det_formula]
  rw [show s + 1 + 1 = (s + 1) + 1 by omega, pow_succ]
  ring

def toyPosResidues : ℕ → ℝ := signedTwoMode (1/2) (1/4) 1
def toyNegResidue : ℕ → ℝ := signedTwoMode (1/2) (1/4) (-1)

/-- Same REAL nodes a=1/2,c=1/4; positive second weight. -/
theorem toyPositiveResidues_det_two_pos (s : ℕ) :
    0 < (sourceMomentMatrix toyPosResidues s 2).det := by
  rw [toyPosResidues, signedTwoMode_det_formula]
  positivity

/-- The *identical nodes* with negative second weight give a
negative 2x2 determinant for EVERY shift s (not only at one cutoff). -/
theorem toyNegativeResidue_det_two_neg (s : ℕ) :
    (sourceMomentMatrix toyNegResidue s 2).det < 0 := by
  rw [toyNegResidue, signedTwoMode_det_formula]
  norm_num

/-- Both scalar modes have positive zeroth moments; negativity is in
the second-order MICROCURVATURE rather than leading decay. -/
theorem toyNegativeResidue_first_moment_pos :
    0 < toyNegResidue 0 := by
  norm_num [toyNegResidue, signedTwoMode]


/-- Despite its negative second-order Hankel pivots, the signed toy
still has STRICTLY POSITIVE individual scalar moments at every shift. -/
theorem toyNegativeResidue_all_moments_pos (s : ℕ) :
    0 < toyNegResidue s := by
  have ht : (1 / 4 : ℝ) ^ (s+1) < (1 / 2 : ℝ) ^ (s+1) := by
    gcongr
    norm_num
  dsimp [toyNegResidue, signedTwoMode]
  linarith

end
end CarryWheelNativeSignedGate
