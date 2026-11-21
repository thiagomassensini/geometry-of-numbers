import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Tactic

/-!
# All consecutive shifted 2x2 windows PSD need NOT imply 3x3 Hankel PSD.

This is a generic LOG-CONVEX sequence, not the C2 native moments.
It supplies a concrete no-go for concluding all-order Hankel positivity
merely from the numerical observation that first NEGATIVE 2x2
window index escapes as the transverse displacement goes to zero.
-/

namespace CarryWheelNativeSignedGate

open CarrySelfAdjointOperator
open Matrix
open scoped Matrix

noncomputable section

def toyEveryTwoByTwoLogConvex (n : ℕ) : ℝ :=
  if n = 0 then 1 else
  if n = 1 then 1 else
  if n = 2 then 2 else
  if n = 3 then 5 else
  (63 / 5 : ℝ) * 3 ^ (n - 4)

private theorem toy_tail_formula (n : ℕ) (hn : 4 ≤ n) :
    toyEveryTwoByTwoLogConvex n = (63 / 5 : ℝ) * 3 ^ (n - 4) := by
  simp [toyEveryTwoByTwoLogConvex,
    show n ≠ 0 by omega,
    show n ≠ 1 by omega,
    show n ≠ 2 by omega,
    show n ≠ 3 by omega]

private theorem toy_tail_ratio (n : ℕ) (hn : 4 ≤ n) :
    toyEveryTwoByTwoLogConvex (n + 1) =
      3 * toyEveryTwoByTwoLogConvex n := by
  rw [toy_tail_formula (n+1) (by omega), toy_tail_formula n hn]
  have hh : n + 1 - 4 = (n - 4) + 1 := by omega
  rw [hh, pow_succ]
  ring

/-- Every shifted adjacent 2x2 determinant is NONNEGATIVE, in all
windows s≥0, without exception. -/
theorem toy_all_consecutive_two_by_two_minors_nonnegative (s : ℕ) :
    0 ≤ toyEveryTwoByTwoLogConvex s *
          toyEveryTwoByTwoLogConvex (s+2) -
        (toyEveryTwoByTwoLogConvex (s+1))^2 := by
  by_cases hs : s < 4
  · interval_cases s <;> norm_num [toyEveryTwoByTwoLogConvex]
  · have h4 : 4 ≤ s := by omega
    have ht1 := toy_tail_ratio s h4
    have ht2 := toy_tail_ratio (s+1) (by omega)
    have heq : s + 2 = (s + 1) + 1 := by omega
    rw [heq,ht2,ht1]
    nlinarith

/-- Nevertheless the ORIGINAL 3x3 unshifted Hankel determinant is
STRICTLY NEGATIVE. Thus the 2x2-window threshold law by itself
does not control every higher-dimensional Schur direction. -/
theorem toy_three_by_three_Hankel_det_negative :
    (sourceMomentMatrix toyEveryTwoByTwoLogConvex 0 3).det =
      (-2 / 5 : ℝ) := by
  norm_num [sourceMomentMatrix, toyEveryTwoByTwoLogConvex,
    Matrix.det_fin_three]

end
end CarryWheelNativeSignedGate
