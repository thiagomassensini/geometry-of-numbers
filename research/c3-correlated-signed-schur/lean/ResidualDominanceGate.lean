import Mathlib

/-!
Pure algebraic all-order SUFFICIENT gate for the original
Euler-Schur identity W = alpha*B - beta*a*p + 4*R.
No native positivity, Hessian positivity, or RH is assumed.
-/
namespace TiltSchurGate
noncomputable section

theorem positive_of_absolute_residual_dominance
    (alpha beta B a p R : ℝ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hMargin : alpha * |B| + beta * |a * p| < 4*R) :
    0 < alpha*B - beta*a*p + 4*R := by
  have h1 : -|B| ≤ B := neg_abs_le B
  have h2 : a*p ≤ |a*p| := le_abs_self (a*p)
  have h1' := mul_le_mul_of_nonneg_left h1 hAlpha
  have h2' := mul_le_mul_of_nonneg_left h2 hBeta
  nlinarith

theorem positive_of_absolute_residual_dominance_with_last_gap
    (alpha beta Bfloor a p R gap : ℝ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hGap : 0 ≤ gap)
    (hMargin : alpha * |Bfloor| + beta * |a*p| < 4*R) :
    0 < alpha*(Bfloor+gap) - beta*a*p + 4*R := by
  have h0 : 0 < alpha*Bfloor - beta*a*p + 4*R :=
    positive_of_absolute_residual_dominance alpha beta Bfloor a p R hAlpha hBeta hMargin
  have h1 : 0 ≤ alpha*gap := mul_nonneg hAlpha hGap
  nlinarith


/-- Certified-head transfer: if TFVD/Green supplies an error envelope for
the two actual original forms B and p, this inequality proves W>0.
The bounds are supplied as hypotheses; no Gram/sign is silently imported. -/
theorem positive_of_head_tail_budget
    (alpha beta a B p R Bhead phead errB errP : ℝ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hB : |B-Bhead| ≤ errB)
    (hP : |p-phead| ≤ errP)
    (hbudget : alpha*(|Bhead|+errB) +
        beta*|a| * (|phead|+errP) < 4*R) :
    0 < alpha*B - beta*a*p + 4*R := by
  have hBabs : |B| ≤ |Bhead|+errB := by
    calc
      |B| = |Bhead+(B-Bhead)| := by ring
      _ ≤ |Bhead| + |B-Bhead| := abs_add_le _ _
      _ ≤ |Bhead|+errB := by linarith
  have hPabs : |p| ≤ |phead|+errP := by
    calc
      |p| = |phead+(p-phead)| := by ring
      _ ≤ |phead| + |p-phead| := abs_add_le _ _
      _ ≤ |phead|+errP := by linarith
  have hProd : |a*p| ≤ |a| * (|phead|+errP) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hPabs (abs_nonneg a)
  have hmajor : alpha*|B|+beta*|a*p| ≤
        alpha*(|Bhead|+errB)+beta*|a| * (|phead|+errP) := by
    have hb := mul_le_mul_of_nonneg_left hBabs hAlpha
    have hp := mul_le_mul_of_nonneg_left hProd hBeta
    nlinarith
  exact positive_of_absolute_residual_dominance
    alpha beta B a p R hAlpha hBeta (lt_of_le_of_lt hmajor hbudget)

end
end TiltSchurGate
