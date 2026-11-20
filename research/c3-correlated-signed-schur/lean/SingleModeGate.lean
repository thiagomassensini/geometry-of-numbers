import Mathlib

/-!
A scalar enough-for-positivity gate. Projection control u² ≤ h R
comes from Cauchy–Schwarz on the *old shifted* PSD prefix, not from
a hypothetical positive representation of the completed native kernel.
-/
namespace TiltSchurSingleMode
noncomputable section

theorem single_mode_positive
    (alpha beta B a p R u h : ℝ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hh : 0 < h)
    (hProjection : u^2 ≤ h*R)
    (hBudget : h*(alpha*|B|+beta*|a*p|) < 4*u^2) :
    0 < alpha*B - beta*a*p + 4*R := by
  have hCost : h*(alpha*|B|+beta*|a*p|) < h*(4*R) := by
    nlinarith [hProjection]
  have hMargin : alpha*|B|+beta*|a*p| < 4*R := by
    nlinarith [hCost, hh]
  have h1 : -|B| ≤ B := neg_abs_le B
  have h2 : a*p ≤ |a*p| := le_abs_self (a*p)
  have h1' := mul_le_mul_of_nonneg_left h1 hAlpha
  have h2' := mul_le_mul_of_nonneg_left h2 hBeta
  nlinarith

end
end TiltSchurSingleMode
