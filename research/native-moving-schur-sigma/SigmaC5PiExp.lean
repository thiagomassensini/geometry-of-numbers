import SigmaC5PiInterval
import ZetaLean.IntervalCExp

/-!
# The π-dependent exponential in the original completion

This module connects the certified interval for `log π` to the exact
archimedean exponential factor used by `completedNativeOperatorCharacteristic`.
It leaves the source parameter as an arbitrary complex rectangle and delegates
only the final exponential enclosure to the existing `expCr` proof.
-/

namespace CarrySigmaObstruction

open ZetaLean
open ZetaLean.ComplexInterval

def c5PiLogComplexInterval (n : ℕ) : ComplexInterval :=
  { re := c5PiLogInterval n, im := Interval.exact 0 }

theorem c5_pi_log_complex_interval_contains (n : ℕ) :
    (c5PiLogComplexInterval n).contains (Real.log Real.pi : ℂ) := by
  constructor
  · rw [Complex.ofReal_re]
    exact c5_pi_log_interval_contains n
  · rw [Complex.ofReal_im]
    simpa [ComplexInterval.contains, c5PiLogComplexInterval] using
      (Interval.contains_exact (0 : ℚ))

def c5CompletionExponentBox (n : ℕ) (W : ComplexInterval) : ComplexInterval :=
  (ComplexInterval.smulQ (-1 / 2) W).mul (c5PiLogComplexInterval n)

theorem c5_completion_exponent_box_contains (n : ℕ)
    {W : ComplexInterval} {s : ℂ} (hW : W.contains s) :
    (c5CompletionExponentBox n W).contains
      (-(s / 2) * (Real.log Real.pi : ℂ)) := by
  have hscaled := ComplexInterval.contains_smulQ (q := (-1 / 2 : ℚ)) hW
  have hhalf : (ComplexInterval.smulQ (-1 / 2) W).contains (-(s / 2)) := by
    have hscalar : (((-1 / 2 : ℚ) : ℝ) : ℂ) = (-1 / 2 : ℂ) := by norm_num
    have hidentity : (-1 / 2 : ℂ) * s = -(s / 2) := by ring
    rw [hscalar, hidentity] at hscaled
    exact hscaled
  exact ComplexInterval.contains_mul hhalf (c5_pi_log_complex_interval_contains n)

theorem c5_completion_exp_interval_contains (nLog nExp p k : ℕ)
    (hnExp : 0 < nExp) {W : ComplexInterval} {s : ℂ}
    (hW : W.contains s)
    (hbound : normBound (c5CompletionExponentBox nLog W) ≤ 2 ^ k) :
    (expCr nExp p k (c5CompletionExponentBox nLog W)).contains
      (Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) := by
  exact ComplexInterval.contains_expCr nExp p hnExp k
    (c5CompletionExponentBox nLog W)
    (-(s / 2) * (Real.log Real.pi : ℂ))
    (c5_completion_exponent_box_contains nLog hW) hbound

end CarrySigmaObstruction
